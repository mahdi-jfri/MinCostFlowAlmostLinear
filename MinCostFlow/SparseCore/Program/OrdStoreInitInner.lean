module

public import MinCostFlow.SparseCore.Program.OrdStoreMoveUnlink
import Mathlib.Tactic

/-!
# Order Store Initialization: Inner Spine-Building Loop and Record Lemmas

This file provides:
* `flatMap_nodup_of_ordUnique` and `ordRecords_sum_len_le`, bounding the total number of ends
  across all records of a unique order by `2 * eCap`;
* `ordInitInnerLoop` and `ordInitInnerLoop_runs`, which builds a left-leaning splay spine for a
  single non-empty vertex record `[v, len, keys…]` in fresh sequential node slots `base + 1 .. base + len`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState MinCostFlow.DynSpanner.Program

/-- Inner loop of `ordStoreInit`: builds a left-leaning spine for `len` keys starting at `r8`,
allocating fresh sequential node IDs `r9 + 1, …, r9 + len` and populating `eNode`. -/
def ordInitInnerLoop : Stmt :=
  .loop (.bin .lt (.reg 14) (.reg 12))
    (.assign 15 (.load (.bin .add (.reg 8) (.reg 14))) ;;
     .assign 9 (.bin .add (.reg 9) (.const 1)) ;;
     .assign 16 (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 9))) ;;
     .store (.reg 16) (.reg 13) ;;
     .store (.bin .add (.reg 16) (.const 4)) (.bin .add (.reg 14) (.const 1)) ;;
     .store (.bin .add (.reg 16) (.const 5)) (.reg 15) ;;
     .cond (.reg 13)
       (.store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 13))) (.const 2)) (.reg 9))
       .nop ;;
     .store (.bin .add (.reg 5) (.reg 15)) (.reg 9) ;;
     .assign 13 (.reg 9) ;;
     .assign 14 (.bin .add (.reg 14) (.const 1)))

theorem ordInitInnerLoop_noRand : ordInitInnerLoop.NoRand := by
  simp [ordInitInnerLoop, Stmt.NoRand]

/-! ### Record list lemmas -/

theorem ordOfRecords_mem_of_nodup {recs : List (ℕ × List End)}
    (hnd : (recs.map Prod.fst).Nodup) {v : ℕ} {xs : List End} (hmem : (v, xs) ∈ recs) :
    ordOfRecords recs v = xs := by
  induction recs with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    rcases hd with ⟨u, ys⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at hmem
    rcases hmem with h1 | h2
    · rcases Prod.mk.inj h1 with ⟨rfl, rfl⟩
      simp [ordOfRecords]
    · have huv : u ≠ v := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨(v, xs), h2, rfl⟩)
      simp only [ordOfRecords, List.find?_cons, beq_eq_false_iff_ne.mpr huv]
      exact ih hnd.2 h2

theorem flatMap_nodup_of_ordUnique {vCap eCap : ℕ} :
    ∀ recs : List (ℕ × List End), (recs.map Prod.fst).Nodup →
      OrdUniqueWithin vCap eCap (ordOfRecords recs) →
      (recs.flatMap Prod.snd).Nodup ∧ ∀ x ∈ recs.flatMap Prod.snd, endKey x < 2 * eCap
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | (v, xs) :: tl, hnd, huniq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hord_v : ordOfRecords ((v, xs) :: tl) v = xs := by simp [ordOfRecords]
    have htl_eq : ∀ u, u ≠ v → ordOfRecords ((v, xs) :: tl) u = ordOfRecords tl u := fun u hu => by
      simp [ordOfRecords, beq_eq_false_iff_ne.mpr (Ne.symm hu)]
    have htl_v : ordOfRecords tl v = [] := by
      unfold ordOfRecords
      cases hf : tl.find? (fun p => p.1 == v) with
      | none => rfl
      | some p =>
        exfalso
        have hp1 := List.mem_of_find?_eq_some hf
        have hp2 : p.1 = v := by simpa using List.find?_some hf
        exact hnd.1 (hp2 ▸ List.mem_map.mpr ⟨p, hp1, rfl⟩)
    have huniq_tl : OrdUniqueWithin vCap eCap (ordOfRecords tl) := by
      refine ⟨⟨fun u => ?_, fun u hu => ?_, fun u x hx => ?_⟩, fun u1 u2 x h1 h2 => ?_⟩
      · by_cases h : u = v
        · subst h; rw [htl_v]; exact List.nodup_nil
        · rw [← htl_eq u h]; exact huniq.nodup u
      · by_cases h : u = v
        · subst h; exact htl_v
        · rw [← htl_eq u h]; exact huniq.eq_nil_of_ge hu
      · by_cases h : u = v
        · subst h; rw [htl_v] at hx; exact absurd hx List.not_mem_nil
        · rw [← htl_eq u h] at hx; exact huniq.edge_lt hx
      · have h1v : u1 ≠ v := fun h => by subst h; rw [htl_v] at h1; exact List.not_mem_nil h1
        have h2v : u2 ≠ v := fun h => by subst h; rw [htl_v] at h2; exact List.not_mem_nil h2
        rw [← htl_eq u1 h1v] at h1; rw [← htl_eq u2 h2v] at h2
        exact huniq.unique_v h1 h2
    obtain ⟨htl_nd, htl_lt⟩ := flatMap_nodup_of_ordUnique tl hnd.2 huniq_tl
    have hxs_nd : xs.Nodup := hord_v ▸ huniq.nodup v
    have hxs_lt : ∀ x ∈ xs, endKey x < 2 * eCap := fun x hx =>
      huniq.key_lt (hord_v.symm ▸ hx)
    refine ⟨?_, ?_⟩
    · simp only [List.flatMap_cons, List.nodup_append]
      refine ⟨hxs_nd, htl_nd, fun a ha b hb hab => ?_⟩
      subst hab
      rw [List.mem_flatMap] at hb
      rcases hb with ⟨⟨u, ys⟩, hu_mem, ha_ys⟩
      have huv : v ≠ u := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨(u, ys), hu_mem, rfl⟩)
      have ha_u : a ∈ ordOfRecords ((v, xs) :: tl) u := by
        rw [htl_eq u (Ne.symm huv), ordOfRecords_mem_of_nodup hnd.2 hu_mem]; exact ha_ys
      exact huv (huniq.unique_v (hord_v.symm ▸ ha) ha_u)
    · intro x hx
      simp only [List.flatMap_cons, List.mem_append] at hx
      rcases hx with h1 | h2
      · exact hxs_lt x h1
      · exact htl_lt x h2

theorem ordRecords_sum_len_le {vCap eCap : ℕ} {recs : List (ℕ × List End)}
    (hnd : (recs.map Prod.fst).Nodup)
    (huniq : OrdUniqueWithin vCap eCap (ordOfRecords recs)) :
    (recs.map fun r => r.2.length).sum ≤ 2 * eCap := by
  obtain ⟨hnd_fm, hlt_fm⟩ := flatMap_nodup_of_ordUnique recs hnd huniq
  have hlen : (recs.map fun r => r.2.length).sum = (recs.flatMap Prod.snd).length := by
    induction recs with
    | nil => simp
    | cons hd tl ih => simp [List.flatMap_cons, ih]
  rw [hlen]
  have hinj : Function.Injective endKey := fun a b h => by
    have := congrArg endOfKey h; simpa [endOfKey_endKey] using this
  have hnd_keys : ((recs.flatMap Prod.snd).map endKey).Nodup := hnd_fm.map hinj
  have hsub : ((recs.flatMap Prod.snd).map endKey).toFinset ⊆ Finset.range (2 * eCap) := by
    intro k hk
    rw [List.mem_toFinset, List.mem_map] at hk
    rcases hk with ⟨x, hx, rfl⟩
    exact Finset.mem_range.mpr (hlt_fm x hx)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd_keys, List.length_map, Finset.card_range] at hcard
  exact hcard

/-! ### Inner loop verification -/

theorem ordInitInnerLoop_runs
    {w b vCap eCap ptr len base : ℕ} {p : Program} (ω : ℕ → Bool)
    {st0 : State} {sp0 : SplayState ℕ Unit Unit} {eN0 : ℕ → ℕ}
    (hlen : 0 < len) (hbase : base + len ≤ 2 * eCap)
    (hptr_lt : ptr + len ≤ b)
    (hkeys_lt : ∀ j < len, st0.mem (ptr + j) < 2 * eCap)
    (hkeys_nd : (readList st0.mem ptr len).Nodup)
    (hnodes : OrdNodesAt st0.mem (ordNodesBase b vCap eCap) base sp0 (fun _ => 0))
    (hzero_nd : ∀ u, base < u → u ≤ base + len →
      ∀ o < 8, st0.mem (ordNodesBase b vCap eCap + 8 * u + o) = 0)
    (hen_at : ∀ k < 2 * eCap, st0.mem (ordENodeBase b vCap + k) = eN0 k)
    (hclean : ∀ u, (sp0.nodes u).rev = false) (hnull : sp0.nodes 0 = ordNullNode)
    (hw : b + ordArenaSize vCap eCap < 2 ^ w) :
    st0.regs 5 = ordENodeBase b vCap → st0.regs 6 = ordNodesBase b vCap eCap →
    st0.regs 8 = ptr → st0.regs 9 = base → st0.regs 12 = len →
    st0.regs 13 = 0 → st0.regs 14 = 0 →
    let ids : List ℕ := (List.range len).map (fun j => base + 1 + j)
    let t : AuxTree := leftSpine ids
    ∃ st' c, ∃ sp' : SplayState ℕ Unit Unit, ∃ eN' : ℕ → ℕ,
      Runs w p ω ordInitInnerLoop st0 .normal st' c ∧
      (∀ r, r ≠ 9 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → st'.regs r = st0.regs r) ∧
      st'.regs 9 = base + len ∧ st'.regs 13 = t.rootId ∧
      OrdNodesAt st'.mem (ordNodesBase b vCap eCap) (base + len) sp' (fun _ => 0) ∧
      (∀ k < 2 * eCap, st'.mem (ordENodeBase b vCap + k) = eN' k) ∧
      (∀ a, ¬ (ordNodesBase b vCap eCap + 8 * (base + 1) ≤ a ∧
               a < ordNodesBase b vCap eCap + 8 * (base + len + 1)) →
            ¬ (ordENodeBase b vCap ≤ a ∧ a < ordENodeBase b vCap + 2 * eCap) →
            st'.mem a = st0.mem a) ∧
      OrdTreeOk (base + len) sp' t ∧
      (∀ u, u ≤ base → sp'.nodes u = sp0.nodes u) ∧
      (∀ j < len, (sp'.nodes (base + 1 + j)).val = st0.mem (ptr + j)) ∧
      (∀ k < 2 * eCap,
        eN' k = match (List.range len).find? (fun j => st0.mem (ptr + j) == k) with
                | some j => base + 1 + j
                | none => eN0 k) ∧
      c ≤ 120 * len + 15 := by
  intro r5 r6 r8 r9 r12 r13 r14
  dsimp only
  set nb := ordNodesBase b vCap eCap with hnb
  set en := ordENodeBase b vCap with hen
  have hw' : b + (16 + vCap + 18 * eCap) < 2 ^ w := hw
  have hnb_end : nb + 8 * (2 * eCap + 1) ≤ b + ordArenaSize vCap eCap := by
    rw [hnb]; unfold ordNodesBase ordArenaSize; omega
  have hnb_ge : b + 8 + vCap + 2 * eCap = nb := by rw [hnb]; unfold ordNodesBase; omega
  have hen_ge : b + 8 + vCap = en := by rw [hen]; unfold ordENodeBase; omega
  have hloop : ∀ rem (j : ℕ) (st : State) (sp : SplayState ℕ Unit Unit) (eN : ℕ → ℕ),
      j + rem = len →
      st.regs 5 = en → st.regs 6 = nb → st.regs 8 = ptr →
      st.regs 9 = base + j → st.regs 12 = len →
      st.regs 13 = (leftSpine ((List.range j).map (fun i => base + 1 + i))).rootId →
      st.regs 14 = j →
      OrdNodesAt st.mem nb (base + j) sp (fun _ => 0) →
      (∀ u, base + j < u → u ≤ base + len → ∀ o < 8, st.mem (nb + 8 * u + o) = 0) →
      (∀ k < 2 * eCap, st.mem (en + k) = eN k) →
      (∀ a, ¬ (nb + 8 * (base + 1) ≤ a ∧ a < nb + 8 * (base + len + 1)) →
            ¬ (en ≤ a ∧ a < en + 2 * eCap) → st.mem a = st0.mem a) →
      OrdTreeOk (base + j) sp (leftSpine ((List.range j).map (fun i => base + 1 + i))) →
      (leftSpine ((List.range j).map (fun i => base + 1 + i)) ≠ .leaf →
        (sp.nodes (leftSpine ((List.range j).map (fun i => base + 1 + i))).rootId).ppar = 0) →
      (∀ u, u ≤ base → sp.nodes u = sp0.nodes u) →
      (∀ i < j, (sp.nodes (base + 1 + i)).val = st0.mem (ptr + i)) →
      (∀ k < 2 * eCap,
        eN k = match (List.range j).find? (fun i => st0.mem (ptr + i) == k) with
               | some i => base + 1 + i
               | none => eN0 k) →
      ∃ st' c, ∃ sp' : SplayState ℕ Unit Unit, ∃ eN' : ℕ → ℕ,
        Runs w p ω ordInitInnerLoop st .normal st' c ∧
        (∀ r, r ≠ 9 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → st'.regs r = st.regs r) ∧
        st'.regs 9 = base + len ∧
        st'.regs 13 = (leftSpine ((List.range len).map (fun i => base + 1 + i))).rootId ∧
        OrdNodesAt st'.mem nb (base + len) sp' (fun _ => 0) ∧
        (∀ k < 2 * eCap, st'.mem (en + k) = eN' k) ∧
        (∀ a, ¬ (nb + 8 * (base + 1) ≤ a ∧ a < nb + 8 * (base + len + 1)) →
              ¬ (en ≤ a ∧ a < en + 2 * eCap) → st'.mem a = st0.mem a) ∧
        OrdTreeOk (base + len) sp' (leftSpine ((List.range len).map (fun i => base + 1 + i))) ∧
        (∀ u, u ≤ base → sp'.nodes u = sp0.nodes u) ∧
        (∀ i < len, (sp'.nodes (base + 1 + i)).val = st0.mem (ptr + i)) ∧
        (∀ k < 2 * eCap,
          eN' k = match (List.range len).find? (fun i => st0.mem (ptr + i) == k) with
                  | some i => base + 1 + i
                  | none => eN0 k) ∧
        c ≤ 120 * rem + 15 := by
    intro rem
    induction rem with
    | zero =>
      intro j st sp eN hj m5 m6 m8 m9 m12 m13 m14 hn hz he hfr hok _ hout hval henf
      have hj_eq : j = len := by omega
      subst hj_eq
      have hcond : (Expr.bin .lt (.reg 14) (.reg 12)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq m14) (Expr.eval_reg_of_eq m12) (by omega) (by omega)
      refine ⟨st, _, sp, eN, ord_runs_loop_false hcond, fun _ _ _ _ _ _ => rfl, m9, m13,
        hn, he, hfr, hok, hout, hval, henf, by simp [Expr.size_bin, Expr.size_reg]⟩
    | succ rem ih =>
      intro j st sp eN hj m5 m6 m8 m9 m12 m13 m14 hn hz he hfr hok hpp hout hval henf
      have hj_lt : j < len := by omega
      have hcond : (Expr.bin .lt (.reg 14) (.reg 12)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq m14) (Expr.eval_reg_of_eq m12) hj_lt (by omega)
      set k := st0.mem (ptr + j) with hk_def
      have hk_lt : k < 2 * eCap := hkeys_lt j hj_lt
      have hm_ptr_j : st.mem (ptr + j) = k :=
        hfr (ptr + j) (by omega) (by omega)
      set u := base + 1 + j with hu_def
      set prevT := leftSpine ((List.range j).map (fun i => base + 1 + i)) with hprevT_def
      have ha15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 8) (.reg 14)))) st .normal
          { st with regs := Function.update st.regs 15 k } _ :=
        runs_assign_iff.mpr ⟨k, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq m8)
          (Expr.eval_reg_of_eq m14) (by omega)) hm_ptr_j, rfl, rfl, rfl⟩
      set st1 : State := { st with regs := Function.update st.regs 15 k }
      have ha9 : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) st1 .normal
          { st1 with regs := Function.update st1.regs 9 u } _ :=
        runs_assign_iff.mpr ⟨u, by
          have h1 : (Expr.bin .add (.reg 9) (.const 1)).eval w st1 = some (base + j + 1) :=
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, m9])) (Expr.eval_const (by omega)) (by omega)
          rwa [show base + j + 1 = u by omega] at h1, rfl, rfl, rfl⟩
      set st2 : State := { st1 with regs := Function.update st1.regs 9 u }
      have ha16 : Runs w p ω (.assign 16 (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 9)))) st2 .normal
          { st2 with regs := Function.update st2.regs 16 (nb + 8 * u) } _ :=
        runs_assign_iff.mpr ⟨nb + 8 * u, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, m6]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st2])) (by omega)) (by omega),
          rfl, rfl, rfl⟩
      set st3 : State := { st2 with regs := Function.update st2.regs 16 (nb + 8 * u) }
      have hs1 : Runs w p ω (.store (.reg 16) (.reg 13)) st3 .normal
          { st3 with mem := Function.update st.mem (nb + 8 * u) prevT.rootId } _ :=
        runs_store_iff.mpr ⟨nb + 8 * u, prevT.rootId, Expr.eval_reg_of_eq (by simp [st3]),
          Expr.eval_reg_of_eq (by simp [st3, st2, st1, m13, hprevT_def]), rfl, rfl, rfl⟩
      set m1 := Function.update st.mem (nb + 8 * u) prevT.rootId
      set st4 : State := { st3 with mem := m1 }
      have hs2 : Runs w p ω (.store (.bin .add (.reg 16) (.const 4)) (.bin .add (.reg 14) (.const 1))) st4 .normal
          { st4 with mem := Function.update m1 (nb + 8 * u + 4) (j + 1) } _ :=
        runs_store_iff.mpr ⟨nb + 8 * u + 4, j + 1,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3])) (Expr.eval_const (by omega)) (by omega),
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, m14])) (Expr.eval_const (by omega)) (by omega),
          rfl, rfl, rfl⟩
      set m2 := Function.update m1 (nb + 8 * u + 4) (j + 1)
      set st5 : State := { st4 with mem := m2 }
      have hs3 : Runs w p ω (.store (.bin .add (.reg 16) (.const 5)) (.reg 15)) st5 .normal
          { st5 with mem := Function.update m2 (nb + 8 * u + 5) k } _ :=
        runs_store_iff.mpr ⟨nb + 8 * u + 5, k,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3])) (Expr.eval_const (by omega)) (by omega),
          Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1]), rfl, rfl, rfl⟩
      set m3 := Function.update m2 (nb + 8 * u + 5) k
      set st6 : State := { st5 with mem := m3 }
      set ndU : SplayNode ℕ Unit Unit :=
        { left := prevT.rootId, right := 0, par := 0, ppar := 0, sz := j + 1, val := k, sum := (), tag := (), rev := false }
      set spA : SplayState ℕ Unit Unit := sp.updateNode u (fun _ => ndU)
      have hnA : OrdNodesAt m3 nb u spA (fun _ => 0) := by
        intro x hx
        by_cases hxu : x = u
        · subst hxu
          have hz_u := hz u (by omega) (by omega)
          refine ⟨by simp only [m3, m2, m1, spA, ndU, SplayState.nodes_updateNode, ordNodeAddr, ite_true, Nat.add_zero]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
            by simp only [m3, m2, m1, spA, ndU, SplayState.nodes_updateNode, ordNodeAddr, ite_true]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz_u 1 (by omega),
            by simp only [m3, m2, m1, spA, ndU, SplayState.nodes_updateNode, ordNodeAddr, ite_true]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz_u 2 (by omega),
            by simp only [m3, m2, m1, spA, ndU, SplayState.nodes_updateNode, ordNodeAddr, ite_true]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz_u 3 (by omega),
            by simp only [m3, m2, m1, spA, ndU, SplayState.nodes_updateNode, ordNodeAddr, ite_true]; rw [Function.update_of_ne (by omega), Function.update_self],
            by simp only [m3, m2, m1, spA, ndU, SplayState.nodes_updateNode, ordNodeAddr, ite_true]; rw [Function.update_self],
            by simp only [m3, m2, m1, ordNodeAddr]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz_u 6 (by omega),
            by simp only [m3, m2, m1, ordNodeAddr]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz_u 7 (by omega)⟩
        · have hle : x ≤ base + j := by omega
          have hnx := hn x hle
          have hupd : ∀ o < 8, m3 (ordNodeAddr nb x + o) = st.mem (ordNodeAddr nb x + o) := fun o ho => by
            dsimp only [m3, m2, m1, ordNodeAddr]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          have hsp_x : spA.nodes x = sp.nodes x := by simp [spA, SplayState.nodes_updateNode, hxu]
          rw [hsp_x]
          exact ⟨(hupd 0 (by omega)).trans hnx.1, (hupd 1 (by omega)).trans hnx.2.1,
            (hupd 2 (by omega)).trans hnx.2.2.1, (hupd 3 (by omega)).trans hnx.2.2.2.1,
            (hupd 4 (by omega)).trans hnx.2.2.2.2.1, (hupd 5 (by omega)).trans hnx.2.2.2.2.2.1,
            (hupd 6 (by omega)).trans hnx.2.2.2.2.2.2.1, (hupd 7 (by omega)).trans hnx.2.2.2.2.2.2.2⟩
      set sp1 : SplayState ℕ Unit Unit := if prevT.rootId = 0 then spA else spA.setPar prevT.rootId u
      have hprev_le : prevT.rootId ≤ base + j := by
        cases hpt : prevT with
        | leaf => simp [AuxTree.rootId]
        | node pid pl pr => exact hok.mem_le pid (by rw [hpt]; exact AuxTree.rootId_mem (t := .node pid pl pr) (by simp))
      have hcondP : ∃ m4 cP,
          Runs w p ω (.cond (.reg 13)
            (.store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 13))) (.const 2)) (.reg 9)) .nop)
            st6 .normal { st6 with mem := m4 } cP ∧
          OrdNodesAt m4 nb u sp1 (fun _ => 0) ∧
          (∀ a, a ≠ nb + 8 * prevT.rootId + 2 → m4 a = m3 a) ∧
          (prevT.rootId = 0 → m4 = m3) ∧ cP ≤ 30 := by
        by_cases hP0 : prevT.rootId = 0
        · have hc : (Expr.reg 13).eval w st6 = some 0 := Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1, m13]; exact hP0)
          refine ⟨m3, _, ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
            by simp [sp1, hP0, hnA], fun _ _ => rfl, fun _ => rfl, by simp [Expr.size_reg]⟩
        · have hc : (Expr.reg 13).eval w st6 = some prevT.rootId := Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1, m13, hprevT_def])
          have hst : Runs w p ω
              (.store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 13))) (.const 2)) (.reg 9))
              st6 .normal { st6 with mem := Function.update m3 (nb + 8 * prevT.rootId + 2) u } _ :=
            runs_store_iff.mpr ⟨nb + 8 * prevT.rootId + 2, u,
              Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1, m6]))
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1, m13, hprevT_def])) (by omega)) (by omega))
                (Expr.eval_const (by omega)) (by omega),
              Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2]), rfl, rfl, rfl⟩
          refine ⟨_, _, ord_runs_cond_true hc hP0 hst,
            by simp only [sp1, hP0, ite_false]; exact hnA.setPar (by omega) (v := u),
            fun a ha => Function.update_of_ne ha _ _, fun h => absurd h hP0,
            by simp [Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
      obtain ⟨m4, cP, hrunP, hn4, hm4_out, hm4_zero, hcP⟩ := hcondP
      set st7 : State := { st6 with mem := m4 }
      have hs4 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 15)) (.reg 9)) st7 .normal
          { st7 with mem := Function.update m4 (en + k) u } _ :=
        runs_store_iff.mpr ⟨en + k, u, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, st3, st2, st1, m5]))
          (Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, st3, st2, st1])) (by omega),
          Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, st3, st2]), rfl, rfl, rfl⟩
      set m5' := Function.update m4 (en + k) u
      set st8 : State := { st7 with mem := m5' }
      have ha13 : Runs w p ω (.assign 13 (.reg 9)) st8 .normal
          { st8 with regs := Function.update st8.regs 13 u } _ :=
        runs_assign_iff.mpr ⟨u, Expr.eval_reg_of_eq (by simp [st8, st7, st6, st5, st4, st3, st2]), rfl, rfl, rfl⟩
      set st9 : State := { st8 with regs := Function.update st8.regs 13 u }
      have ha14 : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.const 1))) st9 .normal
          { st9 with regs := Function.update st9.regs 14 (j + 1) } _ :=
        runs_assign_iff.mpr ⟨j + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st9, st8, st7, st6, st5, st4, st3, st2, st1, m14]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st10 : State := { st9 with regs := Function.update st9.regs 14 (j + 1) }
      have hnextT_eq : leftSpine ((List.range (j + 1)).map (fun i => base + 1 + i)) = .node u prevT .leaf := by
        rw [List.range_succ, List.map_append, List.map_singleton, leftSpine_append_singleton]
      have hprev_gt : prevT.rootId ≠ 0 → base + 1 ≤ prevT.rootId := fun hP0 => by
        cases hpt : prevT with
        | leaf => simp [hpt, AuxTree.rootId] at hP0
        | node pid pl pr =>
          have hmem : pid ∈ prevT.toList := by rw [hpt]; exact AuxTree.rootId_mem (t := .node pid pl pr) (by simp)
          rw [hprevT_def, leftSpine_toList, List.mem_map] at hmem
          rcases hmem with ⟨i, _, rfl⟩; simp only [hpt, AuxTree.rootId]; omega
      have hsp1_out : ∀ x, x ≠ u → x ≠ prevT.rootId → sp1.nodes x = sp.nodes x := fun x h1 h2 => by
        dsimp only [sp1, spA]; split_ifs <;> simp [SplayState.setPar, SplayState.nodes_updateNode, h1, h2]
      have hsp1_u : sp1.nodes u = ndU := by
        dsimp only [sp1, spA]; split_ifs with hP0
        · simp [SplayState.nodes_updateNode]
        · simp [SplayState.setPar, SplayState.nodes_updateNode, show u ≠ prevT.rootId by omega]
      have hsp1_p : prevT.rootId ≠ 0 → sp1.nodes prevT.rootId = { (sp.nodes prevT.rootId) with par := u } := fun hP0 => by
        dsimp only [sp1, spA]; simp [hP0, SplayState.setPar, SplayState.nodes_updateNode, show prevT.rootId ≠ u by omega]
      have h0_sp1 : sp1.nodes 0 = ordNullNode := by
        by_cases hP0 : prevT.rootId = 0
        · dsimp only [sp1, spA]; simp [hP0, SplayState.nodes_updateNode, show (0 : ℕ) ≠ u by omega, hok.null_node]
        · rw [hsp1_out 0 (by omega) (Ne.symm hP0)]; exact hok.null_node
      have hcl_sp1 : ∀ x, (sp1.nodes x).rev = false := fun x => by
        by_cases h1 : x = u
        · rw [h1, hsp1_u]
        · by_cases h2 : x = prevT.rootId
          · by_cases hP0 : prevT.rootId = 0
            · rw [h2, hP0, h0_sp1]; rfl
            · rw [h2, hsp1_p hP0]; exact hok.clean _
          · rw [hsp1_out x h1 h2]; exact hok.clean x
      have hsub_prev' : SplayState.SubtreeInv ordPayload sp1 u prevT := by
        cases hpt : prevT with
        | leaf => trivial
        | node pid pl pr =>
          rcases hpt ▸ hok.inv.sub with ⟨hpid_nz, hpl, hpr, -, -, hpsz, -, hsubL, hsubR⟩
          rcases AuxTree.nodup_node_unfold (hpt ▸ hok.inv.nodup) with ⟨_, hpid_l, _, hpid_r, _⟩
          have hnd_p := hsp1_p (by rw [hpt, AuxTree.rootId]; exact hpid_nz)
          simp only [hpt, AuxTree.rootId] at hnd_p
          refine ⟨hpid_nz, by rw [hnd_p]; exact hpl, by rw [hnd_p]; exact hpr,
            by rw [hnd_p], fun _ => by rw [hnd_p]; have := hpp (by rw [hpt]; simp); simpa [hpt, AuxTree.rootId] using this,
            by rw [hnd_p]; exact hpsz, rfl,
            SplayState.SubtreeInv_agree hsubL (fun x hx => by
              have hx_le := hok.mem_le x (by rw [hpt]; exact List.mem_append_left _ (List.mem_append_left _ hx))
              exact (hsp1_out x (by omega) (by rw [hpt, AuxTree.rootId]; exact fun h => hpid_l (h ▸ hx))).symm),
            SplayState.SubtreeInv_agree hsubR (fun x hx => by
              have hx_le := hok.mem_le x (by rw [hpt]; exact List.mem_append_right _ hx)
              exact (hsp1_out x (by omega) (by rw [hpt, AuxTree.rootId]; exact fun h => hpid_r (h ▸ hx))).symm)⟩
      have hok1 : OrdTreeOk (base + (j + 1)) sp1 (leftSpine ((List.range (j + 1)).map (fun i => base + 1 + i))) := by
        rw [hnextT_eq]
        refine
          { null_node := h0_sp1
            clean := hcl_sp1
            inv := ⟨by
              rw [← hnextT_eq, leftSpine_toList]
              exact List.nodup_range.map (fun a b h => by omega),
              ⟨by omega, by rw [hsp1_u], by rw [hsp1_u]; rfl, by rw [hsp1_u], fun h => absurd rfl h,
               by rw [hsp1_u]; simp [ndU, AuxTree.countNodes, prevT, leftSpine_countNodes]; omega,
               rfl, hsub_prev', trivial⟩⟩
            mem_le := fun x hx => by
              rw [← hnextT_eq, leftSpine_toList, List.mem_map] at hx
              rcases hx with ⟨i, hi, rfl⟩; rw [List.mem_range] at hi; omega
            count_le := by
              rw [← hnextT_eq, leftSpine_countNodes, List.length_map, List.length_range]; omega }
      have hm5_en : ∀ k' < 2 * eCap, m5' (en + k') = Function.update eN k u k' := fun k' hk' => by
        dsimp only [m5']
        by_cases hkk : k' = k
        · subst hkk; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne hkk]
          rw [hm4_out (en + k') (by omega)]; dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact he k' hk'
      have henf1 : ∀ k' < 2 * eCap, Function.update eN k u k' =
          match (List.range (j + 1)).find? (fun i => st0.mem (ptr + i) == k') with
          | some i => base + 1 + i
          | none => eN0 k' := fun k' hk' => by
        rw [List.range_succ, List.find?_append]
        have hprev_k : (List.range j).find? (fun i => st0.mem (ptr + i) == k) = none := by
          cases hf : (List.range j).find? (fun i => st0.mem (ptr + i) == k) with
          | none => rfl
          | some i =>
            exfalso
            have hi_r := List.mem_range.mp (List.mem_of_find?_eq_some hf)
            have hi_eq : st0.mem (ptr + i) = k := by simpa using List.find?_some hf
            have h1 := readList_getElem st0.mem ptr len i (by rw [readList_length]; omega)
            have h2 := readList_getElem st0.mem ptr len j (by rw [readList_length]; omega)
            have hinj := List.nodup_iff_injective_getElem.mp hkeys_nd
            have hfin : (⟨i, by rw [readList_length]; omega⟩ : Fin (readList st0.mem ptr len).length) =
                ⟨j, by rw [readList_length]; omega⟩ := hinj (by dsimp only; rw [h1, h2, hi_eq, hk_def])
            have : i = j := Fin.mk_eq_mk.mp hfin; omega
        by_cases hkk : k' = k
        · subst hkk; rw [Function.update_self, hprev_k]; simp [hk_def, hu_def]
        · rw [Function.update_of_ne hkk, henf k' hk']
          cases (List.range j).find? (fun i => st0.mem (ptr + i) == k') with
          | some i => rfl
          | none =>
            have hne_b : (st0.mem (ptr + j) == k') = false :=
              beq_eq_false_iff_ne.mpr (by rw [← hk_def]; exact Ne.symm hkk)
            simp [List.find?_cons, hne_b]
      have hn10 : OrdNodesAt st10.mem nb (base + (j + 1)) sp1 (fun _ => 0) := by
        rw [show base + (j + 1) = u by omega]
        exact hn4.congr fun a ha => by
          dsimp only [st10, st9, st8, m5']
          rw [Function.update_of_ne (by unfold InOrdNodes at ha; omega)]
      obtain ⟨stF, cF, spF, eNF, hrunF, hregF, r9F, r13F, hnF, heF, hfrF, hokF, houtF, hvalF, henfF, hcF⟩ :=
        ih (j + 1) st10 sp1 (Function.update eN k u) (by omega)
          (by simp [st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, m5])
          (by simp [st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, m6])
          (by simp [st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, m8])
          (by simp [st10, st9, st8, st7, st6, st5, st4, st3, st2, hu_def]; omega)
          (by simp [st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, m12])
          (by simp [st10, st9, hnextT_eq, AuxTree.rootId])
          (by simp [st10]) hn10
          (fun x hx1 hx2 o ho => by
            dsimp only [st10, st9, st8, m5']
            rw [Function.update_of_ne (by omega), hm4_out _ (by omega)]
            dsimp only [m3, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hz x (by omega) hx2 o ho)
          hm5_en
          (fun a ha1 ha2 => by
            dsimp only [st10, st9, st8, m5']
            rw [Function.update_of_ne (by omega)]
            have hm4_a : m4 a = m3 a := by
              by_cases hP0 : prevT.rootId = 0
              · rw [hm4_zero hP0]
              · have := hprev_gt hP0; exact hm4_out a (by omega)
            rw [hm4_a]; dsimp only [m3, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfr a ha1 ha2)
          hok1
          (fun _ => by rw [hnextT_eq, AuxTree.rootId, hsp1_u])
          (fun x hx => by
            by_cases hP0 : prevT.rootId = 0
            · dsimp only [sp1, spA]; simp [hP0, SplayState.nodes_updateNode, show x ≠ u by omega]; exact hout x hx
            · have := hprev_gt hP0; rw [hsp1_out x (by omega) (by omega)]; exact hout x hx)
          (fun i hi => by
            by_cases hij : i = j
            · subst hij; rw [← hu_def, hsp1_u]
            · have hi' : i < j := by omega
              have hne_u : base + 1 + i ≠ u := by omega
              by_cases hp : base + 1 + i = prevT.rootId
              · by_cases hP0 : prevT.rootId = 0
                · omega
                · rw [hp, hsp1_p hP0, ← hp]; exact hval i hi'
              · rw [hsp1_out _ hne_u hp]; exact hval i hi')
          henf1
      refine ⟨stF, _, spF, eNF,
        ord_runs_loop_true hcond Nat.one_ne_zero
          (ord_runs_seq_normal ha15 (ord_runs_seq_normal ha9 (ord_runs_seq_normal ha16
            (ord_runs_seq_normal hs1 (ord_runs_seq_normal hs2 (ord_runs_seq_normal hs3
              (ord_runs_seq_normal hrunP (ord_runs_seq_normal hs4 (ord_runs_seq_normal ha13 ha14))))))))) hrunF,
        fun r h9 h13 h14 h15 h16 => by
          rw [hregF r h9 h13 h14 h15 h16]; simp [st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, h9, h13, h14, h15, h16],
        r9F, r13F, hnF, heF, hfrF, hokF, houtF, hvalF, henfF, ?_⟩
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
      omega
  exact hloop len 0 st0 sp0 eN0 (by omega) r5 r6 r8 r9 r12
    (by simpa [leftSpine, AuxTree.rootId] using r13) r14 hnodes hzero_nd hen_at
    (fun _ _ _ => rfl)
    { null_node := hnull, clean := hclean, inv := ⟨List.nodup_nil, trivial⟩,
      mem_le := fun _ h => absurd h List.not_mem_nil, count_le := by simp [leftSpine, AuxTree.countNodes] }
    (fun h => absurd rfl h) (fun _ _ => rfl) (fun _ hi => by omega) (fun _ _ => rfl)

end MinCostFlow.SparseCore.Program
