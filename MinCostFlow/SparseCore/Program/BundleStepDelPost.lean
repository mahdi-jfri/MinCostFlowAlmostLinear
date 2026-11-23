module

public import MinCostFlow.SparseCore.Program.BundleStepDelSlot

/-!
# Table postcondition assembly for Phase 1 deletion (`BundleStepDelPost`)

Proves `bundleStepDel_active_post`, assembling `BundleTableAfterDel`, `ListAt`, and external
memory framing after one active-edge deletion.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section

/-- Pure postcondition assembly for one active-edge deletion in Phase 1. -/
lemma bundleStepDel_active_post {slotCap vCap eCap tbl touchedBufPtr e p cap b1 b2 : ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {D : Finset ℕ} {touched : List ℕ} {js : Fin slotCap} {B₀ : BundleState}
    {L1 L2 : List ℕ} {mem0 mem1 mem2 memf : ℕ → ℕ}
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (he_lt : e < eCap) (hSjs : S₀ js = some B₀) (heB₀ : e ∈ B₀.edges) (he_not_D : e ∉ D)
    (hm_js : m.slotBlocks js = some (p, cap))
    (hafter : BundleTableAfterDel slotCap vCap eCap tbl S₀ D m touched mem0)
    (htouch_mem : ListAt mem0 touchedBufPtr touched)
    (hb1 : b1 = B₀.bundleOf (e, true)) (hb2 : b2 = B₀.bundleOf (e, false))
    (hL1_nd : L1.Nodup) (hL2_nd : L2.Nodup)
    (hL1_lt : ∀ k ∈ L1, k < 2 * eCap) (hL2_lt : ∀ k ∈ L2, k < 2 * eCap)
    (hL1_mem : ∀ k, k ∈ L1 ↔ endOfKey k ∈ ({ B₀ with edges := B₀.edges \ D } : BundleState).ends b1)
    (hL2_mem : ∀ k, k ∈ L2 ↔ endOfKey k ∈ ({ B₀ with edges := B₀.edges \ D } : BundleState).ends b2)
    (h1_dll : IsDoublyLinkedList mem1 (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (bsHeadBase p + b1) (2 * eCap) (L1.erase (2 * e)))
    (h1_sz : mem1 (bsSizeBase p cap + b1) = (L1.erase (2 * e)).length)
    (h1_par0 : L1.erase (2 * e) = [] → mem1 (bsParentBase p cap + b1) = B₀.parent b1)
    (h1_fr : ∀ a, a ≠ bsHeadBase p + b1 → a ≠ bsSizeBase p cap + b1 →
      a ≠ bsParentBase p cap + b1 →
      (∀ k ∈ L1, a ≠ btEndPrevBase tbl slotCap eCap + k ∧ a ≠ btEndNextBase tbl slotCap eCap + k) →
      mem1 a = mem0 a)
    (h2_dll : IsDoublyLinkedList mem2 (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (bsHeadBase p + b2) (2 * eCap)
      ((if b2 = b1 then L1.erase (2 * e) else L2).erase (2 * e + 1)))
    (h2_sz : mem2 (bsSizeBase p cap + b2) =
      ((if b2 = b1 then L1.erase (2 * e) else L2).erase (2 * e + 1)).length)
    (h2_par0 : (if b2 = b1 then L1.erase (2 * e) else L2).erase (2 * e + 1) = [] →
      mem2 (bsParentBase p cap + b2) = B₀.parent b2)
    (h2_fr : ∀ a, a ≠ bsHeadBase p + b2 → a ≠ bsSizeBase p cap + b2 →
      a ≠ bsParentBase p cap + b2 →
      (∀ k ∈ (if b2 = b1 then L1.erase (2 * e) else L2),
        a ≠ btEndPrevBase tbl slotCap eCap + k ∧ a ≠ btEndNextBase tbl slotCap eCap + k) →
      mem2 a = mem1 a)
    (hmemf_eq :
      let mem_t4 :=
        Function.update
          (Function.update
            (Function.update
              (Function.update mem2 (btEdgeSlotBase tbl slotCap + e) 0)
              (p + 2) ((B₀.edges \ D).card - 1))
            (btSlotDelNextBase tbl slotCap eCap + e)
            (mem0 (btSlotDelHeadBase tbl slotCap eCap + js.1)))
          (btSlotDelHeadBase tbl slotCap eCap + js.1) (e + 1)
      (js.1 ∈ touched → memf = mem_t4) ∧
      (js.1 ∉ touched → memf = Function.update
        (Function.update mem_t4 (btSlotTouchedBase tbl slotCap eCap + js.1) 1)
        (touchedBufPtr + touched.length) js.1)) :
    let touched' := if js.1 ∈ touched then touched else touched ++ [js.1]
    BundleTableAfterDel slotCap vCap eCap tbl S₀ (insert e D) m touched' memf ∧
    ListAt memf touchedBufPtr touched' ∧
    (∀ a, ¬ bundleTableCoreFoot eCap tbl m a →
      (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) → memf a = mem0 a) := by
  intro touched'
  have hjs_lt : js.1 < slotCap := js.2
  set B := ({ B₀ with edges := B₀.edges \ D } : BundleState)
  set L2pre := if b2 = b1 then L1.erase (2 * e) else L2
  have hprev_next : btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ btEndNextBase tbl slotCap eCap ∨
      btEndNextBase tbl slotCap eCap + 2 * eCap ≤ btEndPrevBase tbl slotCap eCap :=
    Or.inl (by unfold btEndPrevBase btEndNextBase; omega)
  rcases hafter with ⟨ar0, ar1, ar2, ar3, ar4, ar5, ar6, ar7, ar8, ar9, ar10, ar11,
    adisjE, aedgeSlot, aendBun, aslots, adisjB, atouch_nd, atouch_lt, atouch_flag,
    acand0, adelLists, adelNext0⟩
  have hScurr_js : tableDelEdges S₀ D js = some B := by simp [tableDelEdges, hSjs, B]
  have he_curr : e ∈ B.edges := Finset.mem_sdiff.mpr ⟨heB₀, he_not_D⟩
  have hslot_js := aslots js; rw [hScurr_js, hm_js] at hslot_js
  rcases hslot_js with ⟨hslotPtr_js, hslotRep_js, hp_disj_tbl⟩
  have hp_disj_tbl' : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hp_disj_tbl
  have hblk_prev : p + bundleSlotBlockSize cap ≤ btEndPrevBase tbl slotCap eCap ∨
      btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ p := by
    unfold btEndPrevBase bundleSlotBlockSize; clear * - hp_disj_tbl'; omega
  have hblk_next : p + bundleSlotBlockSize cap ≤ btEndNextBase tbl slotCap eCap ∨
      btEndNextBase tbl slotCap eCap + 2 * eCap ≤ p := by
    unfold btEndNextBase bundleSlotBlockSize; clear * - hp_disj_tbl'; omega
  have hb1_cap : b1 < cap := lt_of_lt_of_le (hb1 ▸ hslotRep_js.choose_spec.2.2.2.1 (e, true) ((mem_edgeEnds _ _).mpr he_curr)) hslotRep_js.choose_spec.2.1
  have hb2_cap : b2 < cap := lt_of_lt_of_le (hb2 ▸ hslotRep_js.choose_spec.2.2.2.1 (e, false) ((mem_edgeEnds _ _).mpr he_curr)) hslotRep_js.choose_spec.2.1
  have hL2pre_lt : ∀ k ∈ L2pre, k < 2 * eCap := fun k hk => by
    dsimp only [L2pre] at hk; split_ifs at hk
    · exact hL1_lt k (List.mem_of_mem_erase hk)
    · exact hL2_lt k hk
  set a_es := btEdgeSlotBase tbl slotCap + e
  set a_nE := p + 2
  set a_dn := btSlotDelNextBase tbl slotCap eCap + e
  set a_dh := btSlotDelHeadBase tbl slotCap eCap + js.1
  set a_tf := btSlotTouchedBase tbl slotCap eCap + js.1
  set a_tb := touchedBufPtr + touched.length
  have hne_es_nE : a_es ≠ a_nE := by unfold a_es a_nE btEdgeSlotBase; clear * - hp_disj_tbl' he_lt; omega
  have hne_dh_es : a_dh ≠ a_es := by unfold a_dh a_es btSlotDelHeadBase btEdgeSlotBase; clear * - he_lt; omega
  have hne_dh_nE : a_dh ≠ a_nE := by unfold a_dh a_nE btSlotDelHeadBase; clear * - hp_disj_tbl' hjs_lt; omega
  have hne_dn_es : a_dn ≠ a_es := by unfold a_dn a_es btSlotDelNextBase btEdgeSlotBase; clear * - he_lt; omega
  have hne_dn_nE : a_dn ≠ a_nE := by unfold a_dn a_nE btSlotDelNextBase; clear * - hp_disj_tbl' he_lt; omega
  have hne_dn_dh : a_dn ≠ a_dh := by unfold a_dn a_dh btSlotDelNextBase btSlotDelHeadBase; clear * - hjs_lt; omega
  have hne_tf_es : a_tf ≠ a_es := by unfold a_tf a_es btSlotTouchedBase btEdgeSlotBase; clear * - he_lt; omega
  have hne_tf_nE : a_tf ≠ a_nE := by unfold a_tf a_nE btSlotTouchedBase; clear * - hp_disj_tbl' hjs_lt; omega
  have hne_tf_dn : a_tf ≠ a_dn := by unfold a_tf a_dn btSlotTouchedBase btSlotDelNextBase; clear * - hjs_lt; omega
  have hne_tf_dh : a_tf ≠ a_dh := by unfold a_tf a_dh btSlotTouchedBase btSlotDelHeadBase; clear * - hjs_lt; omega
  set mem_t4 :=
    Function.update
      (Function.update
        (Function.update
          (Function.update mem2 a_es 0)
          a_nE ((B₀.edges \ D).card - 1))
        a_dn (mem0 a_dh))
      a_dh (e + 1)
  have htlen_lt_of_not : js.1 ∉ touched → touched.length < slotCap := fun hmem => by
    have hsub : touched.toFinset ⊂ Finset.range slotCap :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨fun x hx => Finset.mem_range.mpr (atouch_lt x (List.mem_toFinset.mp hx)),
         fun heq => hmem (List.mem_toFinset.mp (heq ▸ Finset.mem_range.mpr js.2))⟩
    have := Finset.card_lt_card hsub
    rwa [List.toFinset_card_of_nodup atouch_nd, Finset.card_range] at this
  have hsf_eq_t4_foot : ∀ a, bundleTableCoreFoot eCap tbl m a → a ≠ a_tf → memf a = mem_t4 a :=
    fun a ha hntf => by
      by_cases hmem : js.1 ∈ touched
      · rw [hmemf_eq.1 hmem]
      · have hlt := htlen_lt_of_not hmem
        have hntb : a ≠ a_tb := fun h => htouch_disj_foot a (by unfold a_tb at h; omega) (by unfold a_tb at h; omega) ha
        rw [hmemf_eq.2 hmem, Function.update_of_ne hntb, Function.update_of_ne hntf]
  have hsf_eq_m2_foot : ∀ a, bundleTableCoreFoot eCap tbl m a →
      a ≠ a_es → a ≠ a_nE → a ≠ a_dn → a ≠ a_dh → a ≠ a_tf → memf a = mem2 a :=
    fun a ha h1 h2 h3 h4 h5 => by
      rw [hsf_eq_t4_foot a ha h5]
      simp only [mem_t4, Function.update_of_ne h4, Function.update_of_ne h3,
        Function.update_of_ne h2, Function.update_of_ne h1]
  have hm2_eq_m0 : ∀ a,
      a ≠ bsHeadBase p + b1 → a ≠ bsSizeBase p cap + b1 → a ≠ bsParentBase p cap + b1 →
      a ≠ bsHeadBase p + b2 → a ≠ bsSizeBase p cap + b2 → a ≠ bsParentBase p cap + b2 →
      (∀ k ∈ L1, a ≠ btEndPrevBase tbl slotCap eCap + k ∧ a ≠ btEndNextBase tbl slotCap eCap + k) →
      (∀ k ∈ L2pre, a ≠ btEndPrevBase tbl slotCap eCap + k ∧ a ≠ btEndNextBase tbl slotCap eCap + k) →
      mem2 a = mem0 a := fun a h1a h1b h1c h2a h2b h2c hL1a hL2a =>
    (h2_fr a h2a h2b h2c hL2a).trans (h1_fr a h1a h1b h1c hL1a)
  have hm2_fixed_eq : ∀ a, tbl ≤ a → a < tbl + bundleTableCoreSize slotCap eCap →
      (a < btEndPrevBase tbl slotCap eCap ∨ btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ a) →
      (a < btEndNextBase tbl slotCap eCap ∨ btEndNextBase tbl slotCap eCap + 2 * eCap ≤ a) →
      mem2 a = mem0 a := fun a ha1 ha2 hnp hnn =>
    hm2_eq_m0 a
      (by unfold bsHeadBase; unfold bundleTableCoreSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb1_cap; omega)
      (by unfold bsSizeBase; unfold bundleTableCoreSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb1_cap; omega)
      (by unfold bsParentBase; unfold bundleTableCoreSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb1_cap; omega)
      (by unfold bsHeadBase; unfold bundleTableCoreSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb2_cap; omega)
      (by unfold bsSizeBase; unfold bundleTableCoreSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb2_cap; omega)
      (by unfold bsParentBase; unfold bundleTableCoreSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb2_cap; omega)
      (fun k hk => have := hL1_lt k hk; ⟨by omega, by omega⟩)
      (fun k hk => have := hL2pre_lt k hk; ⟨by omega, by omega⟩)
  have hsf_hdr : ∀ off < 12, memf (tbl + off) = mem0 (tbl + off) := fun off hoff => by
    have hfoot : bundleTableCoreFoot eCap tbl m (tbl + off) :=
      Or.inl ⟨by omega, by unfold bundleTableCoreSize; omega⟩
    rw [hsf_eq_m2_foot _ hfoot
      (by unfold a_es btEdgeSlotBase; omega) (by unfold a_nE; clear * - hp_disj_tbl' hoff; omega)
      (by unfold a_dn btSlotDelNextBase; omega) (by unfold a_dh btSlotDelHeadBase; omega)
      (by unfold a_tf btSlotTouchedBase; omega)]
    exact hm2_fixed_eq _ (by omega) (by unfold bundleTableCoreSize; omega)
      (Or.inl (by unfold btEndPrevBase; omega)) (Or.inl (by unfold btEndNextBase; omega))
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(hsf_hdr 0 (by decide)).trans ar0, (hsf_hdr 1 (by decide)).trans ar1,
      (hsf_hdr 2 (by decide)).trans ar2, (hsf_hdr 3 (by decide)).trans ar3,
      (hsf_hdr 4 (by decide)).trans ar4, (hsf_hdr 5 (by decide)).trans ar5,
      (hsf_hdr 6 (by decide)).trans ar6, (hsf_hdr 7 (by decide)).trans ar7,
      (hsf_hdr 8 (by decide)).trans ar8, (hsf_hdr 9 (by decide)).trans ar9,
      (hsf_hdr 10 (by decide)).trans ar10, (hsf_hdr 11 (by decide)).trans ar11,
      ?_, ?_, ?_, ?_, adisjB, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j₁ j₂ hne B₁ B₂ hB₁ hB₂
      simp only [tableDelEdges, Option.map_eq_some_iff] at hB₁ hB₂
      rcases hB₁ with ⟨B₁₀, hS₁, rfl⟩; rcases hB₂ with ⟨B₂₀, hS₂, rfl⟩
      have h1 : tableDelEdges S₀ D j₁ = some { B₁₀ with edges := B₁₀.edges \ D } := by simp [tableDelEdges, hS₁]
      have h2 : tableDelEdges S₀ D j₂ = some { B₂₀ with edges := B₂₀.edges \ D } := by simp [tableDelEdges, hS₂]
      exact (adisjE j₁ j₂ hne _ _ h1 h2).mono
        (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.subset_insert e D))
        (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.subset_insert e D))
    · intro e' he'
      have hfoot_e' : bundleTableCoreFoot eCap tbl m (btEdgeSlotBase tbl slotCap + e') :=
        Or.inl ⟨by unfold btEdgeSlotBase; omega, by unfold btEdgeSlotBase bundleTableCoreSize; omega⟩
      by_cases hee : e' = e
      · subst e'
        have hval : memf a_es = 0 := by
          rw [hsf_eq_t4_foot a_es hfoot_e' hne_tf_es.symm]
          simp only [mem_t4, Function.update_of_ne hne_dh_es.symm, Function.update_of_ne hne_dn_es.symm,
            Function.update_of_ne hne_es_nE, Function.update_self]
        refine ⟨fun j Bj hSj heBj => ?_, fun _ => hval⟩
        simp only [tableDelEdges, Option.map_eq_some_iff] at hSj
        rcases hSj with ⟨Bj₀, _, rfl⟩
        exact False.elim ((Finset.mem_sdiff.mp heBj).2 (Finset.mem_insert_self e D))
      · have heq : memf (btEdgeSlotBase tbl slotCap + e') = mem0 (btEdgeSlotBase tbl slotCap + e') := by
          rw [hsf_eq_m2_foot _ hfoot_e' (by unfold a_es; omega)
            (by unfold a_nE btEdgeSlotBase; clear * - hp_disj_tbl' he'; omega)
            (by unfold a_dn btEdgeSlotBase btSlotDelNextBase; clear * - he'; omega)
            (by unfold a_dh btEdgeSlotBase btSlotDelHeadBase; clear * - he'; omega)
            (by unfold a_tf btEdgeSlotBase btSlotTouchedBase; clear * - he'; omega)]
          exact hm2_fixed_eq _ (by unfold btEdgeSlotBase; omega)
            (by unfold btEdgeSlotBase bundleTableCoreSize; omega)
            (Or.inl (by unfold btEdgeSlotBase btEndPrevBase; omega))
            (Or.inl (by unfold btEdgeSlotBase btEndNextBase; omega))
        rw [heq]
        refine ⟨fun j Bj hSj heBj => ?_, fun hnone => ?_⟩
        · simp only [tableDelEdges, Option.map_eq_some_iff] at hSj
          rcases hSj with ⟨Bj₀, hS₀, rfl⟩
          exact (aedgeSlot e' he').1 j { Bj₀ with edges := Bj₀.edges \ D }
            (by simp [tableDelEdges, hS₀])
            (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp heBj).1,
              fun hd => (Finset.mem_sdiff.mp heBj).2 (Finset.mem_insert_of_mem hd)⟩)
        · exact (aedgeSlot e' he').2 fun j Bj hSj heBj => by
            simp only [tableDelEdges, Option.map_eq_some_iff] at hSj
            rcases hSj with ⟨Bj₀, hS₀, rfl⟩
            exact hnone j { Bj₀ with edges := Bj₀.edges \ insert e D }
              (by simp [tableDelEdges, hS₀])
              (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp heBj).1,
                fun hm => (Finset.mem_insert.mp hm).elim (fun h => hee h) (Finset.mem_sdiff.mp heBj).2⟩)
    · intro j Bj hSj x hx
      simp only [tableDelEdges, Option.map_eq_some_iff] at hSj
      rcases hSj with ⟨Bj₀, hS₀, rfl⟩
      have hx_in : x ∈ edgeEnds ({ Bj₀ with edges := Bj₀.edges \ D } : BundleState).edges := by
        rw [mem_edgeEnds] at hx ⊢
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
          fun hd => (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hd)⟩
      have hkx : endKey x < 2 * eCap := by
        have hslot := aslots j; simp only [tableDelEdges, hS₀, Option.map_some] at hslot
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hslot; exact False.elim hslot
        | some pb =>
          rw [hm] at hslot
          have he_lt' := hslot.2.1.choose_spec.2.2.1 x.1 ((mem_edgeEnds _ _).mp hx_in)
          rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
      have hfoot_x : bundleTableCoreFoot eCap tbl m (btEndBundleBase tbl slotCap eCap + endKey x) :=
        Or.inl ⟨by unfold btEndBundleBase; omega, by unfold btEndBundleBase bundleTableCoreSize; omega⟩
      rw [hsf_eq_m2_foot _ hfoot_x
        (by unfold a_es btEndBundleBase btEdgeSlotBase; clear * - he_lt; omega)
        (by unfold a_nE btEndBundleBase; clear * - hp_disj_tbl' hkx; omega)
        (by unfold a_dn btEndBundleBase btSlotDelNextBase; clear * - hkx; omega)
        (by unfold a_dh btEndBundleBase btSlotDelHeadBase; clear * - hkx; omega)
        (by unfold a_tf btEndBundleBase btSlotTouchedBase; clear * - hkx; omega),
        hm2_fixed_eq _ (by unfold btEndBundleBase; omega)
          (by unfold btEndBundleBase bundleTableCoreSize; omega)
          (Or.inl (by unfold btEndBundleBase btEndPrevBase; omega))
          (Or.inl (by unfold btEndBundleBase btEndNextBase; omega))]
      exact aendBun j { Bj₀ with edges := Bj₀.edges \ D } (by simp [tableDelEdges, hS₀]) x hx_in
    · intro j
      have hj_lt : j.1 < slotCap := j.2
      have hfoot_ptr : bundleTableCoreFoot eCap tbl m (btSlotPtrBase tbl + j.1) :=
        Or.inl ⟨by unfold btSlotPtrBase; omega, by unfold btSlotPtrBase bundleTableCoreSize; clear * - hj_lt; omega⟩
      have hptr_eq : memf (btSlotPtrBase tbl + j.1) = mem0 (btSlotPtrBase tbl + j.1) := by
        rw [hsf_eq_m2_foot _ hfoot_ptr
          (by unfold a_es btSlotPtrBase btEdgeSlotBase; clear * - hj_lt; omega)
          (by unfold a_nE btSlotPtrBase; clear * - hp_disj_tbl' hj_lt; omega)
          (by unfold a_dn btSlotPtrBase btSlotDelNextBase; clear * - hj_lt; omega)
          (by unfold a_dh btSlotPtrBase btSlotDelHeadBase; clear * - hj_lt; omega)
          (by unfold a_tf btSlotPtrBase btSlotTouchedBase; clear * - hj_lt; omega)]
        exact hm2_fixed_eq _ (by unfold btSlotPtrBase; omega)
          (by unfold btSlotPtrBase bundleTableCoreSize; clear * - hj_lt; omega)
          (Or.inl (by unfold btSlotPtrBase btEndPrevBase; clear * - hj_lt; omega))
          (Or.inl (by unfold btSlotPtrBase btEndNextBase; clear * - hj_lt; omega))
      by_cases hjj : j = js
      · subst j
        have hB_er : ({ B₀ with edges := B₀.edges \ insert e D } : BundleState) =
            { B with edges := B.edges.erase e } := by
          congr 1; ext x; simp only [B, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
          exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h2, h1, h3⟩ => ⟨h1, h2, h3⟩⟩
        simp only [tableDelEdges, hSjs, Option.map_some, hm_js, hB_er]
        refine ⟨hptr_eq.trans hslotPtr_js, ?_, hp_disj_tbl⟩
        refine bundleSlotRepAt_erase_edge he_curr hslotRep_js hb1 hb2 hL1_nd hL2_nd
          hL1_lt hL2_lt hL1_mem hL2_mem hprev_next h1_dll h1_sz h1_par0 h1_fr
          h2_dll h2_sz h2_par0 h2_fr ?_ ?_ hblk_prev hblk_next
        · have hfoot_nE : bundleTableCoreFoot eCap tbl m a_nE :=
            bsAddr_in_coreFoot hm_js (by unfold bundleSlotBlockSize; omega)
          change memf a_nE = B.edges.card - 1
          rw [hsf_eq_t4_foot a_nE hfoot_nE hne_tf_nE.symm]
          simp only [mem_t4, Function.update_of_ne hne_dh_nE.symm, Function.update_of_ne hne_dn_nE.symm,
            Function.update_self, B]
        · intro a ha_nE ha_in
          have hfoot_a : bundleTableCoreFoot eCap tbl m a := by
            rcases ha_in with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inr ⟨js, p, cap, hm_js, h1, h2⟩
            · exact Or.inl ⟨by unfold btEndPrevBase at h1; omega,
                by unfold btEndPrevBase at h2; unfold bundleTableCoreSize; omega⟩
            · exact Or.inl ⟨by unfold btEndNextBase at h1; omega,
                by unfold btEndNextBase at h2; unfold bundleTableCoreSize; omega⟩
          rcases ha_in with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hsf_eq_m2_foot a hfoot_a
              (by unfold a_es btEdgeSlotBase; unfold bundleSlotBlockSize at h2; clear * - hp_disj_tbl' he_lt h1 h2; omega)
              ha_nE
              (by unfold a_dn btSlotDelNextBase; unfold bundleSlotBlockSize at h2; clear * - hp_disj_tbl' he_lt h1 h2; omega)
              (by unfold a_dh btSlotDelHeadBase; unfold bundleSlotBlockSize at h2; clear * - hp_disj_tbl' hjs_lt h1 h2; omega)
              (by unfold a_tf btSlotTouchedBase; unfold bundleSlotBlockSize at h2; clear * - hp_disj_tbl' hjs_lt h1 h2; omega)
          · exact hsf_eq_m2_foot a hfoot_a
              (by unfold a_es btEdgeSlotBase; unfold btEndPrevBase at h1; clear * - he_lt h1; omega)
              ha_nE
              (by unfold a_dn btSlotDelNextBase; unfold btEndPrevBase at h2; omega)
              (by unfold a_dh btSlotDelHeadBase; unfold btEndPrevBase at h2; omega)
              (by unfold a_tf btSlotTouchedBase; unfold btEndPrevBase at h2; omega)
          · exact hsf_eq_m2_foot a hfoot_a
              (by unfold a_es btEdgeSlotBase; unfold btEndNextBase at h1; clear * - he_lt h1; omega)
              ha_nE
              (by unfold a_dn btSlotDelNextBase; unfold btEndNextBase at h2; omega)
              (by unfold a_dh btSlotDelHeadBase; unfold btEndNextBase at h2; omega)
              (by unfold a_tf btSlotTouchedBase; unfold btEndNextBase at h2; omega)
      · have hslot_j := aslots j
        cases hSj : S₀ j with
        | none =>
          simp only [tableDelEdges, hSj, Option.map_none] at hslot_j ⊢
          cases hm : m.slotBlocks j with
          | none => rw [hm] at hslot_j; exact hptr_eq.trans hslot_j
          | some _ => rw [hm] at hslot_j; exact False.elim hslot_j
        | some Bj₀ =>
          have hdisj_Bj : Disjoint (Bj₀.edges \ D) B.edges :=
            adisjE j js hjj { Bj₀ with edges := Bj₀.edges \ D } B (by simp [tableDelEdges, hSj]) hScurr_js
          have he_not_Bj : e ∉ Bj₀.edges \ D := fun h => Finset.disjoint_left.mp hdisj_Bj h he_curr
          have hBj_eq : ({ Bj₀ with edges := Bj₀.edges \ insert e D } : BundleState) =
              { Bj₀ with edges := Bj₀.edges \ D } := by
            congr 1; ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
            exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩,
              fun ⟨h1, h2⟩ => ⟨h1, fun hxe => he_not_Bj (Finset.mem_sdiff.mpr ⟨hxe ▸ h1, hxe ▸ h2⟩), h2⟩⟩
          simp only [tableDelEdges, hSj, Option.map_some, hBj_eq] at hslot_j ⊢
          cases hm : m.slotBlocks j with
          | none => rw [hm] at hslot_j; exact False.elim hslot_j
          | some pb' =>
            rcases pb' with ⟨p', cap'⟩; rw [hm] at hslot_j
            have hp'_disj_p := adisjB j js hjj p' cap' p cap hm hm_js
            refine ⟨hptr_eq.trans hslot_j.1, ?_, hslot_j.2.2⟩
            have hp'_disj_tbl' : p' + (3 + 6 * cap') ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p' := hslot_j.2.2
            refine hslot_j.2.1.of_agree_slot ?_ ?_ ?_
            · intro a ha1 ha2
              have hfoot_a : bundleTableCoreFoot eCap tbl m a := Or.inr ⟨j, p', cap', hm, ha1, ha2⟩
              have ha2' : a < p' + (3 + 6 * cap') := ha2
              have hdisj_p' : p' + (3 + 6 * cap') ≤ p ∨ p + (3 + 6 * cap) ≤ p' := hp'_disj_p
              rw [hsf_eq_m2_foot a hfoot_a
                (by unfold a_es btEdgeSlotBase; clear * - hp'_disj_tbl' he_lt ha1 ha2'; omega)
                (by unfold a_nE; clear * - hdisj_p' ha1 ha2'; omega)
                (by unfold a_dn btSlotDelNextBase; clear * - hp'_disj_tbl' he_lt ha1 ha2'; omega)
                (by unfold a_dh btSlotDelHeadBase; clear * - hp'_disj_tbl' hjs_lt ha1 ha2'; omega)
                (by unfold a_tf btSlotTouchedBase; clear * - hp'_disj_tbl' hjs_lt ha1 ha2'; omega)]
              exact (hm2_eq_m0 a
                (by unfold bsHeadBase; clear * - hdisj_p' ha1 ha2' hb1_cap; omega)
                (by unfold bsSizeBase; clear * - hdisj_p' ha1 ha2' hb1_cap; omega)
                (by unfold bsParentBase; clear * - hdisj_p' ha1 ha2' hb1_cap; omega)
                (by unfold bsHeadBase; clear * - hdisj_p' ha1 ha2' hb2_cap; omega)
                (by unfold bsSizeBase; clear * - hdisj_p' ha1 ha2' hb2_cap; omega)
                (by unfold bsParentBase; clear * - hdisj_p' ha1 ha2' hb2_cap; omega)
                (fun k hk => by
                  have hkl := hL1_lt k hk; unfold btEndPrevBase btEndNextBase
                  exact ⟨by clear * - hp'_disj_tbl' ha1 ha2' hkl; omega, by clear * - hp'_disj_tbl' ha1 ha2' hkl; omega⟩)
                (fun k hk => by
                  have hkl := hL2pre_lt k hk; unfold btEndPrevBase btEndNextBase
                  exact ⟨by clear * - hp'_disj_tbl' ha1 ha2' hkl; omega, by clear * - hp'_disj_tbl' ha1 ha2' hkl; omega⟩)).symm
            · intro k hk
              have he_lt' := hslot_j.2.1.choose_spec.2.2.1 _ hk
              have hkl : k < 2 * eCap := by
                have hke := bundle_endKey_endOfKey k
                rcases h : endOfKey k with ⟨ee, side⟩; rw [h] at he_lt' hke
                cases side <;> simp [endKey] at hke <;> omega
              have hfoot_k : bundleTableCoreFoot eCap tbl m (btEndPrevBase tbl slotCap eCap + k) :=
                Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableCoreSize; omega⟩
              have hmeB : ∀ {b x}, x ∈ B.ends b → x.1 ∈ B.edges := fun h => by
                rw [BundleState.mem_ends] at h; exact h.1
              have hne_L1 : ∀ k' ∈ L1, k ≠ k' := fun k' hk' heq =>
                Finset.disjoint_left.mp hdisj_Bj (heq ▸ hk) (hmeB ((hL1_mem k').mp hk'))
              have hne_L2 : ∀ k' ∈ L2pre, k ≠ k' := fun k' hk' heq => by
                dsimp only [L2pre] at hk'; split_ifs at hk'
                · exact hne_L1 k' (List.mem_of_mem_erase hk') heq
                · exact Finset.disjoint_left.mp hdisj_Bj (heq ▸ hk) (hmeB ((hL2_mem k').mp hk'))
              rw [hsf_eq_m2_foot _ hfoot_k
                (by unfold a_es btEndPrevBase btEdgeSlotBase; clear * - he_lt; omega)
                (by unfold a_nE btEndPrevBase; clear * - hp_disj_tbl' hkl; omega)
                (by unfold a_dn btEndPrevBase btSlotDelNextBase; clear * - hkl; omega)
                (by unfold a_dh btEndPrevBase btSlotDelHeadBase; clear * - hkl; omega)
                (by unfold a_tf btEndPrevBase btSlotTouchedBase; clear * - hkl; omega)]
              exact (hm2_eq_m0 _
                (by unfold btEndPrevBase bsHeadBase; clear * - hp_disj_tbl' hkl hb1_cap; omega)
                (by unfold btEndPrevBase bsSizeBase; clear * - hp_disj_tbl' hkl hb1_cap; omega)
                (by unfold btEndPrevBase bsParentBase; clear * - hp_disj_tbl' hkl hb1_cap; omega)
                (by unfold btEndPrevBase bsHeadBase; clear * - hp_disj_tbl' hkl hb2_cap; omega)
                (by unfold btEndPrevBase bsSizeBase; clear * - hp_disj_tbl' hkl hb2_cap; omega)
                (by unfold btEndPrevBase bsParentBase; clear * - hp_disj_tbl' hkl hb2_cap; omega)
                (fun k' hk' => ⟨by have := hne_L1 k' hk'; omega, by have := hL1_lt k' hk'; clear * - hprev_next hkl this; omega⟩)
                (fun k' hk' => ⟨by have := hne_L2 k' hk'; omega, by have := hL2pre_lt k' hk'; clear * - hprev_next hkl this; omega⟩)).symm
            · intro k hk
              have he_lt' := hslot_j.2.1.choose_spec.2.2.1 _ hk
              have hkl : k < 2 * eCap := by
                have hke := bundle_endKey_endOfKey k
                rcases h : endOfKey k with ⟨ee, side⟩; rw [h] at he_lt' hke
                cases side <;> simp [endKey] at hke <;> omega
              have hfoot_k : bundleTableCoreFoot eCap tbl m (btEndNextBase tbl slotCap eCap + k) :=
                Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableCoreSize; omega⟩
              have hmeB : ∀ {b x}, x ∈ B.ends b → x.1 ∈ B.edges := fun h => by
                rw [BundleState.mem_ends] at h; exact h.1
              have hne_L1 : ∀ k' ∈ L1, k ≠ k' := fun k' hk' heq =>
                Finset.disjoint_left.mp hdisj_Bj (heq ▸ hk) (hmeB ((hL1_mem k').mp hk'))
              have hne_L2 : ∀ k' ∈ L2pre, k ≠ k' := fun k' hk' heq => by
                dsimp only [L2pre] at hk'; split_ifs at hk'
                · exact hne_L1 k' (List.mem_of_mem_erase hk') heq
                · exact Finset.disjoint_left.mp hdisj_Bj (heq ▸ hk) (hmeB ((hL2_mem k').mp hk'))
              rw [hsf_eq_m2_foot _ hfoot_k
                (by unfold a_es btEndNextBase btEdgeSlotBase; clear * - he_lt; omega)
                (by unfold a_nE btEndNextBase; clear * - hp_disj_tbl' hkl; omega)
                (by unfold a_dn btEndNextBase btSlotDelNextBase; clear * - hkl; omega)
                (by unfold a_dh btEndNextBase btSlotDelHeadBase; clear * - hkl; omega)
                (by unfold a_tf btEndNextBase btSlotTouchedBase; clear * - hkl; omega)]
              exact (hm2_eq_m0 _
                (by unfold btEndNextBase bsHeadBase; clear * - hp_disj_tbl' hkl hb1_cap; omega)
                (by unfold btEndNextBase bsSizeBase; clear * - hp_disj_tbl' hkl hb1_cap; omega)
                (by unfold btEndNextBase bsParentBase; clear * - hp_disj_tbl' hkl hb1_cap; omega)
                (by unfold btEndNextBase bsHeadBase; clear * - hp_disj_tbl' hkl hb2_cap; omega)
                (by unfold btEndNextBase bsSizeBase; clear * - hp_disj_tbl' hkl hb2_cap; omega)
                (by unfold btEndNextBase bsParentBase; clear * - hp_disj_tbl' hkl hb2_cap; omega)
                (fun k' hk' => ⟨by have := hL1_lt k' hk'; clear * - hprev_next hkl this; omega, by have := hne_L1 k' hk'; omega⟩)
                (fun k' hk' => ⟨by have := hL2pre_lt k' hk'; clear * - hprev_next hkl this; omega, by have := hne_L2 k' hk'; omega⟩)).symm
    · dsimp only [touched']; split_ifs with hmem
      · exact atouch_nd
      · rw [List.nodup_append]
        exact ⟨atouch_nd, List.nodup_singleton _, fun x hx y hy hxy => hmem (by simp at hy; rwa [← hy, ← hxy])⟩
    · intro s hs; dsimp only [touched'] at hs; split_ifs at hs
      · exact atouch_lt s hs
      · rcases List.mem_append.mp hs with h1 | h2
        · exact atouch_lt s h1
        · simp at h2; rw [h2]; exact js.2
    · intro s hs
      have hfoot_s : bundleTableCoreFoot eCap tbl m (btSlotTouchedBase tbl slotCap eCap + s) :=
        Or.inl ⟨by unfold btSlotTouchedBase; omega, by unfold btSlotTouchedBase bundleTableCoreSize; omega⟩
      by_cases hss : s = js.1
      · subst s
        have hmem_t' : js.1 ∈ touched' := by dsimp only [touched']; split_ifs with h <;> simp [h]
        simp only [hmem_t', ↓reduceIte]
        change memf a_tf = 1
        by_cases hmem : js.1 ∈ touched
        · rw [hmemf_eq.1 hmem]
          simp only [mem_t4, Function.update_of_ne hne_tf_dh, Function.update_of_ne hne_tf_dn,
            Function.update_of_ne hne_tf_nE, Function.update_of_ne hne_tf_es]
          rw [hm2_fixed_eq a_tf (by unfold a_tf btSlotTouchedBase; omega)
            (by unfold a_tf btSlotTouchedBase bundleTableCoreSize; clear * - hjs_lt; omega)
            (Or.inr (by unfold a_tf btSlotTouchedBase btEndPrevBase; omega))
            (Or.inr (by unfold a_tf btSlotTouchedBase btEndNextBase; omega))]
          simpa [a_tf, hmem] using atouch_flag js.1 js.2
        · have hlt := htlen_lt_of_not hmem
          have hntb : a_tf ≠ a_tb := fun h => htouch_disj_foot a_tf (by unfold a_tb at h; omega) (by unfold a_tb at h; omega) hfoot_s
          rw [hmemf_eq.2 hmem, Function.update_of_ne hntb, Function.update_self]
      · have hmem_iff : s ∈ touched' ↔ s ∈ touched := by dsimp only [touched']; split_ifs <;> simp [hss]
        rw [hsf_eq_m2_foot _ hfoot_s
          (by unfold a_es btSlotTouchedBase btEdgeSlotBase; clear * - he_lt; omega)
          (by unfold a_nE btSlotTouchedBase; clear * - hp_disj_tbl' hs; omega)
          (by unfold a_dn btSlotTouchedBase btSlotDelNextBase; clear * - hs; omega)
          (by unfold a_dh btSlotTouchedBase btSlotDelHeadBase; clear * - hs; omega)
          (by unfold a_tf; omega),
          hm2_fixed_eq _ (by unfold btSlotTouchedBase; omega)
            (by unfold btSlotTouchedBase bundleTableCoreSize; omega)
            (Or.inr (by unfold btSlotTouchedBase btEndPrevBase; omega))
            (Or.inr (by unfold btSlotTouchedBase btEndNextBase; omega))]
        simpa [hmem_iff] using atouch_flag s hs
    · intro s hs
      have hfoot_s : bundleTableCoreFoot eCap tbl m (btSlotCandHeadBase tbl slotCap eCap + s) :=
        Or.inl ⟨by unfold btSlotCandHeadBase; omega, by unfold btSlotCandHeadBase bundleTableCoreSize; omega⟩
      rw [hsf_eq_m2_foot _ hfoot_s
        (by unfold a_es btSlotCandHeadBase btEdgeSlotBase; clear * - he_lt; omega)
        (by unfold a_nE btSlotCandHeadBase; clear * - hp_disj_tbl' hs; omega)
        (by unfold a_dn btSlotCandHeadBase btSlotDelNextBase; clear * - he_lt; omega)
        (by unfold a_dh btSlotCandHeadBase btSlotDelHeadBase; clear * - hjs_lt; omega)
        (by unfold a_tf btSlotCandHeadBase btSlotTouchedBase; clear * - hjs_lt; omega),
        hm2_fixed_eq _ (by unfold btSlotCandHeadBase; omega)
          (by unfold btSlotCandHeadBase bundleTableCoreSize; omega)
          (Or.inr (by unfold btSlotCandHeadBase btEndPrevBase; omega))
          (Or.inr (by unfold btSlotCandHeadBase btEndNextBase; omega))]
      exact acand0 s hs
    · intro j
      have hj_lt : j.1 < slotCap := j.2
      have hd_j := adelLists j
      have hdn_eq : ∀ e' < eCap, e' ≠ e →
          memf (btSlotDelNextBase tbl slotCap eCap + e') = mem0 (btSlotDelNextBase tbl slotCap eCap + e') :=
        fun e' he' hne => by
          have hfoot : bundleTableCoreFoot eCap tbl m (btSlotDelNextBase tbl slotCap eCap + e') :=
            Or.inl ⟨by unfold btSlotDelNextBase; omega, by unfold btSlotDelNextBase bundleTableCoreSize; omega⟩
          rw [hsf_eq_m2_foot _ hfoot
            (by unfold a_es btSlotDelNextBase btEdgeSlotBase; clear * - he_lt; omega)
            (by unfold a_nE btSlotDelNextBase; clear * - hp_disj_tbl' he'; omega)
            (by unfold a_dn; omega)
            (by unfold a_dh btSlotDelNextBase btSlotDelHeadBase; clear * - hjs_lt; omega)
            (by unfold a_tf btSlotDelNextBase btSlotTouchedBase; clear * - hjs_lt; omega)]
          exact hm2_fixed_eq _ (by unfold btSlotDelNextBase; omega)
            (by unfold btSlotDelNextBase bundleTableCoreSize; omega)
            (Or.inr (by unfold btSlotDelNextBase btEndPrevBase; omega))
            (Or.inr (by unfold btSlotDelNextBase btEndNextBase; omega))
      by_cases hjj : j = js
      · subst hjj; rw [hSjs] at hd_j ⊢
        rcases hd_j with ⟨_, dL, hdL_sll, hdL_mem⟩
        refine ⟨⟨fun _ => ⟨e, Finset.mem_inter.mpr ⟨heB₀, Finset.mem_insert_self e D⟩⟩,
          fun _ => by dsimp only [touched']; split_ifs with h <;> simp [h]⟩, e :: dL, ?_, ?_⟩
        · have he_not_dL : e ∉ dL := fun h => he_not_D (Finset.mem_inter.mp ((hdL_mem e).mp h)).2
          have hfoot_dh : bundleTableCoreFoot eCap tbl m a_dh :=
            Or.inl ⟨by unfold a_dh btSlotDelHeadBase; omega, by unfold a_dh btSlotDelHeadBase bundleTableCoreSize; clear * - hjs_lt; omega⟩
          have hfoot_dn : bundleTableCoreFoot eCap tbl m a_dn :=
            Or.inl ⟨by unfold a_dn btSlotDelNextBase; omega, by unfold a_dn btSlotDelNextBase bundleTableCoreSize; clear * - he_lt; omega⟩
          have hdh_val : memf a_dh = e + 1 := by
            rw [hsf_eq_t4_foot a_dh hfoot_dh hne_tf_dh.symm]; exact Function.update_self _ _ _
          have hdn_val : memf a_dn = mem0 a_dh := by
            rw [hsf_eq_t4_foot a_dn hfoot_dn hne_tf_dn.symm]
            simp only [mem_t4, Function.update_of_ne hne_dn_dh, Function.update_self]
          exact hdL_sll.cons he_lt he_not_dL hdh_val hdn_val
            fun x hx => hdn_eq x (hdL_sll.mem_lt x hx) (fun h => he_not_dL (h ▸ hx))
        · intro e'
          simp only [List.mem_cons, hdL_mem, Finset.mem_inter, Finset.mem_insert]
          exact ⟨fun h => h.elim (fun heq => ⟨heq ▸ heB₀, Or.inl heq⟩) fun ⟨h1, h2⟩ => ⟨h1, Or.inr h2⟩,
            fun ⟨h1, h2⟩ => h2.elim Or.inl fun hD => Or.inr ⟨h1, hD⟩⟩
      · have hdh_eq : memf (btSlotDelHeadBase tbl slotCap eCap + j.1) = mem0 (btSlotDelHeadBase tbl slotCap eCap + j.1) := by
          have hfoot : bundleTableCoreFoot eCap tbl m (btSlotDelHeadBase tbl slotCap eCap + j.1) :=
            Or.inl ⟨by unfold btSlotDelHeadBase; omega, by unfold btSlotDelHeadBase bundleTableCoreSize; clear * - hj_lt; omega⟩
          rw [hsf_eq_m2_foot _ hfoot
            (by unfold a_es btSlotDelHeadBase btEdgeSlotBase; clear * - he_lt; omega)
            (by unfold a_nE btSlotDelHeadBase; clear * - hp_disj_tbl' hj_lt; omega)
            (by unfold a_dn btSlotDelHeadBase btSlotDelNextBase; clear * - hj_lt; omega)
            (by unfold a_dh; exact fun h => hjj (Fin.ext (by omega)))
            (by unfold a_tf btSlotDelHeadBase btSlotTouchedBase; clear * - hjs_lt; omega)]
          exact hm2_fixed_eq _ (by unfold btSlotDelHeadBase; omega)
            (by unfold btSlotDelHeadBase bundleTableCoreSize; clear * - hj_lt; omega)
            (Or.inr (by unfold btSlotDelHeadBase btEndPrevBase; omega))
            (Or.inr (by unfold btSlotDelHeadBase btEndNextBase; omega))
        have hj_mem_iff : j.1 ∈ touched' ↔ j.1 ∈ touched := by
          dsimp only [touched']; split_ifs <;> simp [Fin.val_ne_of_ne hjj]
        cases hSj : S₀ j with
        | none => rw [hSj] at hd_j; exact ⟨hdh_eq.trans hd_j.1, by rw [hj_mem_iff]; exact hd_j.2⟩
        | some Bj₀ =>
          rw [hSj] at hd_j
          have he_not_Bj₀ : e ∉ Bj₀.edges := fun h => by
            have hd := adisjE j js hjj { Bj₀ with edges := Bj₀.edges \ D } B (by simp [tableDelEdges, hSj]) hScurr_js
            exact Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr ⟨h, he_not_D⟩) he_curr
          have hinter : Bj₀.edges ∩ insert e D = Bj₀.edges ∩ D := by
            ext x; simp only [Finset.mem_inter, Finset.mem_insert]
            exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.elim (fun hx => absurd (hx ▸ h1) he_not_Bj₀) id⟩,
              fun ⟨h1, h2⟩ => ⟨h1, Or.inr h2⟩⟩
          rcases hd_j with ⟨htj, dL, hdL_sll, hdL_mem⟩
          refine ⟨by rw [hj_mem_iff, hinter]; exact htj, dL,
            hdL_sll.of_agree hdh_eq fun x hx =>
              hdn_eq x (hdL_sll.mem_lt x hx) (fun h => he_not_Bj₀ (h ▸ (Finset.mem_inter.mp ((hdL_mem x).mp hx)).1)),
            by simpa [hinter] using hdL_mem⟩
    · intro e' he' hnot
      have hne_e : e' ≠ e := fun h => hnot js B₀ hSjs
        (Finset.mem_inter.mpr ⟨h.symm ▸ heB₀, h.symm ▸ Finset.mem_insert_self e D⟩)
      have hfoot : bundleTableCoreFoot eCap tbl m (btSlotDelNextBase tbl slotCap eCap + e') :=
        Or.inl ⟨by unfold btSlotDelNextBase; omega, by unfold btSlotDelNextBase bundleTableCoreSize; omega⟩
      rw [hsf_eq_m2_foot _ hfoot
        (by unfold a_es btSlotDelNextBase btEdgeSlotBase; clear * - he_lt; omega)
        (by unfold a_nE btSlotDelNextBase; clear * - hp_disj_tbl' he'; omega)
        (by unfold a_dn; omega)
        (by unfold a_dh btSlotDelNextBase btSlotDelHeadBase; clear * - hjs_lt; omega)
        (by unfold a_tf btSlotDelNextBase btSlotTouchedBase; clear * - hjs_lt; omega),
        hm2_fixed_eq _ (by unfold btSlotDelNextBase; omega)
          (by unfold btSlotDelNextBase bundleTableCoreSize; omega)
          (Or.inr (by unfold btSlotDelNextBase btEndPrevBase; omega))
          (Or.inr (by unfold btSlotDelNextBase btEndNextBase; omega))]
      exact adelNext0 e' he' fun j Bj₀ hSj hmem =>
        hnot j Bj₀ hSj (Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hmem).1, Finset.mem_insert_of_mem (Finset.mem_inter.mp hmem).2⟩)
  · have hfoot_eq_out : ∀ a, ¬ bundleTableCoreFoot eCap tbl m a → a ≠ a_tb → memf a = mem0 a :=
      fun a hnf hntb => by
        have hntf : a ≠ a_tf := fun h => hnf (h ▸ Or.inl ⟨by unfold a_tf btSlotTouchedBase; omega,
          by unfold a_tf btSlotTouchedBase bundleTableCoreSize; clear * - hjs_lt; omega⟩)
        have ht4 : memf a = mem_t4 a := by
          by_cases hmem : js.1 ∈ touched
          · rw [hmemf_eq.1 hmem]
          · rw [hmemf_eq.2 hmem, Function.update_of_ne hntb, Function.update_of_ne hntf]
        rw [ht4]
        have ha_es' : a ≠ a_es := fun h => hnf (h ▸ Or.inl ⟨by unfold a_es btEdgeSlotBase; omega,
          by unfold a_es btEdgeSlotBase bundleTableCoreSize; clear * - he_lt; omega⟩)
        have ha_nE' : a ≠ a_nE := fun h => hnf (h ▸ bsAddr_in_coreFoot hm_js (by unfold bundleSlotBlockSize; omega))
        have ha_dn' : a ≠ a_dn := fun h => hnf (h ▸ Or.inl ⟨by unfold a_dn btSlotDelNextBase; omega,
          by unfold a_dn btSlotDelNextBase bundleTableCoreSize; clear * - he_lt; omega⟩)
        have ha_dh' : a ≠ a_dh := fun h => hnf (h ▸ Or.inl ⟨by unfold a_dh btSlotDelHeadBase; omega,
          by unfold a_dh btSlotDelHeadBase bundleTableCoreSize; clear * - hjs_lt; omega⟩)
        simp only [mem_t4, Function.update_of_ne ha_dh', Function.update_of_ne ha_dn',
          Function.update_of_ne ha_nE', Function.update_of_ne ha_es']
        exact hm2_eq_m0 a
          (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsHeadBase; omega, by unfold bsHeadBase bundleSlotBlockSize; omega⟩))
          (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsSizeBase; omega, by unfold bsSizeBase bundleSlotBlockSize; omega⟩))
          (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsParentBase; omega, by unfold bsParentBase bundleSlotBlockSize; omega⟩))
          (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsHeadBase; omega, by unfold bsHeadBase bundleSlotBlockSize; omega⟩))
          (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsSizeBase; omega, by unfold bsSizeBase bundleSlotBlockSize; omega⟩))
          (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsParentBase; omega, by unfold bsParentBase bundleSlotBlockSize; omega⟩))
          (fun k hk => have := hL1_lt k hk;
            ⟨fun h => hnf (h ▸ Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableCoreSize; omega⟩),
             fun h => hnf (h ▸ Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableCoreSize; omega⟩)⟩)
          (fun k hk => have := hL2pre_lt k hk;
            ⟨fun h => hnf (h ▸ Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableCoreSize; omega⟩),
             fun h => hnf (h ▸ Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableCoreSize; omega⟩)⟩)
    have htlen_le : touched.length ≤ slotCap := by
      have hcard := Finset.card_le_card (show touched.toFinset ⊆ Finset.range slotCap from
        fun x hx => Finset.mem_range.mpr (atouch_lt x (List.mem_toFinset.mp hx)))
      simpa [List.toFinset_card_of_nodup atouch_nd] using hcard
    intro idx hidx
    dsimp only [touched'] at hidx ⊢
    split_ifs at hidx ⊢ with hmem
    · rw [hfoot_eq_out _ (htouch_disj_foot _ (by omega) (by omega)) (by unfold a_tb; omega)]
      exact htouch_mem idx hidx
    · simp only [List.length_append, List.length_singleton] at hidx
      by_cases hlt : idx < touched.length
      · rw [List.getElem_append_left hlt,
          hfoot_eq_out _ (htouch_disj_foot _ (by omega) (by omega)) (by unfold a_tb; omega)]
        exact htouch_mem idx hlt
      · have heq : idx = touched.length := by omega
        subst heq; rw [List.getElem_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem_singleton]
        rw [hmemf_eq.2 hmem]; exact Function.update_self _ _ _
  · intro a hnf hout
    have hntf : a ≠ a_tf := fun h => hnf (h ▸ Or.inl ⟨by unfold a_tf btSlotTouchedBase; omega,
      by unfold a_tf btSlotTouchedBase bundleTableCoreSize; clear * - hjs_lt; omega⟩)
    have ht4 : memf a = mem_t4 a := by
      by_cases hmem : js.1 ∈ touched
      · rw [hmemf_eq.1 hmem]
      · have hlt := htlen_lt_of_not hmem
        rw [hmemf_eq.2 hmem, Function.update_of_ne (by unfold a_tb; omega), Function.update_of_ne hntf]
    rw [ht4]
    have ha_es' : a ≠ a_es := fun h => hnf (h ▸ Or.inl ⟨by unfold a_es btEdgeSlotBase; omega,
      by unfold a_es btEdgeSlotBase bundleTableCoreSize; clear * - he_lt; omega⟩)
    have ha_nE' : a ≠ a_nE := fun h => hnf (h ▸ bsAddr_in_coreFoot hm_js (by unfold bundleSlotBlockSize; omega))
    have ha_dn' : a ≠ a_dn := fun h => hnf (h ▸ Or.inl ⟨by unfold a_dn btSlotDelNextBase; omega,
      by unfold a_dn btSlotDelNextBase bundleTableCoreSize; clear * - he_lt; omega⟩)
    have ha_dh' : a ≠ a_dh := fun h => hnf (h ▸ Or.inl ⟨by unfold a_dh btSlotDelHeadBase; omega,
      by unfold a_dh btSlotDelHeadBase bundleTableCoreSize; clear * - hjs_lt; omega⟩)
    simp only [mem_t4, Function.update_of_ne ha_dh', Function.update_of_ne ha_dn',
      Function.update_of_ne ha_nE', Function.update_of_ne ha_es']
    exact hm2_eq_m0 a
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsHeadBase; omega, by unfold bsHeadBase bundleSlotBlockSize; omega⟩))
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsSizeBase; omega, by unfold bsSizeBase bundleSlotBlockSize; omega⟩))
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsParentBase; omega, by unfold bsParentBase bundleSlotBlockSize; omega⟩))
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsHeadBase; omega, by unfold bsHeadBase bundleSlotBlockSize; omega⟩))
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsSizeBase; omega, by unfold bsSizeBase bundleSlotBlockSize; omega⟩))
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsParentBase; omega, by unfold bsParentBase bundleSlotBlockSize; omega⟩))
      (fun k hk => have := hL1_lt k hk;
        ⟨fun h => hnf (h ▸ Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableCoreSize; omega⟩),
         fun h => hnf (h ▸ Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableCoreSize; omega⟩)⟩)
      (fun k hk => have := hL2pre_lt k hk;
        ⟨fun h => hnf (h ▸ Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableCoreSize; omega⟩),
         fun h => hnf (h ▸ Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableCoreSize; omega⟩)⟩)

end

end MinCostFlow.SparseCore.Program
