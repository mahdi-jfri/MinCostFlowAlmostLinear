module

public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalksDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerRev

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Post-state invariant helper for `dsSetLevelWalks_step_triple` (`DynSpannerSetLevelWalksPost`)
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

lemma dsSetLevelWalks_step_post {L vCap eCap b lvl mEmbPtr heapPtr gen0 k
    heapCur heapNext : ℕ} {G H : MGraph} {eL : List ℕ} {emb : MinCostFlow.Embedding}
    {foot0 : ℕ → Prop} {mem st_mem mem3 : ℕ → ℕ} {revCur : ℕ → List ℕ}
    (hlvlL : lvl ≤ L) (hfix_le : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (heL_nd : eL.Nodup) (heG_cov : ∀ e ∈ G.E, e < eCap)
    (_hvH : ∀ v ∈ H.V, v < vCap)
    (heL_spec : ∀ e ∈ eL,
      e ∈ G.E ∧ H.IsWalk (G.tail e) (G.head e) (emb e) ∧
      MWalkAt mem (mem (mEmbPtr + e)) (emb e) ∧
      b + dsFixedSize L vCap eCap ≤ mem (mEmbPtr + e) ∧
      mem (mEmbPtr + e) + (mWalkEncode (emb e)).length ≤ heapPtr)
    (hk : k < eL.length)
    (hhp1 : heapPtr ≤ heapCur)
    (hhp2 : heapCur ≤ heapPtr + 2 * ((eL.take k).map fun e => (emb e).length + 1).sum)
    (hgen_st : st_mem (b + dsGenOff) = gen0 + 1 + k)
    (hdom_st : st_mem (dsDomGenBase b L vCap eCap + lvl) = gen0 + 1)
    (hedg_le : ∀ e' < eCap, st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e') ≤ st_mem (b + dsGenOff))
    (hedg_st : ∀ e' < eCap, st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e') = gen0 + 1 ↔ e' ∈ eL.take k)
    (hpi_st : ∀ e' ∈ eL.take k,
      st_mem (dsPiPtrBase b L vCap eCap + lvl * eCap + e') = mem (mEmbPtr + e') ∧
      MWalkAt st_mem (st_mem (dsPiPtrBase b L vCap eCap + lvl * eCap + e')) (emb e'))
    (hrev_st : ∀ v < vCap,
      st_mem (dsRevGenBase b L vCap eCap + lvl * vCap + v) ≤ st_mem (b + dsGenOff) ∧
      (revCur v).Nodup ∧
      (∀ e', e' ∈ revCur v ↔ e' ∈ eL.take k ∧ v ∈ H.walkVertices (G.tail e') (emb e')) ∧
      if 0 < st_mem (dsDomGenBase b L vCap eCap + lvl) ∧
          st_mem (dsRevGenBase b L vCap eCap + lvl * vCap + v) = st_mem (dsDomGenBase b L vCap eCap + lvl)
      then LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)) st_mem
        (st_mem (dsRevHeadBase b L vCap eCap + lvl * vCap + v)) (revCur v)
      else revCur v = [])
    (hfr : ∀ addr, dsLevelWalksFrameCond L vCap eCap b lvl heapPtr heapCur addr → st_mem addr = mem addr)
    (he_cap : eL[k]'hk < eCap)
    (hmWalk_2 : MWalkAt (Function.update
      (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
      (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk)))
      (mem (mEmbPtr + eL[k]'hk)) (emb (eL[k]'hk)))
    (hhpN1 : heapCur + 2 ≤ heapNext)
    (hhpN2 : heapNext ≤ heapCur + 2 * ((emb (eL[k]'hk)).length + 1))
    (hgen3 : mem3 (b + dsGenOff) = (Function.update
      (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
      (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk))) (b + dsGenOff) + 1)
    (hrev3 : ∀ v < vCap,
      if v ∈ H.walkVertices (G.tail (eL[k]'hk)) (emb (eL[k]'hk)) then
        mem3 (dsRevGenBase b L vCap eCap + lvl * vCap + v) =
          (Function.update
            (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
            (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk)))
            (dsDomGenBase b L vCap eCap + lvl) ∧
        LinkedListIn (fun a => (foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)) ∨ (heapCur ≤ a ∧ a < heapNext))
          mem3 (mem3 (dsRevHeadBase b L vCap eCap + lvl * vCap + v)) ((eL[k]'hk) :: revCur v)
      else
        mem3 (dsRevGenBase b L vCap eCap + lvl * vCap + v) =
          (Function.update
            (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
            (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk)))
            (dsRevGenBase b L vCap eCap + lvl * vCap + v) ∧
        mem3 (dsRevHeadBase b L vCap eCap + lvl * vCap + v) =
          (Function.update
            (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
            (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk)))
            (dsRevHeadBase b L vCap eCap + lvl * vCap + v) ∧
        (if mem3 (dsRevGenBase b L vCap eCap + lvl * vCap + v) =
            (Function.update
              (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
              (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk)))
              (dsDomGenBase b L vCap eCap + lvl)
         then LinkedListIn (fun a => (foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)) ∨ (heapCur ≤ a ∧ a < heapNext))
                mem3 (mem3 (dsRevHeadBase b L vCap eCap + lvl * vCap + v)) (revCur v)
         else revCur v = []))
    (hfr3 : ∀ addr,
      addr ≠ b + dsGenOff →
      (∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v) →
      (∀ v < vCap, addr ≠ dsRevGenBase b L vCap eCap + lvl * vCap + v) →
      (∀ v < vCap, addr ≠ dsRevHeadBase b L vCap eCap + lvl * vCap + v) →
      (addr < heapCur ∨ heapNext ≤ addr) →
      mem3 addr =
        (Function.update
          (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
          (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk))) addr) :
    let e := eL[k]'hk
    let domAddr := dsDomGenBase b L vCap eCap + lvl
    let revNext : ℕ → List ℕ := fun v =>
      if v ∈ H.walkVertices (G.tail e) (emb e) then e :: revCur v else revCur v
    heapNext ≤ heapPtr + 2 * ((eL.take (k + 1)).map fun e => (emb e).length + 1).sum ∧
    mem3 (b + dsGenOff) = gen0 + 1 + (k + 1) ∧
    mem3 domAddr = gen0 + 1 ∧
    (∀ e' < eCap, mem3 (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e') ≤ mem3 (b + dsGenOff)) ∧
    (∀ e' < eCap, mem3 (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e') = gen0 + 1 ↔ e' ∈ eL.take (k + 1)) ∧
    (∀ e' ∈ eL.take (k + 1),
      mem3 (dsPiPtrBase b L vCap eCap + lvl * eCap + e') = mem (mEmbPtr + e') ∧
      MWalkAt mem3 (mem3 (dsPiPtrBase b L vCap eCap + lvl * eCap + e')) (emb e')) ∧
    (∀ v < vCap,
      mem3 (dsRevGenBase b L vCap eCap + lvl * vCap + v) ≤ mem3 (b + dsGenOff) ∧
      (revNext v).Nodup ∧
      (∀ e', e' ∈ revNext v ↔ e' ∈ eL.take (k + 1) ∧ v ∈ H.walkVertices (G.tail e') (emb e')) ∧
      if 0 < mem3 domAddr ∧ mem3 (dsRevGenBase b L vCap eCap + lvl * vCap + v) = mem3 domAddr then
        LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < heapNext)) mem3
          (mem3 (dsRevHeadBase b L vCap eCap + lvl * vCap + v)) (revNext v)
      else revNext v = []) ∧
    (∀ addr, dsLevelWalksFrameCond L vCap eCap b lvl heapPtr heapNext addr → mem3 addr = mem addr) := by
  intro e domAddr revNext
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hb_gen_lt : b + dsGenOff < b + dsHdrSize := by simp [dsGenOff, dsHdrSize]
  have hmin_ge : b + dsHdrSize ≤ dsMinHBase b vCap eCap := by rw [h1]; omega
  have hdom_ge_min : dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap := by rw [h2]; omega
  have hdom_ed : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap := rfl
  have hed_pi : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap ≤ dsPiPtrBase b L vCap eCap := by
    simp [dsPiPtrBase]
  have hpi_rev : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  have hvst_fix : dsVStampBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
    rw [← hf]; simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
  have hdom_lt_ed : domAddr < dsEdgeDomGenBase b L vCap eCap := by dsimp [domAddr]; omega
  have hm_v : ∀ v < vCap, lvl * vCap + v < (L + 1) * vCap := fun _ hv => mul_add_lt_mul_succ hlvlL hv
  have hm_e : lvl * eCap + e < (L + 1) * eCap := by
    calc lvl * eCap + e < lvl * eCap + eCap := Nat.add_lt_add_left he_cap _
      _ = (lvl + 1) * eCap := by ring
      _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvlL)
  have hmem2_fr : ∀ a,
      a ≠ dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk →
      a ≠ dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk →
      Function.update
        (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
        (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk)) a = st_mem a :=
    fun a ha1 ha2 => by rw [Function.update_of_ne ha2, Function.update_of_ne ha1]
  have hfr3_heap : ∀ a, b + dsFixedSize L vCap eCap ≤ a → a < heapCur → mem3 a =
      Function.update
        (Function.update st_mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + eL[k]'hk) (gen0 + 1))
        (dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk) (mem (mEmbPtr + eL[k]'hk)) a := by
    intro a ha1 ha2
    exact hfr3 a (by omega) (fun _ _ => by omega) (fun v hv => by have := hm_v v hv; omega)
      (fun v hv => by have := hm_v v hv; omega) (Or.inl ha2)
  have he_not_take : e ∉ eL.take k := by
    intro hmem
    rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, hje⟩
    simp only [List.length_take, List.getElem_take] at hj hje
    exact absurd (heL_nd.getElem_inj_iff.mp hje) (by omega)
  have hmem3_gen : mem3 (b + dsGenOff) = gen0 + 1 + (k + 1) := by
    rw [hgen3, hmem2_fr _ (by omega) (by omega), hgen_st]; omega
  have hmem3_dom : mem3 domAddr = gen0 + 1 := by
    rw [hfr3 domAddr (by omega) (fun _ _ => by omega) (fun v hv => by have := hm_v v hv; omega)
      (fun v hv => by have := hm_v v hv; omega) (Or.inl (by omega)), hmem2_fr _ (by omega) (by omega), hdom_st]
  have hed'_ne_pi : ∀ e' < eCap, dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e' ≠
      dsPiPtrBase b L vCap eCap + lvl * eCap + eL[k]'hk := by
    intro e' he'
    have hm' : lvl * eCap + e' < (L + 1) * eCap := by
      calc lvl * eCap + e' < lvl * eCap + eCap := Nat.add_lt_add_left he' _
        _ = (lvl + 1) * eCap := by ring
        _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvlL)
    omega
  refine ⟨by rw [take_succ_sum_walks eL emb hk]; omega, hmem3_gen, hmem3_dom, ?_, ?_, ?_, ?_, ?_⟩
  · intro e' he'
    have hm' : lvl * eCap + e' < (L + 1) * eCap := by
      calc lvl * eCap + e' < lvl * eCap + eCap := Nat.add_lt_add_left he' _
        _ = (lvl + 1) * eCap := by ring
        _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvlL)
    rw [hfr3 _ (by omega) (fun _ _ => by omega) (fun v hv => by have := hm_v v hv; omega)
      (fun v hv => by have := hm_v v hv; omega) (Or.inl (by omega))]
    rw [Function.update_of_ne (hed'_ne_pi e' he'), hmem3_gen]
    by_cases hee : e' = eL[k]'hk
    · subst hee; rw [Function.update_self]; omega
    · rw [Function.update_of_ne (by omega)]; exact le_trans (hedg_le e' he') (by omega)
  · intro e' he'
    have hm' : lvl * eCap + e' < (L + 1) * eCap := by
      calc lvl * eCap + e' < lvl * eCap + eCap := Nat.add_lt_add_left he' _
        _ = (lvl + 1) * eCap := by ring
        _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvlL)
    rw [hfr3 _ (by omega) (fun _ _ => by omega) (fun v hv => by have := hm_v v hv; omega)
      (fun v hv => by have := hm_v v hv; omega) (Or.inl (by omega))]
    rw [Function.update_of_ne (hed'_ne_pi e' he'), List.take_succ_eq_append_getElem hk,
      List.mem_append, List.mem_singleton]
    by_cases hee : e' = eL[k]'hk
    · subst hee; rw [Function.update_self]; simp
    · rw [Function.update_of_ne (by omega), hedg_st e' he']; simp [hee]
  · intro e' he'
    rw [List.take_succ_eq_append_getElem hk, List.mem_append, List.mem_singleton] at he'
    have he'_cap : e' < eCap := by
      rcases he' with htk | rfl
      · exact heG_cov e' (heL_spec e' (List.mem_of_mem_take htk)).1
      · exact he_cap
    have hm' : lvl * eCap + e' < (L + 1) * eCap := by
      calc lvl * eCap + e' < lvl * eCap + eCap := Nat.add_lt_add_left he'_cap _
        _ = (lvl + 1) * eCap := by ring
        _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvlL)
    rw [hfr3 _ (by omega) (fun _ _ => by omega) (fun v hv => by have := hm_v v hv; omega)
      (fun v hv => by have := hm_v v hv; omega) (Or.inl (by omega))]
    rcases he' with htk | rfl
    · have hne' : e' ≠ eL[k]'hk := fun h => by dsimp only [e] at he_not_take; exact he_not_take (h ▸ htk)
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      obtain ⟨hpe, hmw⟩ := hpi_st e' htk
      refine ⟨hpe, hmw.of_agree fun a ha1 ha2 => ?_⟩
      obtain ⟨_, _, _, hwlo', hwhi'⟩ := heL_spec e' (List.mem_of_mem_take htk)
      have hml' := mWalkEncode_length (emb e')
      rw [hpe] at ha1 ha2
      rw [hfr3_heap a (le_trans hwlo' ha1) (by omega), hmem2_fr a (by omega) (by omega)]
    · rw [Function.update_self]
      refine ⟨rfl, hmWalk_2.of_agree fun a ha1 ha2 => ?_⟩
      obtain ⟨_, _, _, hwlo', hwhi'⟩ := heL_spec (eL[k]'hk) (List.getElem_mem hk)
      have hml' := mWalkEncode_length (emb (eL[k]'hk))
      exact hfr3_heap a (le_trans hwlo' ha1) (by omega)
  · intro v hv
    have hrv3 := hrev3 v hv
    have hr_v := hrev_st v hv
    have hfoot_sub : ∀ a, ((foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)) ∨ (heapCur ≤ a ∧ a < heapNext)) →
        (foot0 a ∨ (heapPtr ≤ a ∧ a < heapNext)) := by
      intro a ha
      rcases ha with (ha0 | ⟨ha1, ha2⟩) | ⟨ha1, ha2⟩
      · exact Or.inl ha0
      · exact Or.inr ⟨ha1, by omega⟩
      · exact Or.inr ⟨le_trans hhp1 ha1, ha2⟩
    by_cases hv_w : v ∈ H.walkVertices (G.tail e) (emb e)
    · simp only [e, hv_w, ↓reduceIte, revNext] at hrv3 ⊢
      rw [hmem2_fr _ (by omega) (by omega), hdom_st] at hrv3
      refine ⟨by rw [hrv3.1, hmem3_gen]; omega, List.nodup_cons.mpr ⟨?_, hr_v.2.1⟩, ?_, ?_⟩
      · intro hmem; exact he_not_take ((hr_v.2.2.1 e).mp hmem).1
      · intro e'
        rw [List.mem_cons, hr_v.2.2.1 e', List.take_succ_eq_append_getElem hk,
          List.mem_append, List.mem_singleton]
        by_cases hee : e' = e
        · subst hee; simp [e, hv_w]
        · simp [e, hee]
      · rw [hmem3_dom, hrv3.1]
        simp only [Nat.zero_lt_succ, true_and, ↓reduceIte]
        exact hrv3.2.mono hfoot_sub
    · simp only [e, hv_w, ↓reduceIte, revNext] at hrv3 ⊢
      have hrg_old := hmem2_fr (dsRevGenBase b L vCap eCap + lvl * vCap + v)
        (by have := hm_v v hv; omega) (by have := hm_v v hv; omega)
      have hrh_old := hmem2_fr (dsRevHeadBase b L vCap eCap + lvl * vCap + v)
        (by have := hm_v v hv; omega) (by have := hm_v v hv; omega)
      have hdom_old := hmem2_fr (dsDomGenBase b L vCap eCap + lvl) (by omega) (by omega)
      rw [hrv3.1, hrg_old]
      refine ⟨le_trans hr_v.1 (by omega), hr_v.2.1, ?_, ?_⟩
      · intro e'
        rw [hr_v.2.2.1 e', List.take_succ_eq_append_getElem hk, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨htk, hv'⟩; exact ⟨Or.inl htk, hv'⟩
        · rintro ⟨htk | rfl, hv'⟩
          · exact ⟨htk, hv'⟩
          · exact absurd hv' hv_w
      · rw [hmem3_dom]
        rw [hdom_st] at hr_v
        rw [hdom_old, hdom_st, hrv3.1, hrg_old] at hrv3
        by_cases hcond : st_mem (dsRevGenBase b L vCap eCap + lvl * vCap + v) = gen0 + 1
        · simp only [hcond, Nat.zero_lt_succ, and_self, ↓reduceIte] at hr_v hrv3 ⊢
          exact hrv3.2.2.mono hfoot_sub
        · simp only [hcond, and_false, ↓reduceIte] at hr_v hrv3 ⊢
          exact hr_v.2.2.2
  · intro addr hfc
    rw [hfr3 addr hfc.1 hfc.2.2.2.2.2.2.1 hfc.2.2.2.2.1 hfc.2.2.2.2.2.1
      (by rcases hfc.2.2.2.2.2.2.2 with h | h <;> [exact Or.inl (lt_of_lt_of_le h hhp1); exact Or.inr h])]
    rw [hmem2_fr addr (hfc.2.2.1 (eL[k]'hk) he_cap) (hfc.2.2.2.1 (eL[k]'hk) he_cap)]
    exact hfr addr (dsLevelWalksFrameCond_mono (by omega) hfc)

end

end MinCostFlow.DynSpanner.Program
