module

public import MinCostFlow.LSF.Program.BatchTBlockSplitBase
import Mathlib.Tactic.Linarith

/-!
# Post-Split `dgT` Dynamic Graph Invariant (`BatchTBlockSplitPost`)

Proves `dgT_post_dynGraphAt`, showing that the tracker dynamic graph `dgT` remains a valid
`DynGraphAt` after inserting `v'` and moving all tracked incident self-loops.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Reassemble `DynGraphAt` for `dgT` after `dgAddVertex`, slot swap (`tag = 3`), and two
`dgMoveSlotLoop` calls on the same tracker list `L_tr`. -/
lemma dgT_post_dynGraphAt {gPtr vCap eCap tag v v' s_v s_v' : ℕ}
    {S_tr : Finset ℕ} {L_tr : List ℕ} {H : MGraph} {mem₁ mem₂ mem₃ : ℕ → ℕ}
    (hH_val : H.IsValid) (hvH : v ∈ H.V) (hv'H : v' ∉ H.V) (hv'_lt : v' < vCap)
    (hH1 : DynGraphAt mem₁ gPtr vCap eCap { H with V := insert v' H.V })
    (hsv_eq : mem₁ (dgExtToIntBase gPtr vCap + v) = s_v)
    (hsv'_eq : mem₁ (dgExtToIntBase gPtr vCap + v') = s_v')
    (hmem2 : mem₂ = if tag = 3 then
      Function.update
        (Function.update
          (Function.update
            (Function.update mem₁ (dgExtToIntBase gPtr vCap + v) s_v')
            (dgIntToExtBase gPtr vCap + s_v') v)
          (dgExtToIntBase gPtr vCap + v') s_v)
        (dgIntToExtBase gPtr vCap + s_v) v'
      else mem₁)
    (hfr23 : DgSlotsOnlyModified mem₂ mem₃ gPtr vCap eCap)
    (hInc3 : DgIncStateAt mem₃ gPtr vCap eCap H.E
      (fun x => if x ∈ L_tr.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.tail x) = s_v then s_v'
                else mem₁ (dgExtToIntBase gPtr vCap + H.tail x))
      (fun x => if x ∈ L_tr.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.head x) = s_v then s_v'
                else mem₁ (dgExtToIntBase gPtr vCap + H.head x)))
    (hself : ∀ e ∈ H.E, H.tail e = H.head e)
    (htag : (tag = 2 ∧ ∀ e ∈ H.E, e ∈ L_tr ↔ H.tail e = v ∧ e ∈ S_tr) ∨
            (tag = 3 ∧ ∀ e ∈ H.E, e ∈ L_tr ↔ H.tail e = v ∧ e ∉ S_tr)) :
    DynGraphAt mem₃ gPtr vCap eCap (H.applyUpdate (.split v v' (S_tr ∩ H.E) (S_tr ∩ H.E))) := by
  let H1 : MGraph := { H with V := insert v' H.V }
  let H' : MGraph := H.applyUpdate (.split v v' (S_tr ∩ H.E) (S_tr ∩ H.E))
  rcases hH1 with ⟨hval1, hvCap1, heCap1, h0_1, h1_1, h2_1, h3_1, hvp1, ⟨vL, hvL_len, hvL_nd,
    hvL_mem, hvL_at, hvL_pos⟩, heti1, hite1, hep1, ⟨eL, heL_len, heL_nd, heL_mem, heL_at,
    heL_pos⟩, _, _⟩
  have hne_vv' : v ≠ v' := fun h => hv'H (h ▸ hvH)
  have hv_V1 : v ∈ H1.V := Finset.mem_insert_of_mem hvH
  have hv'_V1 : v' ∈ H1.V := Finset.mem_insert_self v' H.V
  have hv_lt : v < vCap := hvCap1 v hv_V1
  have hsv_V1 : s_v ∈ H1.V := hsv_eq ▸ (heti1 v hv_V1).1
  have hsv'_V1 : s_v' ∈ H1.V := hsv'_eq ▸ (heti1 v' hv'_V1).1
  have hsv_lt : s_v < vCap := hvCap1 s_v hsv_V1
  have hsv'_lt : s_v' < vCap := hvCap1 s_v' hsv'_V1
  have hite_sv : mem₁ (dgIntToExtBase gPtr vCap + s_v) = v := hsv_eq ▸ (heti1 v hv_V1).2
  have hite_sv' : mem₁ (dgIntToExtBase gPtr vCap + s_v') = v' := hsv'_eq ▸ (heti1 v' hv'_V1).2
  have hne_s : s_v ≠ s_v' := fun h => hne_vv' (hite_sv.symm.trans (h ▸ hite_sv'))
  have hm3_before_sd : ∀ {addr}, addr < dgSlotDegBase gPtr vCap → mem₃ addr = mem₂ addr :=
    fun h => hfr23.before_slotDeg h
  have hm2_before_eti : ∀ {addr}, addr < dgExtToIntBase gPtr vCap → mem₂ addr = mem₁ addr := by
    intro addr hlt; rw [hmem2]; split_ifs
    · rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega)]
    · rfl
  have hm3_ePres : ∀ {addr}, dgEPresBase gPtr vCap ≤ addr → addr < dgETailSlotBase gPtr vCap eCap →
      mem₃ addr = mem₁ addr := by
    intro addr hlo hhi; rw [hfr23.ePres_eq hlo hhi, hmem2]; split_ifs
    · rw [Function.update_of_ne (by dsimp [dgEPresBase, dgIntToExtBase] at *; omega),
        Function.update_of_ne (by dsimp [dgEPresBase, dgExtToIntBase] at *; omega),
        Function.update_of_ne (by dsimp [dgEPresBase, dgIntToExtBase] at *; omega),
        Function.update_of_ne (by dsimp [dgEPresBase, dgExtToIntBase] at *; omega)]
    · rfl
  have hm3_eti : ∀ x < vCap, mem₃ (dgExtToIntBase gPtr vCap + x) = mem₂ (dgExtToIntBase gPtr vCap + x) :=
    fun x hx => hm3_before_sd (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega)
  have hm3_ite : ∀ x < vCap, mem₃ (dgIntToExtBase gPtr vCap + x) = mem₂ (dgIntToExtBase gPtr vCap + x) :=
    fun x hx => hm3_before_sd (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega)
  have heti2 : ∀ x ∈ H1.V,
      mem₂ (dgExtToIntBase gPtr vCap + x) ∈ H1.V ∧
      mem₂ (dgIntToExtBase gPtr vCap + mem₂ (dgExtToIntBase gPtr vCap + x)) = x := by
    intro x hx; have hx_lt : x < vCap := hvCap1 x hx
    rw [hmem2]; split_ifs
    · by_cases hxv : x = v
      · rw [hxv]
        have h1' : Function.update (Function.update (Function.update
            (Function.update mem₁ (dgExtToIntBase gPtr vCap + v) s_v')
            (dgIntToExtBase gPtr vCap + s_v') v) (dgExtToIntBase gPtr vCap + v') s_v)
            (dgIntToExtBase gPtr vCap + s_v) v' (dgExtToIntBase gPtr vCap + v) = s_v' := by
          rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
            Function.update_self]
        rw [h1']; refine ⟨hsv'_V1, ?_⟩
        rw [Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
          Function.update_of_ne (by dsimp [dgIntToExtBase, dgExtToIntBase]; omega),
          Function.update_self]
      · by_cases hxv' : x = v'
        · rw [hxv']
          have h1' : Function.update (Function.update (Function.update
              (Function.update mem₁ (dgExtToIntBase gPtr vCap + v) s_v')
              (dgIntToExtBase gPtr vCap + s_v') v) (dgExtToIntBase gPtr vCap + v') s_v)
              (dgIntToExtBase gPtr vCap + s_v) v' (dgExtToIntBase gPtr vCap + v') = s_v := by
            rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_self]
          rw [h1']; exact ⟨hsv_V1, Function.update_self _ _ _⟩
        · have hsx_V := (heti1 x hx).1
          have hsx_lt : mem₁ (dgExtToIntBase gPtr vCap + x) < vCap := hvCap1 _ hsx_V
          have hite_x := (heti1 x hx).2
          have hsx_ne_sv : mem₁ (dgExtToIntBase gPtr vCap + x) ≠ s_v :=
            fun hc => hxv (hite_x.symm.trans (hc ▸ hite_sv))
          have hsx_ne_sv' : mem₁ (dgExtToIntBase gPtr vCap + x) ≠ s_v' :=
            fun hc => hxv' (hite_x.symm.trans (hc ▸ hite_sv'))
          have h1' : Function.update (Function.update (Function.update
              (Function.update mem₁ (dgExtToIntBase gPtr vCap + v) s_v')
              (dgIntToExtBase gPtr vCap + s_v') v) (dgExtToIntBase gPtr vCap + v') s_v)
              (dgIntToExtBase gPtr vCap + s_v) v' (dgExtToIntBase gPtr vCap + x) =
              mem₁ (dgExtToIntBase gPtr vCap + x) := by
            rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase]; omega)]
          rw [h1']; refine ⟨hsx_V, ?_⟩
          rw [Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgIntToExtBase, dgExtToIntBase]; omega),
            Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgIntToExtBase, dgExtToIntBase]; omega), hite_x]
    · exact heti1 x hx
  have hite2 : ∀ s ∈ H1.V,
      mem₂ (dgIntToExtBase gPtr vCap + s) ∈ H1.V ∧
      mem₂ (dgExtToIntBase gPtr vCap + mem₂ (dgIntToExtBase gPtr vCap + s)) = s := by
    intro s hs; have hs_lt : s < vCap := hvCap1 s hs
    rw [hmem2]; split_ifs
    · by_cases hss : s = s_v
      · rw [hss, Function.update_self]; refine ⟨hv'_V1, ?_⟩
        rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
          Function.update_self]
      · by_cases hss' : s = s_v'
        · rw [hss']
          have h1' : Function.update (Function.update (Function.update
              (Function.update mem₁ (dgExtToIntBase gPtr vCap + v) s_v')
              (dgIntToExtBase gPtr vCap + s_v') v) (dgExtToIntBase gPtr vCap + v') s_v)
              (dgIntToExtBase gPtr vCap + s_v) v' (dgIntToExtBase gPtr vCap + s_v') = v := by
            rw [Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
              Function.update_of_ne (by dsimp [dgIntToExtBase, dgExtToIntBase]; omega),
              Function.update_self]
          rw [h1']; refine ⟨hv_V1, ?_⟩
          rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
            Function.update_self]
        · have hxs_V := (hite1 s hs).1
          have hxs_lt : mem₁ (dgIntToExtBase gPtr vCap + s) < vCap := hvCap1 _ hxs_V
          have heti_s := (hite1 s hs).2
          have hxs_ne_v : mem₁ (dgIntToExtBase gPtr vCap + s) ≠ v :=
            fun hc => hss (heti_s.symm.trans (hc ▸ hsv_eq))
          have hxs_ne_v' : mem₁ (dgIntToExtBase gPtr vCap + s) ≠ v' :=
            fun hc => hss' (heti_s.symm.trans (hc ▸ hsv'_eq))
          have h1' : Function.update (Function.update (Function.update
              (Function.update mem₁ (dgExtToIntBase gPtr vCap + v) s_v')
              (dgIntToExtBase gPtr vCap + s_v') v) (dgExtToIntBase gPtr vCap + v') s_v)
              (dgIntToExtBase gPtr vCap + s_v) v' (dgIntToExtBase gPtr vCap + s) =
              mem₁ (dgIntToExtBase gPtr vCap + s) := by
            rw [Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega)]
          rw [h1']; refine ⟨hxs_V, ?_⟩
          rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega), heti_s]
    · exact hite1 s hs
  have hend_slot : ∀ e ∈ H.E,
      (if e ∈ L_tr.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.tail e) = s_v then s_v'
       else mem₁ (dgExtToIntBase gPtr vCap + H.tail e)) =
        mem₃ (dgExtToIntBase gPtr vCap + H'.tail e) ∧
      (if e ∈ L_tr.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.head e) = s_v then s_v'
       else mem₁ (dgExtToIntBase gPtr vCap + H.head e)) =
        mem₃ (dgExtToIntBase gPtr vCap + H'.head e) := by
    intro e heE
    have hvalH := hH_val e heE
    have h_step : ∀ (z : ℕ) (hzV : z ∈ H.V),
        ((tag = 2 ∧ (e ∈ L_tr ↔ z = v ∧ e ∈ S_tr)) ∨ (tag = 3 ∧ (e ∈ L_tr ↔ z = v ∧ e ∉ S_tr))) →
        (if e ∈ L_tr.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + z) = s_v then s_v'
         else mem₁ (dgExtToIntBase gPtr vCap + z)) =
        mem₃ (dgExtToIntBase gPtr vCap + (if e ∈ S_tr ∩ H.E ∧ z = v then v' else z)) := by
      intro z hzV hTagL
      have hz_V1 : z ∈ H1.V := Finset.mem_insert_of_mem hzV
      have hz_lt : z < vCap := hvCap1 z hz_V1
      have hz_ne_v' : z ≠ v' := fun hc => hv'H (hc ▸ hzV)
      have hz_eq_sv : mem₁ (dgExtToIntBase gPtr vCap + z) = s_v ↔ z = v :=
        ⟨fun h => (heti1 z hz_V1).2.symm.trans (h ▸ hite_sv), fun h => h ▸ hsv_eq⟩
      rcases hTagL with ⟨rfl, hL2⟩ | ⟨rfl, hL3⟩
      · have hm23 : ∀ x < vCap, mem₃ (dgExtToIntBase gPtr vCap + x) = mem₁ (dgExtToIntBase gPtr vCap + x) := by
          intro x hx; rw [hm3_eti x hx, hmem2]; simp
        rw [hm23 _ (by split_ifs <;> [exact hv'_lt; exact hz_lt])]
        by_cases hzv : z = v
        · rw [hzv]
          by_cases heS : e ∈ S_tr
          · have heL : e ∈ L_tr.toFinset := List.mem_toFinset.mpr (hL2.mpr ⟨hzv, heS⟩)
            simp [heL, hsv_eq, heE, heS, hsv'_eq]
          · have heL : e ∉ L_tr.toFinset := fun hm => heS (hL2.mp (List.mem_toFinset.mp hm)).2
            simp [heL, heS]
        · simp [hz_eq_sv, hzv]
      · have hz'_lt : (if e ∈ S_tr ∩ H.E ∧ z = v then v' else z) < vCap := by split_ifs <;> assumption
        rw [hm3_eti _ hz'_lt, hmem2]; simp only [↓reduceIte]
        by_cases hzv : z = v
        · rw [hzv]
          by_cases heS : e ∈ S_tr
          · have heL : e ∉ L_tr.toFinset := fun hm => (hL3.mp (List.mem_toFinset.mp hm)).2 heS
            simp only [heL, false_and, ↓reduceIte, Finset.mem_inter, heS, heE, and_self]
            rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_self]; exact hsv_eq
          · have heL : e ∈ L_tr.toFinset := List.mem_toFinset.mpr (hL3.mpr ⟨hzv, heS⟩)
            simp only [heL, hsv_eq, and_self, ↓reduceIte, Finset.mem_inter, heS, false_and]
            rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_self]
        · have heq : ¬ (e ∈ L_tr.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + z) = s_v) :=
            fun h => hzv (hz_eq_sv.mp h.2)
          have heq2 : ¬ (e ∈ S_tr ∩ H.E ∧ z = v) := fun h => hzv h.2
          simp only [heq, ↓reduceIte, heq2]
          rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase]; omega)]
    have htag_t : (tag = 2 ∧ (e ∈ L_tr ↔ H.tail e = v ∧ e ∈ S_tr)) ∨
        (tag = 3 ∧ (e ∈ L_tr ↔ H.tail e = v ∧ e ∉ S_tr)) := by
      rcases htag with ⟨rfl, h2⟩ | ⟨rfl, h3⟩
      · exact Or.inl ⟨rfl, h2 e heE⟩
      · exact Or.inr ⟨rfl, h3 e heE⟩
    have htag_h : (tag = 2 ∧ (e ∈ L_tr ↔ H.head e = v ∧ e ∈ S_tr)) ∨
        (tag = 3 ∧ (e ∈ L_tr ↔ H.head e = v ∧ e ∉ S_tr)) := by
      rw [← hself e heE]; exact htag_t
    exact ⟨h_step (H.tail e) hvalH.1 htag_t, h_step (H.head e) hvalH.2 htag_h⟩
  rcases hInc3 with ⟨_, _, _, _, hets3, ⟨incL, hincL3⟩⟩
  have hets_final : ∀ e ∈ H.E,
      mem₃ (dgETailSlotBase gPtr vCap eCap + e) = mem₃ (dgExtToIntBase gPtr vCap + H'.tail e) ∧
      mem₃ (dgEHeadSlotBase gPtr vCap eCap + e) = mem₃ (dgExtToIntBase gPtr vCap + H'.head e) := fun e heE =>
    ⟨(hets3 e heE).1.trans (hend_slot e heE).1, (hets3 e heE).2.trans (hend_slot e heE).2⟩
  refine ⟨?_, hvCap1, heCap1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hets_final, ?_⟩
  · intro e heE; rcases hval1 e heE with ⟨ht1, hh1⟩
    constructor <;> (dsimp only [H', MGraph.applyUpdate]; split_ifs <;> [exact hv'_V1; assumption])
  · rw [hm3_before_sd (by dsimp [dgVCapOff, dgSlotDegBase]; omega),
      hm2_before_eti (by dsimp [dgVCapOff, dgExtToIntBase]; omega), h0_1]
  · rw [hm3_before_sd (by dsimp [dgECapOff, dgSlotDegBase]; omega),
      hm2_before_eti (by dsimp [dgECapOff, dgExtToIntBase]; omega), h1_1]
  · rw [hm3_before_sd (by dsimp [dgNOff, dgSlotDegBase]; omega),
      hm2_before_eti (by dsimp [dgNOff, dgExtToIntBase]; omega), h2_1]; rfl
  · rw [hm3_before_sd (by dsimp [dgMOff, dgSlotDegBase]; omega),
      hm2_before_eti (by dsimp [dgMOff, dgExtToIntBase]; omega), h3_1]; rfl
  · intro w hw
    rw [hm3_before_sd (by dsimp [dgVPresBase, dgSlotDegBase]; omega),
      hm2_before_eti (by dsimp [dgVPresBase, dgExtToIntBase]; omega)]
    simpa [H', H1, MGraph.applyUpdate] using hvp1 w hw
  · refine ⟨vL, hvL_len, hvL_nd, hvL_mem, fun i hi => ?_, fun i hi => ?_⟩
    · have hi_lt : i < vCap := by
        have := nodup_length_le_cap hvL_nd (fun x hx => hvCap1 x ((hvL_mem x).mp hx)); omega
      rw [hm3_before_sd (by dsimp [dgVListBase, dgSlotDegBase]; omega),
        hm2_before_eti (by dsimp [dgVListBase, dgExtToIntBase]; omega), hvL_at i hi]
    · have hv_lt_i : vL[i] < vCap := hvCap1 _ ((hvL_mem _).mp (List.getElem_mem hi))
      rw [hm3_before_sd (by dsimp [dgVPosBase, dgSlotDegBase]; omega),
        hm2_before_eti (by dsimp [dgVPosBase, dgExtToIntBase]; omega), hvL_pos i hi]
  · intro x hx; have hx_lt := hvCap1 x hx
    have hsx_lt := hvCap1 _ (heti2 x hx).1
    rw [hm3_eti x hx_lt, hm3_ite _ hsx_lt]; exact heti2 x hx
  · intro s hs; have hs_lt := hvCap1 s hs
    have hxs_lt := hvCap1 _ (hite2 s hs).1
    rw [hm3_ite s hs_lt, hm3_eti _ hxs_lt]; exact hite2 s hs
  · intro e he_lt
    rw [hm3_ePres (by dsimp [dgEPresBase]; omega) (by dsimp [dgEPresBase, dgETailSlotBase]; omega)]
    simpa [H', H1, MGraph.applyUpdate] using hep1 e he_lt
  · refine ⟨eL, heL_len, heL_nd, heL_mem, fun i hi => ?_, fun i hi => ?_⟩
    · have hi_lt : i < eCap := by
        have := nodup_length_le_cap heL_nd (fun x hx => heCap1 x ((heL_mem x).mp hx)); omega
      rw [hm3_ePres (by dsimp [dgEPresBase, dgEListBase]; omega)
        (by dsimp [dgEListBase, dgETailSlotBase]; omega), heL_at i hi]
    · have he_lt_i : eL[i] < eCap := heCap1 _ ((heL_mem _).mp (List.getElem_mem hi))
      rw [hm3_ePres (by dsimp [dgEPresBase, dgEPosBase]; omega)
        (by dsimp [dgEPosBase, dgETailSlotBase]; omega), heL_pos i hi]
  · refine ⟨incL, fun s hs => ?_⟩
    rcases hincL3 s hs with ⟨hdll, hdeg, hmem⟩
    refine ⟨hdll, hdeg, fun h => ?_⟩
    rw [hmem h]
    constructor <;> rintro ⟨hlt, h2E, hslot⟩ <;> refine ⟨hlt, h2E, ?_⟩
    · rcases hets3 (h / 2) h2E with ⟨hpt, hph⟩
      split_ifs at hslot ⊢ <;> [exact hpt.trans hslot; exact hph.trans hslot]
    · rcases hets3 (h / 2) h2E with ⟨hpt, hph⟩
      split_ifs at hslot ⊢ <;> [exact hpt.symm.trans hslot; exact hph.symm.trans hslot]

end

end MinCostFlow.LSF.Program
