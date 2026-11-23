module

public import MinCostFlow.DynSpanner.Program.DynGraphSplitOps
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# Dynamic graph vertex split verification (`DynGraphSplit`)

This file verifies `dgIdxApplySplit` (`dgApplySplitStmt bOps bSplit` at index `2` of
`dgSplitProcs bOps bSplit`): applying an encoded vertex split (`tag = 2` listing moved tail/head
lists `Lt, Lh`, or `tag = 3` listing kept tail/head ends at `v`) to `DynGraphAt` in
`O(kt + kh + 1)` time. The same procedure and contract uniformly handle direct updates on `G` and
restricted updates on any subgraph `H ⊆ G` sharing `H.V = G.V`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private lemma dgApplySplitSetup_triple {w : ℕ} {p : Program}
    {gPtr tag v v' s_v s_v' vCap eCap kt kh L_ptr : ℕ} {mem₁ : ℕ → ℕ}
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hvc_eq : mem₁ (gPtr + dgVCapOff) = vCap)
    (hsv_eq : mem₁ (dgExtToIntBase gPtr vCap + v) = s_v)
    (hsv'_eq : mem₁ (dgExtToIntBase gPtr vCap + v') = s_v')
    (hv_lt : v < vCap) (hv'_lt : v' < vCap)
    (hsv_lt : s_v < vCap) (hsv'_lt : s_v' < vCap) (_hlt_tag : tag < 2 ^ w) :
    let mem₂ := if tag = 3 then
      Function.update
        (Function.update
          (Function.update
            (Function.update mem₁ (dgExtToIntBase gPtr vCap + v) s_v')
            (dgIntToExtBase gPtr vCap + s_v') v)
          (dgExtToIntBase gPtr vCap + v') s_v)
        (dgIntToExtBase gPtr vCap + s_v) v'
      else mem₁
    Triple w p
      (fun st => st.regs 0 = gPtr ∧ st.regs 1 = tag ∧ st.regs 2 = v ∧ st.regs 3 = v' ∧
        st.regs 4 = kt ∧ st.regs 5 = kh ∧ st.regs 6 = L_ptr ∧ st.mem = mem₁)
      dgApplySplitSetupStmt
      (normalPost fun st => st.regs 0 = gPtr ∧ st.regs 4 = kt ∧ st.regs 5 = kh ∧
        st.regs 6 = L_ptr ∧ st.regs 9 = s_v ∧ st.regs 10 = s_v' ∧ st.mem = mem₂)
      (fun _ => 75) := by
  intro mem₂ st ω ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hmem⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hmem
  rw [hmem] at *
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_gp : gPtr < 2 ^ w := by omega
  have hlt_gp4 : gPtr + 4 < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_3vc : 3 * vCap < 2 ^ w := by omega
  have hlt_4vc : 4 * vCap < 2 ^ w := by omega
  have hlt_eti : dgExtToIntBase gPtr vCap < 2 ^ w := by dsimp [dgExtToIntBase]; omega
  have hlt_ite : dgIntToExtBase gPtr vCap < 2 ^ w := by dsimp [dgIntToExtBase]; omega
  have hlt_eti_v : dgExtToIntBase gPtr vCap + v < 2 ^ w := by dsimp [dgExtToIntBase]; omega
  have hlt_eti_v' : dgExtToIntBase gPtr vCap + v' < 2 ^ w := by dsimp [dgExtToIntBase]; omega
  have hlt_ite_sv : dgIntToExtBase gPtr vCap + s_v < 2 ^ w := by dsimp [dgIntToExtBase]; omega
  have hlt_ite_sv' : dgIntToExtBase gPtr vCap + s_v' < 2 ^ w := by dsimp [dgIntToExtBase]; omega
  have hlt_v : v < 2 ^ w := by omega
  have hlt_v' : v' < 2 ^ w := by omega
  have hlt_sv : s_v < 2 ^ w := by omega
  have hlt_sv' : s_v' < 2 ^ w := by omega
  suffices h : ∃ o st' c,
      Runs w p ω dgApplySplitSetupStmt { mem := mem₁, regs := str, pos := stp } o st' c ∧
      normalPost (fun st => st.regs 0 = gPtr ∧ st.regs 4 = kt ∧ st.regs 5 = kh ∧
        st.regs 6 = L_ptr ∧ st.regs 9 = s_v ∧ st.regs 10 = s_v' ∧ st.mem = mem₂) o st' ∧
      0 + c ≤ 75 by
    rcases h with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', c, hr, hq, by simpa using hc⟩
  dsimp only [dgApplySplitSetupStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := vCap) (by eval_expr)
    (by simpa [dgVCapOff] using hvc_eq)) ?_
  refine runs_seq_assign_le (v := dgExtToIntBase gPtr vCap) (by dsimp [dgExtToIntBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := dgIntToExtBase gPtr vCap) (by dsimp [dgIntToExtBase]; eval_expr) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := s_v) (by eval_expr) hsv_eq) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := s_v') (by eval_expr) hsv'_eq) ?_
  refine runs_cond_le (v := if tag = 3 then 1 else 0) (by eval_expr) ?_ ?_
  · intro hne3
    have htag3 : tag = 3 := by by_contra hc; simp [hc] at hne3
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hr0]
      · simp [hr4]
      · simp [hr5]
      · simp [hr6]
      · simp
      · simp
      · simp [mem₂, htag3]
    · dsimp only [Expr.size]; omega
  · intro he3
    have htag_ne : tag ≠ 3 := fun hc => by simp [hc] at he3
    refine runs_nop_le ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp [mem₂, htag_ne]⟩ ?_
    · simp [hr0]
    · simp [hr4]
    · simp [hr5]
    · simp [hr6]
    · simp
    · simp
    · dsimp only [Expr.size]; omega

private lemma dgApplySplit_post_dynGraphAt {gPtr vCap eCap tag v v' s_v s_v' : ℕ}
    {St Sh : Finset ℕ} {Lt Lh : List ℕ} {H : MGraph} {mem₁ mem₂ mem₃ : ℕ → ℕ}
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
      (fun x => if x ∈ Lt.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.tail x) = s_v then s_v'
                else mem₁ (dgExtToIntBase gPtr vCap + H.tail x))
      (fun x => if x ∈ Lh.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.head x) = s_v then s_v'
                else mem₁ (dgExtToIntBase gPtr vCap + H.head x)))
    (htag : (tag = 2 ∧ (∀ e ∈ H.E, e ∈ Lt ↔ H.tail e = v ∧ e ∈ St) ∧
        (∀ e ∈ H.E, e ∈ Lh ↔ H.head e = v ∧ e ∈ Sh)) ∨
      (tag = 3 ∧ (∀ e ∈ H.E, e ∈ Lt ↔ H.tail e = v ∧ e ∉ St) ∧
        (∀ e ∈ H.E, e ∈ Lh ↔ H.head e = v ∧ e ∉ Sh))) :
    DynGraphAt mem₃ gPtr vCap eCap (H.applyUpdate (.split v v' (St ∩ H.E) (Sh ∩ H.E))) := by
  let H1 : MGraph := { H with V := insert v' H.V }
  let H' : MGraph := H.applyUpdate (.split v v' (St ∩ H.E) (Sh ∩ H.E))
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
    intro addr hlt
    rw [hmem2]; split_ifs
    · rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
        Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega)]
    · rfl
  have hm3_ePres : ∀ {addr}, dgEPresBase gPtr vCap ≤ addr → addr < dgETailSlotBase gPtr vCap eCap →
      mem₃ addr = mem₁ addr := by
    intro addr hlo hhi
    rw [hfr23.ePres_eq hlo hhi, hmem2]; split_ifs
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
    intro x hx
    have hx_lt : x < vCap := hvCap1 x hx
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
        rw [h1']
        refine ⟨hsv'_V1, ?_⟩
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
          rw [h1']
          exact ⟨hsv_V1, Function.update_self _ _ _⟩
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
          rw [h1']
          refine ⟨hsx_V, ?_⟩
          rw [Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgIntToExtBase, dgExtToIntBase]; omega),
            Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgIntToExtBase, dgExtToIntBase]; omega), hite_x]
    · exact heti1 x hx
  have hite2 : ∀ s ∈ H1.V,
      mem₂ (dgIntToExtBase gPtr vCap + s) ∈ H1.V ∧
      mem₂ (dgExtToIntBase gPtr vCap + mem₂ (dgIntToExtBase gPtr vCap + s)) = s := by
    intro s hs
    have hs_lt : s < vCap := hvCap1 s hs
    rw [hmem2]; split_ifs
    · by_cases hss : s = s_v
      · rw [hss, Function.update_self]
        refine ⟨hv'_V1, ?_⟩
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
          rw [h1']
          refine ⟨hv_V1, ?_⟩
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
          rw [h1']
          refine ⟨hxs_V, ?_⟩
          have _ := hxs_lt
          have _ := hxs_ne_v
          have _ := hxs_ne_v'
          rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega), heti_s]
    · exact hite1 s hs
  have hend_slot : ∀ e ∈ H.E,
      (if e ∈ Lt.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.tail e) = s_v then s_v'
       else mem₁ (dgExtToIntBase gPtr vCap + H.tail e)) =
        mem₃ (dgExtToIntBase gPtr vCap + H'.tail e) ∧
      (if e ∈ Lh.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.head e) = s_v then s_v'
       else mem₁ (dgExtToIntBase gPtr vCap + H.head e)) =
        mem₃ (dgExtToIntBase gPtr vCap + H'.head e) := by
    intro e heE
    have hvalH := hH_val e heE
    have h_step : ∀ (L : List ℕ) (S : Finset ℕ) (z : ℕ) (hzV : z ∈ H.V),
        ((tag = 2 ∧ (e ∈ L ↔ z = v ∧ e ∈ S)) ∨ (tag = 3 ∧ (e ∈ L ↔ z = v ∧ e ∉ S))) →
        (if e ∈ L.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + z) = s_v then s_v'
         else mem₁ (dgExtToIntBase gPtr vCap + z)) =
        mem₃ (dgExtToIntBase gPtr vCap + (if e ∈ S ∩ H.E ∧ z = v then v' else z)) := by
      intro L S z hzV hTagL
      have hz_V1 : z ∈ H1.V := Finset.mem_insert_of_mem hzV
      have hz_lt : z < vCap := hvCap1 z hz_V1
      have hz_ne_v' : z ≠ v' := fun hc => hv'H (hc ▸ hzV)
      have hz_eq_sv : mem₁ (dgExtToIntBase gPtr vCap + z) = s_v ↔ z = v :=
        ⟨fun h => (heti1 z hz_V1).2.symm.trans (h ▸ hite_sv), fun h => h ▸ hsv_eq⟩
      rcases hTagL with ⟨rfl, hL2⟩ | ⟨rfl, hL3⟩
      · have hm23 : ∀ x < vCap, mem₃ (dgExtToIntBase gPtr vCap + x) = mem₁ (dgExtToIntBase gPtr vCap + x) := by
          intro x hx
          rw [hm3_eti x hx, hmem2]; simp
        rw [hm23 _ (by split_ifs <;> [exact hv'_lt; exact hz_lt])]
        by_cases hzv : z = v
        · rw [hzv]
          by_cases heS : e ∈ S
          · have heL : e ∈ L.toFinset := List.mem_toFinset.mpr (hL2.mpr ⟨hzv, heS⟩)
            simp [heL, hsv_eq, heE, heS, hsv'_eq]
          · have heL : e ∉ L.toFinset := fun hm => heS (hL2.mp (List.mem_toFinset.mp hm)).2
            simp [heL, heS]
        · simp [hz_eq_sv, hzv]
      · have hz'_lt : (if e ∈ S ∩ H.E ∧ z = v then v' else z) < vCap := by
          split_ifs <;> assumption
        rw [hm3_eti _ hz'_lt, hmem2]
        simp only [↓reduceIte]
        by_cases hzv : z = v
        · rw [hzv]
          by_cases heS : e ∈ S
          · have heL : e ∉ L.toFinset := fun hm => (hL3.mp (List.mem_toFinset.mp hm)).2 heS
            simp only [heL, false_and, ↓reduceIte, Finset.mem_inter, heS, heE, and_self]
            rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_self]
            exact hsv_eq
          · have heL : e ∈ L.toFinset := List.mem_toFinset.mpr (hL3.mpr ⟨hzv, heS⟩)
            simp only [heL, hsv_eq, and_self, ↓reduceIte, Finset.mem_inter, heS, false_and]
            rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
              Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
              Function.update_self]
        · have heq : ¬ (e ∈ L.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + z) = s_v) := by
            intro h; exact hzv (hz_eq_sv.mp h.2)
          have heq2 : ¬ (e ∈ S ∩ H.E ∧ z = v) := fun h => hzv h.2
          simp only [heq, ↓reduceIte, heq2]
          rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase]; omega)]
    exact ⟨h_step Lt St (H.tail e) hvalH.1
        (by rcases htag with ⟨rfl, ht2, _⟩ | ⟨rfl, ht3, _⟩
            · exact Or.inl ⟨rfl, ht2 e heE⟩
            · exact Or.inr ⟨rfl, ht3 e heE⟩),
      h_step Lh Sh (H.head e) hvalH.2
        (by rcases htag with ⟨rfl, _, hh2⟩ | ⟨rfl, _, hh3⟩
            · exact Or.inl ⟨rfl, hh2 e heE⟩
            · exact Or.inr ⟨rfl, hh3 e heE⟩)⟩
  rcases hInc3 with ⟨_, _, _, _, hets3, ⟨incL, hincL3⟩⟩
  have hets_final : ∀ e ∈ H.E,
      mem₃ (dgETailSlotBase gPtr vCap eCap + e) = mem₃ (dgExtToIntBase gPtr vCap + H'.tail e) ∧
      mem₃ (dgEHeadSlotBase gPtr vCap eCap + e) = mem₃ (dgExtToIntBase gPtr vCap + H'.head e) := by
    intro e heE
    rcases hets3 e heE with ⟨hpt, hph⟩
    rcases hend_slot e heE with ⟨hbt, hbh⟩
    exact ⟨hpt.trans hbt, hph.trans hbh⟩
  refine ⟨?_, ?_, heCap1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e heE
    rcases hval1 e heE with ⟨ht1, hh1⟩
    constructor
    · dsimp only [H', MGraph.applyUpdate]; split_ifs <;> [exact hv'_V1; exact ht1]
    · dsimp only [H', MGraph.applyUpdate]; split_ifs <;> [exact hv'_V1; exact hh1]
  · exact hvCap1
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
        have := nodup_length_le_cap hvL_nd (fun x hx => hvCap1 x ((hvL_mem x).mp hx))
        omega
      rw [hm3_before_sd (by dsimp [dgVListBase, dgSlotDegBase]; omega),
        hm2_before_eti (by dsimp [dgVListBase, dgExtToIntBase]; omega), hvL_at i hi]
    · have hv_lt_i : vL[i] < vCap := hvCap1 _ ((hvL_mem _).mp (List.getElem_mem hi))
      rw [hm3_before_sd (by dsimp [dgVPosBase, dgSlotDegBase]; omega),
        hm2_before_eti (by dsimp [dgVPosBase, dgExtToIntBase]; omega), hvL_pos i hi]
  · intro x hx
    have hx_lt : x < vCap := hvCap1 x hx
    have hsx_lt : mem₂ (dgExtToIntBase gPtr vCap + x) < vCap := hvCap1 _ (heti2 x hx).1
    rw [hm3_eti x hx_lt, hm3_ite _ hsx_lt]
    exact heti2 x hx
  · intro s hs
    have hs_lt : s < vCap := hvCap1 s hs
    have hxs_lt : mem₂ (dgIntToExtBase gPtr vCap + s) < vCap := hvCap1 _ (hite2 s hs).1
    rw [hm3_ite s hs_lt, hm3_eti _ hxs_lt]
    exact hite2 s hs
  · intro e he_lt
    rw [hm3_ePres (by dsimp [dgEPresBase]; omega) (by dsimp [dgEPresBase, dgETailSlotBase]; omega)]
    simpa [H', H1, MGraph.applyUpdate] using hep1 e he_lt
  · refine ⟨eL, heL_len, heL_nd, heL_mem, fun i hi => ?_, fun i hi => ?_⟩
    · have hi_lt : i < eCap := by
        have := nodup_length_le_cap heL_nd (fun x hx => heCap1 x ((heL_mem x).mp hx))
        omega
      rw [hm3_ePres (by dsimp [dgEPresBase, dgEListBase]; omega)
        (by dsimp [dgEListBase, dgETailSlotBase]; omega), heL_at i hi]
    · have he_lt_i : eL[i] < eCap := heCap1 _ ((heL_mem _).mp (List.getElem_mem hi))
      rw [hm3_ePres (by dsimp [dgEPresBase, dgEPosBase]; omega)
        (by dsimp [dgEPosBase, dgETailSlotBase]; omega), heL_pos i hi]
  · exact hets_final
  · refine ⟨incL, fun s hs => ?_⟩
    rcases hincL3 s hs with ⟨hdll, hdeg, hmem⟩
    refine ⟨hdll, hdeg, fun h => ?_⟩
    rw [hmem h]
    constructor <;> rintro ⟨hlt, h2E, hslot⟩ <;> refine ⟨hlt, h2E, ?_⟩
    · rcases hets3 (h / 2) h2E with ⟨hpt, hph⟩
      split_ifs at hslot ⊢
      · exact hpt.trans hslot
      · exact hph.trans hslot
    · rcases hets3 (h / 2) h2E with ⟨hpt, hph⟩
      split_ifs at hslot ⊢
      · exact hpt.symm.trans hslot
      · exact hph.symm.trans hslot

theorem dgApplySplit_meetsContract {w : ℕ} {p : Program} {b bOps vCap eCap : ℕ}
    {H : MGraph} {St Sh : Finset ℕ} {Lt Lh : List ℕ}
    (hp : p.HasAt b (dgSplitProcs bOps b)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + dgIdxApplySplit)
      (dgApplySplitContract w vCap eCap H St Sh Lt Lh) := by
  refine meetsContract_of_runs (hp.get (i := dgIdxApplySplit) (by simp [dgSplitProcs, dgIdxApplySplit]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, tag, v, v', kt, kh, L_ptr, rfl, hw16, hbound, hLbound,
    hvH, hv'H, hv'_lt, hH, hLt_len, hLh_len, hL_at, hL_word, hL_disj, htag⟩
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  have hlt_gp : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_tag : tag < 2 ^ w := hargs tag (by simp)
  have hlt_v : v < 2 ^ w := hargs v (by simp)
  have hlt_v' : v' < 2 ^ w := hargs v' (by simp)
  have hlt_kt : kt < 2 ^ w := hargs kt (by simp)
  have hlt_kh : kh < 2 ^ w := hargs kh (by simp)
  have hlt_Lp : L_ptr < 2 ^ w := hargs L_ptr (by simp)
  have hlt_0w : (0 : ℕ) < 2 ^ w := Nat.lt_of_lt_of_le (by decide) hw16
  have hlt_1w : (1 : ℕ) < 2 ^ w := Nat.lt_of_lt_of_le (by decide) hw16
  refine runs_start_le ?_
  dsimp only [dgSplitProcs, dgIdxApplySplit, List.getElem_cons_succ, List.getElem_cons_zero, dgApplySplitStmt]
  have hargs_av : evalArgs w (startState [gPtr, tag, v, v', kt, kh, L_ptr] mem pos) [.reg 0, .reg 3] =
      some [gPtr, v'] := by eval_expr
  have hpre_av : (dgAddVertexContract w vCap eCap H).pre [gPtr, v'] mem :=
    ⟨gPtr, v', rfl, hw16, hbound, hv'_lt, hH⟩
  refine runs_seq_call_le (dgAddVertex_meetsContract hpOps) hargs_av
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl|rfl) <;> omega)
    hpre_av ?_
  rintro ret_av mem₁ pos₁ ⟨_, _, hEq_av, _, hH1, hfr_av⟩
  simp only [List.cons.injEq, and_true] at hEq_av
  rcases hEq_av with ⟨h1, h2⟩
  subst h1 h2
  have hL_at₁ : ListAt mem₁ L_ptr (Lt ++ Lh) := fun i hi => by
    have hi_k : i < kt + kh := by simp only [List.length_append] at hi; omega
    have hfr := hfr_av _ (hL_disj i hi_k)
    simpa [startState] using hfr.trans (hL_at i hi)
  let H1 : MGraph := { H with V := insert v' H.V }
  have hH1_copy := hH1
  rcases hH1_copy with ⟨hval1, hvCap1, heCap1, h0_1, h1_1, _, _, _, _, heti1, _, hep1, _, hets1, ⟨incL1, hincL1⟩⟩
  have hv_V1 : v ∈ H1.V := Finset.mem_insert_of_mem hvH
  have hv'_V1 : v' ∈ H1.V := Finset.mem_insert_self v' H.V
  set s_v := mem₁ (dgExtToIntBase gPtr vCap + v)
  set s_v' := mem₁ (dgExtToIntBase gPtr vCap + v')
  have hsv_V1 : s_v ∈ H1.V := (heti1 v hv_V1).1
  have hsv'_V1 : s_v' ∈ H1.V := (heti1 v' hv'_V1).1
  have hsv_lt : s_v < vCap := hvCap1 s_v hsv_V1
  have hsv'_lt : s_v' < vCap := hvCap1 s_v' hsv'_V1
  have hne_vv' : v ≠ v' := fun h => hv'H (h ▸ hvH)
  have hne_s : s_v ≠ s_v' := fun h => by
    have hite_v := (heti1 v hv_V1).2
    have hite_v' := (heti1 v' hv'_V1).2
    exact hne_vv' (hite_v.symm.trans (by simpa [s_v, s_v', h] using hite_v'))
  have hv_lt : v < vCap := hvCap1 v hv_V1
  let mem₂ := if tag = 3 then
    Function.update
      (Function.update
        (Function.update
          (Function.update mem₁ (dgExtToIntBase gPtr vCap + v) s_v')
          (dgIntToExtBase gPtr vCap + s_v') v)
        (dgExtToIntBase gPtr vCap + v') s_v)
      (dgIntToExtBase gPtr vCap + s_v) v'
    else mem₁
  refine runs_seq_triple_le
    (dgApplySplitSetup_triple (w := w) (tag := tag) (v := v) (v' := v') (s_v := s_v) (s_v' := s_v')
      (vCap := vCap) (eCap := eCap) (kt := kt) (kh := kh) (L_ptr := L_ptr) (mem₁ := mem₁)
      hbound h0_1 rfl rfl hv_lt hv'_lt hsv_lt hsv'_lt hlt_tag)
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], rfl⟩ ?_
  rintro st₃ ⟨hr3_0, hr3_4, hr3_5, hr3_6, hr3_9, hr3_10, hmem₃⟩
  have hlt_sv : s_v < 2 ^ w := by omega
  have hlt_sv' : s_v' < 2 ^ w := by omega
  have hL_at₂ : ListAt mem₂ L_ptr (Lt ++ Lh) := fun i hi => by
    have hi_k : i < kt + kh := by simp only [List.length_append] at hi; omega
    have hout := hL_disj i hi_k
    have hbound'' := hbound'
    have hd_lt : ∀ x < vCap, dgExtToIntBase gPtr vCap + x < gPtr + dynGraphSize vCap eCap ∧
        gPtr ≤ dgExtToIntBase gPtr vCap + x := fun x hx => by
      dsimp [dgExtToIntBase, dynGraphSize]; omega
    have hi_lt : ∀ x < vCap, dgIntToExtBase gPtr vCap + x < gPtr + dynGraphSize vCap eCap ∧
        gPtr ≤ dgIntToExtBase gPtr vCap + x := fun x hx => by
      dsimp [dgIntToExtBase, dynGraphSize]; omega
    have h1 := hd_lt v hv_lt; have h2 := hd_lt v' hv'_lt
    have h3 := hi_lt s_v hsv_lt; have h4 := hi_lt s_v' hsv'_lt
    dsimp only [mem₂]; split_ifs
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), hL_at₁ i hi]
    · exact hL_at₁ i hi
  have hLt_at₂ : ListAt mem₂ L_ptr Lt := fun i hi => by
    have hi' : i < (Lt ++ Lh).length := by simp only [List.length_append]; omega
    have hget := hL_at₂ i hi'
    rwa [List.getElem_append_left hi] at hget
  have hLt_word : ∀ x ∈ Lt, x < 2 ^ w := fun x hx => hL_word x (List.mem_append_left Lh hx)
  have hLt_disj : ∀ i < kt, L_ptr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ L_ptr + i :=
    fun i hi => hL_disj i (by omega)
  have hInc₂ : DgIncStateAt mem₂ gPtr vCap eCap H.E
      (fun x => mem₁ (dgExtToIntBase gPtr vCap + H.tail x))
      (fun x => mem₁ (dgExtToIntBase gPtr vCap + H.head x)) := by
    have hm2_eq : ∀ {addr}, (addr < dgExtToIntBase gPtr vCap ∨ dgSlotDegBase gPtr vCap ≤ addr) →
        mem₂ addr = mem₁ addr := by
      intro addr h
      dsimp only [mem₂]; split_ifs
      · rcases h with hlo | hhi
        · rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega)]
        · rw [Function.update_of_ne (by dsimp [dgSlotDegBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgSlotDegBase, dgExtToIntBase] at *; omega),
            Function.update_of_ne (by dsimp [dgSlotDegBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgSlotDegBase, dgExtToIntBase] at *; omega)]
      · rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm2_eq (Or.inl (by dsimp [dgVCapOff, dgExtToIntBase]; omega)), h0_1]
    · rw [hm2_eq (Or.inl (by dsimp [dgECapOff, dgExtToIntBase]; omega)), h1_1]
    · intro e heE
      have he_lt := heCap1 e heE
      have hvt := (hval1 e heE).1
      have hvh := (hval1 e heE).2
      exact ⟨he_lt, hvCap1 _ (heti1 _ hvt).1, hvCap1 _ (heti1 _ hvh).1⟩
    · intro e he_lt
      rw [hm2_eq (Or.inr (by dsimp [dgEPresBase, dgSlotDegBase]; omega)), hep1 e he_lt]
    · intro e heE
      have he_lt := heCap1 e heE
      rw [hm2_eq (Or.inr (by dsimp [dgETailSlotBase, dgSlotDegBase]; omega)),
        hm2_eq (Or.inr (by dsimp [dgEHeadSlotBase, dgSlotDegBase]; omega))]
      exact hets1 e heE
    · refine ⟨incL1, fun s hs => ?_⟩
      rcases hincL1 s hs with ⟨hdll, hdeg, hmem⟩
      refine ⟨hdll.of_agree
        (hm2_eq (Or.inr (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)))
        (fun x hx => hm2_eq (Or.inr (by dsimp [dgHePrevBase, dgSlotDegBase]; omega)))
        (fun x hx => hm2_eq (Or.inr (by dsimp [dgHeNextBase, dgSlotDegBase]; omega))),
        ?_, fun h => ?_⟩
      · rw [hm2_eq (Or.inr (by dsimp [dgSlotDegBase]; omega)), hdeg]
      · rw [hmem h]
        constructor <;> rintro ⟨hlt, h2E, hslot⟩ <;> refine ⟨hlt, h2E, ?_⟩
        · rcases hets1 (h / 2) h2E with ⟨ht, hh_⟩
          split_ifs at hslot ⊢ <;> [exact ht.symm.trans hslot; exact hh_.symm.trans hslot]
        · rcases hets1 (h / 2) h2E with ⟨ht, hh_⟩
          split_ifs at hslot ⊢ <;> [exact ht.trans hslot; exact hh_.trans hslot]
  have hargs_loopT : evalArgs w st₃ [.reg 0, .reg 9, .reg 10, .reg 6, .reg 4, .const 0] =
      some [gPtr, s_v, s_v', L_ptr, kt, 0] := by eval_expr
  have hpre_loopT : (dgMoveSlotLoopContract w vCap eCap H.E
      (fun x => mem₁ (dgExtToIntBase gPtr vCap + H.tail x))
      (fun x => mem₁ (dgExtToIntBase gPtr vCap + H.head x)) Lt false).pre
      [gPtr, s_v, s_v', L_ptr, kt, 0] st₃.mem := by
    rw [hmem₃]
    exact ⟨gPtr, s_v, s_v', L_ptr, kt, rfl, hw16, hbound, by omega,
      hsv_lt, hsv'_lt, hne_s, hLt_len, hLt_at₂, hLt_word, hLt_disj, hInc₂⟩
  change st₃.mem = mem₂ at hmem₃
  refine runs_seq_call_le (dgMoveSlotLoop_meetsContract hp hpOps) hargs_loopT
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl|rfl|rfl|rfl|rfl|rfl) <;> omega)
    hpre_loopT ?_
  rintro ret₁ mem₃ pos₃ ⟨_, _, _, _, _, hEq₁, _, hInc₃, hfr23⟩
  simp only [List.cons.injEq, and_true] at hEq₁
  rcases hEq₁ with ⟨hl1, hl2, hl3, hl4, hl5, _⟩
  subst hl1 hl2 hl3 hl4 hl5
  rw [hmem₃] at hfr23
  have hlt_Lpkt : L_ptr + kt < 2 ^ w := by omega
  have hLh_at₃ : ListAt mem₃ (L_ptr + kt) Lh := fun i hi => by
    have hout := hL_disj (kt + i) (by omega)
    have hfr := hfr23.outside (by simpa [Nat.add_assoc] using hout)
    rw [Nat.add_assoc, hfr]
    have hi' : kt + i < (Lt ++ Lh).length := by simp only [List.length_append]; omega
    have hget := hL_at₂ (kt + i) hi'
    have hlen_le : Lt.length ≤ kt + i := by omega
    rw [List.getElem_append_right hlen_le] at hget
    simpa [hLt_len] using hget
  have hLh_word : ∀ x ∈ Lh, x < 2 ^ w := fun x hx => hL_word x (List.mem_append_right Lt hx)
  have hLh_disj : ∀ i < kh, L_ptr + kt + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ L_ptr + kt + i :=
    fun i hi => by simpa [Nat.add_assoc] using hL_disj (kt + i) (by omega)
  have hargs_loopH : evalArgs w
      { mem := mem₃, regs := Function.update st₃.regs 14 ret₁, pos := pos₃ }
      [.reg 0, .reg 9, .reg 10, .bin .add (.reg 6) (.reg 4), .reg 5, .const 1] =
      some [gPtr, s_v, s_v', L_ptr + kt, kh, 1] := by eval_expr
  have hpre_loopH : (dgMoveSlotLoopContract w vCap eCap H.E
      (fun x => if x ∈ Lt.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.tail x) = s_v then s_v'
                else mem₁ (dgExtToIntBase gPtr vCap + H.tail x))
      (fun x => mem₁ (dgExtToIntBase gPtr vCap + H.head x)) Lh true).pre
      [gPtr, s_v, s_v', L_ptr + kt, kh, 1] mem₃ := by
    refine ⟨gPtr, s_v, s_v', L_ptr + kt, kh, rfl, hw16, hbound, by omega,
      hsv_lt, hsv'_lt, hne_s, hLh_len, hLh_at₃, hLh_word, hLh_disj, ?_⟩
    simpa only [Bool.false_eq_true, ↓reduceIte] using hInc₃
  refine runs_seq_call_le (dgMoveSlotLoop_meetsContract hp hpOps) hargs_loopH
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl|rfl|rfl|rfl|rfl|rfl) <;> omega)
    hpre_loopH ?_
  rintro _ mem₄ pos₄ ⟨_, _, _, _, _, hEq_loop, _, hInc₄, hfr34⟩
  simp only [List.cons.injEq, and_true] at hEq_loop
  rcases hEq_loop with ⟨hl1', hl2', hl3', hl4', hl5', _⟩
  subst hl1' hl2' hl3' hl4' hl5'
  have hfr24 : DgSlotsOnlyModified mem₂ mem₄ gPtr vCap eCap := hfr23.trans hfr34
  have hInc₄' : DgIncStateAt mem₄ gPtr vCap eCap H.E
      (fun x => if x ∈ Lt.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.tail x) = s_v then s_v'
                else mem₁ (dgExtToIntBase gPtr vCap + H.tail x))
      (fun x => if x ∈ Lh.toFinset ∧ mem₁ (dgExtToIntBase gPtr vCap + H.head x) = s_v then s_v'
                else mem₁ (dgExtToIntBase gPtr vCap + H.head x)) := by
    simpa only [↓reduceIte] using hInc₄
  refine runs_ret_le (by eval_expr) ?_ ?_
  · refine ⟨gPtr, tag, v, v', kt, kh, L_ptr, rfl, rfl, ?_, ?_⟩
    · exact dgApplySplit_post_dynGraphAt hH.1 hvH hv'H hv'_lt hH1 rfl rfl rfl hfr24 hInc₄' htag
    · intro addr hout
      have hm12 : mem₂ addr = mem₁ addr := by
        dsimp only [mem₂]; split_ifs
        · rw [Function.update_of_ne (by dsimp [dgIntToExtBase, dynGraphSize] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dynGraphSize] at *; omega),
            Function.update_of_ne (by dsimp [dgIntToExtBase, dynGraphSize] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dynGraphSize] at *; omega)]
        · rfl
      exact (hfr24.outside hout).trans (hm12.trans (hfr_av addr hout))
  · dsimp only [dgAddVertexContract, dgMoveSlotLoopContract, dgApplySplitContract,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, argsSize, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
