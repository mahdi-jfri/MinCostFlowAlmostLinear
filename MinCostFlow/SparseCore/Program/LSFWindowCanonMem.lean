module

public import MinCostFlow.SparseCore.Program.LSFWindowCanonDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Verification of Canonical Guest Memory (`LSFWindowCanonMem`)

Proves `canonDGMem_fold_props`, `canonGuestMem_dynGraphAt`, `canonGuestMem_lengths`, and
`canonGuestMem_lt_two_pow` for the canonical guest memory image defined in `LSFWindowCanonDefs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.WideWord MinCostFlow.Num

/-! ## Verification of `canonDGMem` (`DynGraphAt` and word bounds) -/

private lemma pushHalfEdgeMem_frame {vCap eCap s he a : ℕ} {mem : ℕ → ℕ}
    (hs : s < vCap) (hhe : he < 2 * eCap)
    (hold : mem (dgIncHeadBase 0 vCap + s) = 0 ∨ mem (dgIncHeadBase 0 vCap + s) - 1 < 2 * eCap)
    (ha_deg : a < dgSlotDegBase 0 vCap ∨ dgEPresBase 0 vCap ≤ a)
    (ha_he : a < dgHePrevBase 0 vCap eCap ∨ dynGraphSize vCap eCap ≤ a) :
    pushHalfEdgeMem vCap eCap s he mem a = mem a := by
  unfold pushHalfEdgeMem
  have hne5 : a ≠ dgSlotDegBase 0 vCap + s := by
    dsimp [dgSlotDegBase, dgEPresBase] at ha_deg ⊢; omega
  have hne4 : a ≠ dgIncHeadBase 0 vCap + s := by
    dsimp [dgSlotDegBase, dgIncHeadBase, dgEPresBase] at ha_deg ⊢; omega
  have hne2 : a ≠ dgHeNextBase 0 vCap eCap + he := by
    dsimp [dgHePrevBase, dgHeNextBase, dynGraphSize] at ha_he ⊢; omega
  have hne1 : a ≠ dgHePrevBase 0 vCap eCap + he := by
    dsimp [dgHePrevBase, dynGraphSize] at ha_he ⊢; omega
  rw [Function.update_of_ne hne5, Function.update_of_ne hne4]
  split_ifs with h0
  · rw [Function.update_of_ne hne2, Function.update_of_ne hne1]
  · have hlt : mem (dgIncHeadBase 0 vCap + s) - 1 < 2 * eCap := hold.resolve_left h0
    have hne3 : a ≠ dgHePrevBase 0 vCap eCap + (mem (dgIncHeadBase 0 vCap + s) - 1) := by
      dsimp [dgHePrevBase, dynGraphSize] at ha_he ⊢; omega
    rw [Function.update_of_ne hne3, Function.update_of_ne hne2, Function.update_of_ne hne1]

private lemma pushHalfEdgeMem_step {vCap eCap s he : ℕ} {mem : ℕ → ℕ} {incL : ℕ → List ℕ}
    (hs : s < vCap) (hhe : he < 2 * eCap)
    (hfresh : ∀ s' < vCap, he ∉ incL s')
    (hinv : ∀ s' < vCap,
      IsDoublyLinkedList mem (dgHePrevBase 0 vCap eCap) (dgHeNextBase 0 vCap eCap)
        (dgIncHeadBase 0 vCap + s') (2 * eCap) (incL s') ∧
      mem (dgSlotDegBase 0 vCap + s') = (incL s').length)
    (hdisj : ∀ s₁ < vCap, ∀ s₂ < vCap, s₁ ≠ s₂ → ∀ x, x ∈ incL s₁ → x ∉ incL s₂) :
    let mem' := pushHalfEdgeMem vCap eCap s he mem
    let incL' : ℕ → List ℕ := fun s' => if s' = s then he :: incL s else incL s'
    (∀ s' < vCap,
      IsDoublyLinkedList mem' (dgHePrevBase 0 vCap eCap) (dgHeNextBase 0 vCap eCap)
        (dgIncHeadBase 0 vCap + s') (2 * eCap) (incL' s') ∧
      mem' (dgSlotDegBase 0 vCap + s') = (incL' s').length) ∧
    (∀ s₁ < vCap, ∀ s₂ < vCap, s₁ ≠ s₂ → ∀ x, x ∈ incL' s₁ → x ∉ incL' s₂) := by
  intro mem' incL'
  obtain ⟨⟨hnd_s, hlt_s, hhd_s, hbody_s⟩, hdeg_s⟩ := hinv s hs
  have hhead_bound : mem (dgIncHeadBase 0 vCap + s) = 0 ∨
      (∃ h0, incL s = h0 :: (incL s).tail ∧ mem (dgIncHeadBase 0 vCap + s) = h0 + 1 ∧ h0 < 2 * eCap) := by
    cases hLs : incL s with
    | nil => left; rw [hhd_s, hLs]
    | cons h0 tl =>
      right
      refine ⟨h0, rfl, by rw [hhd_s, hLs], hlt_s h0 (by rw [hLs]; exact List.mem_cons_self)⟩
  have hslot_ne_inc : ∀ s₁ < vCap, ∀ s₂ < vCap, dgSlotDegBase 0 vCap + s₁ ≠ dgIncHeadBase 0 vCap + s₂ := by
    intro s₁ h1 s₂ h2; dsimp [dgSlotDegBase, dgIncHeadBase]; omega
  have hslot_ne_prev : ∀ s₁ < vCap, ∀ x < 2 * eCap, dgSlotDegBase 0 vCap + s₁ ≠ dgHePrevBase 0 vCap eCap + x := by
    intro s₁ h1 x hx; dsimp [dgSlotDegBase, dgHePrevBase]; omega
  have hslot_ne_next : ∀ s₁ < vCap, ∀ x < 2 * eCap, dgSlotDegBase 0 vCap + s₁ ≠ dgHeNextBase 0 vCap eCap + x := by
    intro s₁ h1 x hx; dsimp [dgSlotDegBase, dgHeNextBase]; omega
  have hinc_ne_prev : ∀ s₁ < vCap, ∀ x < 2 * eCap, dgIncHeadBase 0 vCap + s₁ ≠ dgHePrevBase 0 vCap eCap + x := by
    intro s₁ h1 x hx; dsimp [dgIncHeadBase, dgHePrevBase]; omega
  have hinc_ne_next : ∀ s₁ < vCap, ∀ x < 2 * eCap, dgIncHeadBase 0 vCap + s₁ ≠ dgHeNextBase 0 vCap eCap + x := by
    intro s₁ h1 x hx; dsimp [dgIncHeadBase, dgHeNextBase]; omega
  have hprev_ne_next : ∀ x < 2 * eCap, ∀ y < 2 * eCap, dgHePrevBase 0 vCap eCap + x ≠ dgHeNextBase 0 vCap eCap + y := by
    intro x hx y hy; dsimp [dgHePrevBase, dgHeNextBase]; omega
  constructor
  · intro s' hs'
    by_cases hss : s' = s
    · subst hss
      simp only [incL', ite_true]
      refine ⟨⟨List.nodup_cons.mpr ⟨hfresh s' hs', hnd_s⟩, ?_, ?_, ?_⟩, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hhe
        · exact hlt_s x hx
      · dsimp only [mem', pushHalfEdgeMem]
        rw [Function.update_of_ne (Ne.symm (hslot_ne_inc s' hs' s' hs')), Function.update_self]
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, ite_true]
          have hne_old : ∀ h0, incL s' = h0 :: (incL s').tail → he ≠ h0 := fun h0 hEq hEq2 =>
            hfresh s' hs' (by rw [hEq, hEq2]; exact List.mem_cons_self)
          constructor
          · dsimp only [mem', pushHalfEdgeMem]
            rw [Function.update_of_ne (Ne.symm (hslot_ne_prev s' hs' he hhe)),
                Function.update_of_ne (Ne.symm (hinc_ne_prev s' hs' he hhe))]
            rcases hhead_bound with h0 | ⟨h0, hEq, hhd_eq, hh0_lt⟩
            · rw [ite_eq_left h0, Function.update_of_ne (hprev_ne_next he hhe he hhe), Function.update_self]
            · have hne0 : mem (dgIncHeadBase 0 vCap + s') ≠ 0 := by omega
              rw [ite_eq_right hne0,
                  Function.update_of_ne (by have := hne_old h0 hEq; omega),
                  Function.update_of_ne (hprev_ne_next he hhe he hhe), Function.update_self]
          · dsimp only [mem', pushHalfEdgeMem]
            rw [Function.update_of_ne (Ne.symm (hslot_ne_next s' hs' he hhe)),
                Function.update_of_ne (Ne.symm (hinc_ne_next s' hs' he hhe))]
            rcases hhead_bound with h0 | ⟨h0, hEq, hhd_eq, hh0_lt⟩
            · have hlen0 : (incL s').length = 0 := by
                cases hL : incL s' with
                | nil => rfl
                | cons a l => rw [hL] at hhd_s; simp at hhd_s; omega
              rw [ite_eq_left h0, Function.update_self, h0]
              simp [hlen0]
            · have hne0 : mem (dgIncHeadBase 0 vCap + s') ≠ 0 := by omega
              rw [ite_eq_right hne0,
                  Function.update_of_ne (Ne.symm (hprev_ne_next _ (by omega) he hhe)),
                  Function.update_self, hhd_eq]
              cases hL : incL s' with
              | nil => rw [hL] at hEq; cases hEq
              | cons a l =>
                rw [hL] at hEq
                injection hEq with ha
                subst ha
                simp
        | succ i =>
          have hi_lt : i < (incL s').length := by simp at hi; omega
          set x := (incL s')[i]'hi_lt
          have hx_mem : x ∈ incL s' := List.getElem_mem hi_lt
          have hx_lt : x < 2 * eCap := hlt_s x hx_mem
          have hx_ne_he : x ≠ he := fun h => hfresh s' hs' (h ▸ hx_mem)
          obtain ⟨hp_old, hn_old⟩ := hbody_s i hi_lt
          simp only [List.getElem_cons_succ, Nat.succ_ne_zero, ↓reduceIte]
          constructor
          · dsimp only [mem', pushHalfEdgeMem]
            rw [Function.update_of_ne (Ne.symm (hslot_ne_prev s' hs' x hx_lt)),
                Function.update_of_ne (Ne.symm (hinc_ne_prev s' hs' x hx_lt))]
            cases i with
            | zero =>
              have hhd_eq : mem (dgIncHeadBase 0 vCap + s') = x + 1 := by
                cases hL : incL s' with
                | nil => simp [hL] at hi_lt
                | cons a l =>
                  simp only [x, hL, List.getElem_cons_zero]
                  rw [hhd_s, hL]
              rw [ite_eq_right (by omega), show mem (dgIncHeadBase 0 vCap + s') - 1 = x by omega,
                  Function.update_self]
              simp
            | succ j =>
              have hx_ne_h0 : x ≠ (incL s')[0]'(by omega) := fun hEq => by
                have := (List.Nodup.getElem_inj hnd_s).mp hEq
                omega
              have hhd_eq : mem (dgIncHeadBase 0 vCap + s') = (incL s')[0]'(by omega) + 1 := by
                rcases hhead_bound with h0 | ⟨h0, hEq, hhd_eq, _⟩
                · exfalso
                  cases hL : incL s' with
                  | nil => simp [hL] at hi_lt
                  | cons a l => rw [hL] at hhd_s; simp at hhd_s; omega
                · rw [hhd_eq]
                  have h0_eq : (incL s')[0]'(by omega) = h0 := by
                    have hlen_pos : 0 < (incL s').length := by omega
                    have := congrArg (fun l => l[0]?) hEq
                    simp only [List.getElem?_eq_getElem hlen_pos, List.getElem?_cons_zero, Option.some.injEq] at this
                    exact this
                  rw [h0_eq]
              rw [ite_eq_right (by omega),
                  Function.update_of_ne (by omega),
                  Function.update_of_ne (hprev_ne_next x hx_lt he hhe),
                  Function.update_of_ne (by omega)]
              simpa [x] using hp_old
          · dsimp only [mem', pushHalfEdgeMem]
            rw [Function.update_of_ne (Ne.symm (hslot_ne_next s' hs' x hx_lt)),
                Function.update_of_ne (Ne.symm (hinc_ne_next s' hs' x hx_lt))]
            rcases hhead_bound with h0 | ⟨h0, _, hhd_eq, hh0_lt⟩
            · rw [ite_eq_left h0, Function.update_of_ne (by omega),
                  Function.update_of_ne (Ne.symm (hprev_ne_next he hhe x hx_lt))]
              simpa [x] using hn_old
            · rw [ite_eq_right (by omega),
                  Function.update_of_ne (Ne.symm (hprev_ne_next _ (by omega) x hx_lt)),
                  Function.update_of_ne (by omega),
                  Function.update_of_ne (Ne.symm (hprev_ne_next he hhe x hx_lt))]
              simpa [x] using hn_old
      · dsimp only [mem', pushHalfEdgeMem]
        rw [Function.update_self, hdeg_s, List.length_cons]
    · simp only [incL', ite_eq_right hss]
      obtain ⟨hdll', hdeg'⟩ := hinv s' hs'
      refine ⟨hdll'.of_agree ?_ ?_ ?_, ?_⟩
      · dsimp only [mem', pushHalfEdgeMem]
        rw [Function.update_of_ne (Ne.symm (hslot_ne_inc s hs s' hs')),
            Function.update_of_ne (by omega)]
        rcases hhead_bound with h0 | ⟨h0, _, hhd_eq, hh0_lt⟩
        · rw [ite_eq_left h0, Function.update_of_ne (hinc_ne_next s' hs' he hhe),
              Function.update_of_ne (hinc_ne_prev s' hs' he hhe)]
        · rw [ite_eq_right (by omega), Function.update_of_ne (hinc_ne_prev s' hs' _ (by omega)),
              Function.update_of_ne (hinc_ne_next s' hs' he hhe),
              Function.update_of_ne (hinc_ne_prev s' hs' he hhe)]
      · intro x hx
        have hx_lt : x < 2 * eCap := hdll'.2.1 x hx
        have hx_ne_he : x ≠ he := fun h => hfresh s' hs' (h ▸ hx)
        dsimp only [mem', pushHalfEdgeMem]
        rw [Function.update_of_ne (Ne.symm (hslot_ne_prev s hs x hx_lt)),
            Function.update_of_ne (Ne.symm (hinc_ne_prev s hs x hx_lt))]
        rcases hhead_bound with h0 | ⟨h0, hEq, hhd_eq, hh0_lt⟩
        · rw [ite_eq_left h0, Function.update_of_ne (hprev_ne_next x hx_lt he hhe),
              Function.update_of_ne (by omega)]
        · have hx_ne_h0 : x ≠ h0 := fun h =>
            hdisj s' hs' s hs hss x hx (by rw [h, hEq]; exact List.mem_cons_self)
          rw [ite_eq_right (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (hprev_ne_next x hx_lt he hhe),
              Function.update_of_ne (by omega)]
      · intro x hx
        have hx_lt : x < 2 * eCap := hdll'.2.1 x hx
        have hx_ne_he : x ≠ he := fun h => hfresh s' hs' (h ▸ hx)
        dsimp only [mem', pushHalfEdgeMem]
        rw [Function.update_of_ne (Ne.symm (hslot_ne_next s hs x hx_lt)),
            Function.update_of_ne (Ne.symm (hinc_ne_next s hs x hx_lt))]
        rcases hhead_bound with h0 | ⟨h0, _, hhd_eq, hh0_lt⟩
        · rw [ite_eq_left h0, Function.update_of_ne (by omega),
              Function.update_of_ne (Ne.symm (hprev_ne_next he hhe x hx_lt))]
        · rw [ite_eq_right (by omega), Function.update_of_ne (Ne.symm (hprev_ne_next _ (by omega) x hx_lt)),
              Function.update_of_ne (by omega),
              Function.update_of_ne (Ne.symm (hprev_ne_next he hhe x hx_lt))]
      · dsimp only [mem', pushHalfEdgeMem]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (hslot_ne_inc s' hs' s hs)]
        rcases hhead_bound with h0 | ⟨h0, _, hhd_eq, hh0_lt⟩
        · rw [ite_eq_left h0, Function.update_of_ne (hslot_ne_next s' hs' he hhe),
              Function.update_of_ne (hslot_ne_prev s' hs' he hhe), hdeg']
        · rw [ite_eq_right (by omega), Function.update_of_ne (hslot_ne_prev s' hs' _ (by omega)),
              Function.update_of_ne (hslot_ne_next s' hs' he hhe),
              Function.update_of_ne (hslot_ne_prev s' hs' he hhe), hdeg']
  · intro s₁ h1 s₂ h2 hne x hx1 hx2
    by_cases hs1 : s₁ = s
    · subst hs1
      simp only [incL', ite_true, ite_eq_right (Ne.symm hne)] at hx1 hx2
      rcases List.mem_cons.mp hx1 with rfl | hx1'
      · exact hfresh s₂ h2 hx2
      · exact hdisj s₁ h1 s₂ h2 hne x hx1' hx2
    · by_cases hs2 : s₂ = s
      · subst hs2
        simp only [incL', ite_true, ite_eq_right hs1] at hx1 hx2
        rcases List.mem_cons.mp hx2 with rfl | hx2'
        · exact hfresh s₁ h1 hx1
        · exact hdisj s₁ h1 s₂ h2 hne x hx1 hx2'
      · simp only [incL', ite_eq_right hs1, ite_eq_right hs2] at hx1 hx2
        exact hdisj s₁ h1 s₂ h2 hne x hx1 hx2

lemma canonDGMem_fold_props {G₀ : MGraph} (hG₀ : G₀.IsValid) :
    ∀ (es : List ℕ), es.Nodup → (∀ e ∈ es, e ∈ G₀.E) →
      let vCap := canonVCap G₀
      let eCap := canonECap G₀
      let mem' := es.foldl (pushEdgeIncMem G₀ vCap eCap) (canonDGMemBase G₀)
      (∀ a, (a < dgSlotDegBase 0 vCap ∨ dgEPresBase 0 vCap ≤ a) →
            (a < dgHePrevBase 0 vCap eCap ∨ dynGraphSize vCap eCap ≤ a) →
            mem' a = canonDGMemBase G₀ a) ∧
      (∃ incL : ℕ → List ℕ,
        (∀ s < vCap,
          IsDoublyLinkedList mem' (dgHePrevBase 0 vCap eCap) (dgHeNextBase 0 vCap eCap)
            (dgIncHeadBase 0 vCap + s) (2 * eCap) (incL s) ∧
          mem' (dgSlotDegBase 0 vCap + s) = (incL s).length ∧
          (∀ h, h ∈ incL s ↔
            h < 2 * eCap ∧ h / 2 ∈ es ∧
            (if h % 2 = 0 then G₀.tail (h / 2) else G₀.head (h / 2)) = s)) ∧
        (∀ s₁ < vCap, ∀ s₂ < vCap, s₁ ≠ s₂ → ∀ x, x ∈ incL s₁ → x ∉ incL s₂)) ∧
      (∀ a, mem' a < dynGraphSize vCap eCap) := by
  intro es hnd hsub
  set vCap := canonVCap G₀
  set eCap := canonECap G₀
  have hbase_lt : ∀ a, canonDGMemBase G₀ a < dynGraphSize vCap eCap := by
    classical
    intro a
    have hv_le : G₀.n ≤ vCap := by
      have hsubV : G₀.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (canonVCap_gt hv)
      calc G₀.n = G₀.V.card := rfl
        _ ≤ (Finset.range vCap).card := Finset.card_le_card hsubV
        _ = vCap := Finset.card_range vCap
    have hm_le : G₀.m ≤ eCap := by
      have hsubE : G₀.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (canonECap_gt he)
      calc G₀.m = G₀.E.card := rfl
        _ ≤ (Finset.range eCap).card := Finset.card_le_card hsubE
        _ = eCap := Finset.card_range eCap
    have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
    have hhdr := canonDGMemBase_hdr G₀
    by_cases h0 : a = 0
    · subst h0; rw [hhdr.1]; omega
    by_cases h1 : a = 1
    · subst h1; rw [hhdr.2.1]; omega
    by_cases h2 : a = 2
    · subst h2; rw [hhdr.2.2.1]; omega
    by_cases h3 : a = 3
    · subst h3; rw [hhdr.2.2.2]; omega
    by_cases h4 : a < dgVListBase 0 vCap
    · have hlt : a - 4 < vCap := by dsimp [dgVListBase] at h4; omega
      rw [show a = dgVPresBase 0 + (a - 4) by dsimp [dgVPresBase]; omega,
          canonDGMemBase_vPres hlt]
      split_ifs <;> omega
    by_cases h5 : a < dgVPosBase 0 vCap
    · have hlt : a - dgVListBase 0 vCap < vCap := by dsimp [dgVListBase, dgVPosBase] at h4 h5 ⊢; omega
      rw [show a = dgVListBase 0 vCap + (a - dgVListBase 0 vCap) by omega,
          canonDGMemBase_vList hlt]
      by_cases hi : a - dgVListBase 0 vCap < (canonVList G₀).length
      · rw [List.getD_eq_getElem _ _ hi]
        have := canonVCap_gt ((G₀.V.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)); omega
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; omega
    by_cases h6 : a < dgExtToIntBase 0 vCap
    · have hlt : a - dgVPosBase 0 vCap < vCap := by dsimp [dgVPosBase, dgExtToIntBase] at h5 h6 ⊢; omega
      rw [show a = dgVPosBase 0 vCap + (a - dgVPosBase 0 vCap) by omega,
          canonDGMemBase_vPos hlt]
      split_ifs with hv
      · have hidx : (canonVList G₀).idxOf (a - dgVPosBase 0 vCap) < (canonVList G₀).length :=
          List.idxOf_lt_length_of_mem ((G₀.V.mem_sort (· ≤ ·)).mpr hv)
        have hlen : (canonVList G₀).length = G₀.n := G₀.V.length_sort (· ≤ ·)
        omega
      · omega
    by_cases h7 : a < dgIntToExtBase 0 vCap
    · have hlt : a - dgExtToIntBase 0 vCap < vCap := by dsimp [dgExtToIntBase, dgIntToExtBase] at h6 h7 ⊢; omega
      rw [show a = dgExtToIntBase 0 vCap + (a - dgExtToIntBase 0 vCap) by omega,
          canonDGMemBase_extToInt hlt]
      split_ifs with hv
      · have := canonVCap_gt hv; omega
      · omega
    by_cases h8 : a < dgSlotDegBase 0 vCap
    · have hlt : a - dgIntToExtBase 0 vCap < vCap := by dsimp [dgIntToExtBase, dgSlotDegBase] at h7 h8 ⊢; omega
      rw [show a = dgIntToExtBase 0 vCap + (a - dgIntToExtBase 0 vCap) by omega,
          canonDGMemBase_intToExt hlt]
      split_ifs with hv
      · have := canonVCap_gt hv; omega
      · omega
    by_cases h9 : a < dgIncHeadBase 0 vCap
    · have hlt : a - dgSlotDegBase 0 vCap < vCap := by dsimp [dgSlotDegBase, dgIncHeadBase] at h8 h9 ⊢; omega
      rw [show a = dgSlotDegBase 0 vCap + (a - dgSlotDegBase 0 vCap) by omega,
          canonDGMemBase_slotDeg hlt]; omega
    by_cases h10 : a < dgEPresBase 0 vCap
    · have hlt : a - dgIncHeadBase 0 vCap < vCap := by dsimp [dgIncHeadBase, dgEPresBase] at h9 h10 ⊢; omega
      rw [show a = dgIncHeadBase 0 vCap + (a - dgIncHeadBase 0 vCap) by omega,
          canonDGMemBase_incHead hlt]; omega
    by_cases h11 : a < dgEListBase 0 vCap eCap
    · have hlt : a - dgEPresBase 0 vCap < eCap := by dsimp [dgEPresBase, dgEListBase] at h10 h11 ⊢; omega
      rw [show a = dgEPresBase 0 vCap + (a - dgEPresBase 0 vCap) by omega,
          canonDGMemBase_ePres hlt]
      split_ifs <;> omega
    by_cases h12 : a < dgEPosBase 0 vCap eCap
    · have hlt : a - dgEListBase 0 vCap eCap < eCap := by dsimp [dgEListBase, dgEPosBase] at h11 h12 ⊢; omega
      rw [show a = dgEListBase 0 vCap eCap + (a - dgEListBase 0 vCap eCap) by omega,
          canonDGMemBase_eList hlt]
      by_cases hi : a - dgEListBase 0 vCap eCap < (canonEList G₀).length
      · rw [List.getD_eq_getElem _ _ hi]
        have := canonECap_gt ((G₀.E.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)); omega
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; omega
    by_cases h13 : a < dgETailSlotBase 0 vCap eCap
    · have hlt : a - dgEPosBase 0 vCap eCap < eCap := by dsimp [dgEPosBase, dgETailSlotBase] at h12 h13 ⊢; omega
      rw [show a = dgEPosBase 0 vCap eCap + (a - dgEPosBase 0 vCap eCap) by omega,
          canonDGMemBase_ePos hlt]
      split_ifs with he
      · have hidx : (canonEList G₀).idxOf (a - dgEPosBase 0 vCap eCap) < (canonEList G₀).length :=
          List.idxOf_lt_length_of_mem ((G₀.E.mem_sort (· ≤ ·)).mpr he)
        have hlen : (canonEList G₀).length = G₀.m := G₀.E.length_sort (· ≤ ·)
        omega
      · omega
    by_cases h14 : a < dgEHeadSlotBase 0 vCap eCap
    · have hlt : a - dgETailSlotBase 0 vCap eCap < eCap := by dsimp [dgETailSlotBase, dgEHeadSlotBase] at h13 h14 ⊢; omega
      rw [show a = dgETailSlotBase 0 vCap eCap + (a - dgETailSlotBase 0 vCap eCap) by omega,
          canonDGMemBase_eTailSlot hlt]
      split_ifs with he
      · have := canonVCap_gt (hG₀ _ he).1; omega
      · omega
    by_cases h15 : a < dgHePrevBase 0 vCap eCap
    · have hlt : a - dgEHeadSlotBase 0 vCap eCap < eCap := by dsimp [dgEHeadSlotBase, dgHePrevBase] at h14 h15 ⊢; omega
      rw [show a = dgEHeadSlotBase 0 vCap eCap + (a - dgEHeadSlotBase 0 vCap eCap) by omega,
          canonDGMemBase_eHeadSlot hlt]
      split_ifs with he
      · have := canonVCap_gt (hG₀ _ he).2; omega
      · omega
    · rw [canonDGMemBase_zero_ge_hePrev (Nat.le_of_not_lt h15)]; omega
  have hbase_zero_inc : ∀ s < vCap,
      canonDGMemBase G₀ (dgIncHeadBase 0 vCap + s) = 0 ∧
      canonDGMemBase G₀ (dgSlotDegBase 0 vCap + s) = 0 := fun s hs =>
    ⟨canonDGMemBase_incHead hs, canonDGMemBase_slotDeg hs⟩
  -- Induction from the right using `List.reverseRecOn`
  induction es using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ _ _ => rfl, ⟨fun _ => [], fun s hs => ?_, fun _ _ _ _ _ _ h => by cases h⟩, hbase_lt⟩
    refine ⟨IsDoublyLinkedList.nil (hbase_zero_inc s hs).1, (hbase_zero_inc s hs).2, fun h => ?_⟩
    simp
  | append_singleton es e ih =>
    have hnd_es : es.Nodup := (List.nodup_append.mp hnd).1
    have he_not_es : e ∉ es := fun hmem => (List.nodup_append.mp hnd).2.2 e hmem e (List.mem_singleton_self e) rfl
    have hsub_es : ∀ e' ∈ es, e' ∈ G₀.E := fun e' he' => hsub e' (List.mem_append_left _ he')
    have he_G : e ∈ G₀.E := hsub e (List.mem_append_right _ (List.mem_singleton_self e))
    obtain ⟨hfr_es, ⟨incL, hincL, hdisj_es⟩, hlt_es⟩ := ih hnd_es hsub_es
    dsimp only
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set m0 := es.foldl (pushEdgeIncMem G₀ vCap eCap) (canonDGMemBase G₀)
    have ht_lt : G₀.tail e < vCap := canonVCap_gt (hG₀ e he_G).1
    have hh_lt : G₀.head e < vCap := canonVCap_gt (hG₀ e he_G).2
    have he_lt : e < eCap := canonECap_gt he_G
    have h2e_lt : 2 * e < 2 * eCap := by omega
    have h2e1_lt : 2 * e + 1 < 2 * eCap := by omega
    -- Step 1: push 2 * e onto G₀.tail e
    have hfresh1 : ∀ s' < vCap, 2 * e ∉ incL s' := fun s' hs' hmem => by
      have hdiv := ((hincL s' hs').2.2 (2 * e)).mp hmem
      have : (2 * e) / 2 = e := by omega
      rw [this] at hdiv; exact he_not_es hdiv.2.1
    obtain ⟨hinv1, hdisj1⟩ := pushHalfEdgeMem_step ht_lt h2e_lt hfresh1
      (fun s' hs' => ⟨(hincL s' hs').1, (hincL s' hs').2.1⟩) hdisj_es
    set m1 := pushHalfEdgeMem vCap eCap (G₀.tail e) (2 * e) m0
    set incL1 : ℕ → List ℕ := fun s' => if s' = G₀.tail e then 2 * e :: incL (G₀.tail e) else incL s'
    -- Step 2: push 2 * e + 1 onto G₀.head e
    have hfresh2 : ∀ s' < vCap, 2 * e + 1 ∉ incL1 s' := fun s' hs' hmem => by
      dsimp only [incL1] at hmem
      split_ifs at hmem with hst
      · rcases List.mem_cons.mp hmem with hEq | hmem'
        · omega
        · have hdiv := ((hincL (G₀.tail e) ht_lt).2.2 (2 * e + 1)).mp hmem'
          have : (2 * e + 1) / 2 = e := by omega
          rw [this] at hdiv; exact he_not_es hdiv.2.1
      · have hdiv := ((hincL s' hs').2.2 (2 * e + 1)).mp hmem
        have : (2 * e + 1) / 2 = e := by omega
        rw [this] at hdiv; exact he_not_es hdiv.2.1
    obtain ⟨hinv2, hdisj2⟩ := pushHalfEdgeMem_step hh_lt h2e1_lt hfresh2 hinv1 hdisj1
    set m2 := pushHalfEdgeMem vCap eCap (G₀.head e) (2 * e + 1) m1
    set incL2 : ℕ → List ℕ := fun s' => if s' = G₀.head e then (2 * e + 1) :: incL1 (G₀.head e) else incL1 s'
    have hold0 : m0 (dgIncHeadBase 0 vCap + G₀.tail e) = 0 ∨
        m0 (dgIncHeadBase 0 vCap + G₀.tail e) - 1 < 2 * eCap := by
      have hhd := (hincL (G₀.tail e) ht_lt).1.2.2.1
      cases hL : incL (G₀.tail e) with
      | nil => left; rw [hhd, hL]
      | cons a l =>
        right
        have ha := (hincL (G₀.tail e) ht_lt).1.2.1 a (by rw [hL]; exact List.mem_cons_self)
        rw [hhd, hL]; dsimp only; omega
    have hold1 : m1 (dgIncHeadBase 0 vCap + G₀.head e) = 0 ∨
        m1 (dgIncHeadBase 0 vCap + G₀.head e) - 1 < 2 * eCap := by
      have hhd := (hinv1 (G₀.head e) hh_lt).1.2.2.1
      cases hL : incL1 (G₀.head e) with
      | nil => left; rw [hhd, hL]
      | cons a l =>
        right
        have ha := (hinv1 (G₀.head e) hh_lt).1.2.1 a (by rw [hL]; exact List.mem_cons_self)
        rw [hhd, hL]; dsimp only; omega
    refine ⟨fun a h1 h2 => ?_, ⟨incL2, fun s hs => ?_, hdisj2⟩, ?_⟩
    · exact (pushHalfEdgeMem_frame hh_lt h2e1_lt hold1 h1 h2).trans
        ((pushHalfEdgeMem_frame ht_lt h2e_lt hold0 h1 h2).trans (hfr_es a h1 h2))
    · refine ⟨(hinv2 s hs).1, (hinv2 s hs).2, fun h => ?_⟩
      dsimp only [incL2, incL1]
      have hmem1 : h ∈ (if s = G₀.tail e then 2 * e :: incL (G₀.tail e) else incL s) ↔
          (h = 2 * e ∧ G₀.tail e = s) ∨ h ∈ incL s := by
        by_cases hst : s = G₀.tail e
        · subst hst; rw [ite_eq_left rfl, List.mem_cons]; simp
        · rw [ite_eq_right hst]; simp [Ne.symm hst]
      have hmem2 : h ∈ (if s = G₀.head e then (2 * e + 1) ::
            (if G₀.head e = G₀.tail e then 2 * e :: incL (G₀.tail e) else incL (G₀.head e))
            else if s = G₀.tail e then 2 * e :: incL (G₀.tail e) else incL s) ↔
          (h = 2 * e + 1 ∧ G₀.head e = s) ∨ (h = 2 * e ∧ G₀.tail e = s) ∨ h ∈ incL s := by
        by_cases hsh : s = G₀.head e
        · subst hsh
          rw [ite_eq_left rfl, List.mem_cons, hmem1]
          constructor
          · rintro (rfl | hrest)
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr hrest
          · rintro (⟨rfl, _⟩ | hrest)
            · exact Or.inl rfl
            · exact Or.inr hrest
        · rw [ite_eq_right hsh, hmem1]
          simp [Ne.symm hsh]
      rw [hmem2, (hincL s hs).2.2 h]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hlt, hmem_es, hend⟩)
        · refine ⟨h2e1_lt, List.mem_append_right _ (by simp [show (2 * e + 1) / 2 = e by omega]), ?_⟩
          simp [show (2 * e + 1) % 2 = 1 by omega, show (2 * e + 1) / 2 = e by omega]
        · refine ⟨h2e_lt, List.mem_append_right _ (by simp [show (2 * e) / 2 = e by omega]), ?_⟩
          simp [show (2 * e) % 2 = 0 by omega, show (2 * e) / 2 = e by omega]
        · exact ⟨hlt, List.mem_append_left _ hmem_es, hend⟩
      · rintro ⟨hlt, hmem_ap, hend⟩
        rw [List.mem_append, List.mem_singleton] at hmem_ap
        rcases hmem_ap with hmem_es | hdiv_e
        · exact Or.inr (Or.inr ⟨hlt, hmem_es, hend⟩)
        · rcases Nat.mod_two_eq_zero_or_one h with hmod | hmod
          · rw [ite_eq_left hmod, hdiv_e] at hend
            exact Or.inr (Or.inl ⟨by omega, hend⟩)
          · rw [ite_eq_right (by omega), hdiv_e] at hend
            exact Or.inl ⟨by omega, hend⟩
    · -- All cells in m2 remain < dynGraphSize vCap eCap
      intro a
      have hpush_lt : ∀ (mem : ℕ → ℕ) (s he : ℕ),
          (∀ z, mem z < dynGraphSize vCap eCap) →
          he < 2 * eCap → mem (dgSlotDegBase 0 vCap + s) < 2 * eCap →
          ∀ z, pushHalfEdgeMem vCap eCap s he mem z < dynGraphSize vCap eCap := by
        intro mem s he hmem hhe' hdeg' z
        have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
        unfold pushHalfEdgeMem
        by_cases h5 : z = dgSlotDegBase 0 vCap + s
        · rw [h5, Function.update_self]; omega
        rw [Function.update_of_ne h5]
        by_cases h4 : z = dgIncHeadBase 0 vCap + s
        · rw [h4, Function.update_self]; omega
        rw [Function.update_of_ne h4]
        split_ifs with h0
        · by_cases h2 : z = dgHeNextBase 0 vCap eCap + he
          · rw [h2, Function.update_self]; exact hmem _
          rw [Function.update_of_ne h2]
          by_cases h1 : z = dgHePrevBase 0 vCap eCap + he
          · rw [h1, Function.update_self]; omega
          rw [Function.update_of_ne h1]; exact hmem z
        · by_cases h3 : z = dgHePrevBase 0 vCap eCap + (mem (dgIncHeadBase 0 vCap + s) - 1)
          · rw [h3, Function.update_self]; omega
          rw [Function.update_of_ne h3]
          by_cases h2 : z = dgHeNextBase 0 vCap eCap + he
          · rw [h2, Function.update_self]; exact hmem _
          rw [Function.update_of_ne h2]
          by_cases h1 : z = dgHePrevBase 0 vCap eCap + he
          · rw [h1, Function.update_self]; omega
          rw [Function.update_of_ne h1]; exact hmem z
      have hdeg0_lt : m0 (dgSlotDegBase 0 vCap + G₀.tail e) < 2 * eCap := by
        rw [(hincL (G₀.tail e) ht_lt).2.1]
        have hcard : (incL (G₀.tail e)).length < 2 * eCap := by
          have hsub_rng : (incL (G₀.tail e)).toFinset ⊆ (Finset.range (2 * eCap)).erase (2 * e) := by
            intro x hx
            have hx' := List.mem_toFinset.mp hx
            exact Finset.mem_erase.mpr ⟨fun hEq => hfresh1 _ ht_lt (hEq ▸ hx'),
              Finset.mem_range.mpr ((hincL (G₀.tail e) ht_lt).1.2.1 x hx')⟩
          have h1 := Finset.card_le_card hsub_rng
          rw [List.toFinset_card_of_nodup (hincL (G₀.tail e) ht_lt).1.1,
              Finset.card_erase_of_mem (Finset.mem_range.mpr h2e_lt), Finset.card_range] at h1
          omega
        exact hcard
      have hm1_lt : ∀ z, m1 z < dynGraphSize vCap eCap := hpush_lt m0 (G₀.tail e) (2 * e) hlt_es h2e_lt hdeg0_lt
      have hdeg1_lt : m1 (dgSlotDegBase 0 vCap + G₀.head e) < 2 * eCap := by
        rw [(hinv1 (G₀.head e) hh_lt).2]
        have hsub_rng : (incL1 (G₀.head e)).toFinset ⊆ (Finset.range (2 * eCap)).erase (2 * e + 1) := by
          intro x hx
          have hx' := List.mem_toFinset.mp hx
          exact Finset.mem_erase.mpr ⟨fun hEq => hfresh2 _ hh_lt (hEq ▸ hx'),
            Finset.mem_range.mpr ((hinv1 (G₀.head e) hh_lt).1.2.1 x hx')⟩
        have h1 := Finset.card_le_card hsub_rng
        rw [List.toFinset_card_of_nodup (hinv1 (G₀.head e) hh_lt).1.1,
            Finset.card_erase_of_mem (Finset.mem_range.mpr h2e1_lt), Finset.card_range] at h1
        omega
      exact hpush_lt m1 (G₀.head e) (2 * e + 1) hm1_lt h2e1_lt hdeg1_lt a

lemma canonGuestMem_dynGraphAt {G₀ : MGraph} (hG₀ : G₀.IsValid) (ℓ₀ : ℕ → ℝ) (h L_in P_fp : ℕ) :
    DynGraphAt (canonGuestMem G₀ ℓ₀ h L_in P_fp) 0 (canonVCap G₀) (canonECap G₀) G₀ := by
  classical
  set vCap := canonVCap G₀
  set eCap := canonECap G₀
  set mem := canonGuestMem G₀ ℓ₀ h L_in P_fp
  have hmem_dg : ∀ a < dynGraphSize vCap eCap, mem a = canonDGMem G₀ a := fun a ha => by
    unfold mem canonGuestMem canonLenArr
    exact ite_eq_left ha
  obtain ⟨hfr, ⟨incL, hincL, _⟩, _⟩ :=
    canonDGMem_fold_props hG₀ (canonEList G₀) (G₀.E.sort_nodup (· ≤ ·))
      (fun e he => (G₀.E.mem_sort (· ≤ ·)).mp he)
  have hbase_at : ∀ a, (a < dgSlotDegBase 0 vCap ∨ dgEPresBase 0 vCap ≤ a) →
      (a < dgHePrevBase 0 vCap eCap) → mem a = canonDGMemBase G₀ a := fun a h1 h2 => by
    have hlt : a < dynGraphSize vCap eCap := by dsimp [dgHePrevBase, dynGraphSize] at h2 ⊢; omega
    rw [hmem_dg a hlt]
    exact hfr a h1 (Or.inl h2)
  have hvL_len : (canonVList G₀).length = G₀.n := G₀.V.length_sort (· ≤ ·)
  have hvL_nd : (canonVList G₀).Nodup := G₀.V.sort_nodup (· ≤ ·)
  have hvL_mem : ∀ v, v ∈ canonVList G₀ ↔ v ∈ G₀.V := fun v => G₀.V.mem_sort (· ≤ ·)
  have heL_len : (canonEList G₀).length = G₀.m := G₀.E.length_sort (· ≤ ·)
  have heL_nd : (canonEList G₀).Nodup := G₀.E.sort_nodup (· ≤ ·)
  have heL_mem : ∀ e, e ∈ canonEList G₀ ↔ e ∈ G₀.E := fun e => G₀.E.mem_sort (· ≤ ·)
  have hhdr := canonDGMemBase_hdr G₀
  have hmem_hdr0 : mem 0 = vCap := by
    rw [hbase_at 0 (Or.inl (by dsimp [dgSlotDegBase]; omega)) (by dsimp [dgHePrevBase]; omega), hhdr.1]
  have hmem_hdr1 : mem 1 = eCap := by
    rw [hbase_at 1 (Or.inl (by dsimp [dgSlotDegBase]; omega)) (by dsimp [dgHePrevBase]; omega), hhdr.2.1]
  have hmem_hdr2 : mem 2 = G₀.n := by
    rw [hbase_at 2 (Or.inl (by dsimp [dgSlotDegBase]; omega)) (by dsimp [dgHePrevBase]; omega), hhdr.2.2.1]
  have hmem_hdr3 : mem 3 = G₀.m := by
    rw [hbase_at 3 (Or.inl (by dsimp [dgSlotDegBase]; omega)) (by dsimp [dgHePrevBase]; omega), hhdr.2.2.2]
  have hmem_ext : ∀ v ∈ G₀.V, mem (dgExtToIntBase 0 vCap + v) = v := fun v hv => by
    have hvlt := canonVCap_gt hv
    rw [hbase_at _ (Or.inl (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega))
        (by dsimp [dgExtToIntBase, dgHePrevBase]; omega),
        canonDGMemBase_extToInt hvlt, ite_eq_left hv]
  have hmem_int : ∀ v ∈ G₀.V, mem (dgIntToExtBase 0 vCap + v) = v := fun v hv => by
    have hvlt := canonVCap_gt hv
    rw [hbase_at _ (Or.inl (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega))
        (by dsimp [dgIntToExtBase, dgHePrevBase]; omega),
        canonDGMemBase_intToExt hvlt, ite_eq_left hv]
  have hmem_tail : ∀ e ∈ G₀.E, mem (dgETailSlotBase 0 vCap eCap + e) = G₀.tail e := fun e he => by
    have helt := canonECap_gt he
    rw [hbase_at _ (Or.inr (by dsimp [dgETailSlotBase, dgEPresBase]; omega))
        (by dsimp [dgETailSlotBase, dgHePrevBase]; omega),
        canonDGMemBase_eTailSlot helt, ite_eq_left he]
  have hmem_head : ∀ e ∈ G₀.E, mem (dgEHeadSlotBase 0 vCap eCap + e) = G₀.head e := fun e he => by
    have helt := canonECap_gt he
    rw [hbase_at _ (Or.inr (by dsimp [dgEHeadSlotBase, dgEPresBase]; omega))
        (by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega),
        canonDGMemBase_eHeadSlot helt, ite_eq_left he]
  refine ⟨hG₀, fun v hv => canonVCap_gt hv, fun e he => canonECap_gt he,
    hmem_hdr0, hmem_hdr1, hmem_hdr2, hmem_hdr3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hbase_at _ (Or.inl (by dsimp [dgVPresBase, dgSlotDegBase]; omega))
        (by dsimp [dgVPresBase, dgHePrevBase]; omega), canonDGMemBase_vPres hv]
  · refine ⟨canonVList G₀, hvL_len, hvL_nd, hvL_mem, ?_, ?_⟩
    · intro i hi
      have hi_lt : i < vCap := by
        have hsubV : G₀.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (canonVCap_gt hv)
        calc i < (canonVList G₀).length := hi
          _ = G₀.V.card := hvL_len
          _ ≤ (Finset.range vCap).card := Finset.card_le_card hsubV
          _ = vCap := Finset.card_range vCap
      rw [hbase_at _ (Or.inl (by dsimp [dgVListBase, dgSlotDegBase]; omega))
          (by dsimp [dgVListBase, dgHePrevBase]; omega),
          canonDGMemBase_vList hi_lt, List.getD_eq_getElem _ _ hi]
    · intro i hi
      have hv_mem : (canonVList G₀)[i] ∈ G₀.V := (hvL_mem _).mp (List.getElem_mem hi)
      have hv_lt := canonVCap_gt hv_mem
      rw [hbase_at _ (Or.inl (by dsimp [dgVPosBase, dgSlotDegBase]; omega))
          (by dsimp [dgVPosBase, dgHePrevBase]; omega),
          canonDGMemBase_vPos hv_lt, ite_eq_left hv_mem, List.Nodup.idxOf_getElem hvL_nd i hi]
  · intro v hv
    rw [hmem_ext v hv, hmem_int v hv]; exact ⟨hv, rfl⟩
  · intro s hs
    rw [hmem_int s hs, hmem_ext s hs]; exact ⟨hs, rfl⟩
  · intro e he
    rw [hbase_at _ (Or.inr (by dsimp [dgEPresBase]; omega))
        (by dsimp [dgEPresBase, dgHePrevBase]; omega), canonDGMemBase_ePres he]
  · refine ⟨canonEList G₀, heL_len, heL_nd, heL_mem, ?_, ?_⟩
    · intro i hi
      have hi_lt : i < eCap := by
        have hsubE : G₀.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (canonECap_gt he)
        calc i < (canonEList G₀).length := hi
          _ = G₀.E.card := heL_len
          _ ≤ (Finset.range eCap).card := Finset.card_le_card hsubE
          _ = eCap := Finset.card_range eCap
      rw [hbase_at _ (Or.inr (by dsimp [dgEListBase, dgEPresBase]; omega))
          (by dsimp [dgEListBase, dgHePrevBase]; omega),
          canonDGMemBase_eList hi_lt, List.getD_eq_getElem _ _ hi]
    · intro i hi
      have he_mem : (canonEList G₀)[i] ∈ G₀.E := (heL_mem _).mp (List.getElem_mem hi)
      have he_lt := canonECap_gt he_mem
      rw [hbase_at _ (Or.inr (by dsimp [dgEPosBase, dgEPresBase]; omega))
          (by dsimp [dgEPosBase, dgHePrevBase]; omega),
          canonDGMemBase_ePos he_lt, ite_eq_left he_mem, List.Nodup.idxOf_getElem heL_nd i hi]
  · intro e he
    rw [hmem_tail e he, hmem_head e he, hmem_ext _ (hG₀ e he).1, hmem_ext _ (hG₀ e he).2]
    exact ⟨rfl, rfl⟩
  · refine ⟨incL, fun s hs => ?_⟩
    obtain ⟨hdll, hdeg, hmem_inc⟩ := hincL s hs
    refine ⟨hdll.of_agree
        (hmem_dg _ (by dsimp [dgIncHeadBase, dynGraphSize]; omega))
        (fun x hx => hmem_dg _ (by have := hdll.2.1 x hx; dsimp [dgHePrevBase, dynGraphSize]; omega))
        (fun x hx => hmem_dg _ (by have := hdll.2.1 x hx; dsimp [dgHeNextBase, dynGraphSize]; omega)),
      (hmem_dg _ (by dsimp [dgSlotDegBase, dynGraphSize]; omega)).trans hdeg,
      fun he => ?_⟩
    rw [hmem_inc he]
    constructor
    · rintro ⟨hlt, hmem_eL, hend⟩
      have heG : he / 2 ∈ G₀.E := (heL_mem _).mp hmem_eL
      refine ⟨hlt, heG, ?_⟩
      split_ifs with hmod
      · rw [hmem_tail _ heG]; simpa [hmod] using hend
      · rw [hmem_head _ heG]; simpa [hmod] using hend
    · rintro ⟨hlt, heG, hend⟩
      refine ⟨hlt, (heL_mem _).mpr heG, ?_⟩
      split_ifs with hmod
      · rw [hmem_tail _ heG] at hend; simpa [hmod] using hend
      · rw [hmem_head _ heG] at hend; simpa [hmod] using hend

lemma canonGuestMem_lengths {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {h L_in P_fp : ℕ}
    (hLin1 : 1 ≤ L_in)
    (hrep : ∀ e ∈ G₀.E, ∃ m : ℕ → ℕ, Valid m 0 h L_in ∧ fixVal m 0 h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e) :
    ∀ e ∈ G₀.E,
      Valid (canonGuestMem G₀ ℓ₀ h L_in P_fp) (canonLenArr G₀ + e * L_in) h L_in ∧
      fixVal (canonGuestMem G₀ ℓ₀ h L_in P_fp) (canonLenArr G₀ + e * L_in) h L_in P_fp = ℓ₀ e ∧
      0 < ℓ₀ e := by
  intro e he
  obtain ⟨m, hmV, hmFx, hpos⟩ := hrep e he
  have hlimbs := valid_limbs_eq_natLimb hmV hmFx hpos
  have he_lt : e < canonECap G₀ := canonECap_gt he
  have hag : ∀ t < L_in, canonGuestMem G₀ ℓ₀ h L_in P_fp (canonLenArr G₀ + e * L_in + t) = m (0 + t) := by
    intro t ht
    have h1 : ¬ canonLenArr G₀ + e * L_in + t < canonLenArr G₀ := by omega
    have hmul : (e + 1) * L_in ≤ canonECap G₀ * L_in := Nat.mul_le_mul_right L_in (by omega)
    have hadd : e * L_in + L_in = (e + 1) * L_in := by ring
    have h2 : canonLenArr G₀ + e * L_in + t < canonHandlesOut G₀ L_in := by
      unfold canonHandlesOut; omega
    have hsub : canonLenArr G₀ + e * L_in + t - canonLenArr G₀ = e * L_in + t := by omega
    have hdiv : (e * L_in + t) / L_in = e := by
      rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht, Nat.add_zero]
    have hmod : (e * L_in + t) % L_in = t := by
      rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
    unfold canonGuestMem
    rw [ite_eq_right h1, ite_eq_left h2]
    dsimp only
    rw [hsub, hdiv, hmod, ite_eq_left he]
    exact (hlimbs t ht).symm
  refine ⟨fun t ht => by rw [hag t ht]; exact hmV t ht, ?_, hpos⟩
  unfold fixVal at hmFx ⊢
  rw [intVal_congr hag]
  exact hmFx

lemma canonGuestMem_lt_two_pow {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    {h L_in P_fp : ℕ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {k_nat : ℕ} (hG₀ : G₀.IsValid) :
    ∀ a, canonGuestMem G₀ ℓ₀ h L_in P_fp a <
      2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat := by
  intro a
  obtain ⟨hw_h, hB_lt, _⟩ := canonWordBits_bounds Q_AN c_AN K_AN h L_in P_fp G₀ k_nat
  have hlen_lt_B : canonLenArr G₀ < canonWordBound Q_AN c_AN K_AN h L_in P_fp G₀ k_nat := by
    unfold canonWordBound canonHeap canonHandlesOut
    omega
  have hbase_lt : 2 ^ h < 2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  unfold canonGuestMem
  split_ifs with h1 h2
  · have hdg := (canonDGMem_fold_props hG₀ (canonEList G₀) (G₀.E.sort_nodup (· ≤ ·))
      (fun e he => (G₀.E.mem_sort (· ≤ ·)).mp he)).2.2 a
    exact lt_trans hdg (lt_trans hlen_lt_B hB_lt)
  · dsimp only
    split_ifs
    · exact lt_trans (natLimb_lt_base _ h _) hbase_lt
    · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _

end MinCostFlow.SparseCore.Program
