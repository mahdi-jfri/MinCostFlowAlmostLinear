module

public import MinCostFlow.SparseCore.Program.TourOpsEditCommon
import Mathlib.Tactic

/-!
# WordRAM bodies and execution helpers for `dropEdge` (Op 0)

Defines `tourDropOneBody` (drops a single open end `keyX` from the tour while `ordStore` still
holds `ord0`, handling self-loop open edges whose other end was already dropped) and
`tourEditDropBody` (calls `tourDropOneBody` on `2 * e` and `2 * e + 1`), together with pure
cyclic-successor and prefix execution helpers.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM bodies -/

/-- Drop one open end `keyX` from the tour: args `[b, keyX, heap]`, returning updated `h' ≤ heap + 2`. -/
def tourDropOneBody (deleteNodeProc setValNodeProc rotateFrontProc ordNextProc : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const HDR_END_OWNER))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .cond (.bin .eq (.reg 4) (.const 0))
    (.ret (.reg 2))
    (.assign 4 (.bin .sub (.reg 4) (.const 1)) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.const HDR_NEXT_ARR))) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.const HDR_ECAP))) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.const HDR_VCAP))) ;;
     .assign 6 (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7))) (.reg 8)) ;;
     .assign 5 (.load (.bin .add (.reg 6) (.reg 4))) ;;
     .cond (.reg 5) (.assign 5 (.bin .sub (.reg 5) (.const 1))) (.assign 5 (.reg 4)) ;;
     .store (.bin .add (.reg 3) (.reg 1)) (.const 0) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
     .assign 6 (.load (.bin .add (.reg 6) (.reg 1))) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
     .assign 8 (.load (.bin .add (.reg 7) (.reg 5))) ;;
     .assign 9 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
     .assign 10 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
     .cond (.bin .eq (.reg 6) (.reg 8))
       (.assign 11 (.load (.bin .add (.reg 0) (.const HDR_ORD_H))) ;;
        .assign 12 (.reg 2) ;;
        .call 2 ordNextProc [.reg 11, .reg 5, .reg 1, .reg 2] ;;
        .assign 13 (.load (.reg 12)) ;;
        .cond (.bin .eq (.reg 13) (.reg 1))
          (.assign 14 (.const 0))
          (.assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
           .cond (.bin .eq (.reg 14) (.const 0))
             (.assign 12 (.reg 2) ;;
              .call 2 ordNextProc [.reg 11, .reg 5, .reg 13, .reg 2] ;;
              .assign 13 (.load (.reg 12)))
             .nop ;;
           .cond (.bin .eq (.reg 13) (.reg 1))
             (.assign 14 (.const 0))
             (.assign 14 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
              .assign 14 (.load (.bin .add (.reg 14) (.reg 13))))) ;;
        .store (.bin .add (.reg 7) (.reg 5)) (.reg 14) ;;
        .assign 15 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
        .assign 15 (.load (.bin .add (.reg 15) (.reg 5))) ;;
        .cond (.reg 15)
          (.assign 16 (.const 1) ;;
           .assign 17 (.const 0) ;;
           .call 18 setValNodeProc [.reg 9, .reg 6, .reg 16, .reg 17, .reg 17, .reg 10, .reg 2] ;;
           .call 18 deleteNodeProc [.reg 9, .reg 6, .reg 10, .reg 2] ;;
           .cond (.reg 14)
             (.assign 15 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 14))) ;;
              .assign 16 (.load (.bin .add (.reg 15) (.const 9))) ;;
              .assign 17 (.load (.bin .add (.reg 15) (.const 10))) ;;
              .assign 18 (.bin .add (.reg 5) (.const 1)) ;;
              .call 19 setValNodeProc [.reg 9, .reg 14, .reg 16, .reg 17, .reg 18, .reg 10, .reg 2] ;;
              .call 19 rotateFrontProc [.reg 9, .reg 14, .reg 10, .reg 2])
             .nop)
          (.call 18 deleteNodeProc [.reg 9, .reg 6, .reg 10, .reg 2]) ;;
        .ret (.reg 2))
       (.call 18 deleteNodeProc [.reg 9, .reg 6, .reg 10, .reg 2] ;;
        .ret (.reg 2)))

/-- Tour update for `dropEdge e`: args `[b, e, heap]`, returning updated `h' ≤ heap + 4`. -/
def tourEditDropBody (dropOneProc : ℕ) : Stmt :=
  .assign 3 (.bin .mul (.const 2) (.reg 1)) ;;
  .call 4 dropOneProc [.reg 0, .reg 3, .reg 2] ;;
  .assign 3 (.bin .add (.reg 3) (.const 1)) ;;
  .call 4 dropOneProc [.reg 0, .reg 3, .reg 4] ;;
  .ret (.reg 4)

theorem tourEditDrop_bodies_noRand (dnP svP rfP onP doP : ℕ) :
    (tourDropOneBody dnP svP rfP onP).NoRand ∧
    (tourEditDropBody doP).NoRand := by
  simp [tourDropOneBody, tourEditDropBody, Stmt.NoRand]

/-! ## Pure list helpers for single-end drop and self-loop `cycNext` skipping -/

/-- Drop a single open end `x` from `s.ord` and `s.marked`. -/
def tourDropOneAbs (s : TourAbs) (x : End) : TourAbs :=
  { ord := fun u => (s.ord u).filter fun z => z != x
    rf := s.rf
    marked := s.marked.erase x }

theorem tourValid_dropOneAbs {vCap eCap : ℕ} {s : TourAbs} {x : End}
    (hv : TourValid vCap eCap s) (hx_open : x.1 ∉ s.rf.F.E) :
    TourValid vCap eCap (tourDropOneAbs s x) where
  ordWithin :=
    ⟨fun v => (hv.ordWithin.1 v).filter _,
     fun v hge => by simp [tourDropOneAbs, hv.ordWithin.2.1 v hge],
     fun v z hz => hv.ordWithin.2.2 v z (List.mem_filter.mp hz).1⟩
  compat :=
    ⟨fun v => (hv.compat.nodup v).filter _,
     fun u₁ u₂ z h1 h2 => hv.compat.unique u₁ u₂ z (List.mem_filter.mp h1).1 (List.mem_filter.mp h2).1,
     hv.compat.forest,
     fun u hu => hv.compat.vert u fun h0 => hu (by simp [tourDropOneAbs, h0]),
     fun f hf => by
       have hne_t : (f, true) ≠ x := fun h => hx_open (h ▸ hf)
       have hne_f : (f, false) ≠ x := fun h => hx_open (h ▸ hf)
       have ⟨ht, hh⟩ := hv.compat.forestEnd f hf
       exact ⟨by simp [tourDropOneAbs, ht, hne_t], by simp [tourDropOneAbs, hh, hne_f]⟩⟩
  roots_sub := hv.roots_sub
  verts_lt := hv.verts_lt
  unique_root := hv.unique_root
  marked_open := fun z hz => by
    simp only [tourDropOneAbs, Finset.mem_erase] at hz
    obtain ⟨⟨v, hzv⟩, hzo⟩ := hv.marked_open z hz.2
    exact ⟨⟨v, by simp [tourDropOneAbs, hzv, hz.1]⟩, hzo⟩

theorem tourDropOneAbs_twice_eq_dropEdge (s : TourAbs) (e : ℕ) :
    tourDropOneAbs (tourDropOneAbs s (e, true)) (e, false) = tourApplyEdit s (.dropEdge e) := by
  cases s with | mk ord rf marked =>
  simp only [tourDropOneAbs, tourApplyEdit, applyOrdEdit]
  congr 1
  · funext u
    rw [List.filter_filter]
    refine List.filter_congr fun z _ => ?_
    obtain ⟨f, b⟩ := z; cases b <;> by_cases hfe : f = e <;> simp [bne, BEq.beq, hfe]
  · ext z
    simp only [Finset.mem_erase, Finset.mem_filter, bne_iff_ne]
    obtain ⟨f, b⟩ := z; cases b <;> by_cases hfe : f = e <;> simp [hfe]

theorem tourDropOneAbs_eq_self_of_not_mem {vCap eCap : ℕ} {s : TourAbs} {x : End}
    (hv : TourValid vCap eCap s) (hno : ∀ u, x ∉ s.ord u) :
    tourDropOneAbs s x = s := by
  cases s with | mk ord rf marked =>
  simp only [tourDropOneAbs]
  congr 1
  · funext u
    exact List.filter_eq_self.mpr fun z hz => by
      simp only [bne_iff_ne]; intro h; exact hno u (h ▸ hz)
  · apply Finset.erase_eq_of_notMem
    intro hm; obtain ⟨⟨u, hu⟩, _⟩ := hv.marked_open x hm; exact hno u hu

theorem tourDropOneAbs_ord_eq_update {vCap eCap v : ℕ} {s : TourAbs} {x : End}
    (hv : TourValid vCap eCap s) (hxv : x ∈ s.ord v) :
    (tourDropOneAbs s x).ord = Function.update s.ord v ((s.ord v).filter fun z => z != x) := by
  funext u
  by_cases huv : u = v
  · subst huv; simp [tourDropOneAbs]
  · simp only [tourDropOneAbs, Function.update_of_ne huv]
    exact List.filter_eq_self.mpr fun z hz => by
      simp only [bne_iff_ne]; intro h; exact huv (hv.compat.unique u v x (h ▸ hz) hxv)

private theorem cycNext_append_cons_cons {P Q : List End} {x y : End}
    (hnd : (P ++ x :: y :: Q).Nodup) :
    cycNext (P ++ x :: y :: Q) x = y := by
  have hlt : P.length < (P ++ x :: y :: Q).length := by simp
  have h1 := cycNext_eq_getElem hnd hlt
  have hget : (P ++ x :: y :: Q)[P.length]'hlt = x := by simp
  rw [hget] at h1
  have hlt2 : P.length + 1 < (P ++ x :: y :: Q).length := by simp
  rw [h1]; simp only [Nat.mod_eq_of_lt hlt2, List.getElem_append_right (by omega : P.length ≤ P.length + 1)]
  have hsub : P.length + 1 - P.length = 1 := by omega
  simp [hsub]

/-- When `xs` is obtained from a nodup list `orig` by deleting at most one element `skip`
(`skip ≠ x`), and `x` is the head of `xs`, the head of `xs.filter (· != x)` is found by taking
`k1 := cycNext orig x` and, if `k1 ∉ xs`, taking `cycNext orig k1` once more (yielding `none`
iff the result equals `x`). -/
theorem head?_dropHead_via_orig_cycNext {orig xs : List End} {x : End}
    (hnd : orig.Nodup) (hsub : ∀ z ∈ xs, z ∈ orig)
    (hmiss : (∃ skip : End, skip ≠ x ∧ xs = orig.filter (fun z => z != skip)) ∨ xs = orig)
    (hhead : xs.head? = some x) :
    let k1 := cycNext orig x
    let k2 := if k1 = x then x else if k1 ∈ xs then k1 else cycNext orig k1
    (xs.filter fun z => z != x).head? = if k2 = x then none else some k2 := by
  intro k1 k2
  have hx_xs : x ∈ xs := List.mem_of_head? hhead
  have hx_orig : x ∈ orig := hsub x hx_xs
  have hxs_nd : xs.Nodup := by
    rcases hmiss with ⟨skip, _, rfl⟩ | rfl; exact hnd.filter _; exact hnd
  cases hxs_c : xs with
  | nil => rw [hxs_c] at hhead; simp at hhead
  | cons a tail =>
    rw [hxs_c] at hhead hxs_nd
    have hax : a = x := Option.some.inj hhead
    subst a
    have hfil : (xs.filter fun z => z != x) = tail := by
      rw [hxs_c, List.filter_cons]; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun z hz => by
        simp only [bne_iff_ne]; intro heq; exact (List.nodup_cons.mp hxs_nd).1 (heq ▸ hz)
    rw [← hxs_c, hfil]
    rcases hmiss with ⟨skip, hskip_ne, hxs_eq⟩ | hxs_eq
    · obtain ⟨P, Q, horig⟩ := List.mem_iff_append.mp hx_orig
      have hP_skip : ∀ z ∈ P, z = skip := by
        intro z hz; by_contra hne
        have h1 : z ∈ P.filter (fun w => w != skip) := List.mem_filter.mpr ⟨hz, by simp [hne]⟩
        obtain ⟨p0, ps, hp⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem h1)
        have hxs' : xs = p0 :: (ps ++ (x :: Q).filter (fun w => w != skip)) := by
          rw [hxs_eq, horig, List.filter_append, hp]; rfl
        rw [hxs'] at hxs_c
        have hxP : x ∈ P := (List.mem_filter.mp (by rw [hp, ← (List.cons.inj hxs_c).1]; simp)).1
        exact (List.nodup_append.mp (horig ▸ hnd)).2.2 x hxP x (by simp) rfl
      have hP_cases : P = [] ∨ P = [skip] := by
        have hPnd : P.Nodup := (List.nodup_append.mp (horig ▸ hnd)).1
        cases P with
        | nil => exact Or.inl rfl
        | cons u us =>
          have hu : u = skip := hP_skip u (by simp)
          cases us with
          | nil => exact Or.inr (by simp [hu])
          | cons v vs =>
            have hv : v = skip := hP_skip v (by simp)
            exact absurd (hu.symm ▸ hv.symm ▸ List.mem_cons_self) (List.nodup_cons.mp hPnd).1
      have htail_eq : tail = Q.filter (fun z => z != skip) := by
        have hP0 : P.filter (fun z => z != skip) = [] :=
          List.filter_eq_nil_iff.mpr fun z hz => by simp [hP_skip z hz]
        have h1 : xs = x :: Q.filter (fun z => z != skip) := by
          rw [hxs_eq, horig, List.filter_append, hP0, List.nil_append, List.filter_cons]
          simp [bne_iff_ne, hskip_ne.symm]
        rw [h1] at hxs_c; exact (List.cons.inj hxs_c).2.symm
      rw [htail_eq]
      cases hQc : Q with
      | nil =>
        rcases hP_cases with rfl | rfl
        · have ho : orig = [x] := by simpa [hQc] using horig
          have hk1 : k1 = x := by simp [k1, ho, cycNext]
          simp [k2, hk1]
        · have ho : orig = [skip, x] := by simpa [hQc] using horig
          have hk1 : k1 = skip := by
            have := cycNext_eq_getElem (ho ▸ hnd) (i := 1) (by simp)
            simpa [k1, ho] using this
          have hk2' : cycNext orig skip = x := by
            have := cycNext_eq_getElem (ho ▸ hnd) (i := 0) (by simp)
            simpa [ho] using this
          have hskip_nxs : skip ∉ xs := by rw [hxs_eq]; simp
          simp [k2, hk1, hskip_ne, hskip_nxs, hk2']
      | cons q0 Q' =>
        have hk1 : k1 = q0 := by
          dsimp only [k1]; rw [horig, hQc]
          exact cycNext_append_cons_cons (by rwa [← hQc, ← horig])
        have hq0_ne : q0 ≠ x := fun heq => by
          have := (List.nodup_cons.mp (List.nodup_append.mp (horig ▸ hnd)).2.1).1
          rw [hQc, heq] at this; exact this (by simp)
        by_cases hq0s : q0 = skip
        · rw [hq0s] at hQc hk1 ⊢
          have hP0 : P = [] := by
            rcases hP_cases with rfl | rfl
            · rfl
            · exact absurd rfl ((List.nodup_append.mp (horig ▸ hnd)).2.2 skip (by simp) skip (by rw [hQc]; simp))
          have ho : orig = x :: skip :: Q' := by simpa [hP0, hQc] using horig
          have hskip_nQ' : skip ∉ Q' := (List.nodup_cons.mp (List.nodup_cons.mp (ho ▸ hnd)).2).1
          have hskip_nxs : skip ∉ xs := by rw [hxs_eq]; simp
          have hfilQ' : Q'.filter (fun z => z != skip) = Q' :=
            List.filter_eq_self.mpr fun z hz => by simp [bne_iff_ne]; intro heq; exact hskip_nQ' (heq ▸ hz)
          rw [List.filter_cons]; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfilQ']
          cases hQ'c : Q' with
          | nil =>
            have ho2 : orig = [x, skip] := by simpa [hQ'c] using ho
            have hcs : cycNext orig skip = x := by
              have := cycNext_eq_getElem (ho2 ▸ hnd) (i := 1) (by simp)
              simpa [ho2] using this
            simp [k2, hk1, hskip_ne, hskip_nxs, hcs]
          | cons q1 Q'' =>
            have ho2 : orig = [x] ++ skip :: q1 :: Q'' := by simpa [hQ'c] using ho
            have hcs : cycNext orig skip = q1 := by
              rw [ho2]; exact cycNext_append_cons_cons (by rwa [← ho2])
            have hq1_ne : q1 ≠ x := fun heq =>
              (List.nodup_cons.mp (ho ▸ hnd)).1 (by rw [hQ'c, heq]; simp)
            simp [k2, hk1, hskip_ne, hskip_nxs, hcs, hq1_ne]
        · have hq0_xs : q0 ∈ xs := by
            rw [hxs_c, htail_eq, hQc, List.filter_cons]; simp [bne_iff_ne, hq0s]
          rw [List.filter_cons]; simp [bne_iff_ne, hq0s, k2, hk1, hq0_ne, hq0_xs]
    · have horig : orig = x :: tail := hxs_eq.symm.trans hxs_c
      cases tail with
      | nil =>
        have hk1 : k1 = x := by simp [k1, horig, cycNext]
        simp [k2, hk1]
      | cons y ys =>
        have hk1 : k1 = y := by
          have := cycNext_eq_getElem (horig ▸ hnd) (i := 0) (by simp)
          simpa [k1, horig] using this
        have hy_ne : y ≠ x := fun heq => (List.nodup_cons.mp (horig ▸ hnd)).1 (heq ▸ by simp)
        have hy_xs : y ∈ xs := by rw [hxs_c]; simp
        simp [k2, hk1, hy_ne, hy_xs]

/-! ## Execution helper for `tourDropOneBody` active prefix -/

/-- Execute the active prefix of `tourDropOneBody` (loads `eo`, decodes `v := vertOf (eo - 1)`,
clears `endOwner[keyX] := 0`, loads `u`, `feBase`, `feOld`, `nb`, `fuel`). -/
theorem tourDropOne_prefix_exec {τ_ord : Type}
    {w vCap eCap b keyX heap pos v : ℕ} {p : Program} (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hkeyLt : keyX < 2 * eCap) (hvLt : v < vCap) (_hxv : endOfKey keyX ∈ s.ord v)
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 6 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) :
    let u := x.nodeOf keyX
    let mem1 := Function.update mem (endOwnerBase b vCap eCap + keyX) 0
    ∃ rP cP,
      rP 0 = b ∧ rP 1 = keyX ∧ rP 2 = heap ∧ rP 3 = endOwnerBase b vCap eCap ∧
      rP 5 = v ∧ rP 6 = u ∧ rP 7 = firstEndBase b ∧ rP 8 = mem (firstEndBase b + v) ∧
      rP 9 = nodesBase b vCap eCap ∧ rP 10 = 2 * eCap + 2 ∧ cP ≤ 90 ∧
      Runs w p ω
        (.assign 4 (.bin .sub (.reg 4) (.const 1)) ;;
         .assign 6 (.load (.bin .add (.reg 0) (.const HDR_NEXT_ARR))) ;;
         .assign 7 (.load (.bin .add (.reg 0) (.const HDR_ECAP))) ;;
         .assign 8 (.load (.bin .add (.reg 0) (.const HDR_VCAP))) ;;
         .assign 6 (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7))) (.reg 8)) ;;
         .assign 5 (.load (.bin .add (.reg 6) (.reg 4))) ;;
         .cond (.reg 5) (.assign 5 (.bin .sub (.reg 5) (.const 1))) (.assign 5 (.reg 4)) ;;
         .store (.bin .add (.reg 3) (.reg 1)) (.const 0) ;;
         .assign 6 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
         .assign 6 (.load (.bin .add (.reg 6) (.reg 1))) ;;
         .assign 7 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
         .assign 8 (.load (.bin .add (.reg 7) (.reg 5))) ;;
         .assign 9 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
         .assign 10 (.load (.bin .add (.reg 0) (.const HDR_FUEL))))
        ⟨mem, Function.update (Function.update (startState [b, keyX, heap] mem pos).regs
          3 (endOwnerBase b vCap eCap)) 4 (x.slotOf v + 1), pos⟩
        .normal ⟨mem1, rP, pos⟩ cP := by
  intro u mem1
  have hhdr := h.header
  have hsvLt : x.slotOf v < vCap := (h.slot_bij v hvLt).1
  have hgeo : b + 16 < 2 ^ w ∧ 2 * eCap < 2 ^ w ∧
      slotOfVertBase b vCap eCap < 2 ^ w ∧ vertOfSlotBase b vCap eCap + x.slotOf v < 2 ^ w ∧
      endOwnerBase b vCap eCap + keyX < 2 ^ w ∧ nodeOfEndBase b vCap + keyX < 2 ^ w ∧
      firstEndBase b + v < 2 ^ w := by
    simp only [ordHandleOf, tourFixedSize, slotOfVertBase, vertOfSlotBase,
      endOwnerBase, nodeOfEndBase, firstEndBase] at hord_le ⊢
    omega
  set s0 : State := startState [b, keyX, heap] mem pos
  set r0 := Function.update (Function.update s0.regs 3 (endOwnerBase b vCap eCap)) 4 (x.slotOf v + 1)
  set r1 := Function.update r0 4 (x.slotOf v)
  set r2 := Function.update r1 6 (nextArrBase b vCap eCap)
  set r3 := Function.update r2 7 eCap
  set r4 := Function.update r3 8 vCap
  set r5 := Function.update r4 6 (vertOfSlotBase b vCap eCap)
  set rawV := mem (vertOfSlotBase b vCap eCap + x.slotOf v)
  set r6 := Function.update r5 5 rawV
  set r7 := Function.update r6 5 v
  have hraw_eq : decodeSlot rawV (x.slotOf v) = v := by
    rw [h.vertOf_mem (x.slotOf v) hsvLt, (h.slot_bij v hvLt).2.1]
  have hrawW : rawV < 2 ^ w := by
    by_cases h0 : rawV = 0
    · omega
    · simp only [decodeSlot, h0, ↓reduceIte] at hraw_eq; omega
  have h1 : Runs w p ω (.assign 4 (.bin .sub (.reg 4) (.const 1))) ⟨mem, r0, pos⟩ .normal ⟨mem, r1, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨x.slotOf v, by
      simp [Expr.eval, r0, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : x.slotOf v < 2 ^ w)], rfl, rfl, rfl⟩
  have h2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_NEXT_ARR)
    (b := b) (val := nextArrBase b vCap eCap) (st := ⟨mem, r1, pos⟩) (by simp [r1, r0, s0, startState])
    (by simp [HDR_NEXT_ARR]; omega) (by simp [HDR_NEXT_ARR]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have h3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_ECAP)
    (b := b) (val := eCap) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, r0, s0, startState])
    (by rw [HDR_ECAP]; omega) (by rw [HDR_ECAP]; omega) hhdr.2.1
  have h4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_VCAP)
    (b := b) (val := vCap) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, r0, s0, startState])
    (by rw [HDR_VCAP]; omega) (by rw [HDR_VCAP]; omega) hhdr.1
  have h5 : Runs w p ω (.assign 6 (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7))) (.reg 8)))
      ⟨mem, r4, pos⟩ .normal ⟨mem, r5, pos⟩ 8 :=
    runs_assign_iff.mpr ⟨vertOfSlotBase b vCap eCap, by
      have heq1 : nextArrBase b vCap eCap + 2 * eCap = slotOfVertBase b vCap eCap := (slotOfVertBase_eq b vCap eCap).symm
      have heq2 : slotOfVertBase b vCap eCap + vCap = vertOfSlotBase b vCap eCap := (vertOfSlotBase_eq b vCap eCap).symm
      simp [Expr.eval, r4, r3, r2, BinOp.eval, (by omega : 2 < 2 ^ w), hgeo.2.1, heq1, heq2,
        hgeo.2.2.1, (by omega : vertOfSlotBase b vCap eCap < 2 ^ w)], rfl, rfl, rfl⟩
  have h6 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 6) (rIdx := 4)
    (base := vertOfSlotBase b vCap eCap) (idx := x.slotOf v) (val := rawV) (st := ⟨mem, r5, pos⟩)
    (by simp [r5]) (by simp [r5, r4, r3, r2, r1]) hgeo.2.2.2.1 rfl
  have h7 : Runs w p ω (.cond (.reg 5) (.assign 5 (.bin .sub (.reg 5) (.const 1))) (.assign 5 (.reg 4)))
      ⟨mem, r6, pos⟩ .normal ⟨mem, r7, pos⟩ (if rawV = 0 then 4 else 6) := by
    have hr := runs_decodeSlot_stmt (w := w) (p := p) (ω := ω) (dst := 5) (rRaw := 5) (rIdx := 4)
      (raw := rawV) (idx := x.slotOf v) (st := ⟨mem, r6, pos⟩) (by simp [r6])
      (by simp [r6, r5, r4, r3, r2, r1]) (by omega) hrawW
    simpa [r7, hraw_eq] using hr
  have h8 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 1)) (.const 0))
      ⟨mem, r7, pos⟩ .normal ⟨mem1, r7, pos⟩ 5 :=
    runs_store_iff.mpr ⟨endOwnerBase b vCap eCap + keyX, 0,
      by simp [Expr.eval, r7, r6, r5, r4, r3, r2, r1, r0, s0, startState, BinOp.eval, hgeo.2.2.2.2.1],
      by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
  have hm1_ne : ∀ a, a ≠ endOwnerBase b vCap eCap + keyX → mem1 a = mem a := fun a ha =>
    Function.update_of_ne ha _ _
  set r8 := Function.update r7 6 (nodeOfEndBase b vCap)
  set r9 := Function.update r8 6 u
  set r10 := Function.update r9 7 (firstEndBase b)
  set r11 := Function.update r10 8 (mem (firstEndBase b + v))
  set r12 := Function.update r11 9 (nodesBase b vCap eCap)
  set r13 := Function.update r12 10 (2 * eCap + 2)
  have h9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := ⟨mem1, r7, pos⟩)
    (by simp [r7, r6, r5, r4, r3, r2, r1, r0, s0, startState])
    (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega)
    (by dsimp only; rw [hm1_ne _ (by simp [HDR_NODE_OF_END, endOwnerBase]; omega)]; exact hhdr.2.2.2.2.2.2.1)
  have h10 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 6) (rIdx := 1)
    (base := nodeOfEndBase b vCap) (idx := keyX) (val := u) (st := ⟨mem1, r8, pos⟩)
    (by simp [r8]) (by simp [r8, r7, r6, r5, r4, r3, r2, r1, r0, s0, startState]) hgeo.2.2.2.2.2.1
    (by dsimp only; rw [hm1_ne _ (by simp [nodeOfEndBase, endOwnerBase]; omega)]; exact (h.nodeOf_mem keyX hkeyLt).1)
  have h11 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_FIRST_END)
    (b := b) (val := firstEndBase b) (st := ⟨mem1, r9, pos⟩)
    (by simp [r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, s0, startState])
    (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega)
    (by dsimp only; rw [hm1_ne _ (by simp [HDR_FIRST_END, endOwnerBase]; omega)]; exact hhdr.2.2.2.2.1)
  have h12 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 7) (rIdx := 5)
    (base := firstEndBase b) (idx := v) (val := mem (firstEndBase b + v)) (st := ⟨mem1, r10, pos⟩)
    (by simp [r10]) (by simp [r10, r9, r8, r7]) hgeo.2.2.2.2.2.2
    (by dsimp only; exact hm1_ne _ (by simp [firstEndBase, endOwnerBase]; omega))
  have h13 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem1, r11, pos⟩)
    (by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, s0, startState])
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega)
    (by dsimp only; rw [hm1_ne _ (by simp [HDR_NODES_BASE, endOwnerBase]; omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have h14 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem1, r12, pos⟩)
    (by simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, s0, startState])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega)
    (by dsimp only; rw [hm1_ne _ (by simp [HDR_FUEL, endOwnerBase]; omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  refine ⟨r13, _,
    by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, s0, startState],
    by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, s0, startState],
    by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0, s0, startState],
    by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0],
    by simp [r13, r12, r11, r10, r9, r8, r7],
    by simp [r13, r12, r11, r10, r9],
    by simp [r13, r12, r11, r10],
    by simp [r13, r12, r11],
    by simp [r13, r12],
    by simp [r13],
    by clear * -; split_ifs <;> omega,
    tour_runs_seq_normal h1 (tour_runs_seq_normal h2 (tour_runs_seq_normal h3 (tour_runs_seq_normal h4
      (tour_runs_seq_normal h5 (tour_runs_seq_normal h6 (tour_runs_seq_normal h7 (tour_runs_seq_normal h8
        (tour_runs_seq_normal h9 (tour_runs_seq_normal h10 (tour_runs_seq_normal h11 (tour_runs_seq_normal h12
          (tour_runs_seq_normal h13 h14))))))))))))⟩

end MinCostFlow.SparseCore.Program
