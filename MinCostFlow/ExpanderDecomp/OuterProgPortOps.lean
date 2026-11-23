module

public import MinCostFlow.ExpanderDecomp.OuterProgPortContract
import Mathlib.Tactic.Linarith

/-!
# Verification of `outerRoundPortCutProc` (`OuterProgPortOps`)

Proves `outerRoundPortCutProc_spec` via staged loop triples (`rpcFillLoc_triple`,
`rpcCountPorts_triple`, `rpcSplitVerts_triple`) and re-exports `OuterProgPortContract`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

private lemma disjointRange_ne' {a la b lb x y : ℕ} (hd : DisjointRange a la b lb)
    (hx1 : a ≤ x) (hx2 : x < a + la) (hy1 : b ≤ y) (hy2 : y < b + lb) : x ≠ y := by
  rcases hd with h | h <;> omega

/-! ## 5. Staged Triples and Verification of `outerRoundPortCutProc` -/

private lemma portCountPrefix_succ (owners : List ℕ) (p v : ℕ) :
    portCountPrefix owners (p + 1) v =
      portCountPrefix owners p v + if owners.getD p 0 = v then 1 else 0 := by
  unfold portCountPrefix
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · omega

private lemma portInUCountPrefix_succ (owners : List ℕ) (U : Finset ℕ) (p v : ℕ) :
    portInUCountPrefix owners U (p + 1) v =
      portInUCountPrefix owners U p v + if owners.getD p 0 = v ∧ p ∈ U then 1 else 0 := by
  unfold portInUCountPrefix
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · omega

private lemma portCountPrefix_le (owners : List ℕ) (m v : ℕ) :
    portCountPrefix owners m v ≤ m := by
  unfold portCountPrefix
  exact le_trans (Finset.card_filter_le _ _) (by simp)

private lemma portInUCountPrefix_le (owners : List ℕ) (U : Finset ℕ) (m v : ℕ) :
    portInUCountPrefix owners U m v ≤ m := by
  unfold portInUCountPrefix
  exact le_trans (Finset.card_filter_le _ _) (by simp)

private lemma rpcFillLoc_triple {w n k vertsAddr locAddr : ℕ} (pProg : Program) (st₀ : State)
    (verts : List ℕ)
    (h0 : st₀.regs 0 = k) (h1 : st₀.regs 1 = vertsAddr) (h6 : st₀.regs 6 = locAddr)
    (hlen : verts.length = k) (hnd : verts.Nodup) (hv_lt : ∀ v ∈ verts, v < n)
    (hlist : ListAt st₀.mem vertsAddr verts)
    (hdisj : DisjointRange locAddr n vertsAddr k)
    (hwV : vertsAddr + k < 2 ^ w) (hwLoc : locAddr + n < 2 ^ w) (hwK : k + 1 < 2 ^ w)
    (hw1 : 1 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) rpcFillLocStmt
      (normalPost fun s' =>
        (∀ i (hi : i < k), s'.mem (locAddr + verts[i]'(by omega)) = i + 1) ∧
        (∀ a, (∀ v ∈ verts, a ≠ locAddr + v) → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≠ 11 → r ≠ 12 → s'.regs r = st₀.regs r))
      (fun _ => 30 * k + 15) := by
  have hloop := Triple.forRange_const (p := pProg) (r := 11) (lo := .const 0) (hi := .reg 0)
    (body := .assign 12 (.load (.bin .add (.reg 1) (.reg 11))) ;;
      .store (.bin .add (.reg 6) (.reg 12)) (.bin .add (.reg 11) (.const 1)))
    (P := fun s => s = st₀)
    (Inv := fun i s =>
      s.regs 11 = i ∧
      (∀ r, r ≠ 11 → r ≠ 12 → s.regs r = st₀.regs r) ∧
      (∀ j (hj : j < i) (hjK : j < k), s.mem (locAddr + verts[j]'(by omega)) = j + 1) ∧
      (∀ a, (∀ j (hj : j < i) (hjK : j < k), a ≠ locAddr + verts[j]'(by omega)) → s.mem a = st₀.mem a))
    18 0 k (Nat.zero_le k) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun r hr11 _ => by simp [Function.update_of_ne hr11],
        fun j hj _ => by omega, fun _ _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr0 : s.regs 0 = k := by rw [hi.2.1 0 (by omega) (by omega), h0]
      simp [Expr.eval, hr0])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hkr, hmark, hfr⟩
      have hiLen : i < verts.length := by omega
      have hv_n : verts[i]'hiLen < n := hv_lt _ (List.getElem_mem hiLen)
      have hvs : s.mem (vertsAddr + i) = verts[i]'hiLen := by
        rw [hfr (vertsAddr + i) (fun j hj hjK =>
          (disjointRange_ne' hdisj (by omega) (by have := hv_lt _ (List.getElem_mem (by omega : j < verts.length)); omega)
            (by omega) (by omega)).symm)]
        exact hlist i hiLen
      have hr1 : s.regs 1 = vertsAddr := by rw [hkr 1 (by omega) (by omega), h1]
      have hr6 : s.regs 6 = locAddr := by rw [hkr 6 (by omega) (by omega), h6]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := verts[i]'hiLen)
        (by simp [Expr.eval, BinOp.eval, hr1, hiReg, (by omega : vertsAddr + i < 2 ^ w), hvs]) ?_
      refine runs_store_le (x := locAddr + verts[i]'hiLen) (v := i + 1)
        (by simp [Expr.eval, BinOp.eval, hr6, (by omega : locAddr + verts[i]'hiLen < 2 ^ w)])
        (by simp [Expr.eval, BinOp.eval, hiReg, hw1, (by omega : i + 1 < 2 ^ w)]) ?_
        (by simp [Expr.size])
      refine ⟨⟨by simp, fun r h11 h12 => by
          simp [Function.update_of_ne h11, Function.update_of_ne h12, hkr r h11 h12],
        fun j hj hjK => ?_, fun a ha => ?_⟩, by simp [hiReg]⟩
      · dsimp only
        by_cases hlt : j < i
        · have hne : verts[j]'(by omega) ≠ verts[i]'hiLen := by
            intro heq
            have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨j, by omega⟩) (a₂ := ⟨i, hiLen⟩) heq
            simp at this; omega
          rw [Function.update_of_ne (by omega)]
          exact hmark j hlt hjK
        · have hjeq : j = i := by omega
          subst hjeq; simp
      · dsimp only
        rw [Function.update_of_ne (ha i (by omega) hilt)]
        exact hfr a fun j hj hjK => ha j (by omega) hjK)
  refine hloop.conseq (fun _ h => h)
    (fun o s' h => by
      cases o with
      | returned _ => exact False.elim h
      | normal =>
        rcases h with ⟨_, hkr, hmark, hfr⟩
        refine ⟨fun i hi => hmark i hi hi, fun a ha => hfr a fun j _ hjK => ha _ (List.getElem_mem (by omega)), hkr⟩)
    (fun _ _ => by simp [Expr.size]; omega)

private lemma rpcCountPorts_triple {w k e ownerAddr locAddr degAddr inUAddr portInUAddr : ℕ}
    (pProg : Program) (st₀ : State) (verts owners : List ℕ) (U : Finset ℕ)
    (h2 : st₀.regs 2 = e) (h3 : st₀.regs 3 = ownerAddr) (h6 : st₀.regs 6 = locAddr)
    (h13 : st₀.regs 13 = degAddr) (h14 : st₀.regs 14 = inUAddr) (h15 : st₀.regs 15 = portInUAddr)
    (hlenV : verts.length = k) (hndV : verts.Nodup)
    (hlenO : owners.length = 2 * e) (hownV : ∀ v ∈ owners, v ∈ verts.toFinset)
    (hlistO : ListAt st₀.mem ownerAddr owners)
    (hloc : ∀ i (hi : i < k), st₀.mem (locAddr + verts[i]'(by omega)) = i + 1)
    (hdeg0 : ∀ i < k, st₀.mem (degAddr + i) = 0)
    (hinU0 : ∀ i < k, st₀.mem (inUAddr + i) = 0)
    (hportU : ∀ p < 2 * e, st₀.mem (portInUAddr + p) = if p ∈ U then 1 else 0)
    (hdisjD_O : DisjointRange degAddr k ownerAddr (2 * e))
    (hdisjD_L : ∀ v ∈ verts, ∀ i < k, degAddr + i ≠ locAddr + v)
    (hdisjD_I : DisjointRange degAddr k inUAddr k)
    (hdisjD_P : DisjointRange degAddr k portInUAddr (2 * e))
    (hdisjI_O : DisjointRange inUAddr k ownerAddr (2 * e))
    (hdisjI_L : ∀ v ∈ verts, ∀ i < k, inUAddr + i ≠ locAddr + v)
    (hdisjI_P : DisjointRange inUAddr k portInUAddr (2 * e))
    (hwO : ownerAddr + 2 * e < 2 ^ w) (hwL : ∀ v ∈ verts, locAddr + v < 2 ^ w)
    (hwD : degAddr + k < 2 ^ w) (hwI : inUAddr + k < 2 ^ w) (hwP : portInUAddr + 2 * e < 2 ^ w)
    (hwE : 2 * e + 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) rpcCountPortsStmt
      (normalPost fun s' =>
        (∀ i (hi : i < k), s'.mem (degAddr + i) = portCountPrefix owners (2 * e) (verts[i]'(by omega))) ∧
        (∀ i (hi : i < k), s'.mem (inUAddr + i) = portInUCountPrefix owners U (2 * e) (verts[i]'(by omega))) ∧
        (∀ a, (a < degAddr ∨ degAddr + k ≤ a) → (a < inUAddr ∨ inUAddr + k ≤ a) → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≤ 10 ∨ r = 13 ∨ r = 14 ∨ r = 15 → s'.regs r = st₀.regs r))
      (fun _ => 170 * e + 30) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  intro s ω hs; subst s
  refine runs_start_le ?_
  dsimp only [rpcCountPortsStmt]
  refine runs_seq_assign_le (v := 2 * e)
    (by simp [Expr.eval, BinOp.eval, h2, hw2, (by omega : 2 * e < 2 ^ w)]) ?_
  let st1 : State := { st₀ with regs := Function.update st₀.regs 16 (2 * e) }
  have hloop := Triple.forRange_const (p := pProg) (r := 11) (lo := .const 0) (hi := .reg 16)
    (body :=
      .assign 12 (.load (.bin .add (.reg 3) (.reg 11))) ;;
      .assign 17 (.bin .sub (.load (.bin .add (.reg 6) (.reg 12))) (.const 1)) ;;
      .assign 18 (.load (.bin .add (.reg 13) (.reg 17))) ;;
      .store (.bin .add (.reg 13) (.reg 17)) (.bin .add (.reg 18) (.const 1)) ;;
      .assign 19 (.load (.bin .add (.reg 15) (.reg 11))) ;;
      .cond (.bin .lt (.const 0) (.reg 19))
        (.assign 18 (.load (.bin .add (.reg 14) (.reg 17))) ;;
         .store (.bin .add (.reg 14) (.reg 17)) (.bin .add (.reg 18) (.const 1)))
        .nop)
    (P := fun s => s = st1)
    (Inv := fun p s =>
      s.regs 11 = p ∧
      s.regs 16 = 2 * e ∧
      (∀ r, r ≤ 10 ∨ r = 13 ∨ r = 14 ∨ r = 15 → s.regs r = st₀.regs r) ∧
      (∀ i (hi : i < k), s.mem (degAddr + i) = portCountPrefix owners p (verts[i]'(by omega))) ∧
      (∀ i (hi : i < k), s.mem (inUAddr + i) = portInUCountPrefix owners U p (verts[i]'(by omega))) ∧
      (∀ a, (a < degAddr ∨ degAddr + k ≤ a) → (a < inUAddr ∨ inUAddr + k ≤ a) → s.mem a = st₀.mem a))
    72 0 (2 * e) (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp, by simp [st1],
        fun r hr => by simp [st1, Function.update_of_ne (by omega : r ≠ 11), Function.update_of_ne (by omega : r ≠ 16)],
        fun i hi => by simp [st1, portCountPrefix, hdeg0 i hi],
        fun i hi => by simp [st1, portInUCountPrefix, hinU0 i hi],
        fun _ _ _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by simp [Expr.eval, hi.2.1])
    (fun p _ hp_lt => by
      intro s ω ⟨hpReg, h16, hkr, hdeg, hinU, hfr⟩
      have hpO : p < owners.length := by omega
      set v := owners[p]'hpO
      have hv_mem : v ∈ verts := List.mem_toFinset.mp (hownV v (List.getElem_mem hpO))
      set idx := verts.idxOf v
      have hidx_lt : idx < k := by rw [← hlenV]; exact List.idxOf_lt_length_of_mem hv_mem
      have hv_eq_get : verts[idx]'(by omega) = v := List.getElem_idxOf (by omega)
      have hown_getD : owners.getD p 0 = v := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpO, v]
      have hmem_o : s.mem (ownerAddr + p) = v := by
        rw [hfr (ownerAddr + p)
          (Or.elim hdisjD_O (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
          (Or.elim hdisjI_O (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact hlistO p hpO
      have hmem_loc : s.mem (locAddr + v) = idx + 1 := by
        have h1 : ∀ a, (a < degAddr ∨ degAddr + k ≤ a) → (a < inUAddr ∨ inUAddr + k ≤ a) → s.mem a = st₀.mem a := hfr
        have hneD : locAddr + v < degAddr ∨ degAddr + k ≤ locAddr + v := by
          by_contra hc; push Not at hc
          exact hdisjD_L v hv_mem (locAddr + v - degAddr) (by omega) (by omega)
        have hneI : locAddr + v < inUAddr ∨ inUAddr + k ≤ locAddr + v := by
          by_contra hc; push Not at hc
          exact hdisjI_L v hv_mem (locAddr + v - inUAddr) (by omega) (by omega)
        rw [h1 (locAddr + v) hneD hneI, ← hv_eq_get]
        exact hloc idx hidx_lt
      have hmem_deg : s.mem (degAddr + idx) = portCountPrefix owners p v := by
        rw [← hv_eq_get]; exact hdeg idx hidx_lt
      have hmem_pU : s.mem (portInUAddr + p) = if p ∈ U then 1 else 0 := by
        rw [hfr (portInUAddr + p)
          (Or.elim hdisjD_P (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
          (Or.elim hdisjI_P (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact hportU p hp_lt
      have hdeg_le : portCountPrefix owners p v ≤ p := portCountPrefix_le owners p v
      have hinU_le : portInUCountPrefix owners U p v ≤ p := portInUCountPrefix_le owners U p v
      have hr3 : s.regs 3 = ownerAddr := by rw [hkr 3 (by omega), h3]
      have hr6 : s.regs 6 = locAddr := by rw [hkr 6 (by omega), h6]
      have hr13 : s.regs 13 = degAddr := by rw [hkr 13 (by omega), h13]
      have hr14 : s.regs 14 = inUAddr := by rw [hkr 14 (by omega), h14]
      have hr15 : s.regs 15 = portInUAddr := by rw [hkr 15 (by omega), h15]
      have hv_loc_w : locAddr + v < 2 ^ w := hwL v hv_mem
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := v)
        (by simp [Expr.eval, BinOp.eval, hr3, hpReg, (by omega : ownerAddr + p < 2 ^ w), hmem_o]) ?_
      refine runs_seq_assign_le (v := idx)
        (by simp [Expr.eval, BinOp.eval, hr6, hv_loc_w, hmem_loc, hw1, (by omega : idx < 2 ^ w)]) ?_
      refine runs_seq_assign_le (v := portCountPrefix owners p v)
        (by simp [Expr.eval, BinOp.eval, hr13, (by omega : degAddr + idx < 2 ^ w), hmem_deg]) ?_
      refine runs_seq_store_le (x := degAddr + idx) (v := portCountPrefix owners p v + 1)
        (by simp [Expr.eval, BinOp.eval, hr13, (by omega : degAddr + idx < 2 ^ w)])
        (by simp [Expr.eval, BinOp.eval, hw1, (by omega : portCountPrefix owners p v + 1 < 2 ^ w)]) ?_
      have hmem_pU' : Function.update s.mem (degAddr + idx) (portCountPrefix owners p v + 1) (portInUAddr + p) =
          if p ∈ U then 1 else 0 := by
        rw [Function.update_of_ne (disjointRange_ne' hdisjD_P (by omega) (by omega) (by omega) (by omega)).symm]
        exact hmem_pU
      refine runs_seq_assign_le (v := if p ∈ U then 1 else 0)
        (by simp [Expr.eval, BinOp.eval, hr15, hpReg, (by omega : portInUAddr + p < 2 ^ w), hmem_pU']) ?_
      let mem1 := Function.update s.mem (degAddr + idx) (portCountPrefix owners p v + 1)
      let stA : State := { mem := mem1, pos := s.pos, regs :=
        (Function.update (Function.update (Function.update (Function.update s.regs 12 v) 17 idx)
          18 (portCountPrefix owners p v)) 19 (if p ∈ U then 1 else 0)) }
      have hA_r : ∀ r, r ≤ 11 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 → stA.regs r = s.regs r := fun r hr => by
        simp [stA, Function.update_of_ne (by omega : r ≠ 19), Function.update_of_ne (by omega : r ≠ 18),
          Function.update_of_ne (by omega : r ≠ 17), Function.update_of_ne (by omega : r ≠ 12)]
      have hA_17 : stA.regs 17 = idx := by simp [stA]
      have hA_19 : stA.regs 19 = if p ∈ U then 1 else 0 := by simp [stA]
      have hdeg_post : ∀ i (hi : i < k), mem1 (degAddr + i) = portCountPrefix owners (p + 1) (verts[i]'(by omega)) := by
        intro i hi
        rw [portCountPrefix_succ, hown_getD]
        by_cases hieq : i = idx
        · subst hieq; simp [mem1, hv_eq_get]
        · have hvne : v ≠ verts[i]'(by omega) := by
            intro heq
            have := (List.nodup_iff_injective_getElem.mp hndV) (a₁ := ⟨idx, by omega⟩) (a₂ := ⟨i, by omega⟩)
              (by simpa [hv_eq_get] using heq)
            simp at this; exact hieq this.symm
          simp only [mem1, Function.update_of_ne (by omega : degAddr + i ≠ degAddr + idx), hvne,
            ↓reduceIte, add_zero]
          exact hdeg i hi
      by_cases hpU : p ∈ U
      · have hmem_inU : mem1 (inUAddr + idx) = portInUCountPrefix owners U p v := by
          dsimp only [mem1]
          rw [Function.update_of_ne (disjointRange_ne' hdisjD_I (by omega) (by omega) (by omega) (by omega)).symm,
            ← hv_eq_get]
          exact hinU idx hidx_lt
        let stB : State := { stA with regs := Function.update stA.regs 18 (portInUCountPrefix owners U p v) }
        let mem2 := Function.update mem1 (inUAddr + idx) (portInUCountPrefix owners U p v + 1)
        let stC : State := { stB with mem := mem2 }
        have hs1 : Runs w pProg ω (.assign 18 (.load (.bin .add (.reg 14) (.reg 17)))) stA .normal stB 5 := by
          rw [runs_assign_iff]
          exact ⟨portInUCountPrefix owners U p v,
            by simp [Expr.eval, BinOp.eval, hA_r 14 (by omega), hr14, hA_17,
                 (by omega : inUAddr + idx < 2 ^ w), stA, hmem_inU],
            rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.store (.bin .add (.reg 14) (.reg 17)) (.bin .add (.reg 18) (.const 1)))
            stB .normal stC 7 := by
          rw [runs_store_iff]
          exact ⟨inUAddr + idx, portInUCountPrefix owners U p v + 1,
            by simp [Expr.eval, BinOp.eval, stB, hA_r 14 (by omega), hr14, hA_17,
                 (by omega : inUAddr + idx < 2 ^ w)],
            by simp [Expr.eval, BinOp.eval, stB, hw1, (by omega : portInUCountPrefix owners U p v + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        refine ⟨.normal, stC, 17, runs_cond_iff.mpr ⟨1, 13,
            by simp [Expr.eval, BinOp.eval, hA_19, hpU, hw1, (by omega : 0 < 2 ^ w)],
            by simp only [one_ne_zero, ↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 7, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, by simp [stC, stB, hA_r 16 (by omega), h16],
          fun r hr => by simp [stC, stB, Function.update_of_ne (by omega : r ≠ 11),
            Function.update_of_ne (by omega : r ≠ 18), hA_r r (by omega), hkr r hr],
          ?_, ?_, ?_⟩, by simp [stC, stB, hA_r 11 (by omega), hpReg]⟩
        · intro i hi
          dsimp only [stC, mem2]
          rw [Function.update_of_ne (disjointRange_ne' hdisjD_I (by omega) (by omega) (by omega) (by omega))]
          exact hdeg_post i hi
        · intro i hi
          dsimp only [stC, mem2]
          rw [portInUCountPrefix_succ, hown_getD]
          by_cases hieq : i = idx
          · subst hieq; simp [hv_eq_get, hpU]
          · have hvne : v ≠ verts[i]'(by omega) := by
              intro heq
              have := (List.nodup_iff_injective_getElem.mp hndV) (a₁ := ⟨idx, by omega⟩) (a₂ := ⟨i, by omega⟩)
                (by simpa [hv_eq_get] using heq)
              simp at this; exact hieq this.symm
            rw [Function.update_of_ne (by omega : inUAddr + i ≠ inUAddr + idx)]
            dsimp only [mem1]
            rw [Function.update_of_ne (disjointRange_ne' hdisjD_I (by omega) (by omega) (by omega) (by omega)).symm]
            simp only [hvne, false_and, ↓reduceIte, add_zero]
            exact hinU i hi
        · intro a haD haI
          dsimp only [stC, mem2, mem1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr a haD haI
      · refine ⟨.normal, stA, 5, runs_cond_iff.mpr ⟨0, 1,
            by simp [Expr.eval, BinOp.eval, hA_19, hpU, (by omega : 0 < 2 ^ w)],
            by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, by simp [hA_r 16 (by omega), h16],
          fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 11), hA_r r (by omega), hkr r hr],
          hdeg_post, ?_, ?_⟩, by simp [hA_r 11 (by omega), hpReg]⟩
        · intro i hi
          dsimp only [stA, mem1]
          rw [portInUCountPrefix_succ, Function.update_of_ne (disjointRange_ne' hdisjD_I (by omega) (by omega) (by omega) (by omega)).symm]
          simp only [hpU, and_false, ↓reduceIte, add_zero]
          exact hinU i hi
        · intro a haD haI
          dsimp only [stA, mem1]
          rw [Function.update_of_ne (by omega)]
          exact hfr a haD haI)
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, _, h2_kr, h2_deg, h2_inU, h2_fr⟩
      exact ⟨h2_deg, h2_inU, h2_fr, h2_kr⟩) (by simp [Expr.size]; omega)

private lemma rpcSplitVerts_triple {w k e vertsAddr degAddr inUAddr outSAddr outTAddr : ℕ}
    (pProg : Program) (st₀ : State) (verts owners : List ℕ) (U : Finset ℕ)
    (h0 : st₀.regs 0 = k) (h1 : st₀.regs 1 = vertsAddr) (h7 : st₀.regs 7 = outSAddr)
    (h8 : st₀.regs 8 = outTAddr) (h13 : st₀.regs 13 = degAddr) (h14 : st₀.regs 14 = inUAddr)
    (hlenV : verts.length = k)
    (hlistV : ListAt st₀.mem vertsAddr verts)
    (hdeg : ∀ i (hi : i < k), st₀.mem (degAddr + i) = portCountPrefix owners (2 * e) (verts[i]'(by omega)))
    (hinU : ∀ i (hi : i < k), st₀.mem (inUAddr + i) = portInUCountPrefix owners U (2 * e) (verts[i]'(by omega)))
    (hdSV : DisjointRange outSAddr k vertsAddr k) (hdSD : DisjointRange outSAddr k degAddr k)
    (hdSI : DisjointRange outSAddr k inUAddr k) (hdST : DisjointRange outSAddr k outTAddr k)
    (hdTV : DisjointRange outTAddr k vertsAddr k) (hdTD : DisjointRange outTAddr k degAddr k)
    (hdTI : DisjointRange outTAddr k inUAddr k)
    (hwV : vertsAddr + k < 2 ^ w) (hwD : degAddr + k < 2 ^ w) (hwI : inUAddr + k < 2 ^ w)
    (hwS : outSAddr + k < 2 ^ w) (hwT : outTAddr + k < 2 ^ w)
    (hwE : 4 * e + 16 < 2 ^ w) (hwK : k + 16 < 2 ^ w) :
    let inS : ℕ → Bool := fun x =>
      decide (portCountPrefix owners (2 * e) x ≤ 2 * portInUCountPrefix owners U (2 * e) x)
    Triple w pProg (fun s => s = st₀) rpcSplitVertsStmt
      (normalPost fun s' =>
        s'.regs 17 = (verts.filter inS).length ∧
        s'.regs 18 = (verts.filter fun x => !inS x).length ∧
        ListAt s'.mem outSAddr (verts.filter inS) ∧
        ListAt s'.mem outTAddr (verts.filter fun x => !inS x) ∧
        (∀ a, (a < outSAddr ∨ outSAddr + k ≤ a) → (a < outTAddr ∨ outTAddr + k ≤ a) →
          s'.mem a = st₀.mem a) ∧
        (∀ r, r ≤ 10 ∨ r = 13 ∨ r = 14 ∨ r = 15 → s'.regs r = st₀.regs r))
      (fun _ => 60 * k + 30) := by
  intro inS s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [rpcSplitVertsStmt]
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  let st1 : State := { st₀ with regs := Function.update (Function.update st₀.regs 17 0) 18 0 }
  have hloop := Triple.forRange_const (p := pProg) (r := 11) (lo := .const 0) (hi := .reg 0)
    (body :=
      .assign 12 (.load (.bin .add (.reg 1) (.reg 11))) ;;
      .assign 19 (.load (.bin .add (.reg 13) (.reg 11))) ;;
      .assign 20 (.bin .mul (.const 2) (.load (.bin .add (.reg 14) (.reg 11)))) ;;
      .cond (.bin .lt (.reg 20) (.reg 19))
        (.store (.bin .add (.reg 8) (.reg 18)) (.reg 12) ;;
         .assign 18 (.bin .add (.reg 18) (.const 1)))
        (.store (.bin .add (.reg 7) (.reg 17)) (.reg 12) ;;
         .assign 17 (.bin .add (.reg 17) (.const 1))))
    (P := fun s => s = st1)
    (Inv := fun i s =>
      let sP := (verts.take i).filter inS
      let tP := (verts.take i).filter fun x => !inS x
      s.regs 11 = i ∧
      (∀ r, r ≤ 10 ∨ r = 13 ∨ r = 14 ∨ r = 15 → s.regs r = st₀.regs r) ∧
      s.regs 17 = sP.length ∧
      s.regs 18 = tP.length ∧
      ListAt s.mem outSAddr sP ∧
      ListAt s.mem outTAddr tP ∧
      (∀ a, (a < outSAddr ∨ outSAddr + sP.length ≤ a) →
        (a < outTAddr ∨ outTAddr + tP.length ≤ a) → s.mem a = st₀.mem a))
    48 0 k (Nat.zero_le k) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun r hr => by simp [st1, Function.update_of_ne (by omega : r ≠ 11),
          Function.update_of_ne (by omega : r ≠ 18), Function.update_of_ne (by omega : r ≠ 17)],
        by simp [st1], by simp [st1], fun j hj => by simp at hj, fun j hj => by simp at hj,
        fun _ _ _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr0 : s.regs 0 = k := by rw [hi.2.1 0 (by omega), h0]
      simp [Expr.eval, hr0])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hkr, hr17, hr18, hsL, htL, hfr⟩
      have hiLen : i < verts.length := by omega
      set v := verts[i]'hiLen
      have hsLe : ((verts.take i).filter inS).length ≤ i := by
        have := List.length_filter_le inS (verts.take i)
        rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
      have htLe : ((verts.take i).filter fun x => !inS x).length ≤ i := by
        have := List.length_filter_le (fun x => !inS x) (verts.take i)
        rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
      have hmv : s.mem (vertsAddr + i) = v := by
        rw [hfr (vertsAddr + i)
          (Or.elim hdSV (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
          (Or.elim hdTV (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact hlistV i hiLen
      have hmd : s.mem (degAddr + i) = portCountPrefix owners (2 * e) v := by
        rw [hfr (degAddr + i)
          (Or.elim hdSD (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
          (Or.elim hdTD (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact hdeg i hilt
      have hmi : s.mem (inUAddr + i) = portInUCountPrefix owners U (2 * e) v := by
        rw [hfr (inUAddr + i)
          (Or.elim hdSI (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
          (Or.elim hdTI (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact hinU i hilt
      have hd_le : portCountPrefix owners (2 * e) v ≤ 2 * e := portCountPrefix_le owners (2 * e) v
      have hi_le : portInUCountPrefix owners U (2 * e) v ≤ 2 * e := portInUCountPrefix_le owners U (2 * e) v
      have hr1 : s.regs 1 = vertsAddr := by rw [hkr 1 (by omega), h1]
      have hr7 : s.regs 7 = outSAddr := by rw [hkr 7 (by omega), h7]
      have hr8 : s.regs 8 = outTAddr := by rw [hkr 8 (by omega), h8]
      have hr13 : s.regs 13 = degAddr := by rw [hkr 13 (by omega), h13]
      have hr14 : s.regs 14 = inUAddr := by rw [hkr 14 (by omega), h14]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := v)
        (by simp [Expr.eval, BinOp.eval, hr1, hiReg, (by omega : vertsAddr + i < 2 ^ w), hmv]) ?_
      refine runs_seq_assign_le (v := portCountPrefix owners (2 * e) v)
        (by simp [Expr.eval, BinOp.eval, hr13, hiReg, (by omega : degAddr + i < 2 ^ w), hmd]) ?_
      refine runs_seq_assign_le (v := 2 * portInUCountPrefix owners U (2 * e) v)
        (by simp [Expr.eval, BinOp.eval, hr14, hiReg, hw2, (by omega : inUAddr + i < 2 ^ w), hmi,
              (by omega : 2 * portInUCountPrefix owners U (2 * e) v < 2 ^ w)]) ?_
      let stA : State := { s with regs :=
        (Function.update (Function.update (Function.update s.regs 12 v)
          19 (portCountPrefix owners (2 * e) v)) 20 (2 * portInUCountPrefix owners U (2 * e) v)) }
      have hA_r : ∀ r, r ≤ 11 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 17 ∨ r = 18 → stA.regs r = s.regs r :=
        fun r hr => by
          simp [stA, Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 19),
            Function.update_of_ne (by omega : r ≠ 12)]
      have hA_12 : stA.regs 12 = v := by simp [stA]
      have hA_19 : stA.regs 19 = portCountPrefix owners (2 * e) v := by simp [stA]
      have hA_20 : stA.regs 20 = 2 * portInUCountPrefix owners U (2 * e) v := by simp [stA]
      by_cases hlt_in : 2 * portInUCountPrefix owners U (2 * e) v < portCountPrefix owners (2 * e) v
      · have hinS_f : inS v = false := by simp [inS]; omega
        let tLen := ((verts.take i).filter fun x => !inS x).length
        let memB := Function.update s.mem (outTAddr + tLen) v
        let stB : State := { stA with mem := memB }
        let stC : State := { stB with regs := Function.update stB.regs 18 (tLen + 1) }
        have hs1 : Runs w pProg ω (.store (.bin .add (.reg 8) (.reg 18)) (.reg 12)) stA .normal stB 5 := by
          rw [runs_store_iff]
          exact ⟨outTAddr + tLen, v,
            by simp [Expr.eval, BinOp.eval, hA_r 8 (by omega), hr8, hA_r 18 (by omega), hr18, tLen,
                 (by omega : outTAddr + tLen < 2 ^ w)],
            by simp [Expr.eval, hA_12], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.assign 18 (.bin .add (.reg 18) (.const 1))) stB .normal stC 4 := by
          rw [runs_assign_iff]
          exact ⟨tLen + 1,
            by simp [Expr.eval, BinOp.eval, stB, hA_r 18 (by omega), hr18, hw1, tLen,
                 (by omega : tLen + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        have htS : (verts.take (i + 1)).filter inS = (verts.take i).filter inS := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp [v, hinS_f]
        have htT : (verts.take (i + 1)).filter (fun x => !inS x) =
            (verts.take i).filter (fun x => !inS x) ++ [v] := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp [v, hinS_f]
        refine ⟨.normal, stC, 14, runs_cond_iff.mpr ⟨1, 10,
            by simp [Expr.eval, BinOp.eval, hlt_in, hw1],
            by simp only [one_ne_zero, ↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, fun r hr => by simp [stC, stB, Function.update_of_ne (by omega : r ≠ 11),
            Function.update_of_ne (by omega : r ≠ 18), hA_r r (by omega), hkr r hr],
          by rw [htS]; simp [stC, stB, hA_r 17 (by omega), hr17],
          by simp [stC, htT, tLen], ?_, ?_, ?_⟩, by simp [stC, stB, hA_r 11 (by omega), hiReg]⟩
        · rw [htS]; intro j hj; dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (disjointRange_ne' hdST (by omega) (by omega) (by omega) (by omega))]
          exact hsL j hj
        · rw [htT]; simpa [stC, stB, memB, tLen] using htL.snoc v
        · intro a haS haT
          rw [htS] at haS; rw [htT, List.length_append, List.length_singleton] at haT
          dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (by omega)]
          exact hfr a haS (by omega)
      · have hinS_t : inS v = true := by simp [inS]; omega
        let sLen := ((verts.take i).filter inS).length
        let memB := Function.update s.mem (outSAddr + sLen) v
        let stB : State := { stA with mem := memB }
        let stC : State := { stB with regs := Function.update stB.regs 17 (sLen + 1) }
        have hs1 : Runs w pProg ω (.store (.bin .add (.reg 7) (.reg 17)) (.reg 12)) stA .normal stB 5 := by
          rw [runs_store_iff]
          exact ⟨outSAddr + sLen, v,
            by simp [Expr.eval, BinOp.eval, hA_r 7 (by omega), hr7, hA_r 17 (by omega), hr17, sLen,
                 (by omega : outSAddr + sLen < 2 ^ w)],
            by simp [Expr.eval, hA_12], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.assign 17 (.bin .add (.reg 17) (.const 1))) stB .normal stC 4 := by
          rw [runs_assign_iff]
          exact ⟨sLen + 1,
            by simp [Expr.eval, BinOp.eval, stB, hA_r 17 (by omega), hr17, hw1, sLen,
                 (by omega : sLen + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        have htS : (verts.take (i + 1)).filter inS = (verts.take i).filter inS ++ [v] := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp [v, hinS_t]
        have htT : (verts.take (i + 1)).filter (fun x => !inS x) =
            (verts.take i).filter (fun x => !inS x) := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp [v, hinS_t]
        refine ⟨.normal, stC, 14, runs_cond_iff.mpr ⟨0, 10,
            by simp [Expr.eval, BinOp.eval, hlt_in],
            by simp only [↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, fun r hr => by simp [stC, stB, Function.update_of_ne (by omega : r ≠ 11),
            Function.update_of_ne (by omega : r ≠ 17), hA_r r (by omega), hkr r hr],
          by simp [stC, htS, sLen],
          by rw [htT]; simp [stC, stB, hA_r 18 (by omega), hr18], ?_, ?_, ?_⟩,
          by simp [stC, stB, hA_r 11 (by omega), hiReg]⟩
        · rw [htS]; simpa [stC, stB, memB, sLen] using hsL.snoc v
        · rw [htT]; intro j hj; dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (disjointRange_ne' hdST (by omega) (by omega) (by omega) (by omega)).symm]
          exact htL j hj
        · intro a haS haT
          rw [htS, List.length_append, List.length_singleton] at haS; rw [htT] at haT
          dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (by omega)]
          exact hfr a (by omega) haT)
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, h2_kr, h2_17, h2_18, h2_sL, h2_tL, h2_fr⟩
      have htakeV : verts.take k = verts := by rw [← hlenV, List.take_length]
      rw [htakeV] at h2_17 h2_18 h2_sL h2_tL h2_fr
      have hs_le : (verts.filter inS).length ≤ k := by rw [← hlenV]; exact List.length_filter_le _ _
      have ht_le : (verts.filter fun x => !inS x).length ≤ k := by rw [← hlenV]; exact List.length_filter_le _ _
      exact ⟨h2_17, h2_18, h2_sL, h2_tL, fun a haS haT => h2_fr a (by omega) (by omega), h2_kr⟩)
    (by simp [Expr.size]; omega)

/-- Specification of `outerRoundPortCutProc`. -/
theorem outerRoundPortCutProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [outerRoundPortCutProc]) :
    MeetsContract w pProg b (outerRoundPortCutContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, k, vertsAddr, e, ownerAddr, kU, uAddr, locAddr, outSAddr, outTAddr,
    outLenAddr, h, verts, owners, uList, rfl, hlenV, hndV, hv_lt, hlenO, hownV, hlenU, hndU,
    hu_lt, hlistV, hlistO, hlistU, hloc0, hzero, hw, hdisj⟩
  rcases hw with ⟨hwV, hwO, hwU, hwLoc, hwS, hwT, hwLen, hwH, hw4e, hwK⟩
  rcases hdisj with ⟨hdLocV, hdLocO, hdLocU, hdLocS, hdLocT, hdLocLen, hdSV, hdSO, hdSU, hdST,
    hdSLen, hdTV, hdTO, hdTU, hdTLen, hdLenV, hdLenO, hdLenU⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  unfold roundPortCutSpace at hwH
  let degAddr := h
  let inUAddr := h + k
  let portInUAddr := h + 2 * k
  let h' := h + 2 * k + 2 * e
  set U := uList.toFinset
  set inS : ℕ → Bool := fun x =>
    decide (portCountPrefix owners (2 * e) x ≤ 2 * portInUCountPrefix owners U (2 * e) x)
  refine runs_start_le ?_
  dsimp only [outerRoundPortCutProc]
  refine runs_seq_assign_le (v := degAddr) (by simp [Expr.eval, startState, degAddr]) ?_
  refine runs_seq_assign_le (v := inUAddr)
    (by simp [Expr.eval, BinOp.eval, startState, inUAddr, (by omega : h + k < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := portInUAddr)
    (by simp [Expr.eval, BinOp.eval, startState, inUAddr, portInUAddr,
          (by omega : h + k + k < 2 ^ w)]; omega) ?_
  -- Stage 1: rpcFillLocStmt
  let st0 : State := { startState [k, vertsAddr, e, ownerAddr, kU, uAddr, locAddr, outSAddr,
      outTAddr, outLenAddr, h] mem pos with
    regs := Function.update (Function.update (Function.update
      (startState [k, vertsAddr, e, ownerAddr, kU, uAddr, locAddr, outSAddr, outTAddr,
        outLenAddr, h] mem pos).regs 13 degAddr) 14 inUAddr) 15 portInUAddr }
  have h0_r : ∀ r ≤ 10, st0.regs r = (startState [k, vertsAddr, e, ownerAddr, kU, uAddr, locAddr,
      outSAddr, outTAddr, outLenAddr, h] mem pos).regs r := fun r hr => by
    simp [st0, Function.update_of_ne (by omega : r ≠ 15), Function.update_of_ne (by omega : r ≠ 14),
      Function.update_of_ne (by omega : r ≠ 13)]
  refine runs_seq_triple_le
    (rpcFillLoc_triple (w := w) (n := n) (k := k) (vertsAddr := vertsAddr) (locAddr := locAddr)
      pProg st0 verts (by rw [h0_r 0 (by omega)]; simp [startState])
      (by rw [h0_r 1 (by omega)]; simp [startState]) (by rw [h0_r 6 (by omega)]; simp [startState])
      hlenV hndV hv_lt hlistV hdLocV (by omega) (by omega) (by omega) hw1) rfl ?_
  intro st1 ⟨h1_loc, h1_fr, h1_kr⟩
  -- Stage 2: rpcMarkUStmt (uses markVerts_triple with locAddr := portInUAddr)
  have h1_uList : ListAt st1.mem uAddr uList := by
    intro j hj
    rw [h1_fr (uAddr + j) (fun v hv =>
      (disjointRange_ne' hdLocU (by omega) (by have := hv_lt v hv; omega) (by omega) (by omega)).symm)]
    exact hlistU j hj
  have h1_zero : ZeroFrom st1.mem h := fun a ha => by
    rw [h1_fr a (fun v hv => by have := hv_lt v hv; omega)]
    exact hzero a ha
  refine runs_seq_triple_le
    (markVerts_triple (w := w) (n := 2 * e) (len := kU) (listAddr := uAddr) (locAddr := portInUAddr)
      (val := 1) (rLen := 4) (rList := 5) (rLoc := 15) (rI := 11) (rU := 12)
      pProg st1 uList (by decide)
      (by rw [h1_kr 4 (by omega) (by omega), h0_r 4 (by omega)]; simp [startState])
      (by rw [h1_kr 5 (by omega) (by omega), h0_r 5 (by omega)]; simp [startState])
      (by rw [h1_kr 15 (by omega) (by omega)]; simp [st0])
      hlenU hu_lt h1_uList (Or.inr (by omega)) (by omega) (by omega) hw1 hw1) rfl ?_
  intro st2 ⟨h2_mark, h2_fr, h2_kr⟩
  -- Stage 3: rpcCountPortsStmt
  have h2_owners : ListAt st2.mem ownerAddr owners := by
    intro j hj
    rw [h2_fr (ownerAddr + j) (fun p _ => by omega)]
    rw [h1_fr (ownerAddr + j) (fun v hv =>
      (disjointRange_ne' hdLocO (by omega) (by have := hv_lt v hv; omega) (by omega) (by omega)).symm)]
    exact hlistO j hj
  have h2_loc : ∀ i (hi : i < k), st2.mem (locAddr + verts[i]'(by omega)) = i + 1 := fun i hi => by
    rw [h2_fr _ (fun p _ => by have := hv_lt _ (List.getElem_mem (by omega : i < verts.length)); omega)]
    exact h1_loc i hi
  have h2_deg0 : ∀ i < k, st2.mem (degAddr + i) = 0 := fun i hi => by
    rw [h2_fr (degAddr + i) (fun p _ => by omega)]; exact h1_zero _ (by omega)
  have h2_inU0 : ∀ i < k, st2.mem (inUAddr + i) = 0 := fun i hi => by
    rw [h2_fr (inUAddr + i) (fun p _ => by omega)]; exact h1_zero _ (by omega)
  have h2_portU : ∀ p < 2 * e, st2.mem (portInUAddr + p) = if p ∈ U then 1 else 0 := by
    intro p hp
    by_cases hpU : p ∈ U
    · simp only [hpU, ↓reduceIte]; exact h2_mark p (List.mem_toFinset.mp hpU)
    · simp only [hpU, ↓reduceIte]
      rw [h2_fr (portInUAddr + p) (fun q hq heq => hpU (List.mem_toFinset.mpr ((show p = q by omega) ▸ hq)))]
      exact h1_zero _ (by omega)
  have h2_r : ∀ r, r ≤ 10 ∨ r = 13 ∨ r = 14 ∨ r = 15 → st2.regs r = st0.regs r := fun r hr => by
    rw [h2_kr r (by omega) (by omega), h1_kr r (by omega) (by omega)]
  refine runs_seq_triple_le
    (rpcCountPorts_triple (w := w) (k := k) (e := e) (ownerAddr := ownerAddr) (locAddr := locAddr)
      (degAddr := degAddr) (inUAddr := inUAddr) (portInUAddr := portInUAddr)
      pProg st2 verts owners U
      (by rw [h2_r 2 (by omega), h0_r 2 (by omega)]; simp [startState])
      (by rw [h2_r 3 (by omega), h0_r 3 (by omega)]; simp [startState])
      (by rw [h2_r 6 (by omega), h0_r 6 (by omega)]; simp [startState])
      (by rw [h2_r 13 (by omega)]; simp [st0])
      (by rw [h2_r 14 (by omega)]; simp [st0])
      (by rw [h2_r 15 (by omega)]; simp [st0])
      hlenV hndV hlenO hownV h2_owners h2_loc h2_deg0 h2_inU0 h2_portU
      (Or.inr (by omega)) (fun v hv i _ => by have := hv_lt v hv; omega)
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun v hv i _ => by have := hv_lt v hv; omega) (Or.inl (by omega))
      (by omega) (fun v hv => by have := hv_lt v hv; omega) (by omega) (by omega) (by omega)
      (by omega)) rfl ?_
  intro st3 ⟨h3_deg, h3_inU, h3_fr, h3_kr⟩
  -- Stage 4: rpcSplitVertsStmt
  have h3_verts : ListAt st3.mem vertsAddr verts := by
    intro j hj
    rw [h3_fr (vertsAddr + j) (Or.inl (by omega)) (Or.inl (by omega))]
    rw [h2_fr (vertsAddr + j) (fun _ _ => by omega)]
    rw [h1_fr (vertsAddr + j) (fun v hv =>
      (disjointRange_ne' hdLocV (by omega) (by have := hv_lt v hv; omega) (by omega) (by omega)).symm)]
    exact hlistV j hj
  have h3_r : ∀ r, r ≤ 10 ∨ r = 13 ∨ r = 14 ∨ r = 15 → st3.regs r = st0.regs r := fun r hr => by
    rw [h3_kr r hr, h2_r r hr]
  refine runs_seq_triple_le
    (rpcSplitVerts_triple (w := w) (k := k) (e := e) (vertsAddr := vertsAddr) (degAddr := degAddr)
      (inUAddr := inUAddr) (outSAddr := outSAddr) (outTAddr := outTAddr)
      pProg st3 verts owners U
      (by rw [h3_r 0 (by omega), h0_r 0 (by omega)]; simp [startState])
      (by rw [h3_r 1 (by omega), h0_r 1 (by omega)]; simp [startState])
      (by rw [h3_r 7 (by omega), h0_r 7 (by omega)]; simp [startState])
      (by rw [h3_r 8 (by omega), h0_r 8 (by omega)]; simp [startState])
      (by rw [h3_r 13 (by omega)]; simp [st0])
      (by rw [h3_r 14 (by omega)]; simp [st0])
      hlenV h3_verts h3_deg h3_inU hdSV (Or.inl (by omega)) (Or.inl (by omega)) hdST
      hdTV (Or.inl (by omega)) (Or.inl (by omega))
      (by omega) (by omega) (by omega) (by omega) (by omega) hw4e hwK) rfl ?_
  intro st4 ⟨h4_17, h4_18, h4_sL, h4_tL, h4_fr, h4_kr⟩
  -- Stage 5: clear locAddr over verts
  have h4_verts : ListAt st4.mem vertsAddr verts := by
    intro j hj
    rw [h4_fr (vertsAddr + j)
      (Or.elim hdSV (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
      (Or.elim hdTV (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
    exact h3_verts j hj
  have h4_r : ∀ r, r ≤ 10 ∨ r = 13 ∨ r = 14 ∨ r = 15 → st4.regs r = st0.regs r := fun r hr => by
    rw [h4_kr r hr, h3_r r hr]
  refine runs_seq_triple_le
    (markVerts_triple (w := w) (n := n) (len := k) (listAddr := vertsAddr) (locAddr := locAddr)
      (val := 0) (rLen := 0) (rList := 1) (rLoc := 6) (rI := 11) (rU := 12)
      pProg st4 verts (by decide)
      (by rw [h4_r 0 (by omega), h0_r 0 (by omega)]; simp [startState])
      (by rw [h4_r 1 (by omega), h0_r 1 (by omega)]; simp [startState])
      (by rw [h4_r 6 (by omega), h0_r 6 (by omega)]; simp [startState])
      hlenV hv_lt h4_verts hdLocV (by omega) (by omega) (by omega) hw1) rfl ?_
  intro st5 ⟨h5_clear, h5_fr, h5_kr⟩
  have h5_r : ∀ r, r ≤ 10 ∨ r = 13 ∨ r = 14 ∨ r = 15 → st5.regs r = st0.regs r := fun r hr => by
    rw [h5_kr r (by omega) (by omega), h4_r r hr]
  have h5_17 : st5.regs 17 = (verts.filter inS).length := by
    rw [h5_kr 17 (by omega) (by omega)]; exact h4_17
  have h5_18 : st5.regs 18 = (verts.filter fun x => !inS x).length := by
    rw [h5_kr 18 (by omega) (by omega)]; exact h4_18
  -- Stage 6: store [lenS, lenT] at outLenAddr and return h'
  refine runs_seq_store_le (x := outLenAddr) (v := (verts.filter inS).length)
    (by simp [Expr.eval, h5_r 9 (by omega), h0_r 9 (by omega), startState])
    (by simp [Expr.eval, h5_17]) ?_
  refine runs_seq_store_le (x := outLenAddr + 1) (v := (verts.filter fun x => !inS x).length)
    (by simp [Expr.eval, BinOp.eval, h5_r 9 (by omega), h0_r 9 (by omega), startState, hw1,
          (by omega : outLenAddr + 1 < 2 ^ w)])
    (by simp [Expr.eval, h5_18]) ?_
  refine runs_ret_le (v := h')
    (by simp [Expr.eval, BinOp.eval, h5_r 15 (by omega), h5_r 2 (by omega),
          st0, startState, hw2, portInUAddr, h', (by omega : 2 * e < 2 ^ w),
          (by omega : h + 2 * k + 2 * e < 2 ^ w)]) ?_ ?_
  · dsimp only [outerRoundPortCutContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    have hreadV : readList mem vertsAddr k = verts := by rw [← hlenV]; exact readList_eq_of_listAt hlistV
    have hreadO : readList mem ownerAddr (2 * e) = owners := by rw [← hlenO]; exact readList_eq_of_listAt hlistO
    have hreadU : readList mem uAddr kU = uList := by rw [← hlenU]; exact readList_eq_of_listAt hlistU
    simp only [hreadV, hreadO, hreadU]
    have hs_le : (verts.filter inS).length ≤ k := by rw [← hlenV]; exact List.length_filter_le _ _
    have ht_le : (verts.filter fun x => !inS x).length ≤ k := by rw [← hlenV]; exact List.length_filter_le _ _
    refine ⟨by simp [h', roundPortCutSpace]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rw [h5_fr a (fun v hv => by have := hv_lt v hv; omega)]
      rw [h4_fr a (Or.inr (by omega)) (Or.inr (by omega))]
      rw [h3_fr a (Or.inr (by omega)) (Or.inr (by omega))]
      rw [h2_fr a (fun p hp => by have := hu_lt p hp; omega)]
      exact h1_zero a (by omega)
    · intro j hj
      have hj' : j < (verts.filter inS).length := hj
      rw [Function.update_of_ne (disjointRange_ne' hdSLen (by omega) (by omega) (by omega) (by omega)),
        Function.update_of_ne (disjointRange_ne' hdSLen (by omega) (by omega) (by omega) (by omega))]
      rw [h5_fr (outSAddr + j) (fun v hv =>
        (disjointRange_ne' hdLocS (by omega) (by have := hv_lt v hv; omega) (by omega) (by omega)).symm)]
      exact h4_sL j hj'
    · intro j hj
      have hj' : j < (verts.filter fun x => !inS x).length := hj
      rw [Function.update_of_ne (disjointRange_ne' hdTLen (by omega) (by omega) (by omega) (by omega)),
        Function.update_of_ne (disjointRange_ne' hdTLen (by omega) (by omega) (by omega) (by omega))]
      rw [h5_fr (outTAddr + j) (fun v hv =>
        (disjointRange_ne' hdLocT (by omega) (by have := hv_lt v hv; omega) (by omega) (by omega)).symm)]
      exact h4_tL j hj'
    · rw [Function.update_of_ne (by omega : outLenAddr ≠ outLenAddr + 1), Function.update_self]
    · rw [Function.update_self]
    · intro a haH haS haT haLen
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      by_cases hvMem : ∃ v ∈ verts, a = locAddr + v
      · rcases hvMem with ⟨v, hv, rfl⟩
        rw [h5_clear v hv, hloc0 v (hv_lt v hv)]
      · push Not at hvMem
        rw [h5_fr a hvMem, h4_fr a haS haT, h3_fr a (Or.inl (by omega)) (Or.inl (by omega)),
          h2_fr a (fun _ _ => by omega), h1_fr a hvMem]
        rfl
  · simp only [outerRoundPortCutContract, outerRoundPortCutCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega

end MinCostFlow.ExpanderDecomp
