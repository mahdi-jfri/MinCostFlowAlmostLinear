module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedUpdateSLoops

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerRevHelpers
public import MinCostFlow.DynSpanner.Program.StateLayout
public import WordRAM.Tactic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of `dsUpdateSLevelsStmt` (`DynSpannerAffectedUpdateS`)

Proves `dsUpdateSLevels_meetsContract`: `dsUpdateSLevelsStmt bOps` (`affIdxUpdateSLevels = 0`)
updates generation-stamped singly-linked vertex lists `sLists[0..j-1]` with `touchedVertices G u`
and zeroes `sGen[j..L]`, in `O(L + 1)` time and `O(j)` heap words.

The file is split in three parts: `DynSpannerAffectedUpdateSHelpers.lean` (the contract, layout
facts, the first phase and the insertion of one vertex), `DynSpannerAffectedUpdateSLoops.lean`
(the two loops), and this file (the proof of the contract).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section
/-! ## Public contract proof -/

/-- `dsUpdateSLevelsStmt bOps` (`affIdxUpdateSLevels = 0`) meets `dsUpdateSLevelsContract`. -/
public theorem dsUpdateSLevels_meetsContract {w L vCap eCap b j uLen : ℕ}
    {G : MGraph} {u : Update} {S_level : Fin (L + 1) → Finset ℕ}
    {sLists : Fin (L + 1) → List ℕ} {foot0 : ℕ → Prop}
    {p : Program} {bOps bAff : ℕ}
    (hpAff : p.HasAt bAff (affectedProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bAff + affIdxUpdateSLevels)
      (dsUpdateSLevelsContract w L vCap eCap b j G u uLen S_level sLists foot0) := by
  refine meetsContract_of_runs
    (hpAff.get (i := affIdxUpdateSLevels) (by simp [affectedProcs, affIdxUpdateSLevels]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨updPtr, heapPtr, rfl, hw16, hb1, hj1, hjL, hfix, hh_lt,
    hmL, hmV, hmE, hgen_pos, hgen_lt, hG, hG_val, hGv, hGe, hUpd, hU_val, hds, hupd_lt, htouch_cap,
    hfoot0, hOrigS⟩
  obtain ⟨hL_word, hvC_word⟩ := dsSBounds_lv (w := w) hfix (by omega)
  have hG_fix : dsGPtr b + dynGraphSize vCap eCap < 2 ^ w := by
    have := dsFixedSize_ge_aux b L vCap eCap
    have h1 : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
    have h2 : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
    linarith only [hfix, hh_lt, this, h1, h2]
  dsimp only [affectedProcs, affIdxUpdateSLevels, List.getElem_cons_zero, dsUpdateSLevelsStmt]
  refine dsUpdateS_touched_cont hpOps hw16 (by simpa [startState] using hupd_lt) rfl rfl
    hG_fix hG hG_val hGe (by simpa [startState] using hUpd) hU_val hds
    (fun v hv => lt_trans (htouch_cap v hv) hvC_word)
    (cCont := 500 * (L + 1) + 240) (bound := 500 * (L + 1) + 400) (by omega) ?_
  intro v₁ v₂ htv_eq st ω ⟨hm1, r0_1, r1_1, r2_1, r3_1, r5_1, r6_1⟩
  have hv₁_cap : v₁ < vCap := htouch_cap v₁ (by rw [htv_eq]; simp)
  have hv₂_cap : v₂ < vCap := htouch_cap v₂ (by rw [htv_eq]; simp)
  refine dsUpdateS_computeSBases_cont hw16 hfix (by omega) hmL hmV hmE hm1 r0_1
    (by simpa [startState] using r3_1) (by omega) (cCont := 500 * (L + 1) + 60)
    (bound := 500 * (L + 1) + 240) (by omega) ?_
  wram_enter
  rcases hpre with ⟨hm2, r0_2, r1_2, r3_2, r5_2, r6_2, r7_2, r8_2, r9_2, r10_2, r11_2, r12_2, r13_2⟩
  set gen0 := mem (b + dsGenOff)
  have hj_lt_word : j < 2 ^ w := by omega
  have hbody1 := dsUpdateS_loop1_body_triple (p := p) mem S_level sLists foot0 hj1 hjL
    hv₁_cap hv₂_cap hw16 hfix hh_lt hgen_pos hgen_lt hfoot0 hOrigS
  set Inv1 := fun i (st : State) =>
    st.regs 0 = b ∧ st.regs 1 = j ∧ st.regs 3 ≤ heapPtr + 4 * i ∧ heapPtr ≤ st.regs 3 ∧
    st.regs 5 = v₁ ∧ st.regs 6 = v₂ ∧ st.regs 7 = vCap ∧ st.regs 8 = eCap ∧ st.regs 9 = L ∧
    gen0 ≤ st.regs 10 ∧ st.regs 10 ≤ gen0 + i ∧ 1 ≤ st.regs 10 ∧
    st.mem (b + dsGenOff) = st.regs 10 ∧
    st.regs 11 = dsSGenBase b L vCap eCap ∧ st.regs 12 = dsVSGenBase b L vCap eCap ∧
    st.regs 13 = dsSHeadBase b L vCap eCap ∧ st.regs 14 = i ∧
    (∀ k : Fin (L + 1), k.1 < i →
      0 < st.mem (dsSGenBase b L vCap eCap + k.1) ∧
      st.mem (dsSGenBase b L vCap eCap + k.1) ≤ st.regs 10 ∧
      (∀ v < vCap, st.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) ≤ st.regs 10 ∧
        ((0 < st.mem (dsSGenBase b L vCap eCap + k.1) ∧
          st.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) =
            st.mem (dsSGenBase b L vCap eCap + k.1)) ↔ v ∈ S_level k ∪ {v₁, v₂})) ∧
      ∃ xs', xs'.Nodup ∧ (∀ v, v ∈ xs' ↔ v ∈ S_level k ∪ {v₁, v₂}) ∧
        LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < st.regs 3)) st.mem
          (st.mem (dsSHeadBase b L vCap eCap + k.1)) xs') ∧
    (∀ addr,
      addr ≠ b + dsGenOff →
      (∀ k < i, addr ≠ dsSGenBase b L vCap eCap + k) →
      (∀ k < i, ∀ v < vCap, addr ≠ dsVSGenBase b L vCap eCap + k * vCap + v) →
      (∀ k < i, addr ≠ dsSHeadBase b L vCap eCap + k) →
      (addr < heapPtr ∨ st.regs 3 ≤ addr) →
      st.mem addr = mem addr)
  have hloop1 := Triple.forRange_const 350 0 j (Nat.zero_le j) (by omega)
    (fun _ => hj_lt_word) (Inv := Inv1)
    (fun st' (hst' : st' = st) => ⟨Expr.eval_const (by omega), by
      subst hst'
      refine ⟨r0_2, r1_2.trans (by simpa [startState] using r1_1), by simp [Function.update, r3_2],
        by simp [Function.update, r3_2], r5_2.trans r5_1, r6_2.trans r6_1, r7_2, r8_2, r9_2,
        by simp [Function.update, r10_2, gen0], by simp [Function.update, r10_2, gen0],
        by simp [Function.update, r10_2, gen0, hgen_pos],
        by simp [Function.update, hm2, r10_2, gen0], r11_2, r12_2, r13_2,
        by simp [Function.update], fun _ hk => by omega, fun _ _ _ _ _ _ => hm2 ▸ rfl⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => by have := h.2.1; eval_expr)
    (fun i _ hij => hbody1 i hij)
  refine runs_seq_triple_le hloop1 rfl ?_
  intro st3 ⟨_, r1_3, ret_le, hh_ret, _, _, _, _, r9_3, hgen3_ge, hgen3_le, hgen3_pos,
    hm_gen3, r11_3, _, _, _, hDone3, hFr3⟩
  set ret := st3.regs 3
  set endGen := st3.regs 10
  have hret_lt : ret < 2 ^ w := by omega
  have hsg_lt' : dsSGenBase b L vCap eCap + L < 2 ^ w := by
    have := (dsSAddrs_disjoint (le_refl L) hv₁_cap hjL hv₁_cap hfix).sg_lt_hp; omega
  refine runs_seq_triple_le (dsUpdateS_loop2_triple st3.mem hjL hw16 hL_word hsg_lt')
    ⟨rfl, r1_3, r9_3, r11_3, rfl, rfl⟩ ?_
  intro st4 ⟨r9_4, r11_4, r14_4, r3_4, r10_4, hzeros4, hfr4⟩
  wram_run
  · have hbg_ne : ∀ k, j ≤ k → k < L + 1 → b + dsGenOff ≠ dsSGenBase b L vCap eCap + k := fun k _ hk =>
      (dsSAddrs_disjoint (by omega) hv₁_cap hjL hv₁_cap hfix).sg_ne_gen.symm
    have hgen_4 : st4.mem (b + dsGenOff) = endGen := (hfr4 _ hbg_ne).trans hm_gen3
    have hfoot_fr4 : ∀ a, (foot0 a ∨ (heapPtr ≤ a ∧ a < ret)) → st4.mem a = st3.mem a := fun a ha => by
      have ha_fix : b + dsFixedSize L vCap eCap ≤ a := by
        rcases ha with ha | ⟨h1, _⟩
        · exact (hfoot0 a ha).1
        · exact le_trans hfix h1
      refine hfr4 a fun k' _ hk' => ?_
      have := (dsSAddrs_disjoint (by omega : k' ≤ L) hv₁_cap hjL hv₁_cap hfix).sg_lt_fix
      omega
    let sLists' : Fin (L + 1) → List ℕ := fun k =>
      if hk : k.1 < j then Classical.choose (hDone3 k hk).2.2.2 else []
    dsimp only [Outcome.value]
    refine ⟨updPtr, heapPtr, rfl, hh_ret, ret_le,
      hgen_4 ▸ hgen3_ge, hgen_4 ▸ hgen3_le,
      hgen_4 ▸ hgen3_pos, ⟨sLists', fun k => ?_⟩, fun addr hfr => ?_⟩
    · by_cases hkj : k.1 < j
      · have hDk := hDone3 k hkj
        have hspec := Classical.choose_spec hDk.2.2.2
        have hsk : sLists' k = Classical.choose hDk.2.2.2 := by simp [sLists', hkj]
        have hsg4 : st4.mem (dsSGenBase b L vCap eCap + k.1) = st3.mem (dsSGenBase b L vCap eCap + k.1) :=
          hfr4 _ fun _ hi' _ => by omega
        have hsh4 : st4.mem (dsSHeadBase b L vCap eCap + k.1) = st3.mem (dsSHeadBase b L vCap eCap + k.1) :=
          hfr4 _ fun i' _ hi' =>
            (dsSAddrs_disjoint (by omega : i' ≤ L) hv₁_cap (Nat.le_of_lt_succ k.2) hv₁_cap hfix).sg_ne_sh.symm
        have hS_eq : S_level k ∪ touchedVertices G u = S_level k ∪ {v₁, v₂} := by rw [htv_eq]
        simp only [hkj, ↓reduceIte, hS_eq]
        refine ⟨hgen_4 ▸ hsg4 ▸ hDk.2.1, fun h => by omega,
          fun v hv => by
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with hv | rfl | rfl <;> [exact (hOrigS k).2.1 v hv; exact hv₁_cap; exact hv₂_cap],
          fun v hv => ?_, hsk ▸ hspec.1, fun v => by rw [hsk]; exact hspec.2.1 v, ?_⟩
        · have hvs4 : st4.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) =
              st3.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) :=
            hfr4 _ fun i' _ hi' =>
              (dsSAddrs_disjoint (by omega : i' ≤ L) hv₁_cap (Nat.le_of_lt_succ k.2) hv hfix).sg_ne_vs.symm
          rw [hvs4, hgen_4, hsg4]; exact hDk.2.2.1 v hv
        · simp only [show 0 < st4.mem (dsSGenBase b L vCap eCap + k.1) from hsg4 ▸ hDk.1,
            ↓reduceIte, hsh4, hsk]
          exact linkedListIn_mono (fun _ h => h) hfoot_fr4 hspec.2.2
      · have hk_ge : j ≤ k.1 := Nat.le_of_not_lt hkj
        have hsk : sLists' k = [] := by simp [sLists', hkj]
        have hsg4 : st4.mem (dsSGenBase b L vCap eCap + k.1) = 0 := hzeros4 k.1 hk_ge k.2
        simp only [hkj, ↓reduceIte]
        refine ⟨hsg4 ▸ Nat.zero_le _, fun _ => hsg4, fun _ h => by simp at h, fun v hv => ?_,
          by simp [hsk], by simp [hsk], by simp [hsg4, hsk]⟩
        have hvd := dsSAddrs_disjoint (Nat.le_of_lt_succ k.2) hv hjL hv₁_cap hfix
        have hvs4 : st4.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) =
            st3.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) :=
          hfr4 _ fun i' _ hi' =>
            (dsSAddrs_disjoint (by omega : i' ≤ L) hv₁_cap (Nat.le_of_lt_succ k.2) hv hfix).sg_ne_vs.symm
        have hvs3 : st3.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) =
            mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) :=
          hFr3 _ hvd.vs_ne_gen
            (fun i' _ => (dsSAddrs_disjoint (by omega : i' ≤ L) hv₁_cap (Nat.le_of_lt_succ k.2) hv hfix).sg_ne_vs.symm)
            (fun i' hi' v' hv' heq => by
              have : i' * vCap + v' < (i' + 1) * vCap := by rw [Nat.succ_mul]; omega
              have : (i' + 1) * vCap ≤ k.1 * vCap := Nat.mul_le_mul_right vCap (by omega)
              omega)
            (fun i' _ => (dsSAddrs_disjoint (by omega : i' ≤ L) hv₁_cap (Nat.le_of_lt_succ k.2) hv hfix).sh_ne_vs.symm)
            (Or.inl hvd.vs_lt_hp)
        refine ⟨by rw [hvs4, hvs3, hgen_4]; exact le_trans ((hOrigS k).2.2.1 v hv).1 hgen3_ge, ?_⟩
        simp [hsg4]
    · rcases hfr with ⟨h1, h2, h3, h4, h5⟩
      refine (hfr4 addr fun i' _ hi' => h2 i' (by omega)).trans ?_
      exact hFr3 addr h1 (fun i' hi' => h2 i' (by omega)) (fun i' hi' => h3 i' (by omega))
        (fun i' hi' => h4 i' (by omega)) (by simpa [r3_4] using h5)
  · wram_cost

end

end MinCostFlow.DynSpanner.Program
