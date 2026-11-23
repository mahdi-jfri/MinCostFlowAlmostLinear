module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedUpdateSHelpers

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerRevHelpers
public import MinCostFlow.DynSpanner.Program.StateLayout
public import WordRAM.Tactic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Part 2 of `DynSpannerAffectedUpdateS`

See `DynSpannerAffectedUpdateS.lean` for the overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section
lemma dsUpdateS_loop1_body_triple {w L vCap eCap b j v₁ v₂ heapPtr gen0 : ℕ}
    {p : Program} (mem0 : ℕ → ℕ)
    (S_level : Fin (L + 1) → Finset ℕ) (sLists : Fin (L + 1) → List ℕ) (foot0 : ℕ → Prop)
    (hj : 1 ≤ j) (hjL : j ≤ L) (hv₁ : v₁ < vCap) (hv₂ : v₂ < vCap) (hw16 : 16 ≤ 2 ^ w)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hh_lt : heapPtr + 4 * j < 2 ^ w)
    (_hgen0_pos : 1 ≤ gen0) (hgen0_lt : gen0 + j < 2 ^ w)
    (hfoot0 : ∀ a, foot0 a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr)
    (hOrigS : ∀ k : Fin (L + 1),
      mem0 (dsSGenBase b L vCap eCap + k.1) ≤ gen0 ∧
      (∀ v ∈ S_level k, v < vCap) ∧
      (∀ v < vCap, mem0 (dsVSGenBase b L vCap eCap + k.1 * vCap + v) ≤ gen0 ∧
        ((0 < mem0 (dsSGenBase b L vCap eCap + k.1) ∧
          mem0 (dsVSGenBase b L vCap eCap + k.1 * vCap + v) =
            mem0 (dsSGenBase b L vCap eCap + k.1)) ↔ v ∈ S_level k)) ∧
      (sLists k).Nodup ∧ (∀ v, v ∈ sLists k ↔ v ∈ S_level k) ∧
      (if 0 < mem0 (dsSGenBase b L vCap eCap + k.1)
       then LinkedListIn foot0 mem0 (mem0 (dsSHeadBase b L vCap eCap + k.1)) (sLists k)
       else sLists k = [])) :
    let body :=
      (.assign 15 (.load (.bin .add (.reg 11) (.reg 14))) ;;
       .cond (.reg 15) .nop
         (.assign 10 (.bin .add (.reg 10) (.const 1)) ;;
          .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 10) ;;
          .store (.bin .add (.reg 11) (.reg 14)) (.reg 10) ;;
          .store (.bin .add (.reg 13) (.reg 14)) (.const 0) ;;
          .assign 15 (.reg 10)) ;;
       .assign 16 (.bin .add (.reg 12) (.bin .mul (.reg 14) (.reg 7))) ;;
       dsInsertSLevelVertexStmt (.reg 5) ;;
       dsInsertSLevelVertexStmt (.reg 6))
    let Inv : ℕ → State → Prop := fun i st =>
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
        st.mem addr = mem0 addr)
    ∀ i, i < j →
      Triple w p (Inv i) body
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 14 (i + 1) } ∧ st₁.regs 14 = i)
        (fun _ => 350) := by
  intro body Inv i hij
  wram_enter
  rcases hpre with ⟨r0, r1, r3_le, hh_r3, r5, r6, r7, r8, r9, hgen_ge, hgen_le, hgen_pos, hm_gen,
    r11, r12, r13, r14, hDone, hFr⟩
  have hiL : i ≤ L := by omega
  have hi_fin : i < L + 1 := Nat.lt_succ_of_le hiL
  have hdisj := dsSAddrs_disjoint hiL hv₁ hiL hv₂ hfix
  have hOrig_i := hOrigS ⟨i, hi_fin⟩
  set sgi0 := mem0 (dsSGenBase b L vCap eCap + i)
  have hsgi0_lt : sgi0 < 2 ^ w := by have := hOrig_i.1; omega
  have hm_sg : st.mem (dsSGenBase b L vCap eCap + i) = sgi0 :=
    hFr _ hdisj.sg_ne_gen (fun _ hk => by omega)
      (fun k _ v hv => (dsSAddrs_disjoint hiL hv₁ (by omega) hv hfix).sg_ne_vs)
      (fun k _ => (dsSAddrs_disjoint hiL hv₁ (by omega) hv₂ hfix).sg_ne_sh) (Or.inl hdisj.sg_lt_hp)
  have hm_sh : st.mem (dsSHeadBase b L vCap eCap + i) = mem0 (dsSHeadBase b L vCap eCap + i) :=
    hFr _ hdisj.sh_ne_gen
      (fun k _ => (dsSAddrs_disjoint (by omega) hv₁ hiL hv₂ hfix).sg_ne_sh.symm)
      (fun k _ v hv => (dsSAddrs_disjoint hiL hv₂ (by omega) hv hfix).sh_ne_vs)
      (fun _ hk => by omega) (Or.inl hdisj.sh_lt_hp)
  have hm_vs : ∀ z < vCap, st.mem (dsVSGenBase b L vCap eCap + i * vCap + z) =
      mem0 (dsVSGenBase b L vCap eCap + i * vCap + z) := fun z hz => by
    have hz_d := dsSAddrs_disjoint hiL hz hiL hv₁ hfix
    refine hFr _ hz_d.vs_ne_gen
      (fun k _ => (dsSAddrs_disjoint (by omega) hv₁ hiL hz hfix).sg_ne_vs.symm) ?_
      (fun k _ => (dsSAddrs_disjoint (by omega) hv₁ hiL hz hfix).sh_ne_vs.symm) (Or.inl hz_d.vs_lt_hp)
    intro k hk v' hv' heq
    have : k * vCap + v' < (k + 1) * vCap := by rw [Nat.succ_mul]; omega
    have : (k + 1) * vCap ≤ i * vCap := Nat.mul_le_mul_right vCap hk
    omega
  have hS_empty_of_0 : sgi0 = 0 → S_level ⟨i, hi_fin⟩ = ∅ := fun h0 => by
    ext v; simp only [Finset.notMem_empty, iff_false]
    intro hvS
    have := ((hOrig_i.2.2.1 v (hOrig_i.2.1 v hvS)).2).mpr hvS
    omega
  obtain ⟨_, _, _, _, hr11_lt, hr12_lt, hr13_lt, _, _, _, _, _, _, _, _, _, _, hLv_w, _, _⟩ :=
    dsSCompute_bounds hfix (by omega : heapPtr < 2 ^ w)
  have hmul_le : i * vCap + v₁ < (L + 1) * vCap := mul_add_lt_mul_succ hiL hv₁
  have hvs0_lt : i * vCap < 2 ^ w := by omega
  have hi_lt : i < 2 ^ w := by omega
  have hvC_lt : vCap < 2 ^ w := by omega
  have hsg_lt : dsSGenBase b L vCap eCap + i < 2 ^ w := by linarith only [hdisj.sg_lt_hp, hh_lt]
  have hsh_lt : dsSHeadBase b L vCap eCap + i < 2 ^ w := by linarith only [hdisj.sh_lt_hp, hh_lt]
  have hbg_lt : b + dsGenOff < 2 ^ w := by linarith only [hdisj.gen_lt_hp, hh_lt]
  have hvs_base_lt : dsVSGenBase b L vCap eCap + i * vCap < 2 ^ w := by
    linarith only [hdisj.vs_lt_hp, hh_lt]
  have hds_gen_n : st.regs 10 + 1 < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have hdg_lt : dsGenOff < dsHdrSize := by decide
  have hdg_w : dsGenOff < 2 ^ w := by simp [dsHdrSize] at hdg_lt; omega
  have hb_lt : b < 2 ^ w := by omega
  have hr14_r7_w : st.regs 14 * st.regs 7 < 2 ^ w := by rw [r14, r7]; exact hvs0_lt
  have hr12_mul_w : st.regs 12 + st.regs 14 * st.regs 7 < 2 ^ w := by
    rw [r12, r14, r7]; exact hvs_base_lt
  have hr11_i_w : st.regs 11 + st.regs 14 < 2 ^ w := by rw [r11, r14]; exact hsg_lt
  have hr13_i_w : st.regs 13 + st.regs 14 < 2 ^ w := by rw [r13, r14]; exact hsh_lt
  have hr0_gen_w : st.regs 0 + dsGenOff < 2 ^ w := by rw [r0]; exact hbg_lt
  have hstep1 : Triple w p
      (fun stA : State =>
        stA.regs 0 = b ∧ stA.regs 1 = j ∧ stA.regs 3 = st.regs 3 ∧
        stA.regs 5 = v₁ ∧ stA.regs 6 = v₂ ∧ stA.regs 7 = vCap ∧
        stA.regs 8 = eCap ∧ stA.regs 9 = L ∧
        gen0 ≤ stA.regs 10 ∧ stA.regs 10 ≤ gen0 + (i + 1) ∧ 1 ≤ stA.regs 10 ∧
        st.regs 10 ≤ stA.regs 10 ∧
        stA.mem (b + dsGenOff) = stA.regs 10 ∧
        stA.regs 11 = dsSGenBase b L vCap eCap ∧ stA.regs 12 = dsVSGenBase b L vCap eCap ∧
        stA.regs 13 = dsSHeadBase b L vCap eCap ∧ stA.regs 14 = i ∧
        stA.regs 15 = stA.mem (dsSGenBase b L vCap eCap + i) ∧
        0 < stA.mem (dsSGenBase b L vCap eCap + i) ∧
        stA.mem (dsSGenBase b L vCap eCap + i) ≤ stA.regs 10 ∧
        stA.regs 16 = dsVSGenBase b L vCap eCap + i * vCap ∧
        (∀ v < vCap, stA.mem (dsVSGenBase b L vCap eCap + i * vCap + v) ≤ stA.regs 10 ∧
          ((0 < stA.mem (dsSGenBase b L vCap eCap + i) ∧
            stA.mem (dsVSGenBase b L vCap eCap + i * vCap + v) =
              stA.mem (dsSGenBase b L vCap eCap + i)) ↔ v ∈ S_level ⟨i, hi_fin⟩)) ∧
        LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < st.regs 3)) stA.mem
          (stA.mem (dsSHeadBase b L vCap eCap + i)) (sLists ⟨i, hi_fin⟩) ∧
        (∀ addr, addr ≠ b + dsGenOff → addr ≠ dsSGenBase b L vCap eCap + i →
          addr ≠ dsSHeadBase b L vCap eCap + i → stA.mem addr = st.mem addr))
      (dsInsertSLevelVertexStmt (.reg 5) ;; dsInsertSLevelVertexStmt (.reg 6))
      (normalPost fun st' =>
        Inv (i + 1) { st' with regs := Function.update st'.regs 14 (i + 1) } ∧ st'.regs 14 = i)
      (fun _ => 225) := by
    intro stA ωA ⟨r0A, r1A, r3A, r5A, r6A, r7A, r8A, r9A, hgA_ge, hgA_le, hgA_pos, hgenA_inc, hmA_gen,
      r11A, r12A, r13A, r14A, r15A, hsgA_pos, hsgA_le, r16A, hvsA, hllA, hmemA_fr⟩
    refine runs_start_le ?_
    refine runs_seq_triple_le (dsInsertSLevelVertex_triple stA.regs stA.mem
      (S_level ⟨i, hi_fin⟩) (sLists ⟨i, hi_fin⟩) foot0 (Or.inl rfl) hiL hv₁ hw16 hfix
      (r3A ▸ hh_r3) (by omega) hsgA_pos hsgA_le (by omega) hfoot0)
      ⟨rfl, rfl, r0A, r11A, r12A, r13A, r14A, r3A, r15A, r16A, r5A, hOrig_i.2.1, hvsA,
        hOrig_i.2.2.2.1, hOrig_i.2.2.2.2.1, r3A ▸ hllA⟩ ?_
    intro stB ⟨r3B_ge, r3B_le, hregB, hmB_gen, hmB_sg, hSB_cap, hvsB,
      ⟨xsB, hxsB_nd, hxsB_mem, hllB⟩, hmemB_fr⟩
    refine runs_triple_le (dsInsertSLevelVertex_triple stB.regs stB.mem
      (S_level ⟨i, hi_fin⟩ ∪ {v₁}) xsB foot0 (Or.inr rfl) hiL hv₂ hw16 hfix
      (le_trans hh_r3 (r3A ▸ r3B_ge)) (by omega) (hmB_sg ▸ hsgA_pos)
      (hmB_sg ▸ hsgA_le) (by omega) hfoot0)
      ⟨rfl, rfl, (hregB 0 (by decide) (by decide)).trans r0A,
        (hregB 11 (by decide) (by decide)).trans r11A,
        (hregB 12 (by decide) (by decide)).trans r12A,
        (hregB 13 (by decide) (by decide)).trans r13A,
        (hregB 14 (by decide) (by decide)).trans r14A, rfl,
        ((hregB 15 (by decide) (by decide)).trans r15A).trans hmB_sg.symm,
        (hregB 16 (by decide) (by decide)).trans r16A,
        (hregB 6 (by decide) (by decide)).trans r6A,
        hSB_cap, fun z hz => by simpa [hmB_sg] using hvsB z hz,
        hxsB_nd, hxsB_mem, hllB⟩ ?_ (by dsimp only; omega)
    rintro oC stC hC
    cases oC with
    | returned => exact False.elim hC
    | normal =>
      rcases hC with ⟨r3C_ge, r3C_le, hregC, hmC_gen, hmC_sg, _, hvsC,
        ⟨xsC, hxsC_nd, hxsC_mem, hllC⟩, hmemC_fr⟩
      have hS_union : (S_level ⟨i, hi_fin⟩ ∪ {v₁}) ∪ {v₂} = S_level ⟨i, hi_fin⟩ ∪ {v₁, v₂} := by
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]
      have hr10C : stC.regs 10 = stA.regs 10 :=
        (hregC 10 (by decide) (by decide)).trans ((hregB 10 (by decide) (by decide)))
      have hr14C : stC.regs 14 = i :=
        (hregC 14 (by decide) (by decide)).trans ((hregB 14 (by decide) (by decide)).trans r14A)
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hr14C⟩
      · simp [Function.update, hregC 0 (by decide) (by decide), hregB 0 (by decide) (by decide), r0A]
      · simp [Function.update, hregC 1 (by decide) (by decide), hregB 1 (by decide) (by decide), r1A]
      · simp [Function.update]; omega
      · simp [Function.update]; omega
      · simp [Function.update, hregC 5 (by decide) (by decide), hregB 5 (by decide) (by decide), r5A]
      · simp [Function.update, hregC 6 (by decide) (by decide), hregB 6 (by decide) (by decide), r6A]
      · simp [Function.update, hregC 7 (by decide) (by decide), hregB 7 (by decide) (by decide), r7A]
      · simp [Function.update, hregC 8 (by decide) (by decide), hregB 8 (by decide) (by decide), r8A]
      · simp [Function.update, hregC 9 (by decide) (by decide), hregB 9 (by decide) (by decide), r9A]
      · simp [Function.update, hr10C, hgA_ge]
      · simp [Function.update, hr10C, hgA_le]
      · simp [Function.update, hr10C, hgA_pos]
      · simp [Function.update, hr10C, hmC_gen, hmB_gen, hmA_gen]
      · simp [Function.update, hregC 11 (by decide) (by decide), hregB 11 (by decide) (by decide), r11A]
      · simp [Function.update, hregC 12 (by decide) (by decide), hregB 12 (by decide) (by decide), r12A]
      · simp [Function.update, hregC 13 (by decide) (by decide), hregB 13 (by decide) (by decide), r13A]
      · simp [Function.update]
      · intro k hk
        by_cases hki : k.1 = i
        · have hk_eq : k = ⟨i, hi_fin⟩ := Fin.ext hki
          subst hk_eq
          refine ⟨by rw [hmC_sg, hmB_sg]; exact hsgA_pos,
            by simp only [Function.update]; rw [hr10C, hmC_sg, hmB_sg]; exact hsgA_le,
            fun v hv => ?_, xsC, hxsC_nd, fun v => by rw [hxsC_mem v, hS_union], by simpa [Function.update] using hllC⟩
          simp only [Function.update, hr10C]
          have := hvsC v hv
          rw [hmC_sg, hmB_sg, hS_union] at this
          simpa [hmC_sg, hmB_sg] using this
        · have hki_lt : k.1 < i := by omega
          obtain ⟨h1, h2, h3, xs_k, hxk1, hxk2, hxk3⟩ := hDone k hki_lt
          have hk_d := dsSAddrs_disjoint (Nat.le_of_lt_succ k.2) hv₁ hiL hv₂ hfix
          have hk_d1 := dsSAddrs_disjoint (Nat.le_of_lt_succ k.2) hv₁ hiL hv₁ hfix
          have hk_d' := dsSAddrs_disjoint hiL hv₁ (Nat.le_of_lt_succ k.2) hv₂ hfix
          have h_sg_C : stC.mem (dsSGenBase b L vCap eCap + k.1) = st.mem (dsSGenBase b L vCap eCap + k.1) :=
            (hmemC_fr _ hk_d.sg_ne_vs hk_d.sg_ne_sh
              (Or.inl (lt_of_lt_of_le hk_d.sg_lt_hp (le_trans hh_r3 r3B_ge)))).trans
              ((hmemB_fr _ hk_d1.sg_ne_vs hk_d.sg_ne_sh
                (Or.inl (lt_of_lt_of_le hk_d.sg_lt_hp (r3A ▸ hh_r3)))).trans
                (hmemA_fr _ hk_d.sg_ne_gen (by intro h; apply hki; omega) hk_d.sg_ne_sh))
          have h_sh_C : stC.mem (dsSHeadBase b L vCap eCap + k.1) = st.mem (dsSHeadBase b L vCap eCap + k.1) :=
            (hmemC_fr _ hk_d.sh_ne_vs (by intro h; apply hki; omega)
              (Or.inl (lt_of_lt_of_le hk_d.sh_lt_hp (le_trans hh_r3 r3B_ge)))).trans
              ((hmemB_fr _ hk_d1.sh_ne_vs (by intro h; apply hki; omega)
                (Or.inl (lt_of_lt_of_le hk_d.sh_lt_hp (r3A ▸ hh_r3)))).trans
                (hmemA_fr _ hk_d.sh_ne_gen hk_d'.sg_ne_sh.symm (by intro h; apply hki; omega)))
          have h_vs_C : ∀ v < vCap, stC.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) =
              st.mem (dsVSGenBase b L vCap eCap + k.1 * vCap + v) := fun v hv => by
            have hvd := dsSAddrs_disjoint (Nat.le_of_lt_succ k.2) hv hiL hv₂ hfix
            have hvd1 := dsSAddrs_disjoint (Nat.le_of_lt_succ k.2) hv hiL hv₁ hfix
            have hvd_ik := dsSAddrs_disjoint hiL hv₂ (Nat.le_of_lt_succ k.2) hv hfix
            have hvd_ik1 := dsSAddrs_disjoint hiL hv₁ (Nat.le_of_lt_succ k.2) hv hfix
            have : k.1 * vCap + v < (k.1 + 1) * vCap := by rw [Nat.succ_mul]; omega
            have : (k.1 + 1) * vCap ≤ i * vCap := Nat.mul_le_mul_right vCap hki_lt
            refine (hmemC_fr _ (by omega) hvd_ik.sh_ne_vs.symm
              (Or.inl (lt_of_lt_of_le hvd.vs_lt_hp (le_trans hh_r3 r3B_ge)))).trans ?_
            refine (hmemB_fr _ (by omega) hvd_ik1.sh_ne_vs.symm
              (Or.inl (lt_of_lt_of_le hvd.vs_lt_hp (r3A ▸ hh_r3)))).trans ?_
            exact hmemA_fr _ hvd.vs_ne_gen hvd_ik1.sg_ne_vs.symm hvd_ik1.sh_ne_vs.symm
          have hten_le : st.regs 10 ≤ stA.regs 10 := hgenA_inc
          have hr10_ne14 : (10 : ℕ) ≠ 14 := by decide
          refine ⟨h_sg_C.symm ▸ h1, by simp only [Function.update_of_ne hr10_ne14]; rw [hr10C, h_sg_C]; omega,
            fun v hv => ?_, xs_k, hxk1, hxk2, ?_⟩
          · simp only [Function.update_of_ne hr10_ne14]; rw [hr10C, h_vs_C v hv, h_sg_C]
            exact ⟨le_trans (h3 v hv).1 hten_le, (h3 v hv).2⟩
          · simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 14)]; rw [h_sh_C]
            refine linkedListIn_mono
              (fun a ha => ha.imp id fun ⟨ha1, ha2⟩ => ⟨ha1, by omega⟩)
              (fun a ha => ?_) hxk3
            have ha_fix : b + dsFixedSize L vCap eCap ≤ a ∧ a < st.regs 3 := by
              rcases ha with ha | ⟨ha1, ha2⟩
              · exact ⟨(hfoot0 a ha).1, lt_of_lt_of_le (hfoot0 a ha).2 hh_r3⟩
              · exact ⟨le_trans hfix ha1, ha2⟩
            have hdisj1 := dsSAddrs_disjoint hiL hv₁ hiL hv₁ hfix
            have hdisj2 := dsSAddrs_disjoint hiL hv₂ hiL hv₂ hfix
            refine (hmemC_fr a (by linarith only [hdisj2.vs_lt_fix, ha_fix.1])
              (by linarith only [hdisj2.sh_lt_fix, ha_fix.1]) (Or.inl (lt_of_lt_of_le ha_fix.2 r3B_ge))).trans ?_
            refine (hmemB_fr a (by linarith only [hdisj1.vs_lt_fix, ha_fix.1])
              (by linarith only [hdisj.sh_lt_fix, ha_fix.1]) (Or.inl (r3A ▸ ha_fix.2))).trans ?_
            exact hmemA_fr a (by linarith only [hdisj.gen_lt_fix, ha_fix.1])
              (by linarith only [hdisj.sg_lt_fix, ha_fix.1]) (by linarith only [hdisj.sh_lt_fix, ha_fix.1])
      · intro addr hgen hk1 hk2 hk3 hheap
        have hlt_B : addr < stB.regs 3 ∨ stC.regs 3 ≤ addr := by
          rcases hheap with h | h <;> [exact Or.inl (lt_of_lt_of_le h (le_trans hh_r3 r3B_ge)); exact Or.inr h]
        have hlt_A : addr < st.regs 3 ∨ stB.regs 3 ≤ addr := by
          rcases hheap with h | h <;> [exact Or.inl (lt_of_lt_of_le h hh_r3); exact Or.inr (le_trans r3C_ge h)]
        refine (hmemC_fr addr (hk2 i (Nat.lt_succ_self i) v₂ hv₂) (hk3 i (Nat.lt_succ_self i)) hlt_B).trans ?_
        refine (hmemB_fr addr (hk2 i (Nat.lt_succ_self i) v₁ hv₁) (hk3 i (Nat.lt_succ_self i)) (r3A ▸ hlt_A)).trans ?_
        refine (hmemA_fr addr hgen (hk1 i (Nat.lt_succ_self i)) (hk3 i (Nat.lt_succ_self i))).trans ?_
        exact hFr addr hgen (fun k hk => hk1 k (Nat.lt_succ_of_lt hk))
          (fun k hk => hk2 k (Nat.lt_succ_of_lt hk)) (fun k hk => hk3 k (Nat.lt_succ_of_lt hk))
          (hheap.imp id fun h => le_trans (le_trans (r3A ▸ r3B_ge) r3C_ge) h)
  dsimp only [body]
  wram_run
  · -- `sgi0 ≠ 0`
    have hsgi0_pos : 0 < sgi0 := Nat.pos_of_ne_zero (by simpa [hm_sg] using hcond)
    have hll_i : LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < st.regs 3)) st.mem
        (st.mem (dsSHeadBase b L vCap eCap + i)) (sLists ⟨i, hi_fin⟩) := by
      have h0 := hOrig_i.2.2.2.2.2
      dsimp only at h0
      simp only [show 0 < sgi0 from hsgi0_pos, ↓reduceIte] at h0
      rw [hm_sh]
      exact linkedListIn_mono (fun a ha => Or.inl ha) (fun a ha =>
        hFr a (by linarith only [(hfoot0 a ha).1, hdisj.gen_lt_fix])
          (fun k hk => by
            have := (dsSAddrs_disjoint (by omega : k ≤ L) hv₁ hiL hv₂ hfix).sg_lt_fix
            linarith only [(hfoot0 a ha).1, this])
          (fun k hk v hv => by
            have := (dsSAddrs_disjoint (by omega : k ≤ L) hv hiL hv₂ hfix).vs_lt_fix
            linarith only [(hfoot0 a ha).1, this])
          (fun k hk => by
            have hk1 := (dsSAddrs_disjoint (by omega : k ≤ L) hv₁ hiL hv₂ hfix).sh_lt_fix
            linarith only [(hfoot0 a ha).1, hk1])
          (Or.inl (hfoot0 a ha).2)) h0
    refine runs_triple_le hstep1 ?_ (fun _ _ h => h) (by wram_cost)
    refine ⟨by simp [Function.update, r0], by simp [Function.update, r1],
      by simp [Function.update], by simp [Function.update, r5], by simp [Function.update, r6],
      by simp [Function.update, r7], by simp [Function.update, r8], by simp [Function.update, r9],
      by simp [Function.update]; omega, by simp [Function.update]; omega,
      by simp [Function.update]; omega, by simp [Function.update],
      by simp [Function.update, hm_gen], by simp [Function.update, r11],
      by simp [Function.update, r12], by simp [Function.update, r13],
      by simp [Function.update, r14], by simp [Function.update, hm_sg, sgi0],
      by simp [hm_sg, sgi0, hsgi0_pos],
      by simp [Function.update, hm_sg, sgi0]; have := hOrig_i.1; omega,
      by simp [Function.update, r12, r14, r7], fun v hv => ?_, hll_i, fun _ _ _ _ => rfl⟩
    simp only [Function.update]
    rw [hm_vs v hv, hm_sg]
    exact ⟨le_trans (hOrig_i.2.2.1 v hv).1 hgen_ge, by simpa [sgi0] using (hOrig_i.2.2.1 v hv).2⟩
  · -- `sgi0 = 0`
    have hs0 : sgi0 = 0 := by simpa [hm_sg] using hcond
    have hS_emp : S_level ⟨i, hi_fin⟩ = ∅ := hS_empty_of_0 hs0
    have hxs_emp : sLists ⟨i, hi_fin⟩ = [] := by
      dsimp only at hOrig_i
      simpa [sgi0, hs0] using hOrig_i.2.2.2.2.2
    have hmA_gen' : Function.update (Function.update (Function.update st.mem
        (st.regs 0 + dsGenOff) (st.regs 10 + 1)) (st.regs 11 + st.regs 14) (st.regs 10 + 1))
        (st.regs 13 + st.regs 14) 0 (b + dsGenOff) = st.regs 10 + 1 := by
      rw [r0, r11, r13, r14, Function.update_of_ne hdisj.sh_ne_gen.symm,
        Function.update_of_ne hdisj.sg_ne_gen.symm, Function.update_self]
    have hmA_sg' : Function.update (Function.update (Function.update st.mem
        (st.regs 0 + dsGenOff) (st.regs 10 + 1)) (st.regs 11 + st.regs 14) (st.regs 10 + 1))
        (st.regs 13 + st.regs 14) 0 (dsSGenBase b L vCap eCap + i) = st.regs 10 + 1 := by
      rw [r0, r11, r13, r14, Function.update_of_ne hdisj.sg_ne_sh, Function.update_self]
    have hmA_sh' : Function.update (Function.update (Function.update st.mem
        (st.regs 0 + dsGenOff) (st.regs 10 + 1)) (st.regs 11 + st.regs 14) (st.regs 10 + 1))
        (st.regs 13 + st.regs 14) 0 (dsSHeadBase b L vCap eCap + i) = 0 := by
      rw [r0, r11, r13, r14, Function.update_self]
    have hmA_fr' : ∀ addr, addr ≠ b + dsGenOff → addr ≠ dsSGenBase b L vCap eCap + i →
        addr ≠ dsSHeadBase b L vCap eCap + i →
        Function.update (Function.update (Function.update st.mem
          (st.regs 0 + dsGenOff) (st.regs 10 + 1)) (st.regs 11 + st.regs 14) (st.regs 10 + 1))
          (st.regs 13 + st.regs 14) 0 addr = st.mem addr := fun addr h1 h2 h3 => by
      rw [r0, r11, r13, r14, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1]
    refine runs_triple_le hstep1 ?_ (fun _ _ h => h) (by wram_cost)
    refine ⟨by simp [Function.update, r0], by simp [Function.update, r1],
      by simp [Function.update], by simp [Function.update, r5], by simp [Function.update, r6],
      by simp [Function.update, r7], by simp [Function.update, r8], by simp [Function.update, r9],
      by simp [Function.update]; omega, by simp [Function.update]; omega,
      by simp [Function.update], by simp [Function.update],
      by simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 16),
        Function.update_of_ne (by decide : (10 : ℕ) ≠ 15), Function.update_self]; exact hmA_gen',
      by simp [Function.update, r11], by simp [Function.update, r12],
      by simp [Function.update, r13], by simp [Function.update, r14],
      by dsimp only; simp only [Function.update_of_ne (by decide : (15 : ℕ) ≠ 16),
        Function.update_self]; exact hmA_sg'.symm,
      by dsimp only; rw [hmA_sg']; omega,
      by dsimp only; rw [hmA_sg']; simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 16),
        Function.update_of_ne (by decide : (10 : ℕ) ≠ 15), Function.update_self]; exact le_refl _,
      by simp [Function.update, r12, r14, r7],
      fun v hv => ?_,
      by dsimp only; rw [hmA_sh', hxs_emp]; rfl, hmA_fr'⟩
    have hzd := dsSAddrs_disjoint hiL hv hiL hv₁ hfix
    have hzd2 := dsSAddrs_disjoint hiL hv₁ hiL hv hfix
    have hmv : Function.update (Function.update (Function.update st.mem
        (st.regs 0 + dsGenOff) (st.regs 10 + 1)) (st.regs 11 + st.regs 14) (st.regs 10 + 1))
        (st.regs 13 + st.regs 14) 0 (dsVSGenBase b L vCap eCap + i * vCap + v) =
        mem0 (dsVSGenBase b L vCap eCap + i * vCap + v) := by
      rw [hmA_fr' _ hzd.vs_ne_gen hzd2.sg_ne_vs.symm hzd2.sh_ne_vs.symm, hm_vs v hv]
    have hle0 : mem0 (dsVSGenBase b L vCap eCap + i * vCap + v) ≤ st.regs 10 :=
      le_trans (hOrig_i.2.2.1 v hv).1 hgen_ge
    dsimp only
    rw [hmv, hmA_sg']
    simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 16),
      Function.update_of_ne (by decide : (10 : ℕ) ≠ 15), Function.update_self, hS_emp]
    refine ⟨by omega, ?_⟩
    simp only [Finset.notMem_empty, iff_false, not_and]
    intro _; omega

lemma dsUpdateS_loop2_triple {w L vCap eCap b j retHeap endGen : ℕ}
    {p : Program} (mem1 : ℕ → ℕ)
    (hjL : j ≤ L) (hw16 : 16 ≤ 2 ^ w) (hL_word : L + 1 < 2 ^ w)
    (hsg_lt : dsSGenBase b L vCap eCap + L < 2 ^ w) :
    let Inv2 : ℕ → State → Prop := fun i st =>
      st.regs 9 = L ∧ st.regs 11 = dsSGenBase b L vCap eCap ∧ st.regs 14 = i ∧
      st.regs 3 = retHeap ∧ st.regs 10 = endGen ∧
      (∀ k, j ≤ k → k < i → st.mem (dsSGenBase b L vCap eCap + k) = 0) ∧
      (∀ addr, (∀ k, j ≤ k → k < i → addr ≠ dsSGenBase b L vCap eCap + k) →
        st.mem addr = mem1 addr)
    Triple w p
      (fun st => st.mem = mem1 ∧ st.regs 1 = j ∧ st.regs 9 = L ∧
        st.regs 11 = dsSGenBase b L vCap eCap ∧ st.regs 3 = retHeap ∧ st.regs 10 = endGen)
      (forRange 14 (.reg 1) (.bin .add (.reg 9) (.const 1))
        (.store (.bin .add (.reg 11) (.reg 14)) (.const 0)))
      (normalPost (Inv2 (L + 1)))
      (fun _ => (L + 1 - j) * 51 + 9) := by
  intro Inv2
  refine (Triple.forRange_const 40 j (L + 1) (by omega) (by omega) (fun _ => hL_word)
    (Inv := Inv2) ?_ ?_ ?_ ?_).mono_cost ?_
  · intro st ⟨hm, r1, r9, r11, r3, r10⟩
    refine ⟨by eval_expr,
      ⟨by simp [r9], by simp [r11], by simp [Function.update],
       by simp [Function.update, r3], by simp [Function.update, r10],
       fun _ h1 h2 => by omega, fun _ _ => hm ▸ rfl⟩⟩
  · intro _ _ _ _ hInv; exact hInv.2.2.1
  · intro i st _ _ hInv; have hL : L < 2 ^ w := by omega
    have h1 : st.regs 9 = L := hInv.1; eval_expr
  · intro i hi0 hiL
    wram_enter
    rcases hpre with ⟨r9, r11, r14, r3, r10, hzeros, hfr⟩
    have hi_lt : i < 2 ^ w := by omega
    have haddr_lt : dsSGenBase b L vCap eCap + i < 2 ^ w := by omega
    have hr11_lt : dsSGenBase b L vCap eCap < 2 ^ w := by omega
    wram_run
    · refine ⟨⟨by simp [r9], by simp [r11], by simp, by simp [r3], by simp [r10],
        fun k hk1 hk2 => ?_, fun addr hne => ?_⟩, r14⟩
      · by_cases hki : k = i
        · subst hki; simp [Function.update]
        · simp only [Function.update, show dsSGenBase b L vCap eCap + k ≠ dsSGenBase b L vCap eCap + i by omega]
          exact hzeros k hk1 (by omega)
      · have hne_i : addr ≠ dsSGenBase b L vCap eCap + i := hne i hi0 (Nat.lt_succ_self i)
        simp only [Function.update, hne_i]
        exact hfr addr (fun k hk1 hk2 => hne k hk1 (Nat.lt_succ_of_lt hk2))
    · wram_cost
  · intro _ _; simp [Expr.size]

end

end MinCostFlow.DynSpanner.Program
