module


public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerRevHelpers
public import MinCostFlow.DynSpanner.Program.StateLayout
public import WordRAM.Tactic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Part 1 of `DynSpannerAffectedUpdateS`

The first part of the proofs of `DynSpannerAffectedUpdateS.lean`, split off to keep files short. See `DynSpannerAffectedUpdateS.lean`
for the overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Frame condition and contract -/

/-- Predicate stating `addr` is outside all cells modified by `dsUpdateSLevelsStmt`. -/
def dsUpdateSLevelsFrameCond (L vCap eCap b heapPtr ret addr : ℕ) : Prop :=
  addr ≠ b + dsGenOff ∧
  (∀ i ≤ L, addr ≠ dsSGenBase b L vCap eCap + i) ∧
  (∀ i ≤ L, ∀ v < vCap, addr ≠ dsVSGenBase b L vCap eCap + i * vCap + v) ∧
  (∀ i ≤ L, addr ≠ dsSHeadBase b L vCap eCap + i) ∧
  (addr < heapPtr ∨ ret ≤ addr)

lemma dsUpdateSLevelsFrameCond_mono {L vCap eCap b h0 h1 h2 addr : ℕ}
    (hle : h1 ≤ h2) (hfr : dsUpdateSLevelsFrameCond L vCap eCap b h0 h2 addr) :
    dsUpdateSLevelsFrameCond L vCap eCap b h0 h1 addr := by
  rcases hfr with ⟨a1, a2, a3, a4, a5⟩
  refine ⟨a1, a2, a3, a4, ?_⟩
  rcases a5 with h | h <;> [exact Or.inl h; exact Or.inr (le_trans hle h)]

/-- Contract for `dsUpdateSLevelsStmt bOps` (`args = [b, j, updPtr, heapPtr]`). -/
def dsUpdateSLevelsContract (w L vCap eCap b j : ℕ) (G : MGraph) (u : Update) (uLen : ℕ)
    (S_level : Fin (L + 1) → Finset ℕ) (sLists : Fin (L + 1) → List ℕ)
    (foot0 : ℕ → Prop) : Contract where
  pre args mem := ∃ updPtr heapPtr,
    args = [b, j, updPtr, heapPtr] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ b ∧ 1 ≤ j ∧ j ≤ L ∧
    b + dsFixedSize L vCap eCap ≤ heapPtr ∧
    heapPtr + 4 * j < 2 ^ w ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    1 ≤ mem (b + dsGenOff) ∧ mem (b + dsGenOff) + j < 2 ^ w ∧
    DynGraphAt mem (dsGPtr b) vCap eCap G ∧ G.IsValid ∧
    (∀ v ∈ G.V, v < vCap) ∧ (∀ e ∈ G.E, e < eCap) ∧
    UpdateAt mem updPtr G u uLen ∧ G.UpdateIsValid u ∧ isDelOrSplit u ∧ updPtr + uLen < 2 ^ w ∧
    (∀ v ∈ touchedVertices G u, v < vCap) ∧
    (∀ a, foot0 a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr) ∧
    (∀ i : Fin (L + 1),
      mem (dsSGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff) ∧
      (∀ v ∈ S_level i, v < vCap) ∧
      (∀ v < vCap,
        mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
        ((0 < mem (dsSGenBase b L vCap eCap + i.1) ∧
          mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
            mem (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ S_level i)) ∧
      (sLists i).Nodup ∧
      (∀ v, v ∈ sLists i ↔ v ∈ S_level i) ∧
      (if 0 < mem (dsSGenBase b L vCap eCap + i.1)
       then LinkedListIn foot0 mem (mem (dsSHeadBase b L vCap eCap + i.1)) (sLists i)
       else sLists i = []))
  post args mem ret mem' := ∃ updPtr heapPtr,
    args = [b, j, updPtr, heapPtr] ∧
    heapPtr ≤ ret ∧ ret ≤ heapPtr + 4 * j ∧
    mem (b + dsGenOff) ≤ mem' (b + dsGenOff) ∧
    mem' (b + dsGenOff) ≤ mem (b + dsGenOff) + j ∧
    1 ≤ mem' (b + dsGenOff) ∧
    (∃ sLists' : Fin (L + 1) → List ℕ, ∀ i : Fin (L + 1),
      let S' : Finset ℕ := if i.1 < j then S_level i ∪ touchedVertices G u else ∅
      mem' (dsSGenBase b L vCap eCap + i.1) ≤ mem' (b + dsGenOff) ∧
      (j ≤ i.1 → mem' (dsSGenBase b L vCap eCap + i.1) = 0) ∧
      (∀ v ∈ S', v < vCap) ∧
      (∀ v < vCap,
        mem' (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem' (b + dsGenOff) ∧
        ((0 < mem' (dsSGenBase b L vCap eCap + i.1) ∧
          mem' (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
            mem' (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ S')) ∧
      (sLists' i).Nodup ∧
      (∀ v, v ∈ sLists' i ↔ v ∈ S') ∧
      (if 0 < mem' (dsSGenBase b L vCap eCap + i.1)
       then LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < ret)) mem'
              (mem' (dsSHeadBase b L vCap eCap + i.1)) (sLists' i)
       else sLists' i = [])) ∧
    ∀ addr, dsUpdateSLevelsFrameCond L vCap eCap b heapPtr ret addr → mem' addr = mem addr
  cost _ _ := 500 * (L + 1) + 400

/-! ## Layout and list helpers -/

lemma linkedListIn_mono {f₁ f₂ : ℕ → Prop} {mem mem' : ℕ → ℕ} {head : ℕ}
    (hf : ∀ a, f₁ a → f₂ a) (hm : ∀ a, f₁ a → mem' a = mem a) :
    ∀ {xs : List ℕ},
      LinkedListIn f₁ mem head xs →
      LinkedListIn f₂ mem' head xs
  | [], h => h
  | _ :: _, ⟨hne, hfa, hfa1, hhead, hnext⟩ =>
    ⟨hne, hf _ hfa, hf _ hfa1, (hm _ hfa).trans hhead,
      linkedListIn_mono hf hm ((hm _ hfa1) ▸ hnext)⟩

structure DsSLayoutFacts (b L vCap eCap i v i' v' heapPtr : ℕ) : Prop where
  sg_ne_gen : dsSGenBase b L vCap eCap + i ≠ b + dsGenOff
  vs_ne_gen : dsVSGenBase b L vCap eCap + i * vCap + v ≠ b + dsGenOff
  sh_ne_gen : dsSHeadBase b L vCap eCap + i ≠ b + dsGenOff
  sg_lt_fix : dsSGenBase b L vCap eCap + i < b + dsFixedSize L vCap eCap
  vs_lt_fix : dsVSGenBase b L vCap eCap + i * vCap + v < b + dsFixedSize L vCap eCap
  sh_lt_fix : dsSHeadBase b L vCap eCap + i < b + dsFixedSize L vCap eCap
  gen_lt_fix : b + dsGenOff < b + dsFixedSize L vCap eCap
  sg_lt_hp : dsSGenBase b L vCap eCap + i < heapPtr
  vs_lt_hp : dsVSGenBase b L vCap eCap + i * vCap + v < heapPtr
  sh_lt_hp : dsSHeadBase b L vCap eCap + i < heapPtr
  sg_ne_sh : dsSGenBase b L vCap eCap + i ≠ dsSHeadBase b L vCap eCap + i'
  sg_ne_vs : dsSGenBase b L vCap eCap + i ≠ dsVSGenBase b L vCap eCap + i' * vCap + v'
  sh_ne_vs : dsSHeadBase b L vCap eCap + i ≠ dsVSGenBase b L vCap eCap + i' * vCap + v'
  L1_le_hp : L + 1 ≤ heapPtr
  g_lt_hp : dsGPtr b + dynGraphSize vCap eCap ≤ heapPtr
  gen_lt_hp : b + dsGenOff < heapPtr

lemma dsSAddrs_disjoint {b L vCap eCap i v i' v' heapPtr : ℕ}
    (hi : i ≤ L) (hv : v < vCap) (hi' : i' ≤ L) (hv' : v' < vCap)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) :
    DsSLayoutFacts b L vCap eCap i v i' v' heapPtr := by
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hm := dsMEmbTempBase_eq_rev b L vCap eCap
  have hdg : dsGenOff < dsHdrSize := by decide
  have hml := mul_add_lt_mul_succ hi hv
  have hml' := mul_add_lt_mul_succ hi' hv'
  have hsb : dsSBitBase b L vCap eCap = dsSHeadBase b L vCap eCap + (L + 1) := rfl
  have hvsb : dsVStampBase b L vCap eCap = dsSBitBase b L vCap eCap + vCap := rfl
  have hsg1 : dsSGenBase b L vCap eCap = dsRevHeadBase b L vCap eCap + (L + 1) * vCap := rfl
  have hvsg1 : dsVSGenBase b L vCap eCap = dsSGenBase b L vCap eCap + (L + 1) := rfl
  have hsh1 : dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hgp : dsGPtr b = b + dsHdrSize := rfl
  have hhp : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hap : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hmp : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

lemma dsSCompute_bounds {b L vCap eCap heapPtr w : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hh_lt : heapPtr < 2 ^ w) :
    b + dsHdrSize + 3 * (4 + (7 * vCap + 9 * eCap)) + (3 * eCap + 2 * (L + 1)) +
      ((L + 1) + 2 * ((L + 1) * eCap)) + 2 * ((L + 1) * vCap) = dsSGenBase b L vCap eCap ∧
    dsVSGenBase b L vCap eCap = dsSGenBase b L vCap eCap + (L + 1) ∧
    dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap ∧
    dsSHeadBase b L vCap eCap + (L + 1) ≤ heapPtr ∧
    dsSGenBase b L vCap eCap < 2 ^ w ∧ dsVSGenBase b L vCap eCap < 2 ^ w ∧
    dsSHeadBase b L vCap eCap < 2 ^ w ∧ 4 + (7 * vCap + 9 * eCap) < 2 ^ w ∧
    b + dsHdrSize + 3 * (4 + (7 * vCap + 9 * eCap)) < 2 ^ w ∧
    b + dsHdrSize + 3 * (4 + (7 * vCap + 9 * eCap)) + (3 * eCap + 2 * (L + 1)) < 2 ^ w ∧
    b + dsHdrSize + 3 * (4 + (7 * vCap + 9 * eCap)) + (3 * eCap + 2 * (L + 1)) +
      ((L + 1) + 2 * ((L + 1) * eCap)) < 2 ^ w ∧
    7 * vCap < 2 ^ w ∧ 9 * eCap < 2 ^ w ∧ 2 * (L + 1) < 2 ^ w ∧ 3 * eCap < 2 ^ w ∧
    2 * ((L + 1) * eCap) < 2 ^ w ∧ 2 * ((L + 1) * vCap) < 2 ^ w ∧
    (L + 1) * vCap < 2 ^ w ∧ b < 2 ^ w ∧ dsHdrSize < 2 ^ w := by
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hm := dsMEmbTempBase_eq_rev b L vCap eCap
  have hfa := dsFixedSize_add b L vCap eCap
  have hsb : dsSBitBase b L vCap eCap = dsSHeadBase b L vCap eCap + (L + 1) := rfl
  have hvsb : dsVStampBase b L vCap eCap = dsSBitBase b L vCap eCap + vCap := rfl
  have hsg1 : dsSGenBase b L vCap eCap = dsRevHeadBase b L vCap eCap + (L + 1) * vCap := rfl
  have hvsg1 : dsVSGenBase b L vCap eCap = dsSGenBase b L vCap eCap + (L + 1) := rfl
  have hsh1 : dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hgp : dsGPtr b = b + dsHdrSize := rfl
  have hhp : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hap : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hmp : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hdgs : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hdsh : dsHdrSize = 6 := rfl
  have hr11_eq : b + dsHdrSize + 3 * (4 + (7 * vCap + 9 * eCap)) + (3 * eCap + 2 * (L + 1)) +
      ((L + 1) + 2 * ((L + 1) * eCap)) + 2 * ((L + 1) * vCap) = dsSGenBase b L vCap eCap := by
    linarith only [h1, h2, h3, h4, hsg1, hgp, hhp, hap, hmp, hdgs]
  have hsh_hp : dsSHeadBase b L vCap eCap + (L + 1) ≤ heapPtr := by
    linarith only [hfix, hfa, h1, h2, h3, h4, h5, hm, hsb, hvsb, hsg1, hvsg1, hsh1]
  clear h1 h2 h3 h4 h5 hm hfa hsb hvsb hsg1 hgp hhp hap hmp hdgs hdsh
  have hsh_w : dsSHeadBase b L vCap eCap < 2 ^ w := by omega
  have hvsg_w : dsVSGenBase b L vCap eCap < 2 ^ w := by omega
  have hsg_w : dsSGenBase b L vCap eCap < 2 ^ w := by omega
  exact ⟨hr11_eq, hvsg1, hsh1, hsh_hp, hsg_w, hvsg_w, hsh_w,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩

lemma dsSBounds_lv {b L vCap eCap heapPtr w : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hh_lt : heapPtr < 2 ^ w) :
    L + 1 < 2 ^ w ∧ vCap < 2 ^ w := by
  have h := dsSCompute_bounds hfix hh_lt
  omega

/-! ## Phase 1: Touched vertices and base setup -/

lemma dsUpdateS_touched_cont {w vCap eCap b uLen : ℕ} {G : MGraph} {u : Update}
    {p : Program} {bOps : ℕ} (hpOps : p.HasAt bOps dgOpsProcs)
    {rest : Stmt} {Q : Outcome → State → Prop} {cCont bound : ℕ}
    {mem : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hupdPtr : st.regs 2 + uLen < 2 ^ w)
    (hb : st.regs 0 = b) (hst_mem : st.mem = mem)
    (hG_fix : dsGPtr b + dynGraphSize vCap eCap < 2 ^ w)
    (hG : DynGraphAt mem (dsGPtr b) vCap eCap G) (_hG_val : G.IsValid)
    (hGe : ∀ e ∈ G.E, e < eCap)
    (hUpd : UpdateAt mem (st.regs 2) G u uLen) (hU_val : G.UpdateIsValid u)
    (hds : isDelOrSplit u) (htouch_lt : ∀ v ∈ touchedVertices G u, v < 2 ^ w)
    (hc_bound : 160 + cCont ≤ bound)
    (hcont : ∀ v₁ v₂ : ℕ, touchedVertices G u = {v₁, v₂} →
      Triple w p
        (fun st1 : State =>
          st1.mem = mem ∧ st1.regs 0 = b ∧ st1.regs 1 = st.regs 1 ∧
          st1.regs 2 = st.regs 2 ∧ st1.regs 3 = st.regs 3 ∧
          st1.regs 5 = v₁ ∧ st1.regs 6 = v₂)
        rest Q (fun _ => cCont)) :
    ∃ o st' c, Runs w p ω
      (.cond (.bin .eq (.load (.reg 2)) (.const 1))
        (.assign 7 (.load (.bin .add (.reg 2) (.const 1))) ;;
         .call 5 (bOps + dgIdxGetTail) [.bin .add (.reg 0) (.const dsHdrSize), .reg 7] ;;
         .call 6 (bOps + dgIdxGetHead) [.bin .add (.reg 0) (.const dsHdrSize), .reg 7])
        (.assign 5 (.load (.bin .add (.reg 2) (.const 1))) ;;
         .assign 6 (.load (.bin .add (.reg 2) (.const 2)))) ;; rest)
      st o st' c ∧ Q o st' ∧ c ≤ bound := by
  have hgt := dgGetTail_meetsContract (w := w) (vCap := vCap) (eCap := eCap) (G := G) hpOps
  have hgh := dgGetHead_meetsContract (w := w) (vCap := vCap) (eCap := eCap) (G := G) hpOps
  have hb_lt : b < 2 ^ w := by have : b ≤ dsGPtr b := dsGPtr_ge b; omega
  have hhdr_lt : dsHdrSize < 2 ^ w := by simp [dsHdrSize]; omega
  have hb_hdr_lt : b + dsHdrSize < 2 ^ w := by
    have : dsGPtr b = b + dsHdrSize := rfl
    have : 4 ≤ dynGraphSize vCap eCap := by
      have : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl; omega
    omega
  cases u with
  | insert => simp [isDelOrSplit] at hds
  | delete e =>
    rcases hUpd with ⟨hlen, hL⟩
    have heE : e ∈ G.E := hU_val
    have hm0 : st.mem (st.regs 2) = 1 := by
      have h := hL.getElem_of_eq (Nat.add_zero _).symm (by simp)
      simp at h; exact hst_mem ▸ h
    have hm1 : st.mem (st.regs 2 + 1) = e := by
      have h := hL.getElem_of_eq (i := 1) rfl (by simp)
      simp at h; exact hst_mem ▸ h
    have he_lt : e < 2 ^ w := by
      have := hGe e heE
      have : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
      omega
    refine runs_start_le ?_
    wram_run
    · refine ⟨dsGPtr b, e, rfl, hw16, hG_fix, heE, by simpa [hst_mem] using hG⟩
    · intro v₁ mem₁ pos₁ ⟨g₁, e₁, harg₁, hmem₁, hret₁⟩
      obtain ⟨rfl, rfl⟩ := by simpa [dsGPtr, dsHdrSize, hb] using harg₁
      wram_run
      · refine ⟨dsGPtr b, e, rfl, hw16, hG_fix, heE, by simpa [hmem₁, hst_mem] using hG⟩
      · intro v₂ mem₂ pos₂ ⟨g₂, e₂, harg₂, hmem₂, hret₂⟩
        obtain ⟨rfl, rfl⟩ := by simpa [dsGPtr, dsHdrSize, hb] using harg₂
        refine runs_triple_le (hcont (G.tail e) (G.head e) rfl)
          ⟨by simp [hmem₂, hmem₁, hst_mem], by simp [hb], by simp, by simp, by simp,
            by simp [hret₁], by simp [hret₂]⟩ (fun _ _ h => h) ?_
        dsimp only [dgGetTailContract, dgGetHeadContract] at *
        wram_cost
  | split v v' S Sh =>
    have hcases : ∃ hm0 : mem (st.regs 2) ≠ 1,
        mem (st.regs 2 + 1) = v ∧ mem (st.regs 2 + 2) = v' ∧ 4 ≤ uLen ∧ mem (st.regs 2) < 2 ^ w := by
      rcases hUpd with ⟨Lt, Lh, _, _, _, _, hlen, hL⟩ | ⟨Lt, Lh, _, _, _, _, hlen, hL⟩
      · have h0 := hL.getElem_of_eq (Nat.add_zero _).symm (by simp); simp at h0
        have h1 := hL.getElem_of_eq (i := 1) rfl (by simp); simp at h1
        have h2 := hL.getElem_of_eq (i := 2) rfl (by simp); simp at h2
        exact ⟨by omega, h1, h2, by omega, by omega⟩
      · have h0 := hL.getElem_of_eq (Nat.add_zero _).symm (by simp); simp at h0
        have h1 := hL.getElem_of_eq (i := 1) rfl (by simp); simp at h1
        have h2 := hL.getElem_of_eq (i := 2) rfl (by simp); simp at h2
        exact ⟨by omega, h1, h2, by omega, by omega⟩
    rcases hcases with ⟨hm0_ne, hm1, hm2, hlen4, hmem_lt⟩
    have hm0' : st.mem (st.regs 2) = mem (st.regs 2) := congrFun hst_mem _
    have hm1' : st.mem (st.regs 2 + 1) = v := hst_mem ▸ hm1
    have hm2' : st.mem (st.regs 2 + 2) = v' := hst_mem ▸ hm2
    have hv_lt : v < 2 ^ w := htouch_lt v (by simp [touchedVertices])
    have hv'_lt : v' < 2 ^ w := htouch_lt v' (by simp [touchedVertices])
    refine runs_start_le ?_
    wram_run
    refine runs_triple_le (hcont v v' rfl)
      ⟨hst_mem, by simp [hb], by simp, by simp, by simp, by simp [hm1'], by simp [hm2']⟩
      (fun _ _ h => h) ?_
    wram_cost

lemma dsUpdateS_computeSBases_cont {w L vCap eCap b heapPtr : ℕ}
    {p : Program} {rest : Stmt} {Q : Outcome → State → Prop} {cCont bound : ℕ}
    {mem : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hh_lt : heapPtr < 2 ^ w)
    (hmL : mem (b + dsLOff) = L) (hmV : mem (b + dsVCapOff) = vCap) (hmE : mem (b + dsECapOff) = eCap)
    (hst_mem : st.mem = mem) (hb : st.regs 0 = b)
    (h3 : st.regs 3 = heapPtr) (hgen_lt : mem (b + dsGenOff) < 2 ^ w)
    (hc_bound : 180 + cCont ≤ bound)
    (hcont : Triple w p
      (fun st1 : State =>
        st1.mem = mem ∧ st1.regs 0 = b ∧ st1.regs 1 = st.regs 1 ∧ st1.regs 3 = heapPtr ∧
        st1.regs 5 = st.regs 5 ∧ st1.regs 6 = st.regs 6 ∧
        st1.regs 7 = vCap ∧ st1.regs 8 = eCap ∧ st1.regs 9 = L ∧
        st1.regs 10 = mem (b + dsGenOff) ∧
        st1.regs 11 = dsSGenBase b L vCap eCap ∧
        st1.regs 12 = dsVSGenBase b L vCap eCap ∧
        st1.regs 13 = dsSHeadBase b L vCap eCap)
      rest Q (fun _ => cCont)) :
    ∃ o st' c, Runs w p ω
      (.assign 7 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
       .assign 8 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
       .assign 9 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
       .assign 10 (.load (.bin .add (.reg 0) (.const dsGenOff))) ;;
       dsComputeSBasesStmt ;; rest)
      st o st' c ∧ Q o st' ∧ c ≤ bound := by
  obtain ⟨hr11_eq, hvsg_eq, hsh_eq, _, hr11_w, hr12_w, hr13_w, hdgs_w, ha_w, hb_w, hc_w,
    h7vc_w, h9ec_w, h2L_w, h3ec_w, h2Le_w, h2Lv_w, hLv_w, hb_w', hdr_w⟩ :=
    dsSCompute_bounds hfix hh_lt
  have hdg_lt : dsGenOff < dsHdrSize := by decide
  have hdv_lt : dsVCapOff < dsHdrSize := by decide
  have hde_lt : dsECapOff < dsHdrSize := by decide
  have hdl_lt : dsLOff < dsHdrSize := by decide
  have hmV' : st.mem (b + dsVCapOff) = vCap := hst_mem ▸ hmV
  have hmE' : st.mem (b + dsECapOff) = eCap := hst_mem ▸ hmE
  have hmL' : st.mem (b + dsLOff) = L := hst_mem ▸ hmL
  have hdg_w : dsGenOff < 2 ^ w := by omega
  have hdv_w : dsVCapOff < 2 ^ w := by omega
  have hde_w : dsECapOff < 2 ^ w := by omega
  have hdl_w : dsLOff < 2 ^ w := by omega
  have hbv_w : b + dsVCapOff < 2 ^ w := by omega
  have hbe_w : b + dsECapOff < 2 ^ w := by omega
  have hbl_w : b + dsLOff < 2 ^ w := by omega
  have hbg_w : b + dsGenOff < 2 ^ w := by omega
  have h47v_w : 7 * vCap + 9 * eCap < 2 ^ w := by omega
  have h3dgs_w : 3 * (4 + (7 * vCap + 9 * eCap)) < 2 ^ w := by omega
  have hL1_w : L + 1 < 2 ^ w := by omega
  have h3ec2L_w : 3 * eCap + 2 * (L + 1) < 2 ^ w := by omega
  have hLe_w : (L + 1) * eCap < 2 ^ w := by omega
  have hL2Le_w : (L + 1) + 2 * ((L + 1) * eCap) < 2 ^ w := by omega
  have hr0_w : st.regs 0 < 2 ^ w := by rw [hb]; exact hb_w'
  have hr0_vc : st.regs 0 + dsVCapOff < 2 ^ w := by rw [hb]; exact hbv_w
  have hr0_ec : st.regs 0 + dsECapOff < 2 ^ w := by rw [hb]; exact hbe_w
  have hr0_l : st.regs 0 + dsLOff < 2 ^ w := by rw [hb]; exact hbl_w
  have hr0_g : st.regs 0 + dsGenOff < 2 ^ w := by rw [hb]; exact hbg_w
  have hm_vc_w : st.mem (st.regs 0 + dsVCapOff) < 2 ^ w := by rw [hb, hst_mem, hmV]; omega
  have hm_ec_w : st.mem (st.regs 0 + dsECapOff) < 2 ^ w := by rw [hb, hst_mem, hmE]; omega
  have hm_l_w : st.mem (st.regs 0 + dsLOff) < 2 ^ w := by rw [hb, hst_mem, hmL]; omega
  have hm_g_w : st.mem (st.regs 0 + dsGenOff) < 2 ^ w := by rw [hb, hst_mem]; exact hgen_lt
  clear hfix hh_lt
  refine runs_start_le ?_
  wram_step; wram_step; wram_step; wram_step
  simp only [hb, hst_mem, hmV, hmE, hmL]
  dsimp only [dsComputeSBasesStmt]
  wram_run
  refine runs_triple_le hcont
    ⟨rfl, by simp [hb], by simp, by simp [h3], by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp [Function.update]; omega,
      by simp [Function.update]; omega,
      by simp [Function.update]; omega⟩
    (fun _ _ h => h) ?_
  wram_cost

/-! ## Inner vertex insertion and loops -/

lemma dsInsertSLevelVertex_triple {w L vCap eCap b i rV v₁ heapPtr curHeap gen0 : ℕ}
    {p : Program} (regs0 mem0 : ℕ → ℕ) (S0 : Finset ℕ) (xs0 : List ℕ) (foot0 : ℕ → Prop)
    (hrV : rV = 5 ∨ rV = 6) (hi : i ≤ L) (hv : v₁ < vCap) (hw16 : 16 ≤ 2 ^ w)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hh_le : heapPtr ≤ curHeap)
    (hcur_lt : curHeap + 2 < 2 ^ w) (hsgi_pos : 0 < mem0 (dsSGenBase b L vCap eCap + i))
    (hsgi_le : mem0 (dsSGenBase b L vCap eCap + i) ≤ gen0) (hgen_lt : gen0 < 2 ^ w)
    (hfoot0 : ∀ a, foot0 a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr) :
    Triple w p
      (fun st : State =>
        st.mem = mem0 ∧ st.regs = regs0 ∧
        regs0 0 = b ∧ regs0 11 = dsSGenBase b L vCap eCap ∧
        regs0 12 = dsVSGenBase b L vCap eCap ∧ regs0 13 = dsSHeadBase b L vCap eCap ∧
        regs0 14 = i ∧ regs0 3 = curHeap ∧
        regs0 15 = mem0 (dsSGenBase b L vCap eCap + i) ∧
        regs0 16 = dsVSGenBase b L vCap eCap + i * vCap ∧ regs0 rV = v₁ ∧
        (∀ z ∈ S0, z < vCap) ∧
        (∀ z < vCap,
          mem0 (dsVSGenBase b L vCap eCap + i * vCap + z) ≤ gen0 ∧
          ((0 < mem0 (dsSGenBase b L vCap eCap + i) ∧
            mem0 (dsVSGenBase b L vCap eCap + i * vCap + z) =
              mem0 (dsSGenBase b L vCap eCap + i)) ↔ z ∈ S0)) ∧
        xs0.Nodup ∧ (∀ z, z ∈ xs0 ↔ z ∈ S0) ∧
        LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < curHeap)) mem0
          (mem0 (dsSHeadBase b L vCap eCap + i)) xs0)
      (dsInsertSLevelVertexStmt (.reg rV))
      (normalPost fun st' =>
        curHeap ≤ st'.regs 3 ∧ st'.regs 3 ≤ curHeap + 2 ∧
        (∀ r, r ≠ 3 → r ≠ 17 → st'.regs r = regs0 r) ∧
        st'.mem (b + dsGenOff) = mem0 (b + dsGenOff) ∧
        st'.mem (dsSGenBase b L vCap eCap + i) = mem0 (dsSGenBase b L vCap eCap + i) ∧
        (∀ z ∈ S0 ∪ {v₁}, z < vCap) ∧
        (∀ z < vCap,
          st'.mem (dsVSGenBase b L vCap eCap + i * vCap + z) ≤ gen0 ∧
          ((0 < st'.mem (dsSGenBase b L vCap eCap + i) ∧
            st'.mem (dsVSGenBase b L vCap eCap + i * vCap + z) =
              mem0 (dsSGenBase b L vCap eCap + i)) ↔ z ∈ S0 ∪ {v₁})) ∧
        (∃ xs', xs'.Nodup ∧ (∀ z, z ∈ xs' ↔ z ∈ S0 ∪ {v₁}) ∧
          LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < st'.regs 3)) st'.mem
            (st'.mem (dsSHeadBase b L vCap eCap + i)) xs') ∧
        ∀ addr,
          addr ≠ dsVSGenBase b L vCap eCap + i * vCap + v₁ →
          addr ≠ dsSHeadBase b L vCap eCap + i →
          (addr < curHeap ∨ st'.regs 3 ≤ addr) →
          st'.mem addr = mem0 addr)
      (fun _ => 110) := by
  wram_enter
  rcases hpre with ⟨hmem, hregs, r0, r11, r12, r13, r14, r3, r15, r16, rrV,
    hS0_cap, hvs0, hxs_nd, hxs_mem, hll0⟩
  set sgi := mem0 (dsSGenBase b L vCap eCap + i)
  set vsAddr := dsVSGenBase b L vCap eCap + i * vCap + v₁
  set shAddr := dsSHeadBase b L vCap eCap + i
  have hdisj := dsSAddrs_disjoint hi hv hi hv hfix
  have hvs_lt : vsAddr < 2 ^ w := by dsimp only [vsAddr]; have := hdisj.vs_lt_hp; omega
  have hsh_lt : shAddr < 2 ^ w := by dsimp only [shAddr]; have := hdisj.sh_lt_hp; omega
  have hv₁_lt : v₁ < 2 ^ w := by have := mul_add_lt_mul_succ hi hv; omega
  have hr3_lt : curHeap < 2 ^ w := by omega
  have holdH_lt : mem0 shAddr < 2 ^ w := by
    rcases xs0 with _ | ⟨y, ys⟩
    · have : mem0 shAddr = 0 := hll0; rw [this]; omega
    · rcases hll0.2.1 with h | ⟨_, h⟩
      · have := (hfoot0 (mem0 shAddr) h).2; omega
      · omega
  have hm_vs : st.mem vsAddr = mem0 vsAddr := congrFun hmem _
  have hm_sh : st.mem shAddr = mem0 shAddr := congrFun hmem _
  have hsr13 : st.regs 13 = dsSHeadBase b L vCap eCap := (congrFun hregs 13).trans r13
  have hsr14 : st.regs 14 = i := (congrFun hregs 14).trans r14
  have hsr15 : st.regs 15 = sgi := (congrFun hregs 15).trans r15
  have hsr16 : st.regs 16 = dsVSGenBase b L vCap eCap + i * vCap := (congrFun hregs 16).trans r16
  have hsrrV : st.regs rV = v₁ := (congrFun hregs rV).trans rrV
  have hsr3 : st.regs 3 = curHeap := (congrFun hregs 3).trans r3
  have hsgi_lt : sgi < 2 ^ w := lt_of_le_of_lt hsgi_le hgen_lt
  have hr16_lt : dsVSGenBase b L vCap eCap + i * vCap < 2 ^ w := by omega
  have hr13_lt : dsSHeadBase b L vCap eCap < 2 ^ w := by omega
  have hi_lt : i < 2 ^ w := by omega
  have hrV17 : rV ≠ 17 := by rcases hrV with rfl | rfl <;> decide
  have hr17_false : (rV = 17) = False := eq_false hrV17
  dsimp only [dsInsertSLevelVertexStmt]
  wram_run
  · -- Branch: `mem0 vsAddr = sgi` (`v₁ ∈ S0`)
    have hv_S0 : v₁ ∈ S0 := (hvs0 v₁ hv).2.mp ⟨hsgi_pos, hm_vs.symm.trans hcond⟩
    have hSu : S0 ∪ {v₁} = S0 := Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hv_S0)
    rw [hSu]
    refine ⟨le_of_eq hsr3.symm, by omega, fun r _ _ => (congrFun hregs r),
      congrFun hmem _, congrFun hmem _, hS0_cap,
      fun z hz => by simpa [hmem] using hvs0 z hz,
      ⟨xs0, hxs_nd, hxs_mem, by simpa [hmem, hsr3] using hll0⟩,
      fun a _ _ _ => congrFun hmem a⟩
  · wram_cost
  · -- Branch: `mem0 vsAddr ≠ sgi` (`v₁ ∉ S0`)
    have hv_mem_ne : mem0 vsAddr ≠ sgi := fun h =>
      hcond (by dsimp only [vsAddr] at hm_vs; rw [hm_vs]; exact h)
    have hv_nS0 : v₁ ∉ S0 := fun h => hv_mem_ne ((hvs0 v₁ hv).2.mpr h).2
    have hvs_ne_sh : vsAddr ≠ shAddr := hdisj.sh_ne_vs.symm
    have hvs_ne_gen : vsAddr ≠ b + dsGenOff := hdisj.vs_ne_gen
    have hsh_ne_gen : shAddr ≠ b + dsGenOff := hdisj.sh_ne_gen
    have hvs_ne_sg : vsAddr ≠ dsSGenBase b L vCap eCap + i := hdisj.sg_ne_vs.symm
    have hsh_ne_sg : shAddr ≠ dsSGenBase b L vCap eCap + i := hdisj.sg_ne_sh.symm
    have hvs_lt_cur : vsAddr < curHeap := lt_of_lt_of_le hdisj.vs_lt_hp hh_le
    have hsh_lt_cur : shAddr < curHeap := lt_of_lt_of_le hdisj.sh_lt_hp hh_le
    set oldH := mem0 shAddr
    set mem1 := Function.update mem0 vsAddr sgi
    set mem2 := Function.update mem1 curHeap v₁
    set mem3 := Function.update mem2 (curHeap + 1) oldH
    set mem4 := Function.update mem3 shAddr curHeap
    have hagree : ∀ addr, addr ≠ vsAddr → addr ≠ shAddr →
        (addr < curHeap ∨ curHeap + 2 ≤ addr) → mem4 addr = mem0 addr := fun a h1 h2 h3 => by
      simp [mem4, mem3, mem2, mem1, Function.update, h1, h2, show a ≠ curHeap by omega,
        show a ≠ curHeap + 1 by omega]
    have hll4_old : LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < curHeap + 2))
        mem4 oldH xs0 := by
      refine linkedListIn_mono (fun a ha => ha.imp id fun ⟨h1, h2⟩ => ⟨h1, by omega⟩)
        (fun a ha => ?_) hll0
      have ha_fix : b + dsFixedSize L vCap eCap ≤ a ∧ a < curHeap := by
        rcases ha with ha | ⟨h1, h2⟩
        · exact ⟨(hfoot0 a ha).1, lt_of_lt_of_le (hfoot0 a ha).2 hh_le⟩
        · exact ⟨le_trans hfix h1, h2⟩
      exact hagree a (by dsimp only [vsAddr]; have := hdisj.vs_lt_fix; omega)
        (by dsimp only [shAddr]; have := hdisj.sh_lt_fix; omega) (Or.inl ha_fix.2)
    have hcur_pos : 0 < curHeap := by
      have : 1 ≤ dsFixedSize L vCap eCap := by
        have := dsFixedSize_pos L vCap eCap; omega
      omega
    have hm4_sh : mem4 shAddr = curHeap := by simp [mem4]
    have hm4_c : mem4 curHeap = v₁ := by
      simp [mem4, mem3, mem2, Function.update, show curHeap ≠ shAddr by omega]
    have hm4_c1 : mem4 (curHeap + 1) = oldH := by
      simp [mem4, mem3, Function.update, show curHeap + 1 ≠ shAddr by omega]
    have hll4_new : LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < curHeap + 2))
        mem4 (mem4 shAddr) (v₁ :: xs0) := by
      rw [hm4_sh]; exact ⟨hcur_pos, Or.inr ⟨hh_le, by omega⟩, Or.inr ⟨by omega, by omega⟩,
        hm4_c, hm4_c1 ▸ hll4_old⟩
    have hmem_upd' : Function.update
        (Function.update
          (Function.update (Function.update st.mem (dsVSGenBase b L vCap eCap + i * vCap + v₁) sgi)
            curHeap v₁) (curHeap + 1) (st.mem (dsSHeadBase b L vCap eCap + i)))
        (dsSHeadBase b L vCap eCap + i) curHeap = mem4 := by
      rw [hmem]
    simp only [hsr13, hsr14, hsrrV, hsr3, hr17_false, hdisj.sh_ne_vs, ↓reduceIte]
    rw [hmem_upd']
    refine ⟨by simp [Function.update], by simp [Function.update],
      fun r hr3 hr17 => by rcases hrV with rfl | rfl <;> simp [Function.update, hr3, hr17, hregs],
      hagree _ hvs_ne_gen.symm hsh_ne_gen.symm (Or.inl (lt_of_lt_of_le hdisj.gen_lt_hp hh_le)),
      hagree _ hvs_ne_sg.symm hsh_ne_sg.symm (Or.inl (lt_of_lt_of_le hdisj.sg_lt_hp hh_le)),
      fun z hz => by
        simp only [Finset.mem_union, Finset.mem_singleton] at hz
        rcases hz with hz | rfl <;> [exact hS0_cap z hz; exact hv],
      fun z hz => ?_,
      ⟨v₁ :: xs0, List.nodup_cons.mpr ⟨fun h => hv_nS0 ((hxs_mem v₁).mp h), hxs_nd⟩,
        fun z => by simp [hxs_mem z], by simpa [Function.update] using hll4_new⟩,
      by simpa [Function.update] using hagree⟩
    by_cases hzv : z = v₁
    · subst hzv
      have hvs4 : mem4 vsAddr = sgi := by
        simp [mem4, mem3, mem2, mem1, Function.update, hvs_ne_sh,
          show vsAddr ≠ curHeap + 1 by omega, show vsAddr ≠ curHeap by omega]
      have hsg4 : mem4 (dsSGenBase b L vCap eCap + i) = sgi :=
        hagree _ hvs_ne_sg.symm hsh_ne_sg.symm (Or.inl (lt_of_lt_of_le hdisj.sg_lt_hp hh_le))
      dsimp only [vsAddr] at hvs4
      dsimp only
      refine ⟨hvs4 ▸ hsgi_le, ?_⟩
      rw [hvs4, hsg4]
      simp [hsgi_pos]
    · set zAddr := dsVSGenBase b L vCap eCap + i * vCap + z
      have hz_disj := dsSAddrs_disjoint hi hz hi hv hfix
      have hzsh_disj := dsSAddrs_disjoint hi hv hi hz hfix
      have hz4 : mem4 zAddr = mem0 zAddr :=
        hagree zAddr (by dsimp only [zAddr, vsAddr]; omega)
          (by dsimp only [zAddr, shAddr]; exact hzsh_disj.sh_ne_vs.symm)
          (Or.inl (lt_of_lt_of_le hz_disj.vs_lt_hp hh_le))
      have hsg4 : mem4 (dsSGenBase b L vCap eCap + i) = sgi :=
        hagree _ hvs_ne_sg.symm hsh_ne_sg.symm (Or.inl (lt_of_lt_of_le hdisj.sg_lt_hp hh_le))
      dsimp only
      refine ⟨hz4 ▸ (hvs0 z hz).1, ?_⟩
      rw [hz4, hsg4]
      simpa [Finset.mem_union, Finset.mem_singleton, hzv] using (hvs0 z hz).2
  · wram_cost

end

end MinCostFlow.DynSpanner.Program
