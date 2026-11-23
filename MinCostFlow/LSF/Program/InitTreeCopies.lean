module

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import MinCostFlow.LSF.Program.InitEdgeCopy
public import MinCostFlow.LSF.Program.InitArena
public import MinCostFlow.LSF.Program.SharedProcs
public import WordRAM.Tactic
public import Mathlib.Tactic.Linarith

/-!
# Parallel Edge Copy Construction for `InitTree` (`InitTreeCopies`)

Implements and verifies `initTreeCopiesProc`: iterates over `G₀`'s active edge list
`eList[0..m0)` and multiplicity array `multPtr[0..m0)`, queries endpoints `G₀.tail e` and
`G₀.head e` from `DynGraphAt G₀`, translates them to `0`-indexed vertex positions
`mem[vIdxBase + u] - 1 < G₀.n`, and invokes `emitEdgeCopiesProc` to populate the contiguous
copy arrays `copyTail`, `copyHead`, `copyLen`, `copyWt`, `copyOrigIdx`, and `copySubIdx`
over `[0, M_copies)` in linear time `O(M_copies * L_in + m0)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Procedure and Contract -/

def initTreeCopiesLoopStmt (b f_ec : ℕ) : Stmt :=
  forRange 14 (.const 0) (.reg 4)
    (.assign 15 (.load (.bin .add (.reg 1) (.reg 14))) ;;
     .assign 16 (.load (.bin .add (.reg 5) (.reg 14))) ;;
     .assign 17 (.bin .add (.reg 2) (.bin .mul (.reg 15) (.reg 3))) ;;
     .call 18 (lsfBaseDg b + dgIdxGetTail) [.reg 0, .reg 15] ;;
     .call 19 (lsfBaseDg b + dgIdxGetHead) [.reg 0, .reg 15] ;;
     .assign 18 (.bin .sub (.load (.bin .add (.reg 6) (.reg 18))) (.const 1)) ;;
     .assign 19 (.bin .sub (.load (.bin .add (.reg 6) (.reg 19))) (.const 1)) ;;
     .call 13 f_ec
       [.reg 18, .reg 19, .reg 17, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12,
        .reg 3, .reg 15, .reg 16, .reg 13])

/-- Emit all `M_copies = ∑ j < m0, mem[multPtr + j]` parallel copies of `G₀`'s edges with
`0`-indexed endpoints `vIdx[u] - 1` into `copyTail..copySubIdx`, returning `M_copies`.
Args: `[gPtr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase, copyTailPtr, copyHeadPtr,
  copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr]`. -/
def initTreeCopiesProc (b f_ec : ℕ) : Stmt :=
  .assign 13 (.const 0) ;;
  initTreeCopiesLoopStmt b f_ec ;;
  .ret (.reg 13)

lemma initTreeCopiesProc_noRand (b f_ec : ℕ) : (initTreeCopiesProc b f_ec).NoRand := by
  simp [initTreeCopiesProc, initTreeCopiesLoopStmt, forRange, forUp, Stmt.NoRand]

def initTreeCopiesCost (m0 L_in M_copies : ℕ) : ℕ :=
  M_copies * (25 * L_in + 80) + 180 * m0 + 30

def initTreeCopiesContract (w : ℕ) (G₀ : MGraph) (vList eList : List ℕ) : Contract where
  pre args mem :=
    ∃ (vCap eCap gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
       copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr M_copies : ℕ),
      args = [gPtr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase,
        copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr] ∧
      16 ≤ 2 ^ w ∧
      G₀.IsValid ∧ (∀ u ∈ G₀.V, u < vCap) ∧ G₀.E.card = m0 ∧
      1 ≤ L_in ∧ L_in < 2 ^ w ∧ lenArr < 2 ^ w ∧
      G₀.n < 2 ^ w ∧ m0 < 2 ^ w ∧ vCap < 2 ^ w ∧
      DynGraphAt mem gPtr vCap eCap G₀ ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
      eList.length = m0 ∧ eList.Nodup ∧ (∀ e, e ∈ eList ↔ e ∈ G₀.E) ∧
      ListAt mem eListPtr eList ∧
      vList.length = G₀.n ∧ vList.Nodup ∧ (∀ u, u ∈ vList ↔ u ∈ G₀.V) ∧
      (∀ i (hi : i < vList.length), mem (vIdxBase + vList[i]) = i + 1) ∧
      M_copies = ((List.range m0).map (fun j => mem (multPtr + j))).sum ∧
      (∀ e ∈ G₀.E, lenArr + e * L_in + L_in ≤ copyTailPtr) ∧
      eListPtr + m0 < 2 ^ w ∧
      (∀ a, eListPtr ≤ a → a < eListPtr + m0 → a < copyTailPtr ∨ copySubIdxPtr + M_copies ≤ a) ∧
      multPtr + m0 < 2 ^ w ∧
      (∀ a, multPtr ≤ a → a < multPtr + m0 → a < copyTailPtr ∨ copySubIdxPtr + M_copies ≤ a) ∧
      vIdxBase + vCap < 2 ^ w ∧
      (∀ a, vIdxBase ≤ a → a < vIdxBase + vCap → a < copyTailPtr ∨ copySubIdxPtr + M_copies ≤ a) ∧
      (∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap →
        a < copyTailPtr ∨ copySubIdxPtr + M_copies ≤ a) ∧
      copyTailPtr + M_copies ≤ copyHeadPtr ∧
      copyHeadPtr + M_copies ≤ copyLenPtr ∧
      copyLenPtr + M_copies * L_in ≤ copyWtPtr ∧
      copyWtPtr + M_copies * L_in ≤ copyOrigIdxPtr ∧
      copyOrigIdxPtr + M_copies ≤ copySubIdxPtr ∧
      copySubIdxPtr + M_copies < 2 ^ w
  post args mem ret mem' :=
    ∃ (vCap eCap gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
       copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr M_copies : ℕ),
      args = [gPtr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase,
        copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr] ∧
      M_copies = ((List.range m0).map (fun j => mem (multPtr + j))).sum ∧
      ret = M_copies ∧
      (∀ j < m0, ∀ k < mem (multPtr + j),
        let q := ((List.range j).map (fun t => mem (multPtr + t))).sum + k
        let e := eList.getD j 0
        q < M_copies ∧
        mem' (copyTailPtr + q) = mem (vIdxBase + G₀.tail e) - 1 ∧
        mem' (copyHeadPtr + q) = mem (vIdxBase + G₀.head e) - 1 ∧
        mem' (copyTailPtr + q) < G₀.n ∧
        vList[mem' (copyTailPtr + q)]? = some (G₀.tail e) ∧
        mem' (copyHeadPtr + q) < G₀.n ∧
        vList[mem' (copyHeadPtr + q)]? = some (G₀.head e) ∧
        (∀ i < L_in, mem' (copyLenPtr + q * L_in + i) = mem (lenArr + e * L_in + i)) ∧
        mem' (copyWtPtr + q * L_in) = 1 ∧
        (∀ i, 0 < i → i < L_in → mem' (copyWtPtr + q * L_in + i) = mem (copyWtPtr + q * L_in + i)) ∧
        mem' (copyOrigIdxPtr + q) = e ∧
        mem' (copySubIdxPtr + q) = k) ∧
      ∀ a, a < copyTailPtr ∨ copySubIdxPtr + M_copies ≤ a → mem' a = mem a
  cost args mem :=
    let L_in := args.getD 3 0
    let m0 := args.getD 4 0
    let multPtr := args.getD 5 0
    let M_copies := ((List.range m0).map (fun j => mem (multPtr + j))).sum
    initTreeCopiesCost m0 L_in M_copies

/-! ## Pure Prefix-Sum Helpers -/

lemma list_range_prefix_succ (f : ℕ → ℕ) (j : ℕ) :
    ((List.range (j + 1)).map f).sum = ((List.range j).map f).sum + f j := by
  rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]

lemma list_range_prefix_mono (f : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    ((List.range a).map f).sum ≤ ((List.range b).map f).sum := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    rw [ha0]
  | succ b ih =>
    rcases Nat.le_succ_iff.mp h with hab | rfl
    · exact le_trans (ih hab) (by rw [list_range_prefix_succ]; omega)
    · exact le_rfl

lemma list_map_mul_sum (l : List ℕ) (f : ℕ → ℕ) (C : ℕ) :
    (l.map fun i => f i * C).sum = (l.map f).sum * C := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

lemma exists_copy_coords (f : ℕ → ℕ) {n q : ℕ}
    (hq : q < ((List.range n).map f).sum) :
    ∃ j < n, ∃ k < f j, q = ((List.range j).map f).sum + k := by
  induction n with
  | zero => simp at hq
  | succ n ih =>
    rw [list_range_prefix_succ] at hq
    by_cases hlt : q < ((List.range n).map f).sum
    · obtain ⟨j, hj, k, hk, hq_eq⟩ := ih hlt
      exact ⟨j, Nat.lt_succ_of_lt hj, k, hk, hq_eq⟩
    · refine ⟨n, Nat.lt_succ_self n, q - ((List.range n).map f).sum, by omega, ?_⟩
      omega

lemma copy_coords_unique (f : ℕ → ℕ) {j₁ k₁ j₂ k₂ : ℕ}
    (hk₁ : k₁ < f j₁) (hk₂ : k₂ < f j₂)
    (heq : ((List.range j₁).map f).sum + k₁ = ((List.range j₂).map f).sum + k₂) :
    j₁ = j₂ ∧ k₁ = k₂ := by
  have hlt_imp : ∀ {a b ka kb : ℕ}, a < b → ka < f a →
      ((List.range a).map f).sum + ka < ((List.range b).map f).sum + kb := by
    intro a b ka kb hab hka
    have h1 : ((List.range a).map f).sum + ka < ((List.range (a + 1)).map f).sum := by
      rw [list_range_prefix_succ]; omega
    have h2 : ((List.range (a + 1)).map f).sum ≤ ((List.range b).map f).sum :=
      list_range_prefix_mono f hab
    omega
  rcases Nat.lt_trichotomy j₁ j₂ with h12 | rfl | h21
  · exact False.elim ((Nat.ne_of_lt (hlt_imp h12 hk₁)) heq)
  · exact ⟨rfl, by omega⟩
  · exact False.elim ((Nat.ne_of_gt (hlt_imp h21 hk₂)) heq)

/-! ## Loop Invariant and Verification -/

private structure CopiesBaseRegs
    (gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
     copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr : ℕ)
    (st : State) : Prop where
  r0 : st.regs 0 = gPtr
  r1 : st.regs 1 = eListPtr
  r2 : st.regs 2 = lenArr
  r3 : st.regs 3 = L_in
  r4 : st.regs 4 = m0
  r5 : st.regs 5 = multPtr
  r6 : st.regs 6 = vIdxBase
  r7 : st.regs 7 = copyTailPtr
  r8 : st.regs 8 = copyHeadPtr
  r9 : st.regs 9 = copyLenPtr
  r10 : st.regs 10 = copyWtPtr
  r11 : st.regs 11 = copyOrigIdxPtr
  r12 : st.regs 12 = copySubIdxPtr

private lemma copiesBaseRegs_upd_hi
    {gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
     copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr r v : ℕ}
    {st : State}
    (hb : CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
      copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr st)
    (hr : 13 ≤ r) :
    CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
      copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
      { st with regs := Function.update st.regs r v } :=
  ⟨by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r0,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r1,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r2,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r3,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r4,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r5,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r6,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r7,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r8,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r9,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r10,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r11,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r12⟩

private structure CopiesLoopInv (G₀ : MGraph) (vList eList : List ℕ)
    (gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
     copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr : ℕ)
    (mem0 : ℕ → ℕ) (t : ℕ) (st : State) : Prop where
  t_le : t ≤ m0
  regs : CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
    copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr st
  r13 : st.regs 13 = ((List.range t).map (fun i => mem0 (multPtr + i))).sum
  r14 : st.regs 14 = t
  entries : ∀ j < t, ∀ k < mem0 (multPtr + j),
    let q := ((List.range j).map (fun i => mem0 (multPtr + i))).sum + k
    let e := eList.getD j 0
    st.mem (copyTailPtr + q) = mem0 (vIdxBase + G₀.tail e) - 1 ∧
    st.mem (copyHeadPtr + q) = mem0 (vIdxBase + G₀.head e) - 1 ∧
    st.mem (copyTailPtr + q) < G₀.n ∧
    vList[st.mem (copyTailPtr + q)]? = some (G₀.tail e) ∧
    st.mem (copyHeadPtr + q) < G₀.n ∧
    vList[st.mem (copyHeadPtr + q)]? = some (G₀.head e) ∧
    (∀ i < L_in, st.mem (copyLenPtr + q * L_in + i) = mem0 (lenArr + e * L_in + i)) ∧
    st.mem (copyWtPtr + q * L_in) = 1 ∧
    (∀ i, 0 < i → i < L_in → st.mem (copyWtPtr + q * L_in + i) = mem0 (copyWtPtr + q * L_in + i)) ∧
    st.mem (copyOrigIdxPtr + q) = e ∧
    st.mem (copySubIdxPtr + q) = k
  hframe : ∀ a,
    let qt := ((List.range t).map (fun i => mem0 (multPtr + i))).sum
    (a < copyTailPtr ∨ copyTailPtr + qt ≤ a) →
    (a < copyHeadPtr ∨ copyHeadPtr + qt ≤ a) →
    (a < copyLenPtr ∨ copyLenPtr + qt * L_in ≤ a) →
    (a < copyWtPtr ∨ copyWtPtr + qt * L_in ≤ a) →
    (a < copyOrigIdxPtr ∨ copyOrigIdxPtr + qt ≤ a) →
    (a < copySubIdxPtr ∨ copySubIdxPtr + qt ≤ a) →
    st.mem a = mem0 a

private lemma copiesLoopInv_upd_hi {G₀ : MGraph} {vList eList : List ℕ}
    {gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
     copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr : ℕ}
    {mem0 : ℕ → ℕ} {t r v : ℕ} {st : State}
    (hr : 15 ≤ r)
    (hL : CopiesLoopInv G₀ vList eList gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
      copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr mem0 t st) :
    CopiesLoopInv G₀ vList eList gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
      copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr mem0 t
      { st with regs := Function.update st.regs r v } :=
  ⟨hL.t_le, copiesBaseRegs_upd_hi hL.regs (by omega),
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.r13,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.r14,
   hL.entries, hL.hframe⟩

private lemma copiesLoopInv_upd_hi_mem_pos {G₀ : MGraph} {vList eList : List ℕ}
    {gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
     copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr : ℕ}
    {mem0 mem1 : ℕ → ℕ} {t r v pos1 : ℕ} {st : State}
    (hr : 15 ≤ r) (hmem : mem1 = st.mem)
    (hL : CopiesLoopInv G₀ vList eList gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
      copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr mem0 t st) :
    CopiesLoopInv G₀ vList eList gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
      copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr mem0 t
      { mem := mem1, regs := Function.update st.regs r v, pos := pos1 } := by
  subst hmem
  exact ⟨hL.t_le,
   ⟨by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r0,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r1,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r2,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r3,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r4,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r5,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r6,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r7,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r8,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r9,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r10,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r11,
    by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.regs.r12⟩,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.r13,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.r14,
   hL.entries, hL.hframe⟩

private lemma copiesBaseRegs_mk {gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
    copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
    r1 v1 r2 v2 pos1 : ℕ} {mem1 : ℕ → ℕ} {st : State}
    (hr1 : 13 ≤ r1) (hr2 : 13 ≤ r2)
    (hb : CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
      copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr st) :
    CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
      copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
      { mem := mem1, regs := Function.update (Function.update st.regs r1 v1) r2 v2, pos := pos1 } :=
  ⟨by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r0,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r1,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r2,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r3,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r4,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r5,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r6,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r7,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r8,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r9,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r10,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r11,
   by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb.r12⟩

theorem initTreeCopies_meetsContract {w b K_AN h f_ec f : ℕ} {p : Program} {G₀ : MGraph}
    {vList eList : List ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (hec : MeetsContract w p f_ec (emitEdgeCopiesContract w))
    (hproc : p.procs[f]? = some (initTreeCopiesProc b f_ec)) :
    MeetsContract w p f (initTreeCopiesContract w G₀ vList eList) := by
  refine meetsContract_of_triple hproc ?_
  intro args mem0 pos _ hpre
  rcases hpre with ⟨vCap, eCap, gPtr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase,
    copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr, M_copies,
    rfl, hw16, hG_val, hvCap_lt, hm_card, hLin1, hLin_w, hlen_w, hn_w, hm0_w, hvCap_w,
    hdg0, hdg_bd, hEL_len, hEL_nd, hEL_mem, hEL_at, hVL_len, hVL_nd, hVL_mem, hvIdx_at,
    hM_eq, hlen_bd, heLP_w, heL_disj, hmult_w, hmult_disj, hvIdx_w, hvIdx_disj, hdg_disj,
    hct_le, hch_le, hcl_le, hcw_le, hco_le, hcs_bd⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hgt_mc : MeetsContract w p (lsfBaseDg b + dgIdxGetTail) (dgGetTailContract w vCap eCap G₀) :=
    dgGetTail_meetsContract (dgReloc_hasAt_ops (lsfHasAt_dg hp))
  have hgh_mc : MeetsContract w p (lsfBaseDg b + dgIdxGetHead) (dgGetHeadContract w vCap eCap G₀) :=
    dgGetHead_meetsContract (dgReloc_hasAt_ops (lsfHasAt_dg hp))
  let mults : ℕ → ℕ := fun j => mem0 (multPtr + j)
  let Inv := CopiesLoopInv G₀ vList eList gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
    copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr mem0
  have hinit_q : Triple w p
      (fun st => st = startState [gPtr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase,
        copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr] mem0 pos)
      (.assign 13 (.const 0))
      (normalPost fun st =>
        CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
          copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr st ∧
        st.regs 13 = 0 ∧ st.mem = mem0) fun _ => 2 :=
    Triple.assign (val := fun _ => 0) (fun _ _ => Expr.eval_const (by omega)) fun st hst => by
      subst hst
      have hb0 : CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
          copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
          (startState [gPtr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase,
            copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr]
            mem0 pos) :=
        ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
         by simp [startState], by simp [startState], by simp [startState], by simp [startState],
         by simp [startState], by simp [startState], by simp [startState], by simp [startState],
         by simp [startState]⟩
      exact ⟨copiesBaseRegs_upd_hi hb0 (by omega), by dsimp; rw [Function.update_self], rfl⟩
  have hinit : ∀ st,
      (CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
        copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr st ∧
       st.regs 13 = 0 ∧ st.mem = mem0) →
      (Expr.const 0).eval w st = some 0 ∧
        Inv 0 { st with regs := Function.update st.regs 14 0 } := by
    intro st ⟨hb, hr13, hm⟩
    refine ⟨Expr.eval_const (by omega), ⟨Nat.zero_le _, copiesBaseRegs_upd_hi hb (by omega),
      by dsimp; rw [Function.update_of_ne (by omega), List.map_nil, List.sum_nil]; exact hr13,
      by dsimp; rw [Function.update_self],
      fun _ h => False.elim (Nat.not_lt_zero _ h),
      fun _ _ _ _ _ _ _ => hm ▸ rfl⟩⟩
  let stepCost : ℕ → ℕ := fun j => mults j * (25 * L_in + 80) + 170
  have hbody : ∀ j, 0 ≤ j → j < m0 →
      Triple w p (Inv j)
        (.assign 15 (.load (.bin .add (.reg 1) (.reg 14))) ;;
         .assign 16 (.load (.bin .add (.reg 5) (.reg 14))) ;;
         .assign 17 (.bin .add (.reg 2) (.bin .mul (.reg 15) (.reg 3))) ;;
         .call 18 (lsfBaseDg b + dgIdxGetTail) [.reg 0, .reg 15] ;;
         .call 19 (lsfBaseDg b + dgIdxGetHead) [.reg 0, .reg 15] ;;
         .assign 18 (.bin .sub (.load (.bin .add (.reg 6) (.reg 18))) (.const 1)) ;;
         .assign 19 (.bin .sub (.load (.bin .add (.reg 6) (.reg 19))) (.const 1)) ;;
         .call 13 f_ec
           [.reg 18, .reg 19, .reg 17, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12,
            .reg 3, .reg 15, .reg 16, .reg 13])
        (normalPost fun st₁ =>
          Inv (j + 1) { st₁ with regs := Function.update st₁.regs 14 (j + 1) } ∧ st₁.regs 14 = j)
        (fun _ => stepCost j) := by
    intro j _ hj
    have hj_len : j < eList.length := by omega
    let e := eList[j]'hj_len
    have he_mem : e ∈ G₀.E := (hEL_mem e).mp (List.getElem_mem hj_len)
    have hq_next : ((List.range (j + 1)).map mults).sum ≤ M_copies := by
      rw [hM_eq]; exact list_range_prefix_mono mults (by omega)
    have hq_succ : ((List.range (j + 1)).map mults).sum =
        ((List.range j).map mults).sum + mults j := list_range_prefix_succ mults j
    let qCur := ((List.range j).map mults).sum
    let mj := mults j
    have hq_le : qCur + mj ≤ M_copies := by rw [← hq_succ]; exact hq_next
    have hq_prev : qCur ≤ M_copies := le_trans (Nat.le_add_right _ _) hq_le
    have hlen_e := hlen_bd e he_mem
    have he_le_mul : e ≤ e * L_in := Nat.le_mul_of_pos_right _ hLin1
    have he_w : e < 2 ^ w := by omega
    have heL_mul_w : e * L_in < 2 ^ w := by omega
    have hlenSrc_w : lenArr + e * L_in < 2 ^ w := by omega
    have heL_j_w : eListPtr + j < 2 ^ w := by omega
    have hmult_j_w : multPtr + j < 2 ^ w := by omega
    have hj_w : j < 2 ^ w := by omega
    have hu_V : G₀.tail e ∈ G₀.V := (hG_val e he_mem).1
    have hv_V : G₀.head e ∈ G₀.V := (hG_val e he_mem).2
    have hu_lt_vCap : G₀.tail e < vCap := hvCap_lt _ hu_V
    have hv_lt_vCap : G₀.head e < vCap := hvCap_lt _ hv_V
    have hu_in_vL : G₀.tail e ∈ vList := (hVL_mem _).mpr hu_V
    have hv_in_vL : G₀.head e ∈ vList := (hVL_mem _).mpr hv_V
    obtain ⟨iu, hiu_len, hiu_eq⟩ := List.mem_iff_getElem.mp hu_in_vL
    obtain ⟨iv, hiv_len, hiv_eq⟩ := List.mem_iff_getElem.mp hv_in_vL
    have hvIdx_u_addr_w : vIdxBase + G₀.tail e < 2 ^ w := by omega
    have hvIdx_v_addr_w : vIdxBase + G₀.head e < 2 ^ w := by omega
    have hu_idx1_eq : mem0 (vIdxBase + G₀.tail e) = iu + 1 := by
      rw [← hiu_eq]; exact hvIdx_at iu hiu_len
    have hv_idx1_eq : mem0 (vIdxBase + G₀.head e) = iv + 1 := by
      rw [← hiv_eq]; exact hvIdx_at iv hiv_len
    have hu_idx1_w : mem0 (vIdxBase + G₀.tail e) < 2 ^ w := by omega
    have hv_idx1_w : mem0 (vIdxBase + G₀.head e) < 2 ^ w := by omega
    have hu_idx_lt : mem0 (vIdxBase + G₀.tail e) - 1 < G₀.n := by omega
    have hv_idx_lt : mem0 (vIdxBase + G₀.head e) - 1 < G₀.n := by omega
    have h_frame_of_lt_or_ge : ∀ {st : State} (hL : Inv j st) {a : ℕ},
        (a < copyTailPtr ∨ copySubIdxPtr + M_copies ≤ a) → st.mem a = mem0 a := by
      intro st hL a ha
      have hqp : ((List.range j).map (fun i => mem0 (multPtr + i))).sum ≤ M_copies := hq_prev
      have hqm : ((List.range j).map (fun i => mem0 (multPtr + i))).sum * L_in ≤ M_copies * L_in :=
        Nat.mul_le_mul_right L_in hqp
      exact hL.hframe a
        (ha.elim Or.inl fun h => Or.inr (by omega))
        (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by omega))
        (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by omega))
        (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by omega))
        (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by omega))
        (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by omega))
    have a15 : Triple w p (Inv j) (.assign 15 (.load (.bin .add (.reg 1) (.reg 14))))
        (normalPost fun st => Inv j st ∧ st.regs 15 = e) fun _ => 5 :=
      Triple.assign
        (fun _ hst => Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hst.regs.r1) (Expr.eval_reg_of_eq hst.r14) heL_j_w)
          (by rw [h_frame_of_lt_or_ge hst (heL_disj _ (by omega) (by omega)), hEL_at j hj_len]))
        fun _ hst => ⟨copiesLoopInv_upd_hi (by omega) hst, by dsimp; rw [Function.update_self]⟩
    have a16 : Triple w p (fun st => Inv j st ∧ st.regs 15 = e)
        (.assign 16 (.load (.bin .add (.reg 5) (.reg 14))))
        (normalPost fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj) fun _ => 5 :=
      Triple.assign
        (fun _ hst => Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hst.1.regs.r5) (Expr.eval_reg_of_eq hst.1.r14) hmult_j_w)
          (h_frame_of_lt_or_ge hst.1 (hmult_disj _ (by omega) (by omega))))
        fun _ hst => ⟨copiesLoopInv_upd_hi (by omega) hst.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2,
          by dsimp; rw [Function.update_self]⟩
    have a17 : Triple w p (fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj)
        (.assign 17 (.bin .add (.reg 2) (.bin .mul (.reg 15) (.reg 3))))
        (normalPost fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in) fun _ => 6 :=
      Triple.assign
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.regs.r2)
          (Expr.eval_mul (Expr.eval_reg_of_eq hst.2.1) (Expr.eval_reg_of_eq hst.1.regs.r3) heL_mul_w)
          hlenSrc_w)
        fun _ hst => ⟨copiesLoopInv_upd_hi (by omega) hst.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2,
          by dsimp; rw [Function.update_self]⟩
    have ctail : Triple w p
        (fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧ st.regs 17 = lenArr + e * L_in)
        (.call 18 (lsfBaseDg b + dgIdxGetTail) [.reg 0, .reg 15])
        (normalPost fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in ∧ st.regs 18 = G₀.tail e) fun _ => 49 :=
      Triple.conseq
        (Triple.call (vs := fun _ => [gPtr, e]) hgt_mc
          (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r0)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.2.1) (evalArgs_nil _ _)))
          (fun _ _ x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl <;> omega)
          (fun st hst => ⟨gPtr, e, rfl, hw16, hdg_bd, he_mem,
            DynGraphAt.of_agree hdg0 fun addr ha1 ha2 =>
              h_frame_of_lt_or_ge hst.1 (hdg_disj addr ha1 ha2)⟩)
          (fun st ret mem1 pos1 hst ⟨_, _, heq, hmem_eq, hret⟩ => by
            simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
            dsimp only
            refine ⟨?_, by rw [Function.update_of_ne (by omega)]; exact hst.2.1,
              by rw [Function.update_of_ne (by omega)]; exact hst.2.2.1,
              by rw [Function.update_of_ne (by omega)]; exact hst.2.2.2,
              by rw [Function.update_self]; exact hret⟩
            exact copiesLoopInv_upd_hi_mem_pos (by omega) hmem_eq hst.1))
        (fun _ hst => hst) (fun _ _ hst => hst) fun _ _ => by
          simp only [dgGetTailContract, argsSize, Expr.size]
          omega
    have chead : Triple w p
        (fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in ∧ st.regs 18 = G₀.tail e)
        (.call 19 (lsfBaseDg b + dgIdxGetHead) [.reg 0, .reg 15])
        (normalPost fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in ∧ st.regs 18 = G₀.tail e ∧ st.regs 19 = G₀.head e)
        fun _ => 49 :=
      Triple.conseq
        (Triple.call (vs := fun _ => [gPtr, e]) hgh_mc
          (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r0)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.2.1) (evalArgs_nil _ _)))
          (fun _ _ x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl <;> omega)
          (fun st hst => ⟨gPtr, e, rfl, hw16, hdg_bd, he_mem,
            DynGraphAt.of_agree hdg0 fun addr ha1 ha2 =>
              h_frame_of_lt_or_ge hst.1 (hdg_disj addr ha1 ha2)⟩)
          (fun st ret mem1 pos1 hst ⟨_, _, heq, hmem_eq, hret⟩ => by
            simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl⟩
            dsimp only
            refine ⟨?_, by rw [Function.update_of_ne (by omega)]; exact hst.2.1,
              by rw [Function.update_of_ne (by omega)]; exact hst.2.2.1,
              by rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1,
              by rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2,
              by rw [Function.update_self]; exact hret⟩
            exact copiesLoopInv_upd_hi_mem_pos (by omega) hmem_eq hst.1))
        (fun _ hst => hst) (fun _ _ hst => hst) fun _ _ => by
          simp only [dgGetHeadContract, argsSize, Expr.size]
          omega
    have a18 : Triple w p
        (fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in ∧ st.regs 18 = G₀.tail e ∧ st.regs 19 = G₀.head e)
        (.assign 18 (.bin .sub (.load (.bin .add (.reg 6) (.reg 18))) (.const 1)))
        (normalPost fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in ∧
          st.regs 18 = mem0 (vIdxBase + G₀.tail e) - 1 ∧ st.regs 19 = G₀.head e) fun _ => 7 :=
      Triple.assign
        (fun _ hst => Expr.eval_sub
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq hst.1.regs.r6) (Expr.eval_reg_of_eq hst.2.2.2.2.1)
              hvIdx_u_addr_w)
            (h_frame_of_lt_or_ge hst.1 (hvIdx_disj _ (by omega) (by omega))))
          (Expr.eval_const hw1) hu_idx1_w)
        fun _ hst => ⟨copiesLoopInv_upd_hi (by omega) hst.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1,
          by dsimp; rw [Function.update_self],
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2⟩
    have a19 : Triple w p
        (fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in ∧
          st.regs 18 = mem0 (vIdxBase + G₀.tail e) - 1 ∧ st.regs 19 = G₀.head e)
        (.assign 19 (.bin .sub (.load (.bin .add (.reg 6) (.reg 19))) (.const 1)))
        (normalPost fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in ∧
          st.regs 18 = mem0 (vIdxBase + G₀.tail e) - 1 ∧
          st.regs 19 = mem0 (vIdxBase + G₀.head e) - 1) fun _ => 7 :=
      Triple.assign
        (fun _ hst => Expr.eval_sub
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq hst.1.regs.r6) (Expr.eval_reg_of_eq hst.2.2.2.2.2)
              hvIdx_v_addr_w)
            (h_frame_of_lt_or_ge hst.1 (hvIdx_disj _ (by omega) (by omega))))
          (Expr.eval_const hw1) hv_idx1_w)
        fun _ hst => ⟨copiesLoopInv_upd_hi (by omega) hst.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.1,
          by dsimp; rw [Function.update_self]⟩
    have cemit : Triple w p
        (fun st => Inv j st ∧ st.regs 15 = e ∧ st.regs 16 = mj ∧
          st.regs 17 = lenArr + e * L_in ∧
          st.regs 18 = mem0 (vIdxBase + G₀.tail e) - 1 ∧
          st.regs 19 = mem0 (vIdxBase + G₀.head e) - 1)
        (.call 13 f_ec
          [.reg 18, .reg 19, .reg 17, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12,
           .reg 3, .reg 15, .reg 16, .reg 13])
        (normalPost fun st₁ =>
          Inv (j + 1) { st₁ with regs := Function.update st₁.regs 14 (j + 1) } ∧ st₁.regs 14 = j)
        fun _ => mj * (25 * L_in + 80) + 35 := by
      refine Triple.conseq
        (Triple.call (vs := fun _ =>
            [mem0 (vIdxBase + G₀.tail e) - 1, mem0 (vIdxBase + G₀.head e) - 1,
             lenArr + e * L_in, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr,
             copyOrigIdxPtr, copySubIdxPtr, L_in, e, mj, qCur]) hec
          (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.2.2.1)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.2.2.2)
              (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.2.1)
                (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r7)
                  (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r8)
                    (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r9)
                      (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r10)
                        (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r11)
                          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r12)
                            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r3)
                              (evalArgs_cons (Expr.eval_reg_of_eq hst.2.1)
                                (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.1)
                                  (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r13)
                                    (evalArgs_nil _ _))))))))))))))
          (fun _ _ x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              omega)
          (fun _ _ => by
            have hmul_le : (qCur + mj) * L_in ≤ M_copies * L_in :=
              Nat.mul_le_mul_right L_in hq_le
            refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
              hw16, by omega, by omega, hLin1, he_w, hlen_e,
              by omega, by omega, by omega, by omega, by omega, by omega⟩)
          (fun st ret1 mem1 pos1 hst ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, heq,
              hret, hct, hch, hcl, hcw0, hcwk, hco, hcs, hfr⟩ => by
            simp only [List.cons.injEq, and_true] at heq
            rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            dsimp only [qCur, mj, mults] at hret hct hch hcl hcw0 hcwk hco hcs hfr ⊢
            have hL := hst.1
            have hb' := copiesBaseRegs_mk (r1 := 13) (v1 := ret1) (r2 := 14) (v2 := j + 1)
              (pos1 := pos1) (mem1 := mem1) (by omega) (by omega) hL.regs
            have hq_le' : ((List.range j).map (fun i => mem0 (multPtr + i))).sum +
                mem0 (multPtr + j) ≤ M_copies := hq_le
            have hq_prev' : ((List.range j).map (fun i => mem0 (multPtr + i))).sum ≤ M_copies :=
              hq_prev
            have hq_mul_prev : ((List.range j).map (fun i => mem0 (multPtr + i))).sum * L_in ≤
                M_copies * L_in := Nat.mul_le_mul_right L_in hq_prev'
            have hq_mul_le : (((List.range j).map (fun i => mem0 (multPtr + i))).sum +
                mem0 (multPtr + j)) * L_in ≤ M_copies * L_in := Nat.mul_le_mul_right L_in hq_le'
            have hq_mul_step : ((List.range j).map (fun i => mem0 (multPtr + i))).sum * L_in ≤
                (((List.range j).map (fun i => mem0 (multPtr + i))).sum +
                  mem0 (multPtr + j)) * L_in :=
              Nat.mul_le_mul_right L_in (Nat.le_add_right _ _)
            have hlen_same : ∀ i < L_in, st.mem (lenArr + e * L_in + i) = mem0 (lenArr + e * L_in + i) :=
              fun i hi => h_frame_of_lt_or_ge hL (Or.inl (by omega))
            have hfr_wt_prev : ∀ (t k : ℕ) (ht : t < j) (hk : k < mem0 (multPtr + t))
                (i : ℕ), 0 < i → i < L_in →
                mem1 (copyWtPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k) * L_in + i) =
                  mem0 (copyWtPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k) * L_in + i) := by
              intro t k ht hk i hi0 hiL
              have hqt_le1 : ((List.range t).map (fun s => mem0 (multPtr + s))).sum + k + 1 ≤
                  ((List.range j).map (fun s => mem0 (multPtr + s))).sum := by
                have h1 : ((List.range t).map (fun s => mem0 (multPtr + s))).sum + k + 1 ≤
                    ((List.range (t + 1)).map (fun s => mem0 (multPtr + s))).sum := by
                  rw [list_range_prefix_succ]; omega
                exact le_trans h1 (list_range_prefix_mono (fun s => mem0 (multPtr + s)) ht)
              have hqtL : (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k) * L_in + L_in ≤
                  ((List.range j).map (fun s => mem0 (multPtr + s))).sum * L_in := by
                rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in hqt_le1
              rw [hfr (copyWtPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k) * L_in + i)
                (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
                (Or.inl (by omega)) (Or.inl (by omega))]
              exact (hL.entries t ht k hk).2.2.2.2.2.2.2.2.1 i hi0 hiL
            refine ⟨⟨by omega, hb',
              by
                dsimp
                rw [Function.update_of_ne (by omega), Function.update_self, hret]
                dsimp only [mults] at hq_succ
                rw [← hq_succ],
              by dsimp; rw [Function.update_self],
              fun t ht k hk => by
                dsimp only
                rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | htj
                · have hprev := hL.entries t ht k hk
                  have hqt_le1 : ((List.range t).map (fun s => mem0 (multPtr + s))).sum + k + 1 ≤
                      ((List.range j).map (fun s => mem0 (multPtr + s))).sum := by
                    have h1 : ((List.range t).map (fun s => mem0 (multPtr + s))).sum + k + 1 ≤
                        ((List.range (t + 1)).map (fun s => mem0 (multPtr + s))).sum := by
                      rw [list_range_prefix_succ]; omega
                    exact le_trans h1 (list_range_prefix_mono (fun s => mem0 (multPtr + s)) ht)
                  have hqtL : (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k) * L_in + L_in ≤
                      ((List.range j).map (fun s => mem0 (multPtr + s))).sum * L_in := by
                    rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in hqt_le1
                  have hqt_wt0 :
                      mem1 (copyWtPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k) * L_in) = 1 := by
                    rw [hfr (copyWtPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k) * L_in)
                      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.2.2.2.2.2.2.2.1
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hqt_wt0, hfr_wt_prev t k ht hk, ?_, ?_⟩
                  · rw [hfr (copyTailPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k))
                      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.1
                  · rw [hfr (copyHeadPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k))
                      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.2.1
                  · rw [hfr (copyTailPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k))
                      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.2.2.1
                  · rw [hfr (copyTailPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k))
                      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.2.2.2.1
                  · rw [hfr (copyHeadPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k))
                      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.2.2.2.2.1
                  · rw [hfr (copyHeadPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k))
                      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.2.2.2.2.2.1
                  · intro i hi
                    rw [hfr (copyLenPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k) * L_in + i)
                      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.2.2.2.2.2.2.1 i hi
                  · rw [hfr (copyOrigIdxPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k))
                      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega))]
                    exact hprev.2.2.2.2.2.2.2.2.2.1
                  · rw [hfr (copySubIdxPtr + (((List.range t).map (fun s => mem0 (multPtr + s))).sum + k))
                      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
                      (Or.inr (by omega)) (Or.inl (by omega))]
                    exact hprev.2.2.2.2.2.2.2.2.2.2
                · subst t
                  rw [List.getD_eq_getElem _ _ hj_len]
                  have hTail_eq :
                      mem1 (copyTailPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum + k)) =
                        mem0 (vIdxBase + G₀.tail e) - 1 := hct k hk
                  have hHead_eq :
                      mem1 (copyHeadPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum + k)) =
                        mem0 (vIdxBase + G₀.head e) - 1 := hch k hk
                  refine ⟨hTail_eq, hHead_eq, ?_, ?_, ?_, ?_, ?_, hcw0 k hk, ?_, hco k hk, hcs k hk⟩
                  · rw [hTail_eq]; exact hu_idx_lt
                  · rw [hTail_eq, hu_idx1_eq, Nat.add_sub_cancel]; simp only [List.getElem?_eq_getElem hiu_len, hiu_eq]; rfl
                  · rw [hHead_eq]; exact hv_idx_lt
                  · rw [hHead_eq, hv_idx1_eq, Nat.add_sub_cancel]; simp only [List.getElem?_eq_getElem hiv_len, hiv_eq]; rfl
                  · intro i hi; rw [hcl k hk i hi, hlen_same i hi]
                  · intro i hi0 hiL
                    rw [hcwk k hk i hi0 hiL]
                    have hqk_ge :
                        ((List.range j).map (fun s => mem0 (multPtr + s))).sum * L_in ≤
                          (((List.range j).map (fun s => mem0 (multPtr + s))).sum + k) * L_in :=
                      Nat.mul_le_mul_right L_in (by omega)
                    have h1 :
                        (((List.range j).map (fun s => mem0 (multPtr + s))).sum + k) * L_in + i <
                          (((List.range j).map (fun s => mem0 (multPtr + s))).sum + k + 1) * L_in := by
                      rw [Nat.add_one_mul]; omega
                    have h2 :
                        (((List.range j).map (fun s => mem0 (multPtr + s))).sum + k + 1) * L_in ≤
                          (((List.range j).map (fun s => mem0 (multPtr + s))).sum +
                            mem0 (multPtr + j)) * L_in :=
                      Nat.mul_le_mul_right L_in (by omega)
                    exact hL.hframe
                      (copyWtPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum + k) * L_in + i)
                      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
                      (Or.inl (by omega)) (Or.inl (by omega)),
              fun a ha1 ha2 ha3 ha4 ha5 ha6 => by
                dsimp only
                rw [list_range_prefix_succ] at ha1 ha2 ha3 ha4 ha5 ha6
                have ha3' : a < copyLenPtr + ((List.range j).map (fun s => mem0 (multPtr + s))).sum * L_in ∨
                    copyLenPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum +
                      mem0 (multPtr + j)) * L_in ≤ a := ha3.elim (fun h => Or.inl (by omega)) Or.inr
                have ha4' : a < copyWtPtr + ((List.range j).map (fun s => mem0 (multPtr + s))).sum * L_in ∨
                    copyWtPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum +
                      mem0 (multPtr + j)) * L_in ≤ a := ha4.elim (fun h => Or.inl (by omega)) Or.inr
                have ha1' : a < copyTailPtr + ((List.range j).map (fun s => mem0 (multPtr + s))).sum ∨
                    copyTailPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum +
                      mem0 (multPtr + j)) ≤ a := ha1.elim (fun h => Or.inl (by omega)) Or.inr
                have ha2' : a < copyHeadPtr + ((List.range j).map (fun s => mem0 (multPtr + s))).sum ∨
                    copyHeadPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum +
                      mem0 (multPtr + j)) ≤ a := ha2.elim (fun h => Or.inl (by omega)) Or.inr
                have ha5' : a < copyOrigIdxPtr + ((List.range j).map (fun s => mem0 (multPtr + s))).sum ∨
                    copyOrigIdxPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum +
                      mem0 (multPtr + j)) ≤ a := ha5.elim (fun h => Or.inl (by omega)) Or.inr
                have ha6' : a < copySubIdxPtr + ((List.range j).map (fun s => mem0 (multPtr + s))).sum ∨
                    copySubIdxPtr + (((List.range j).map (fun s => mem0 (multPtr + s))).sum +
                      mem0 (multPtr + j)) ≤ a := ha6.elim (fun h => Or.inl (by omega)) Or.inr
                rw [hfr a ha1' ha2' ha3' ha4' ha5' ha6']
                exact hL.hframe a
                  (ha1.elim Or.inl fun h => Or.inr (by omega))
                  (ha2.elim Or.inl fun h => Or.inr (by omega))
                  (ha3.elim Or.inl fun h => Or.inr (by omega))
                  (ha4.elim Or.inl fun h => Or.inr (by omega))
                  (ha5.elim Or.inl fun h => Or.inr (by omega))
                  (ha6.elim Or.inl fun h => Or.inr (by omega))⟩,
              by change Function.update st.regs 13 ret1 14 = j; rw [Function.update_of_ne (by omega)]; exact hL.r14⟩))
        (fun _ hst => hst) (fun _ _ hst => hst) fun _ _ => by
          simp only [emitEdgeCopiesContract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
          omega
    exact (Triple.seq_normal_const a15 (Triple.seq_normal_const a16 (Triple.seq_normal_const a17
      (Triple.seq_normal_const ctail (Triple.seq_normal_const chead (Triple.seq_normal_const a18
        (Triple.seq_normal_const a19 cemit))))))).mono_cost fun _ _ => by
      dsimp only [stepCost, mj, mults]; omega
  have hloop := Triple.forRange_le (p := p) (r := 14) (lo := .const 0) (hi := .reg 4)
    (body :=
      (.assign 15 (.load (.bin .add (.reg 1) (.reg 14))) ;;
       .assign 16 (.load (.bin .add (.reg 5) (.reg 14))) ;;
       .assign 17 (.bin .add (.reg 2) (.bin .mul (.reg 15) (.reg 3))) ;;
       .call 18 (lsfBaseDg b + dgIdxGetTail) [.reg 0, .reg 15] ;;
       .call 19 (lsfBaseDg b + dgIdxGetHead) [.reg 0, .reg 15] ;;
       .assign 18 (.bin .sub (.load (.bin .add (.reg 6) (.reg 18))) (.const 1)) ;;
       .assign 19 (.bin .sub (.load (.bin .add (.reg 6) (.reg 19))) (.const 1)) ;;
       .call 13 f_ec
         [.reg 18, .reg 19, .reg 17, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12,
          .reg 3, .reg 15, .reg 16, .reg 13]))
    (P := fun st =>
      CopiesBaseRegs gPtr eListPtr lenArr L_in m0 multPtr vIdxBase
        copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr st ∧
      st.regs 13 = 0 ∧ st.mem = mem0)
    (Inv := Inv)
    stepCost 0 m0 (Nat.zero_le _) hw1 (fun _ => hm0_w)
    hinit
    (fun _ _ _ _ hi => hi.r14)
    (fun _ _ _ _ hi => Expr.eval_reg_of_eq hi.regs.r4)
    hbody
  change Triple w p _ (initTreeCopiesLoopStmt b f_ec) (normalPost (Inv m0)) _ at hloop
  have hret : Triple w p (Inv m0) (.ret (.reg 13))
      (retPost fun u st' => u = M_copies ∧
        (∀ j < m0, ∀ k < mem0 (multPtr + j),
          let q := ((List.range j).map (fun t => mem0 (multPtr + t))).sum + k
          let e := eList.getD j 0
          q < M_copies ∧
          st'.mem (copyTailPtr + q) = mem0 (vIdxBase + G₀.tail e) - 1 ∧
          st'.mem (copyHeadPtr + q) = mem0 (vIdxBase + G₀.head e) - 1 ∧
          st'.mem (copyTailPtr + q) < G₀.n ∧
          vList[st'.mem (copyTailPtr + q)]? = some (G₀.tail e) ∧
          st'.mem (copyHeadPtr + q) < G₀.n ∧
          vList[st'.mem (copyHeadPtr + q)]? = some (G₀.head e) ∧
          (∀ i < L_in, st'.mem (copyLenPtr + q * L_in + i) = mem0 (lenArr + e * L_in + i)) ∧
          st'.mem (copyWtPtr + q * L_in) = 1 ∧
          (∀ i, 0 < i → i < L_in →
            st'.mem (copyWtPtr + q * L_in + i) = mem0 (copyWtPtr + q * L_in + i)) ∧
          st'.mem (copyOrigIdxPtr + q) = e ∧
          st'.mem (copySubIdxPtr + q) = k) ∧
        ∀ a, a < copyTailPtr ∨ copySubIdxPtr + M_copies ≤ a → st'.mem a = mem0 a)
      fun _ => 2 :=
    Triple.ret (fun _ hi => Expr.eval_reg_of_eq (hi.r13.trans hM_eq.symm)) fun st hi =>
      ⟨rfl,
       fun j hj k hk => by
         have hq_lt : ((List.range j).map mults).sum + k < M_copies := by
           have h1 : ((List.range j).map mults).sum + k < ((List.range (j + 1)).map mults).sum := by
             rw [list_range_prefix_succ]
             dsimp only [mults]
             omega
           exact lt_of_lt_of_le h1 (hM_eq ▸ list_range_prefix_mono mults (by omega))
         exact ⟨hq_lt, hi.entries j hj k hk⟩,
       fun a ha => hi.hframe a
         (ha.elim Or.inl fun h => Or.inr (by rw [← hM_eq]; omega))
         (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by rw [← hM_eq]; omega))
         (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by
           rw [← hM_eq]
           have := Nat.mul_le_mul_right L_in (le_refl M_copies)
           omega))
         (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by rw [← hM_eq]; omega))
         (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by rw [← hM_eq]; omega))
         (ha.elim (fun h => Or.inl (by omega)) fun h => Or.inr (by rw [← hM_eq]; omega))⟩
  have hrc : rangeCost stepCost 0 m0 = M_copies * (25 * L_in + 80) + m0 * 170 := by
    dsimp only [stepCost]
    rw [rangeCost_add, rangeCost_const, Nat.sub_zero, rangeCost_zero_eq_range,
      list_map_mul_sum, ← hM_eq]
  refine Triple.conseq (Triple.seq_normal_const hinit_q (Triple.seq_normal_const hloop hret))
    (fun _ hst => hst)
    (fun o st' hpost => by
      cases o with
      | normal => exact False.elim hpost
      | returned u =>
        rcases hpost with ⟨hu, hent, hfr⟩
        exact ⟨vCap, eCap, gPtr, eListPtr, lenArr, L_in, m0, multPtr, vIdxBase,
          copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr, M_copies,
          rfl, hM_eq, hu, hent, hfr⟩)
    fun _ _ => by
      simp only [initTreeCopiesContract, initTreeCopiesCost, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Expr.size]
      rw [hrc, ← hM_eq, Nat.sub_zero]
      omega

end

end MinCostFlow.LSF.Program
