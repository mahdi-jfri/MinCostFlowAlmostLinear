module

public import MinCostFlow.Expander.DecomposeLevelBase

import Mathlib.Tactic.Linarith

/-!
# Level Initialization (`zeroKeptStmt`) and Edge Partitioning (`splitEdgesStmt`)

1. `zeroKeptStmt` & `zeroKept_triple`: clears `keptVert[0..curN)` before the part loop.
2. `splitEdgesStmt` & `splitEdges_triple`: scans `curG.edges` and `curIdx`, assigns level `lvl`
   in `lvlArr[origJ]` to edges whose endpoints satisfy `partId[u] = partId[v] ∧ kept[u] ≠ 0 ∧
   kept[v] ≠ 0`, and writes all remaining edges + original indices to `(nextGAddr, nextIdxAddr)`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

private lemma state_update_regs_eq {st : State} {r v : ℕ} (h : st.regs r = v) :
    { st with regs := Function.update st.regs r v } = st := by
  cases st; dsimp at h; congr 1; funext k; by_cases hk : k = r <;> simp [Function.update, hk, h]

/-! ## 1. `zeroKeptStmt` -/

/-- Zeros `keptVert[0 .. curN)` (`reg 8 + 0..curN-1`). -/
def zeroKeptStmt : Stmt :=
  forRange 19 (.const 0) (.reg 14) (.store (.bin .add (.reg 8) (.reg 19)) (.const 0))

lemma zeroKeptStmt_noRand : zeroKeptStmt.NoRand := by
  simp [zeroKeptStmt, forRange, WordRAM.forUp, Stmt.NoRand]

lemma zeroKept_triple {w : ℕ} (p : Program) (mem : ℕ → ℕ)
    (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr keptVertAddr
      statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr : ℕ)
    (hkv_w : keptVertAddr + curN < 2 ^ w) (hw2 : 1 < 2 ^ w) :
    Triple w p
      (fun st =>
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr st ∧
        st.mem = mem)
      zeroKeptStmt
      (normalPost fun st =>
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr st ∧
        (∀ u < curN, st.mem (keptVertAddr + u) = 0) ∧
        MemFrame mem st.mem keptVertAddr (keptVertAddr + curN))
      (fun _ => 20 * curN + 15) := by
  let Inv : ℕ → State → Prop := fun u st =>
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr st ∧
    st.regs 19 = u ∧
    (∀ t < u, st.mem (keptVertAddr + t) = 0) ∧
    MemFrame mem st.mem keptVertAddr (keptVertAddr + curN)
  have hloop := Triple.forRange_const (p := p) (r := 19) (lo := .const 0) (hi := .reg 14)
    (body := .store (.bin .add (.reg 8) (.reg 19)) (.const 0))
    (P := fun st => LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr st ∧ st.mem = mem)
    (Inv := Inv) 6 0 curN (Nat.zero_le _) hw2 (fun _ => by omega)
    (fun st ⟨hlvl, hm⟩ => ⟨by eval_expr,
      lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]) hlvl,
      by simp, fun _ h => by omega, fun a _ => by rw [hm]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun u _ hult st ω hI => by
      rcases hI with ⟨hlvl, r19, hprev, hfr⟩
      rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
      let st1 : State := { st with mem := Function.update st.mem (keptVertAddr + u) 0 }
      have hst : Runs w p ω (.store (.bin .add (.reg 8) (.reg 19)) (.const 0)) st .normal st1 5 :=
        runs_store_iff.mpr ⟨keptVertAddr + u, 0,
          by simp [Expr.eval, BinOp.eval, r8, r19, show keptVertAddr + u < 2 ^ w by omega],
          by simp [Expr.eval], rfl, rfl, rfl⟩
      refine ⟨.normal, st1, 5, hst, ⟨⟨lvlRegs_of_eq (fun r hr => by
          dsimp only [st1]; rw [Function.update_of_ne (by omega)])
          ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
        by simp, fun t ht => ?_, fun a ha => ?_⟩, by simp [st1, r19]⟩, by dsimp only; omega⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
        · dsimp only [st1]; rw [Function.update_of_ne (by omega)]; exact hprev t hlt
        · dsimp only [st1]; rw [Function.update_self]
      · dsimp only [st1]; rw [Function.update_of_ne (by rcases ha with h | h <;> omega)]; exact hfr a ha)
  refine hloop.conseq (fun _ h => h) (fun o st h => ?_) (fun _ _ => ?_)
  · cases o with
    | returned _ => exact False.elim h
    | normal => exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  · simp only [Expr.size, Nat.sub_zero]; omega

/-! ## 2. Pure Edge-Splitting Helpers and Disjointness -/

/-- Decides whether edge `j` of `curG` lies inside one of the kept parts (via `partId` and
`kept`). -/
def edgeKeptBool (curG : Cited.Graph) (partId kept : ℕ → ℕ) (j : ℕ) : Bool :=
  let e := curG.edges.getD j (0, 0)
  decide (partId e.1 = partId e.2 ∧ kept e.1 ≠ 0 ∧ kept e.2 ≠ 0)

/-- Remaining edges among `curG.edges[0 .. j)` that do NOT fall inside any kept part. -/
def remEdgesPrefix (curG : Cited.Graph) (partId kept : ℕ → ℕ) (j : ℕ) : List (ℕ × ℕ) :=
  ((List.range j).filter fun t => !(edgeKeptBool curG partId kept t)).map
    fun t => curG.edges.getD t (0, 0)

/-- Remaining original edge indices among `curIdx[0 .. j)`. -/
def remIdxPrefix (curG : Cited.Graph) (curIdx : List ℕ) (partId kept : ℕ → ℕ) (j : ℕ) :
    List ℕ :=
  ((List.range j).filter fun t => !(edgeKeptBool curG partId kept t)).map
    fun t => curIdx.getD t 0

/-- Expected value of `lvlArr[a]` after processing `curG.edges[0 .. j)`. -/
def splitLvlVal (mem₀ : ℕ → ℕ) (curG : Cited.Graph) (curIdx : List ℕ) (partId kept : ℕ → ℕ)
    (lvlArrAddr lvl j a : ℕ) : ℕ :=
  if ∃ t < j, curIdx.getD t 0 = a ∧ edgeKeptBool curG partId kept t = true
  then lvl
  else mem₀ (lvlArrAddr + a)

lemma remEdgesPrefix_zero (curG : Cited.Graph) (partId kept : ℕ → ℕ) :
    remEdgesPrefix curG partId kept 0 = [] := by
  simp [remEdgesPrefix]

lemma remIdxPrefix_zero (curG : Cited.Graph) (curIdx : List ℕ) (partId kept : ℕ → ℕ) :
    remIdxPrefix curG curIdx partId kept 0 = [] := by
  simp [remIdxPrefix]

lemma remEdgesPrefix_succ (curG : Cited.Graph) (partId kept : ℕ → ℕ) (j : ℕ) :
    remEdgesPrefix curG partId kept (j + 1) =
      if edgeKeptBool curG partId kept j = true then
        remEdgesPrefix curG partId kept j
      else
        remEdgesPrefix curG partId kept j ++ [curG.edges.getD j (0, 0)] := by
  unfold remEdgesPrefix
  rw [List.range_succ, List.filter_append]
  cases h : edgeKeptBool curG partId kept j <;> simp [h]

lemma remIdxPrefix_succ (curG : Cited.Graph) (curIdx : List ℕ) (partId kept : ℕ → ℕ) (j : ℕ) :
    remIdxPrefix curG curIdx partId kept (j + 1) =
      if edgeKeptBool curG partId kept j = true then
        remIdxPrefix curG curIdx partId kept j
      else
        remIdxPrefix curG curIdx partId kept j ++ [curIdx.getD j 0] := by
  unfold remIdxPrefix
  rw [List.range_succ, List.filter_append]
  cases h : edgeKeptBool curG partId kept j <;> simp [h]

lemma remIdxPrefix_length_eq (curG : Cited.Graph) (curIdx : List ℕ) (partId kept : ℕ → ℕ)
    (j : ℕ) :
    (remIdxPrefix curG curIdx partId kept j).length =
      (remEdgesPrefix curG partId kept j).length := by
  simp [remIdxPrefix, remEdgesPrefix]

lemma remEdgesPrefix_length_le (curG : Cited.Graph) (partId kept : ℕ → ℕ) (j : ℕ) :
    (remEdgesPrefix curG partId kept j).length ≤ j := by
  simpa [remEdgesPrefix] using (List.length_filter_le _ (List.range j)).trans_eq (List.length_range)

lemma remEdgesPrefix_isValid {curG : Cited.Graph} (hV : curG.IsValid) (partId kept : ℕ → ℕ)
    {j : ℕ} (hj : j ≤ curG.m) :
    Cited.Graph.IsValid ⟨curG.n, remEdgesPrefix curG partId kept j⟩ := by
  intro e he
  simp only [remEdgesPrefix, List.mem_map, List.mem_filter, List.mem_range] at he
  rcases he with ⟨t, ⟨ht, _⟩, rfl⟩
  have htm : t < curG.edges.length := by rw [← Cited.Graph.m]; exact lt_of_lt_of_le ht hj
  rw [List.getD_eq_getElem _ _ htm]
  exact hV _ (List.getElem_mem htm)

lemma remIdxPrefix_spec {curG : Cited.Graph} {curIdx : List ℕ} {partId kept : ℕ → ℕ}
    {mCap j : ℕ} (hj : j ≤ curG.m) (hlen : curIdx.length = curG.m) (hnd : curIdx.Nodup)
    (hlt : ∀ a ∈ curIdx, a < mCap) :
    (remIdxPrefix curG curIdx partId kept j).Nodup ∧
    (∀ a ∈ remIdxPrefix curG curIdx partId kept j, a < mCap) ∧
    (∀ t < j, edgeKeptBool curG partId kept t = true →
      curIdx.getD t 0 ∉ remIdxPrefix curG curIdx partId kept j) := by
  have hfilt_nd : ((List.range j).filter fun t => !(edgeKeptBool curG partId kept t)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  refine ⟨?_, ?_, ?_⟩
  · unfold remIdxPrefix
    refine List.Nodup.map_on (fun t₁ ht₁ t₂ ht₂ heq => ?_) hfilt_nd
    simp only [List.mem_filter, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true] at ht₁ ht₂
    have h1 : t₁ < curIdx.length := by omega
    have h2 : t₂ < curIdx.length := by omega
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at heq
    exact (List.Nodup.getElem_inj_iff hnd).mp heq
  · intro a ha
    simp only [remIdxPrefix, List.mem_map, List.mem_filter, List.mem_range] at ha
    rcases ha with ⟨t, ⟨ht, _⟩, rfl⟩
    have htc : t < curIdx.length := by omega
    rw [List.getD_eq_getElem _ _ htc]
    exact hlt _ (List.getElem_mem htc)
  · intro t ht hkept hmem
    simp only [remIdxPrefix, List.mem_map, List.mem_filter, List.mem_range] at hmem
    rcases hmem with ⟨t', ⟨ht', hk'⟩, heq⟩
    have h1 : t < curIdx.length := by omega
    have h2 : t' < curIdx.length := by omega
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at heq
    have htt' : t' = t := (List.Nodup.getElem_inj_iff hnd).mp heq
    subst htt'
    simp [hkept] at hk'

/-- Non-overlapping read/write regions required by `splitEdgesStmt`. -/
def SplitDisjoint (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr bufAddr keptVertAddr
    curN curM mCap : ℕ) : Prop :=
  lvlArrAddr + mCap ≤ curGAddr ∧
  lvlArrAddr + mCap ≤ curIdxAddr ∧
  lvlArrAddr + mCap ≤ nextGAddr ∧
  lvlArrAddr + mCap ≤ nextIdxAddr ∧
  curGAddr + 2 + 2 * curM ≤ bufAddr ∧
  curIdxAddr + curM ≤ bufAddr ∧
  nextGAddr + 2 + 2 * curM ≤ bufAddr ∧
  nextIdxAddr + curM ≤ bufAddr ∧
  (curGAddr + 2 + 2 * curM ≤ nextGAddr ∨ nextGAddr + 2 + 2 * curM ≤ curGAddr) ∧
  (curGAddr + 2 + 2 * curM ≤ nextIdxAddr ∨ nextIdxAddr + curM ≤ curGAddr) ∧
  (curIdxAddr + curM ≤ nextGAddr ∨ nextGAddr + 2 + 2 * curM ≤ curIdxAddr) ∧
  (curIdxAddr + curM ≤ nextIdxAddr ∨ nextIdxAddr + curM ≤ curIdxAddr) ∧
  (nextGAddr + 2 + 2 * curM ≤ nextIdxAddr ∨ nextIdxAddr + curM ≤ nextGAddr) ∧
  bufAddr + 4 * curN ≤ keptVertAddr

/-- Memory agreement outside the three `splitEdgesStmt` write blocks: `lvlArr`, `nextG`, and
`nextIdx`. -/
def SplitMemFrame (mem₀ mem : ℕ → ℕ) (nextGAddr nextIdxAddr lvlArrAddr mCap curM : ℕ) : Prop :=
  ∀ a,
    (a < lvlArrAddr ∨ lvlArrAddr + mCap ≤ a) →
    (a < nextGAddr ∨ nextGAddr + 2 + 2 * curM ≤ a) →
    (a < nextIdxAddr ∨ nextIdxAddr + curM ≤ a) →
    mem a = mem₀ a

/-! ## 3. `splitEdgesStmt` and `splitEdges_triple` -/

/-- Splits edges `0 .. curM - 1` of `curG` between `lvlArr` (for intra-part kept edges) and
`(nextGAddr, nextIdxAddr)` (remaining edges), then writes the `(curN, remM)` header to
`nextGAddr` and leaves `remM` in `reg 20`. -/
def splitEdgesStmt : Stmt :=
  seqStmts
    [ .assign 20 (.const 0)
    , forRange 19 (.const 0) (.reg 15)
        (seqStmts
          [ .assign 21 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 19)))))
          , .assign 22 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 19)))))
          , .assign 23 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.const 3) (.reg 14)) (.reg 21))))
          , .assign 24 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.const 3) (.reg 14)) (.reg 22))))
          , .assign 25 (.load (.bin .add (.reg 1) (.reg 19)))
          , .assign 26 (.const 0)
          , .cond (.bin .eq (.reg 23) (.reg 24))
              (.cond (.load (.bin .add (.reg 8) (.reg 21)))
                (.cond (.load (.bin .add (.reg 8) (.reg 22))) (.assign 26 (.const 1)) .nop)
                .nop)
              .nop
          , .cond (.reg 26)
              (.store (.bin .add (.reg 4) (.reg 25)) (.reg 10))
              (seqStmts
                [ .store (.bin .add (.reg 2) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20)))) (.reg 21)
                , .store (.bin .add (.reg 2) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 20)))) (.reg 22)
                , .store (.bin .add (.reg 3) (.reg 20)) (.reg 25)
                , .assign 20 (.bin .add (.reg 20) (.const 1)) ]) ])
    , .store (.reg 2) (.reg 14)
    , .store (.bin .add (.reg 2) (.const 1)) (.reg 20) ]

lemma splitEdgesStmt_noRand : splitEdgesStmt.NoRand := by
  simp [splitEdgesStmt, forRange, WordRAM.forUp, seqStmts, Stmt.NoRand]

lemma splitEdges_triple {w : ℕ} (p : Program) (mem₀ : ℕ → ℕ) (curG : Cited.Graph)
    (curIdx : List ℕ) (partId kept : ℕ → ℕ)
    (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr keptVertAddr
      statePtr lvl D D_phi mCap csrAddr qAddr lblAddr : ℕ)
    (hV : curG.IsValid) (hga : GraphAt mem₀ curGAddr curG)
    (hidx_len : curIdx.length = curG.m) (hidx_nd : curIdx.Nodup)
    (hidx_lt : ∀ a ∈ curIdx, a < mCap) (hidx_list : ListAt mem₀ curIdxAddr curIdx)
    (hpart_read : ∀ u < curG.n, mem₀ (bufAddr + 3 * curG.n + u) = partId u)
    (hpart_w : ∀ u < curG.n, partId u < 2 ^ w)
    (hkept_read : ∀ u < curG.n, mem₀ (keptVertAddr + u) = kept u)
    (hkept_w : ∀ u < curG.n, kept u < 2 ^ w)
    (hdj : SplitDisjoint curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr bufAddr keptVertAddr
      curG.n curG.m mCap)
    (_hlvl_w : lvl < 2 ^ w) (hmCap_w : mCap < 2 ^ w) (hcurM_w : curG.m < 2 ^ w)
    (hm_next_w : nextGAddr + 2 + 2 * curG.m < 2 ^ w) (_hcur_n_w : 4 * curG.n < 2 ^ w)
    (hkept_w_addr : keptVertAddr + curG.n < 2 ^ w)
    (hlvl_w_addr : lvlArrAddr + mCap < 2 ^ w) (hbuf_w_addr : bufAddr + 4 * curG.n < 2 ^ w)
    (hw2 : 1 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    Triple w p
      (fun st =>
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
        st.mem = mem₀)
      splitEdgesStmt
      (normalPost fun st =>
        let remE := remEdgesPrefix curG partId kept curG.m
        let remI := remIdxPrefix curG curIdx partId kept curG.m
        let remG : Cited.Graph := ⟨curG.n, remE⟩
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
        st.regs 20 = remE.length ∧
        remE.length ≤ curG.m ∧
        remG.IsValid ∧
        GraphAt st.mem nextGAddr remG ∧
        ListAt st.mem nextIdxAddr remI ∧
        remI.length = remG.m ∧
        remI.Nodup ∧
        (∀ a ∈ remI, a < mCap) ∧
        (∀ a < mCap, st.mem (lvlArrAddr + a) =
          splitLvlVal mem₀ curG curIdx partId kept lvlArrAddr lvl curG.m a) ∧
        SplitMemFrame mem₀ st.mem nextGAddr nextIdxAddr lvlArrAddr mCap curG.m)
      (fun _ => 125 * curG.m + 25) := by
  have hw2_lt : 2 < 2 ^ w := by omega
  have hw3_lt : 3 < 2 ^ w := by omega
  rcases hdj with ⟨hlcG, hlcI, hlnG, hlnI, hcGb, hcIb, hnGb, hnIb, hcnG, hcnI, hcinG, hcinI, hnnGI, hbk⟩
  -- Init: `reg 20 := 0`
  let S0 : State → Prop := fun st =>
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 20 = 0 ∧ st.mem = mem₀
  have hinit20 : Triple w p
      (fun st => LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
        keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧ st.mem = mem₀)
      (.assign 20 (.const 0)) (normalPost S0) (fun _ => 2) := by
    intro st ω ⟨hlvl, hm⟩
    rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
    refine ⟨.normal, { st with regs := Function.update st.regs 20 0 }, 2,
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩,
      ⟨lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)])
          ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
        by simp, hm⟩, le_rfl⟩
  -- Loop over `j = 0 .. curG.m - 1`
  let LoopInv : ℕ → State → Prop := fun j st =>
    let remE := remEdgesPrefix curG partId kept j
    let remI := remIdxPrefix curG curIdx partId kept j
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 19 = j ∧ st.regs 20 = remE.length ∧
    (∀ (t : ℕ) (ht : t < remE.length),
      st.mem (nextGAddr + 2 + 2 * t) = remE[t].1 ∧
      st.mem (nextGAddr + 3 + 2 * t) = remE[t].2) ∧
    (∀ t (ht : t < remI.length), st.mem (nextIdxAddr + t) = remI[t]) ∧
    (∀ a < mCap, st.mem (lvlArrAddr + a) =
      splitLvlVal mem₀ curG curIdx partId kept lvlArrAddr lvl j a) ∧
    SplitMemFrame mem₀ st.mem nextGAddr nextIdxAddr lvlArrAddr mCap curG.m
  let body : Stmt := seqStmts
    [ .assign 21 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 19)))))
    , .assign 22 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 19)))))
    , .assign 23 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.const 3) (.reg 14)) (.reg 21))))
    , .assign 24 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.const 3) (.reg 14)) (.reg 22))))
    , .assign 25 (.load (.bin .add (.reg 1) (.reg 19)))
    , .assign 26 (.const 0)
    , .cond (.bin .eq (.reg 23) (.reg 24))
        (.cond (.load (.bin .add (.reg 8) (.reg 21)))
          (.cond (.load (.bin .add (.reg 8) (.reg 22))) (.assign 26 (.const 1)) .nop)
          .nop)
        .nop
    , .cond (.reg 26)
        (.store (.bin .add (.reg 4) (.reg 25)) (.reg 10))
        (seqStmts
          [ .store (.bin .add (.reg 2) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20)))) (.reg 21)
          , .store (.bin .add (.reg 2) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 20)))) (.reg 22)
          , .store (.bin .add (.reg 3) (.reg 20)) (.reg 25)
          , .assign 20 (.bin .add (.reg 20) (.const 1)) ]) ]
  have hloop := Triple.forRange_const (p := p) (r := 19) (lo := .const 0) (hi := .reg 15)
    (body := body) (P := S0) (Inv := LoopInv) 105 0 curG.m (Nat.zero_le _) hw2 (fun _ => hcurM_w)
    (fun st ⟨hlvl, r20, hm⟩ => by
      refine ⟨by eval_expr,
        lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]) hlvl,
        by simp, by simpa [remEdgesPrefix_zero] using r20,
        fun t ht => by simp [remEdgesPrefix_zero] at ht,
        fun t ht => by simp [remIdxPrefix_zero] at ht,
        fun a _ => by simp [splitLvlVal, hm],
        fun a _ _ _ => by rw [hm]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun j _ hjlt st ω hI => by
      rcases hI with ⟨hlvl, r19, r20, hnextG_e, hnextI, hlvl_prev, hfr⟩
      rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
      set remE := remEdgesPrefix curG partId kept j
      set remI := remIdxPrefix curG curIdx partId kept j
      set cnt := remE.length
      have hcnt_le : cnt ≤ j := remEdgesPrefix_length_le curG partId kept j
      have hj_e : j < curG.edges.length := hjlt
      have hj_idx : j < curIdx.length := by omega
      set u := curG.edges[j].1
      set v := curG.edges[j].2
      set origJ := curIdx[j]
      rcases hV _ (List.getElem_mem hj_e) with ⟨hu_n, hv_n⟩
      have horig_lt : origJ < mCap := hidx_lt _ (List.getElem_mem hj_idx)
      have hgd_e : curG.edges.getD j (0, 0) = (u, v) := by
        rw [List.getD_eq_getElem _ _ hj_e]
      have hgd_i : curIdx.getD j 0 = origJ := List.getD_eq_getElem _ _ hj_idx
      have hu_mem : st.mem (curGAddr + 2 + 2 * j) = u := by
        rw [hfr _ (by omega) (by rcases hcnG with h | h <;> omega) (by rcases hcnI with h | h <;> omega)]
        exact graphAt_edge_fst hga hj_e
      have hv_mem : st.mem (curGAddr + 3 + 2 * j) = v := by
        rw [hfr _ (by omega) (by rcases hcnG with h | h <;> omega) (by rcases hcnI with h | h <;> omega)]
        exact graphAt_edge_snd hga hj_e
      have hpu_mem : st.mem (bufAddr + 3 * curG.n + u) = partId u := by
        rw [hfr _ (by omega) (by omega) (by omega)]; exact hpart_read u hu_n
      have hpv_mem : st.mem (bufAddr + 3 * curG.n + v) = partId v := by
        rw [hfr _ (by omega) (by omega) (by omega)]; exact hpart_read v hv_n
      have hidx_mem : st.mem (curIdxAddr + j) = origJ := by
        rw [hfr _ (by omega) (by rcases hcinG with h | h <;> omega) (by rcases hcinI with h | h <;> omega)]
        exact hidx_list.getElem hj_idx
      have hku_mem : st.mem (keptVertAddr + u) = kept u := by
        rw [hfr _ (by omega) (by omega) (by omega)]; exact hkept_read u hu_n
      have hkv_mem : st.mem (keptVertAddr + v) = kept v := by
        rw [hfr _ (by omega) (by omega) (by omega)]; exact hkept_read v hv_n
      have hu_w : u < 2 ^ w := by omega
      have hv_w : v < 2 ^ w := by omega
      have hpu_w : partId u < 2 ^ w := hpart_w u hu_n
      have hpv_w : partId v < 2 ^ w := hpart_w v hv_n
      have horig_w : origJ < 2 ^ w := by omega
      have hku_w : kept u < 2 ^ w := hkept_w u hu_n
      have hkv_w : kept v < 2 ^ w := hkept_w v hv_n
      let s1 : State := { st with regs := Function.update st.regs 21 u }
      let s2 : State := { s1 with regs := Function.update s1.regs 22 v }
      let s3 : State := { s2 with regs := Function.update s2.regs 23 (partId u) }
      let s4 : State := { s3 with regs := Function.update s3.regs 24 (partId v) }
      let s5 : State := { s4 with regs := Function.update s4.regs 25 origJ }
      let s6 : State := { s5 with regs := Function.update s5.regs 26 0 }
      have ha1 : Runs w p ω
          (.assign 21 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 19))))))
          st .normal s1 9 :=
        runs_assign_iff.mpr ⟨u, by
          simp [Expr.eval, BinOp.eval, hw2_lt, r0, r19, show 2 * j < 2 ^ w by omega,
            show 2 + 2 * j < 2 ^ w by omega, show curGAddr + (2 + 2 * j) = curGAddr + 2 + 2 * j by omega,
            show curGAddr + 2 + 2 * j < 2 ^ w by omega, hu_mem],
          rfl, rfl, rfl⟩
      have ha2 : Runs w p ω
          (.assign 22 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 19))))))
          s1 .normal s2 9 :=
        runs_assign_iff.mpr ⟨v, by
          simp [s1, Expr.eval, BinOp.eval, hw2_lt, hw3_lt, r0, r19, show 2 * j < 2 ^ w by omega,
            show 3 + 2 * j < 2 ^ w by omega, show curGAddr + (3 + 2 * j) = curGAddr + 3 + 2 * j by omega,
            show curGAddr + 3 + 2 * j < 2 ^ w by omega, hv_mem],
          rfl, rfl, rfl⟩
      have ha3 : Runs w p ω
          (.assign 23 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.const 3) (.reg 14)) (.reg 21)))))
          s2 .normal s3 9 :=
        runs_assign_iff.mpr ⟨partId u, by
          simp [s2, s1, Expr.eval, BinOp.eval, hw3_lt, r6, r14, show 3 * curG.n < 2 ^ w by omega,
            show 3 * curG.n + u < 2 ^ w by omega,
            show bufAddr + (3 * curG.n + u) = bufAddr + 3 * curG.n + u by omega,
            show bufAddr + 3 * curG.n + u < 2 ^ w by omega, hpu_mem],
          rfl, rfl, rfl⟩
      have ha4 : Runs w p ω
          (.assign 24 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.const 3) (.reg 14)) (.reg 22)))))
          s3 .normal s4 9 :=
        runs_assign_iff.mpr ⟨partId v, by
          simp [s3, s2, s1, Expr.eval, BinOp.eval, hw3_lt, r6, r14, show 3 * curG.n < 2 ^ w by omega,
            show 3 * curG.n + v < 2 ^ w by omega,
            show bufAddr + (3 * curG.n + v) = bufAddr + 3 * curG.n + v by omega,
            show bufAddr + 3 * curG.n + v < 2 ^ w by omega, hpv_mem],
          rfl, rfl, rfl⟩
      have ha5 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 1) (.reg 19)))) s4 .normal s5 5 :=
        runs_assign_iff.mpr ⟨origJ, by
          simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, r1, r19,
            show curIdxAddr + j < 2 ^ w by omega, hidx_mem],
          rfl, rfl, rfl⟩
      have ha6 : Runs w p ω (.assign 26 (.const 0)) s5 .normal s6 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
      -- Condition evaluation into `reg 26`
      let flagVal : ℕ := if edgeKeptBool curG partId kept j = true then 1 else 0
      let s7 : State := { s6 with regs := Function.update s6.regs 26 flagVal }
      have hs6_23 : s6.regs 23 = partId u := by simp [s6, s5, s4, s3]
      have hs6_24 : s6.regs 24 = partId v := by simp [s6, s5, s4]
      have hs6_21 : s6.regs 21 = u := by simp [s6, s5, s4, s3, s2, s1]
      have hs6_22 : s6.regs 22 = v := by simp [s6, s5, s4, s3, s2]
      have hs6_8 : s6.regs 8 = keptVertAddr := by simp [s6, s5, s4, s3, s2, s1, r8]
      have hs6_mem : s6.mem = st.mem := rfl
      have hflag_run : ∃ c7, Runs w p ω
          (.cond (.bin .eq (.reg 23) (.reg 24))
            (.cond (.load (.bin .add (.reg 8) (.reg 21)))
              (.cond (.load (.bin .add (.reg 8) (.reg 22))) (.assign 26 (.const 1)) .nop)
              .nop)
            .nop) s6 .normal s7 c7 ∧ c7 ≤ 18 := by
        have hk_eq : edgeKeptBool curG partId kept j = decide (partId u = partId v ∧ kept u ≠ 0 ∧ kept v ≠ 0) := by
          dsimp only [edgeKeptBool]; rw [hgd_e]
        by_cases hp : partId u = partId v
        · have hev1 : (Expr.bin .eq (.reg 23) (.reg 24)).eval w s6 = some 1 := by
            simp [Expr.eval, BinOp.eval, hs6_23, hs6_24, hp, hw2]
          by_cases hku : kept u = 0
          · have hk_f : edgeKeptBool curG partId kept j = false := by simp [hk_eq, hku]
            have hf0 : flagVal = 0 := by simp [flagVal, hk_f]
            have hs7_eq : s7 = s6 := by dsimp [s7]; rw [hf0]; exact state_update_regs_eq (by simp [s6])
            have hev2 : (Expr.load (.bin .add (.reg 8) (.reg 21))).eval w s6 = some 0 := by
              simp [Expr.eval, BinOp.eval, hs6_8, hs6_21, hs6_mem, show keptVertAddr + u < 2 ^ w by omega, hku_mem, hku]
            have hc2 : Runs w p ω (.cond (.load (.bin .add (.reg 8) (.reg 21)))
                (.cond (.load (.bin .add (.reg 8) (.reg 22))) (.assign 26 (.const 1)) .nop) .nop)
                s6 .normal s6 6 :=
              runs_cond_iff.mpr ⟨0, 1, hev2, by simp [runs_nop_iff], rfl⟩
            refine ⟨10, ?_, by omega⟩
            rw [hs7_eq]
            exact runs_cond_iff.mpr ⟨1, 6, hev1, by simp [hc2], rfl⟩
          · have hev2 : (Expr.load (.bin .add (.reg 8) (.reg 21))).eval w s6 = some (kept u) := by
              simp [Expr.eval, BinOp.eval, hs6_8, hs6_21, hs6_mem, show keptVertAddr + u < 2 ^ w by omega, hku_mem]
            by_cases hkv : kept v = 0
            · have hk_f : edgeKeptBool curG partId kept j = false := by simp [hk_eq, hkv]
              have hf0 : flagVal = 0 := by simp [flagVal, hk_f]
              have hs7_eq : s7 = s6 := by dsimp [s7]; rw [hf0]; exact state_update_regs_eq (by simp [s6])
              have hev3 : (Expr.load (.bin .add (.reg 8) (.reg 22))).eval w s6 = some 0 := by
                simp [Expr.eval, BinOp.eval, hs6_8, hs6_22, hs6_mem, show keptVertAddr + v < 2 ^ w by omega, hkv_mem, hkv]
              have hc3 : Runs w p ω (.cond (.load (.bin .add (.reg 8) (.reg 22))) (.assign 26 (.const 1)) .nop)
                  s6 .normal s6 6 :=
                runs_cond_iff.mpr ⟨0, 1, hev3, by simp [runs_nop_iff], rfl⟩
              have hc2 : Runs w p ω (.cond (.load (.bin .add (.reg 8) (.reg 21)))
                  (.cond (.load (.bin .add (.reg 8) (.reg 22))) (.assign 26 (.const 1)) .nop) .nop)
                  s6 .normal s6 11 :=
                runs_cond_iff.mpr ⟨kept u, 6, hev2, by simp [hku, hc3], rfl⟩
              refine ⟨15, ?_, by omega⟩
              rw [hs7_eq]
              exact runs_cond_iff.mpr ⟨1, 11, hev1, by simp [hc2], rfl⟩
            · have hk_t : edgeKeptBool curG partId kept j = true := by simp [hk_eq, hp, hku, hkv]
              have hf1 : flagVal = 1 := by simp [flagVal, hk_t]
              have ha1' : Runs w p ω (.assign 26 (.const 1)) s6 .normal s7 2 :=
                runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw2], rfl, by dsimp [s7]; rw [hf1], rfl⟩
              have hev3 : (Expr.load (.bin .add (.reg 8) (.reg 22))).eval w s6 = some (kept v) := by
                simp [Expr.eval, BinOp.eval, hs6_8, hs6_22, hs6_mem, show keptVertAddr + v < 2 ^ w by omega, hkv_mem]
              have hc3 : Runs w p ω (.cond (.load (.bin .add (.reg 8) (.reg 22))) (.assign 26 (.const 1)) .nop)
                  s6 .normal s7 7 :=
                runs_cond_iff.mpr ⟨kept v, 2, hev3, by simp [hkv, ha1'], rfl⟩
              have hc2 : Runs w p ω (.cond (.load (.bin .add (.reg 8) (.reg 21)))
                  (.cond (.load (.bin .add (.reg 8) (.reg 22))) (.assign 26 (.const 1)) .nop) .nop)
                  s6 .normal s7 12 :=
                runs_cond_iff.mpr ⟨kept u, 7, hev2, by simp [hku, hc3], rfl⟩
              refine ⟨16, ?_, by omega⟩
              exact runs_cond_iff.mpr ⟨1, 12, hev1, by simp [hc2], rfl⟩
        · have hk_f : edgeKeptBool curG partId kept j = false := by simp [hk_eq, hp]
          have hf0 : flagVal = 0 := by simp [flagVal, hk_f]
          have hs7_eq : s7 = s6 := by dsimp [s7]; rw [hf0]; exact state_update_regs_eq (by simp [s6])
          have hev1 : (Expr.bin .eq (.reg 23) (.reg 24)).eval w s6 = some 0 := by
            simp [Expr.eval, BinOp.eval, hs6_23, hs6_24, hp]
          refine ⟨5, ?_, by omega⟩
          rw [hs7_eq]
          exact runs_cond_iff.mpr ⟨0, 1, hev1, by simp [runs_nop_iff], rfl⟩
      rcases hflag_run with ⟨c7, hr7, hc7⟩
      -- Branch on `reg 26`
      have hs7_regs : ∀ r < 20, s7.regs r = st.regs r := fun r hr => by
        dsimp [s7, s6, s5, s4, s3, s2, s1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
      have hs7_20 : s7.regs 20 = cnt := by
        dsimp [s7, s6, s5, s4, s3, s2, s1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), r20]
      have hs7_21 : s7.regs 21 = u := by simp [s7, hs6_21]
      have hs7_22 : s7.regs 22 = v := by simp [s7, hs6_22]
      have hs7_25 : s7.regs 25 = origJ := by simp [s7, s6, s5]
      have hs7_4 : s7.regs 4 = lvlArrAddr := by rw [hs7_regs 4 (by omega), r4]
      have hs7_10 : s7.regs 10 = lvl := by rw [hs7_regs 10 (by omega), r10]
      have hs7_2 : s7.regs 2 = nextGAddr := by rw [hs7_regs 2 (by omega), r2]
      have hs7_3 : s7.regs 3 = nextIdxAddr := by rw [hs7_regs 3 (by omega), r3]
      have hs7_mem : s7.mem = st.mem := rfl
      have hbranch : ∃ s8 c8, Runs w p ω
          (.cond (.reg 26)
            (.store (.bin .add (.reg 4) (.reg 25)) (.reg 10))
            (seqStmts
              [ .store (.bin .add (.reg 2) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20)))) (.reg 21)
              , .store (.bin .add (.reg 2) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 20)))) (.reg 22)
              , .store (.bin .add (.reg 3) (.reg 20)) (.reg 25)
              , .assign 20 (.bin .add (.reg 20) (.const 1)) ])) s7 .normal s8 c8 ∧
          c8 ≤ 32 ∧ LoopInv (j + 1) { s8 with regs := Function.update s8.regs 19 (j + 1) } ∧
          s8.regs 19 = j := by
        by_cases hkept_j : edgeKeptBool curG partId kept j = true
        · have hf1 : flagVal = 1 := by simp [flagVal, hkept_j]
          have hs7_26 : s7.regs 26 = 1 := by simp [s7, hf1]
          let s8 : State := { s7 with mem := Function.update s7.mem (lvlArrAddr + origJ) lvl }
          have hst_lvl : Runs w p ω (.store (.bin .add (.reg 4) (.reg 25)) (.reg 10)) s7 .normal s8 5 :=
            runs_store_iff.mpr ⟨lvlArrAddr + origJ, lvl,
              by simp [Expr.eval, BinOp.eval, hs7_4, hs7_25, show lvlArrAddr + origJ < 2 ^ w by omega],
              by simp [Expr.eval, hs7_10], rfl, rfl, rfl⟩
          have hcond_26 : Runs w p ω
              (.cond (.reg 26)
                (.store (.bin .add (.reg 4) (.reg 25)) (.reg 10))
                (seqStmts
                  [ .store (.bin .add (.reg 2) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20)))) (.reg 21)
                  , .store (.bin .add (.reg 2) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 20)))) (.reg 22)
                  , .store (.bin .add (.reg 3) (.reg 20)) (.reg 25)
                  , .assign 20 (.bin .add (.reg 20) (.const 1)) ])) s7 .normal s8 7 :=
            runs_cond_iff.mpr ⟨1, 5, by simp [Expr.eval, hs7_26], by simpa using hst_lvl, rfl⟩
          refine ⟨s8, 7, hcond_26, by omega, ?_, by simp [s8, hs7_regs 19 (by omega), r19]⟩
          refine ⟨lvlRegs_of_eq (fun r hr => by
              dsimp only [s8]; rw [Function.update_of_ne (by omega)]; exact hs7_regs r (by omega))
              ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
            by simp, by simp [remEdgesPrefix_succ, hkept_j, s8, hs7_20, remE, cnt],
            fun t ht => ?_, fun t ht => ?_, fun a ha => ?_, fun a ha1 ha2 ha3 => ?_⟩
          · have ht' : t < remE.length := by simpa [remEdgesPrefix_succ, hkept_j, remE] using ht
            dsimp only [s8, remEdgesPrefix_succ]
            simp only [remEdgesPrefix_succ, hkept_j, ↓reduceIte, hs7_mem]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hnextG_e t ht'
          · have ht' : t < remI.length := by simpa [remIdxPrefix_succ, hkept_j, remI] using ht
            dsimp only [s8]
            simp only [remIdxPrefix_succ, hkept_j, ↓reduceIte, hs7_mem]
            rw [Function.update_of_ne (by omega)]
            exact hnextI t ht'
          · dsimp only [s8]
            rw [hs7_mem]
            by_cases ha_eq : a = origJ
            · subst ha_eq
              rw [Function.update_self]
              have hex : ∃ t < j + 1, curIdx.getD t 0 = origJ ∧ edgeKeptBool curG partId kept t = true :=
                ⟨j, Nat.lt_succ_self j, hgd_i, hkept_j⟩
              simp only [splitLvlVal, hex, ↓reduceIte]
            · rw [Function.update_of_ne (by omega), hlvl_prev a ha]
              have hiff : (∃ t < j + 1, curIdx.getD t 0 = a ∧ edgeKeptBool curG partId kept t = true) ↔
                  (∃ t < j, curIdx.getD t 0 = a ∧ edgeKeptBool curG partId kept t = true) := by
                constructor
                · rintro ⟨t, htj, hta, hkt⟩
                  rcases Nat.lt_succ_iff_lt_or_eq.mp htj with hlt | rfl
                  · exact ⟨t, hlt, hta, hkt⟩
                  · exact absurd (hta.symm.trans hgd_i) ha_eq
                · rintro ⟨t, htj, hta, hkt⟩
                  exact ⟨t, Nat.lt_succ_of_lt htj, hta, hkt⟩
              simp only [splitLvlVal, hiff]
          · dsimp only [s8]; rw [Function.update_of_ne (by omega), hs7_mem]
            exact hfr a ha1 ha2 ha3
        · have hk_f : edgeKeptBool curG partId kept j = false := Bool.eq_false_iff.mpr hkept_j
          have hf0 : flagVal = 0 := by simp [flagVal, hk_f]
          have hs7_26 : s7.regs 26 = 0 := by simp [s7, hf0]
          let m1 : ℕ → ℕ := Function.update s7.mem (nextGAddr + 2 + 2 * cnt) u
          let m2 : ℕ → ℕ := Function.update m1 (nextGAddr + 3 + 2 * cnt) v
          let m3 : ℕ → ℕ := Function.update m2 (nextIdxAddr + cnt) origJ
          let s8a : State := { s7 with mem := m1 }
          let s8b : State := { s7 with mem := m2 }
          let s8c : State := { s7 with mem := m3 }
          let s8 : State := { s8c with regs := Function.update s8c.regs 20 (cnt + 1) }
          have hs8_1 : Runs w p ω
              (.store (.bin .add (.reg 2) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20)))) (.reg 21))
              s7 .normal s8a 9 :=
            runs_store_iff.mpr ⟨nextGAddr + 2 + 2 * cnt, u,
              by simp [Expr.eval, BinOp.eval, hw2_lt, hs7_2, hs7_20, show 2 * cnt < 2 ^ w by omega,
                show 2 + 2 * cnt < 2 ^ w by omega,
                show nextGAddr + (2 + 2 * cnt) = nextGAddr + 2 + 2 * cnt by omega,
                show nextGAddr + 2 + 2 * cnt < 2 ^ w by omega],
              by simp [Expr.eval, hs7_21], rfl, rfl, rfl⟩
          have hs8_2 : Runs w p ω
              (.store (.bin .add (.reg 2) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 20)))) (.reg 22))
              s8a .normal s8b 9 :=
            runs_store_iff.mpr ⟨nextGAddr + 3 + 2 * cnt, v,
              by simp [s8a, Expr.eval, BinOp.eval, hw2_lt, hw3_lt, hs7_2, hs7_20,
                show 2 * cnt < 2 ^ w by omega, show 3 + 2 * cnt < 2 ^ w by omega,
                show nextGAddr + (3 + 2 * cnt) = nextGAddr + 3 + 2 * cnt by omega,
                show nextGAddr + 3 + 2 * cnt < 2 ^ w by omega],
              by simp [s8a, Expr.eval, hs7_22], rfl, rfl, rfl⟩
          have hs8_3 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 20)) (.reg 25))
              s8b .normal s8c 5 :=
            runs_store_iff.mpr ⟨nextIdxAddr + cnt, origJ,
              by simp [s8b, Expr.eval, BinOp.eval, hs7_3, hs7_20, show nextIdxAddr + cnt < 2 ^ w by omega],
              by simp [s8b, Expr.eval, hs7_25], rfl, rfl, rfl⟩
          have ha8_20 : Runs w p ω (.assign 20 (.bin .add (.reg 20) (.const 1))) s8c .normal s8 4 :=
            runs_assign_iff.mpr ⟨cnt + 1,
              by simp [s8c, Expr.eval, BinOp.eval, hw2, hs7_20, show cnt + 1 < 2 ^ w by omega],
              rfl, rfl, rfl⟩
          have hseq8 : Runs w p ω
              (seqStmts
                [ .store (.bin .add (.reg 2) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20)))) (.reg 21)
                , .store (.bin .add (.reg 2) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 20)))) (.reg 22)
                , .store (.bin .add (.reg 3) (.reg 20)) (.reg 25)
                , .assign 20 (.bin .add (.reg 20) (.const 1)) ]) s7 .normal s8 30 :=
            runs_seq_iff.mpr (Or.inr ⟨s8a, 9, _, hs8_1,
              runs_seq_iff.mpr (Or.inr ⟨s8b, 9, _, hs8_2,
                runs_seq_iff.mpr (Or.inr ⟨s8c, 5, 4, hs8_3, ha8_20, rfl⟩), rfl⟩), rfl⟩)
          have hcond_26 : Runs w p ω
              (.cond (.reg 26)
                (.store (.bin .add (.reg 4) (.reg 25)) (.reg 10))
                (seqStmts
                  [ .store (.bin .add (.reg 2) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20)))) (.reg 21)
                  , .store (.bin .add (.reg 2) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 20)))) (.reg 22)
                  , .store (.bin .add (.reg 3) (.reg 20)) (.reg 25)
                  , .assign 20 (.bin .add (.reg 20) (.const 1)) ])) s7 .normal s8 32 :=
            runs_cond_iff.mpr ⟨0, 30, by simp [Expr.eval, hs7_26], by simpa using hseq8, rfl⟩
          refine ⟨s8, 32, hcond_26, le_rfl, ?_, by simp [s8, s8c, hs7_regs 19 (by omega), r19]⟩
          have hlen_succ_e : (remEdgesPrefix curG partId kept (j + 1)).length = cnt + 1 := by
            simp [remEdgesPrefix_succ, hk_f, remE, cnt]
          have hlen_remI_cnt : remI.length = cnt := remIdxPrefix_length_eq curG curIdx partId kept j
          refine ⟨lvlRegs_of_eq (fun r hr => by
              dsimp only [s8, s8c]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hs7_regs r (by omega))
              ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
            by simp, by simp [s8, s8c, hlen_succ_e], fun t ht => ?_, fun t ht => ?_,
            fun a ha => ?_, fun a ha1 ha2 ha3 => ?_⟩
          · dsimp only [s8, s8c, m3, m2, m1]; rw [hs7_mem]
            have ht' : t < cnt + 1 := hlen_succ_e ▸ ht
            simp only [remEdgesPrefix_succ, hk_f, Bool.false_eq_true, ↓reduceIte, hgd_e]
            rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with hlt | rfl
            · refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne (by rcases hnnGI with h | h <;> omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  List.getElem_append_left hlt]
                exact (hnextG_e t hlt).1
              · rw [Function.update_of_ne (by rcases hnnGI with h | h <;> omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  List.getElem_append_left hlt]
                exact (hnextG_e t hlt).2
            · refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne (by rcases hnnGI with h | h <;> omega),
                  Function.update_of_ne (by omega), Function.update_self,
                  List.getElem_append_right (le_refl _)]
                simp
              · rw [Function.update_of_ne (by rcases hnnGI with h | h <;> omega),
                  Function.update_self, List.getElem_append_right (le_refl _)]
                simp
          · dsimp only [s8, s8c, m3, m2, m1]; rw [hs7_mem]
            simp only [remIdxPrefix_succ, hk_f, Bool.false_eq_true, ↓reduceIte, hgd_i] at ht ⊢
            change t < (remI ++ [origJ]).length at ht
            change _ = (remI ++ [origJ])[t]
            rw [List.length_append, List.length_singleton, hlen_remI_cnt] at ht
            rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
            · have hltI : t < remI.length := hlt.trans_eq hlen_remI_cnt.symm
              rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by rcases hnnGI with h | h <;> omega),
                Function.update_of_ne (by rcases hnnGI with h | h <;> omega),
                List.getElem_append_left hltI]
              exact hnextI t hltI
            · rw [Function.update_self, List.getElem_append_right hlen_remI_cnt.le]
              simp [hlen_remI_cnt]
          · dsimp only [s8, s8c, m3, m2, m1]; rw [hs7_mem]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), hlvl_prev a ha]
            have hiff : (∃ t < j + 1, curIdx.getD t 0 = a ∧ edgeKeptBool curG partId kept t = true) ↔
                (∃ t < j, curIdx.getD t 0 = a ∧ edgeKeptBool curG partId kept t = true) := by
              constructor
              · rintro ⟨t, htj, hta, hkt⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp htj with hlt | rfl
                · exact ⟨t, hlt, hta, hkt⟩
                · exact absurd hkt (by simp [hk_f])
              · rintro ⟨t, htj, hta, hkt⟩
                exact ⟨t, Nat.lt_succ_of_lt htj, hta, hkt⟩
            simp only [splitLvlVal, hiff]
          · dsimp only [s8, s8c, m3, m2, m1]; rw [hs7_mem]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hfr a ha1 ha2 ha3
      rcases hbranch with ⟨s8, c8, hr8, hc8, hinv8, hr8_19⟩
      have hseq_j : Runs w p ω body st .normal s8
          (9 + (9 + (9 + (9 + (5 + (2 + (c7 + c8 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 9, _, ha1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 9, _, ha2,
            runs_seq_iff.mpr (Or.inr ⟨s3, 9, _, ha3,
              runs_seq_iff.mpr (Or.inr ⟨s4, 9, _, ha4,
                runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, ha5,
                  runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, ha6,
                    runs_seq_iff.mpr (Or.inr ⟨s7, c7, c8, hr7, hr8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      exact ⟨.normal, s8, _, hseq_j, ⟨hinv8, hr8_19⟩, by dsimp only; omega⟩)
  -- Final header stores at `nextGAddr` and `nextGAddr + 1`
  let Stail_pre : State → Prop := fun st =>
    let remE := remEdgesPrefix curG partId kept curG.m
    let remI := remIdxPrefix curG curIdx partId kept curG.m
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 20 = remE.length ∧
    (∀ (t : ℕ) (ht : t < remE.length),
      st.mem (nextGAddr + 2 + 2 * t) = remE[t].1 ∧
      st.mem (nextGAddr + 3 + 2 * t) = remE[t].2) ∧
    (∀ t (ht : t < remI.length), st.mem (nextIdxAddr + t) = remI[t]) ∧
    (∀ a < mCap, st.mem (lvlArrAddr + a) =
      splitLvlVal mem₀ curG curIdx partId kept lvlArrAddr lvl curG.m a) ∧
    SplitMemFrame mem₀ st.mem nextGAddr nextIdxAddr lvlArrAddr mCap curG.m
  have htail : Triple w p Stail_pre
      (seqStmts [ .store (.reg 2) (.reg 14), .store (.bin .add (.reg 2) (.const 1)) (.reg 20) ])
      (normalPost fun st =>
        let remE := remEdgesPrefix curG partId kept curG.m
        let remI := remIdxPrefix curG curIdx partId kept curG.m
        let remG : Cited.Graph := ⟨curG.n, remE⟩
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
        st.regs 20 = remE.length ∧
        remE.length ≤ curG.m ∧
        remG.IsValid ∧
        GraphAt st.mem nextGAddr remG ∧
        ListAt st.mem nextIdxAddr remI ∧
        remI.length = remG.m ∧
        remI.Nodup ∧
        (∀ a ∈ remI, a < mCap) ∧
        (∀ a < mCap, st.mem (lvlArrAddr + a) =
          splitLvlVal mem₀ curG curIdx partId kept lvlArrAddr lvl curG.m a) ∧
        SplitMemFrame mem₀ st.mem nextGAddr nextIdxAddr lvlArrAddr mCap curG.m)
      (fun _ => 10) := by
    intro st ω ⟨hlvl, r20, hnextG_e, hnextI, hlvl_arr, hfr⟩
    rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
    set remE := remEdgesPrefix curG partId kept curG.m
    set remI := remIdxPrefix curG curIdx partId kept curG.m
    have hrem_le : remE.length ≤ curG.m := remEdgesPrefix_length_le curG partId kept curG.m
    let s1 : State := { st with mem := Function.update st.mem nextGAddr curG.n }
    let s2 : State := { s1 with mem := Function.update s1.mem (nextGAddr + 1) remE.length }
    have hs1 : Runs w p ω (.store (.reg 2) (.reg 14)) st .normal s1 3 :=
      runs_store_iff.mpr ⟨nextGAddr, curG.n,
        by simp [Expr.eval, r2], by simp [Expr.eval, r14], rfl, rfl, rfl⟩
    have hs2 : Runs w p ω (.store (.bin .add (.reg 2) (.const 1)) (.reg 20)) s1 .normal s2 5 :=
      runs_store_iff.mpr ⟨nextGAddr + 1, remE.length,
        by simp [s1, Expr.eval, BinOp.eval, hw2, r2, show nextGAddr + 1 < 2 ^ w by omega],
        by simp [s1, Expr.eval, r20], rfl, rfl, rfl⟩
    refine ⟨.normal, s2, 9, runs_seq hs1 hs2, ?_, by dsimp only; omega⟩
    have hn_next : s2.mem nextGAddr = curG.n := by
      dsimp only [s2, s1]
      rw [Function.update_of_ne (by omega : nextGAddr ≠ nextGAddr + 1), Function.update_self]
    have hm_next : s2.mem (nextGAddr + 1) = remE.length := by
      dsimp only [s2, s1]; rw [Function.update_self]
    have hga_next : GraphAt s2.mem nextGAddr ⟨curG.n, remE⟩ :=
      graphAt_of_cells hn_next hm_next fun t ht => by
        dsimp only [s2, s1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hnextG_e t ht
    have hlist_next : ListAt s2.mem nextIdxAddr remI := fun t ht => by
      have ht_m : t < curG.m := by
        rw [remIdxPrefix_length_eq] at ht; exact lt_of_lt_of_le ht hrem_le
      dsimp only [s2, s1]
      rw [Function.update_of_ne (by rcases hnnGI with h | h <;> omega),
        Function.update_of_ne (by rcases hnnGI with h | h <;> omega)]
      exact hnextI t ht
    have hidx_sp := remIdxPrefix_spec (partId := partId) (kept := kept) (le_refl curG.m) hidx_len hidx_nd hidx_lt
    refine ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
      r20, hrem_le, remEdgesPrefix_isValid hV partId kept (le_refl _), hga_next, hlist_next,
      remIdxPrefix_length_eq curG curIdx partId kept curG.m, hidx_sp.1, hidx_sp.2.1,
      fun a ha => by
        dsimp only [s2, s1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hlvl_arr a ha,
      fun a ha1 ha2 ha3 => by
        dsimp only [s2, s1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha1 ha2 ha3⟩
  have hloop' : Triple w p S0 (seqStmts [forRange 19 (.const 0) (.reg 15) body])
      (normalPost Stail_pre) (fun _ => 120 * curG.m + 10) :=
    hloop.conseq (fun _ h => h) (fun o st h => by
      cases o with
      | returned _ => exact False.elim h
      | normal => exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
      (fun _ _ => by simp only [Expr.size, Nat.sub_zero]; omega)
  -- Compose `init`, `loop`, and `tail` (using explicit `Runs` sequencing on `seqStmts`)
  intro st ω hpre
  obtain ⟨o0, st0, c0, hr0, hP0, hc0⟩ := hinit20 st ω hpre
  cases o0 with
  | returned _ => exact False.elim hP0
  | normal =>
    obtain ⟨o1, st1, c1, hr1, hP1, hc1⟩ := hloop' st0 ω hP0
    cases o1 with
    | returned _ => exact False.elim hP1
    | normal =>
      obtain ⟨o2, st2, c2, hr2, hP2, hc2⟩ := htail st1 ω hP1
      cases o2 with
      | returned _ => exact False.elim hP2
      | normal =>
        exact ⟨.normal, st2, c0 + (c1 + c2 + 1) + 1,
          runs_seq hr0 (runs_seq hr1 hr2), hP2, by dsimp only at hc0 hc1 hc2 ⊢; omega⟩

end MinCostFlow.Expander
