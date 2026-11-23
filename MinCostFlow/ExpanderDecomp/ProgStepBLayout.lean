module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBModel
public import MinCostFlow.ExpanderDecomp.ProgStepBPrep
public import MinCostFlow.ExpanderDecomp.ProgStepBMatched
public import MinCostFlow.ExpanderDecomp.ProgStepBRelabel

import Mathlib.Tactic.Linarith

/-!
# Step B Persistent Layout, Round Invariant, and Query Statements (`ProgStepBLayout`)

Defines the persistent heap layout `SbPersist` (including the reusable `rangeB_A` and `wRelA`
scratch regions for local sub-core witness relabeling), the register/memory invariants `SbArgs`,
`SbPersistAt`, `SbLoopInv`, and `SbQueryInv`, the flat-encoding bridge `multiPairsAt_of_fixed_stride`,
and the per-round sub-core query loop statements `sbQueryAfterCallStmt`, `sbQueryOneBlockStmt`,
and `sbQueryLoopStmt`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Persistent Layout and Round-Loop Invariant -/

/-- Fixed persistent-heap addresses allocated once from `h0` at Step B startup:
`[h0, h0 + 1 + k)`: `LenListAt` of `X.sort`;
`actA, savLenA, cmpLenA` (`3 * nBlocks` words);
`savA, cmpA` (`2 * nBlocks * b` words);
`wBaseA` (`nBlocks * wStride` words for the per-block witness graphs);
`rangeB_A` (`b` words holding `[0, …, b - 1]`);
`wRelA` (`wStride` words reusable scratch for the relabeled witness graph passed to `bSubCore`). -/
structure SbPersist (h0 k b nBlocks L : ℕ) where
  maxR : ℕ := 49 * L + 1
  wStride : ℕ := 2 + 2 * (49 * L + 1) * (b / 2)
  actA : ℕ := h0 + 1 + k
  savLenA : ℕ := h0 + 1 + k + nBlocks
  cmpLenA : ℕ := h0 + 1 + k + 2 * nBlocks
  savA : ℕ := h0 + 1 + k + 3 * nBlocks
  cmpA : ℕ := h0 + 1 + k + 3 * nBlocks + nBlocks * b
  wBaseA : ℕ := h0 + 1 + k + 3 * nBlocks + 2 * (nBlocks * b)
  rangeB_A : ℕ := h0 + 1 + k + 3 * nBlocks + 2 * (nBlocks * b) +
    nBlocks * (2 + 2 * (49 * L + 1) * (b / 2))
  wRelA : ℕ := h0 + 1 + k + 3 * nBlocks + 2 * (nBlocks * b) +
    nBlocks * (2 + 2 * (49 * L + 1) * (b / 2)) + b
  hPersist : ℕ := h0 + 1 + k + 3 * nBlocks + 2 * (nBlocks * b) +
    nBlocks * (2 + 2 * (49 * L + 1) * (b / 2)) + b + (2 + 2 * (49 * L + 1) * (b / 2))

/-- Canonical persistent layout instance for `(h0, k, b, nBlocks, L)`. -/
def sbPersist (h0 k b nBlocks L : ℕ) : SbPersist h0 k b nBlocks L := {}

lemma numFullBlocks_mul_le (vs : List ℕ) (b : ℕ) :
    numFullBlocks vs b * b ≤ vs.length :=
  Nat.div_mul_le_self vs.length b

lemma sbPersist_size_le {h0 k b nBlocks L : ℕ} (hb_le : b ≤ k) (hnb_b : nBlocks * b ≤ k) (hL : 4 ≤ L) :
    (sbPersist h0 k b nBlocks L).hPersist ≤ h0 + 100 * k * L + 6 * k + 6 * nBlocks + 4 := by
  dsimp only [sbPersist]
  have hhalf : 2 * (b / 2) ≤ b := Nat.mul_div_le b 2
  have h1 : nBlocks * (2 + 2 * (49 * L + 1) * (b / 2)) =
      2 * nBlocks + (49 * L + 1) * (nBlocks * (2 * (b / 2))) := by ring
  have h2 : nBlocks * (2 * (b / 2)) ≤ k :=
    le_trans (Nat.mul_le_mul_left nBlocks hhalf) hnb_b
  have h3 : (49 * L + 1) * (nBlocks * (2 * (b / 2))) ≤ (50 * L) * k :=
    Nat.mul_le_mul (by omega) h2
  have h4 : (50 * L) * k = 50 * k * L := by ring
  have h5 : 2 * (49 * L + 1) * (b / 2) = (49 * L + 1) * (2 * (b / 2)) := by ring
  have h6 : (49 * L + 1) * (2 * (b / 2)) ≤ (50 * L) * k :=
    Nat.mul_le_mul (by omega) (le_trans hhalf hb_le)
  have h7 : 100 * k * L = 50 * k * L + 50 * k * L := by ring
  omega

/-- Read-only register bundle: input args `r0..r11` plus persistent constants `r16..r21`. -/
structure SbArgs (q gA k xA b nBlocks z pA locA fA outA h0 L : ℕ) (st : State) : Prop where
  r0 : st.regs 0 = q
  r1 : st.regs 1 = gA
  r2 : st.regs 2 = k
  r3 : st.regs 3 = xA
  r4 : st.regs 4 = b
  r5 : st.regs 5 = nBlocks
  r6 : st.regs 6 = z
  r7 : st.regs 7 = pA
  r8 : st.regs 8 = locA
  r9 : st.regs 9 = fA
  r10 : st.regs 10 = outA
  r11 : st.regs 11 = h0
  r16 : st.regs 16 = (sbPersist h0 k b nBlocks L).wStride
  r17 : st.regs 17 = (sbPersist h0 k b nBlocks L).actA
  r18 : st.regs 18 = (sbPersist h0 k b nBlocks L).savA
  r19 : st.regs 19 = (sbPersist h0 k b nBlocks L).cmpA
  r20 : st.regs 20 = (sbPersist h0 k b nBlocks L).wBaseA
  r21 : st.regs 21 = (sbPersist h0 k b nBlocks L).maxR

lemma sbArgs_of_eq {q gA k xA b nBlocks z pA locA fA outA h0 L : ℕ} {st st' : State}
    (ha : SbArgs q gA k xA b nBlocks z pA locA fA outA h0 L st)
    (heq : ∀ r, (r < 12 ∨ (16 ≤ r ∧ r ≤ 21)) → st'.regs r = st.regs r) :
    SbArgs q gA k xA b nBlocks z pA locA fA outA h0 L st' where
  r0 := (heq 0 (Or.inl (by decide))).trans ha.r0
  r1 := (heq 1 (Or.inl (by decide))).trans ha.r1
  r2 := (heq 2 (Or.inl (by decide))).trans ha.r2
  r3 := (heq 3 (Or.inl (by decide))).trans ha.r3
  r4 := (heq 4 (Or.inl (by decide))).trans ha.r4
  r5 := (heq 5 (Or.inl (by decide))).trans ha.r5
  r6 := (heq 6 (Or.inl (by decide))).trans ha.r6
  r7 := (heq 7 (Or.inl (by decide))).trans ha.r7
  r8 := (heq 8 (Or.inl (by decide))).trans ha.r8
  r9 := (heq 9 (Or.inl (by decide))).trans ha.r9
  r10 := (heq 10 (Or.inl (by decide))).trans ha.r10
  r11 := (heq 11 (Or.inl (by decide))).trans ha.r11
  r16 := (heq 16 (Or.inr (by decide))).trans ha.r16
  r17 := (heq 17 (Or.inr (by decide))).trans ha.r17
  r18 := (heq 18 (Or.inr (by decide))).trans ha.r18
  r19 := (heq 19 (Or.inr (by decide))).trans ha.r19
  r20 := (heq 20 (Or.inr (by decide))).trans ha.r20
  r21 := (heq 21 (Or.inr (by decide))).trans ha.r21

/-- Memory representation of `BlockGameState` `bst` inside the persistent heap region
`[h0, hPersist)`. -/
structure SbPersistAt (mem : ℕ → ℕ) (G : Graph) (X : Finset ℕ) (b nBlocks L h0 : ℕ)
    (bst : BlockGameState) : Prop where
  xLen_at : LenListAt mem h0 (X.sort (· ≤ ·))
  act_at : ∀ i < nBlocks, mem ((sbPersist h0 X.card b nBlocks L).actA + i) = if bst.active i then 1 else 0
  inact_saved : ∀ i < nBlocks, bst.active i = false →
    let ps := sbPersist h0 X.card b nBlocks L
    let vs := X.sort (· ≤ ·)
    mem (ps.savLenA + i) = (bst.savedS i).card ∧
    mem (ps.cmpLenA + i) = (blockSet vs b i \ bst.savedS i).card ∧
    ListAt mem (ps.savA + i * b) ((bst.savedS i).sort (· ≤ ·)) ∧
    ListAt mem (ps.cmpA + i * b) ((blockSet vs b i \ bst.savedS i).sort (· ≤ ·))
  w_at : ∀ i < nBlocks,
    let ps := sbPersist h0 X.card b nBlocks L
    GraphAt mem (ps.wBaseA + i * ps.wStride)
      (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i)))
  rangeB_at : ListAt mem (sbPersist h0 X.card b nBlocks L).rangeB_A (List.range b)

/-- Per-round space step budget (used in `SbLoopInv`). -/
def sbRoundSpaceStep (C_sp Sprev n N L q k nBlocks : ℕ) : ℕ :=
  nBlocks * Sprev + outerRouterSpace C_sp n (stepBRouterR1 N L q) +
    6 * k + 6 * nBlocks + 2 * n + 10

/-- Round-loop invariant after `m` rounds (`0 ≤ m ≤ 49 * L + 1`). -/
structure SbLoopInv (cfg : ParamConfig) (M r q C_sp Sprev : ℕ)
    (gA k xA b nBlocks z pA locA fA outA h0 : ℕ)
    (mem0 : ℕ → ℕ) (G : Graph) (X : Finset ℕ) (m : ℕ) (st : State) : Prop where
  args : SbArgs q gA k xA b nBlocks z pA locA fA outA h0 (LParam M) st
  rm : st.regs 15 = m
  loc0 : ∀ u < G.n, st.mem (locA + u) = 0
  h_ge : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ st.regs 12
  h_le : st.regs 12 ≤ (sbPersist h0 k b nBlocks (LParam M)).hPersist +
    m * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks
  zf : ZeroFrom st.mem (st.regs 12)
  frame : ∀ a < h0, (a < locA ∨ locA + G.n ≤ a) →
    (a < fA ∨ fA + 2 * k ≤ a) → (a < outA ∨ outA + 2 + k ≤ a) → st.mem a = mem0 a
  state_match :
    (st.regs 13 = 1 ∧ ∃ U : Finset ℕ, CoreOutAt st.mem outA (.cut U) ∧ RouteCutSpec G X 100 z U) ∨
    (st.regs 13 = 0 ∧ ∃ bst : BlockGameState,
      SbModelInv (coreParamsOf cfg M r) q G X (X.sort (· ≤ ·)) b nBlocks z m bst ∧
      SbPersistAt st.mem G X b nBlocks (LParam M) h0 bst ∧
      st.regs 14 = (callsFakeEdges bst.calls).length ∧
      EdgesAt st.mem fA (callsFakeEdges bst.calls))

/-! ## 2. Per-Round Sub-Core Query Statements -/

/-- Post-`bSubCore` dispatch inside `sbQueryOneBlockStmt`: saves `(S, B \ S)` and deactivates
block `i` on `.expander S`, or pads/bisects `U` into `pairsA` and appends `[wAddr_i, cA, oA]`
to `cutRecsA` on `.cut U`. -/
def sbQueryAfterCallStmt : Stmt :=
  seqStmts [
    .assign 31 (.load (.bin .add (.reg 30) (.const 1))),
    .cond (.bin .eq (.load (.reg 30)) (.const 1))
      (seqStmts [
        .assign 30 (.bin .add (.reg 30) (.const 2)),
        .assign 32 (.bin .add (.reg 18) (.bin .mul (.reg 27) (.reg 4))),
        .assign 33 (.bin .add (.reg 19) (.bin .mul (.reg 27) (.reg 4))),
        sbSaveExpStmt,
        .store (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 27)) (.reg 34),
        .store (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 27)) (.reg 35),
        .store (.bin .add (.reg 17) (.reg 27)) (.const 0)
      ])
      (seqStmts [
        .assign 30 (.bin .add (.reg 30) (.const 2)),
        sbPadBisectStmt,
        .assign 32 (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 25))),
        .store (.reg 32) (.reg 29),
        .store (.bin .add (.reg 32) (.const 1)) (.bin .add (.reg 26) (.const 1)),
        .store (.bin .add (.reg 32) (.const 2))
          (.bin .add (.bin .add (.reg 26) (.const 2)) (.bin .div (.reg 4) (.const 2))),
        .assign 25 (.bin .add (.reg 25) (.const 1)),
        .assign 26 (.bin .add (.reg 26) (.bin .add (.const 2) (.reg 4)))
      ])
  ]

/-- One block iteration (`r27 = i`) of the Step B query loop: skips inactive blocks; on active
block `i`, relabels `W_i` to `Finset.range b` at `wRelA`, calls
`bSubCore [q - 1, wRelA, b, rangeB_A, pAddr, locAddr, subOutA, hCur]`, lifts the output back
to original vertex IDs via `sbLiftOutStmt`, and dispatches via `sbQueryAfterCallStmt`. -/
def sbQueryOneBlockStmt (bSubCore : ℕ) : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 17) (.reg 27))) (.const 1))
    (seqStmts [
      .assign 28 (.bin .add (.reg 3) (.bin .mul (.reg 27) (.reg 4))),
      .assign 29 (.bin .add (.reg 20) (.bin .mul (.reg 27) (.reg 16))),
      .assign 30 (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 4))),
      .assign 31 (.bin .add (.reg 20) (.bin .mul (.reg 5) (.reg 16))),
      .assign 32 (.bin .add (.reg 31) (.reg 4)),
      sbRelabelGraphStmt,
      .assign 33 (.bin .sub (.reg 0) (.const 1)),
      .call 12 bSubCore [.reg 33, .reg 32, .reg 4, .reg 31, .reg 7, .reg 8, .reg 30, .reg 12],
      sbLiftOutStmt,
      sbQueryAfterCallStmt
    ])
    .nop

/-- Full query loop over `i = 0..nBlocks-1` (`r27`). -/
def sbQueryLoopStmt (bSubCore : ℕ) : Stmt :=
  forRange 27 (.const 0) (.reg 5) (sbQueryOneBlockStmt bSubCore)

theorem sbQueryOneBlockStmt_noRand (bSubCore : ℕ) : (sbQueryOneBlockStmt bSubCore).NoRand := by
  simp [sbQueryOneBlockStmt, sbQueryAfterCallStmt, sbRelabelGraphStmt_noRand, sbLiftOutStmt_noRand,
    sbSaveExpStmt, sbPadBisectStmt, sbMarkListStmt, sbPartitionStmt, scCopySliceStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

theorem sbQueryLoopStmt_noRand (bSubCore : ℕ) : (sbQueryLoopStmt bSubCore).NoRand := by
  simp [sbQueryLoopStmt, sbQueryOneBlockStmt_noRand, forRange, forUp, Stmt.NoRand]

/-! ## 3. Query-Loop Invariant and Flat-Encoding Helper -/

/-- State invariant after querying blocks `0, …, j - 1` (`j ≤ nBlocks`) in a round. -/
structure SbQueryInv (cfg : ParamConfig) (M r q Sprev : ℕ)
    (gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA tmpA hSub0 : ℕ)
    (memStart : ℕ → ℕ) (G : Graph) (X : Finset ℕ) (bst : BlockGameState)
    (j : ℕ) (res : ℕ → CoreResult) (cutIds : List ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (cPrimeAddrs compAddrs : List ℕ) (cPrimeLists compLists : List (List ℕ)) (st : State) : Prop where
  args : SbArgs q gA k xA b nBlocks z pA locA fA outA h0 (LParam M) st
  r13 : st.regs 13 = 0
  r22 : st.regs 22 = cutRecsA
  r23 : st.regs 23 = pairsA
  r24 : st.regs 24 = tmpA
  r25 : st.regs 25 = cutIds.length
  r26 : st.regs 26 = pairsA + 1 + cutIds.length * (2 + b)
  r27 : st.regs 27 = j
  h_ge : hSub0 ≤ st.regs 12
  h_le : st.regs 12 ≤ hSub0 + j * Sprev
  zf : ZeroFrom st.mem (st.regs 12)
  loc0 : ∀ u < G.n, st.mem (locA + u) = 0
  res_spec : ∀ i < j, bst.active i = true →
    CoreSpec (coreParamsOf cfg M r) (q - 1)
      (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i)))
      (blockSet (X.sort (· ≤ ·)) b i) (res i)
  cutIds_eq : cutIds = ((List.range j).filterMap fun i =>
    if bst.active i then match res i with | .cut _ => some i | .expander _ => none else none)
  pairs_eq : pairs = ((List.range j).filterMap fun i =>
    if bst.active i then match res i with
      | .cut U =>
          let B := blockSet (X.sort (· ≤ ·)) b i
          let C' := padToHalf B (smallerSide B U)
          some (C', B \ C')
      | .expander _ => none
    else none)
  lens_eq : cPrimeAddrs.length = cutIds.length ∧ compAddrs.length = cutIds.length ∧
    cPrimeLists.length = cutIds.length ∧ compLists.length = cutIds.length ∧
    pairs.length = cutIds.length
  recs_at : ∀ idx (hidx : idx < cutIds.length),
    let ps := sbPersist h0 k b nBlocks (LParam M)
    let i := cutIds[idx]'hidx
    let cA := cPrimeAddrs[idx]'(lens_eq.1.symm ▸ hidx)
    let oA := compAddrs[idx]'(lens_eq.2.1.symm ▸ hidx)
    let cL := cPrimeLists[idx]'(lens_eq.2.2.1.symm ▸ hidx)
    let oL := compLists[idx]'(lens_eq.2.2.2.1.symm ▸ hidx)
    let p_i := pairs[idx]'(lens_eq.2.2.2.2.symm ▸ hidx)
    cA = pairsA + 1 + idx * (2 + b) + 1 ∧
    oA = pairsA + 1 + idx * (2 + b) + 2 + b / 2 ∧
    st.mem (cutRecsA + 3 * idx) = ps.wBaseA + i * ps.wStride ∧
    st.mem (cutRecsA + 3 * idx + 1) = cA ∧
    st.mem (cutRecsA + 3 * idx + 2) = oA ∧
    st.mem (pairsA + 1 + idx * (2 + b)) = b / 2 ∧
    st.mem (pairsA + 1 + idx * (2 + b) + 1 + b / 2) = b / 2 ∧
    cL = p_i.1.sort (· ≤ ·) ∧ oL = p_i.2.sort (· ≤ ·) ∧
    cL.length = b / 2 ∧ oL.length = b / 2 ∧
    ListAt st.mem cA cL ∧ ListAt st.mem oA oL
  act_mem : ∀ i < nBlocks,
    let ps := sbPersist h0 k b nBlocks (LParam M)
    st.mem (ps.actA + i) =
      if i < j ∧ bst.active i then match res i with | .expander _ => 0 | .cut _ => 1
      else if bst.active i then 1 else 0
  saved_mem : ∀ i < nBlocks,
    let ps := sbPersist h0 k b nBlocks (LParam M)
    let vs := X.sort (· ≤ ·)
    (bst.active i = false →
      st.mem (ps.savLenA + i) = (bst.savedS i).card ∧
      st.mem (ps.cmpLenA + i) = (blockSet vs b i \ bst.savedS i).card ∧
      ListAt st.mem (ps.savA + i * b) ((bst.savedS i).sort (· ≤ ·)) ∧
      ListAt st.mem (ps.cmpA + i * b) ((blockSet vs b i \ bst.savedS i).sort (· ≤ ·))) ∧
    (i < j → bst.active i = true → ∀ S, res i = .expander S →
      st.mem (ps.savLenA + i) = S.card ∧
      st.mem (ps.cmpLenA + i) = (blockSet vs b i \ S).card ∧
      ListAt st.mem (ps.savA + i * b) (S.sort (· ≤ ·)) ∧
      ListAt st.mem (ps.cmpA + i * b) ((blockSet vs b i \ S).sort (· ≤ ·)))
  frame_persist : ∀ a < (sbPersist h0 k b nBlocks (LParam M)).wRelA,
    let ps := sbPersist h0 k b nBlocks (LParam M)
    (a < locA ∨ locA + G.n ≤ a) →
    (a < ps.actA ∨ ps.wBaseA ≤ a) →
    st.mem a = memStart a
  frame_w : ∀ a, (sbPersist h0 k b nBlocks (LParam M)).wBaseA ≤ a →
    a < (sbPersist h0 k b nBlocks (LParam M)).wRelA → st.mem a = memStart a

private lemma encodePair_getElem (cL oL : List ℕ) (rem : ℕ)
    (hrem : rem < (encodePair (cL, oL)).length) :
    (encodePair (cL, oL))[rem]'hrem =
      if h0 : rem = 0 then cL.length
      else if h1 : rem ≤ cL.length then cL[rem - 1]'(by omega)
      else if h2 : rem = 1 + cL.length then oL.length
      else oL[rem - (2 + cL.length)]'(by
        simp only [encodePair, List.length_cons, List.length_append] at hrem; omega) := by
  have hlen_ep : (encodePair (cL, oL)).length = 1 + cL.length + (1 + oL.length) := by
    simp [encodePair]; omega
  unfold encodePair
  cases rem with
  | zero => simp
  | succ r' =>
    simp only [Nat.add_one_ne_zero, ↓reduceDIte, List.cons_append, List.getElem_cons_succ, Nat.add_sub_cancel]
    by_cases h1 : r' + 1 ≤ cL.length
    · simp only [h1, ↓reduceDIte]
      rw [List.getElem_append_left (by omega)]
    · simp only [h1, ↓reduceDIte]
      rw [List.getElem_append_right (by omega)]
      by_cases h2 : r' + 1 = 1 + cL.length
      · simp only [h2, ↓reduceDIte]
        have hz : r' - cL.length = 0 := by omega
        simp [hz]
      · simp only [h2, ↓reduceDIte]
        have hs : r' - cL.length = (r' + 1 - (2 + cL.length)) + 1 := by omega
        simp only [hs, List.getElem_cons_succ]

/-- Flat encoding equivalence: `MultiPairsAt` follows directly from per-pair `b / 2` blocks at
`pairsA + 1 + idx * (2 + b)`. -/
lemma multiPairsAt_of_fixed_stride {mem : ℕ → ℕ} {pairsA b t : ℕ} (hb_even : Even b)
    {cPrimeLists compLists : List (List ℕ)}
    (hcpl : cPrimeLists.length = t) (hcol : compLists.length = t)
    (htag : mem pairsA = t)
    (hp : ∀ idx (hidx : idx < t),
      let cL := cPrimeLists[idx]'(hcpl.symm ▸ hidx)
      let oL := compLists[idx]'(hcol.symm ▸ hidx)
      mem (pairsA + 1 + idx * (2 + b)) = b / 2 ∧
      mem (pairsA + 1 + idx * (2 + b) + 1 + b / 2) = b / 2 ∧
      cL.length = b / 2 ∧ oL.length = b / 2 ∧
      ListAt mem (pairsA + 1 + idx * (2 + b) + 1) cL ∧
      ListAt mem (pairsA + 1 + idx * (2 + b) + 2 + b / 2) oL) :
    MultiPairsAt mem pairsA (cPrimeLists.zip compLists) ∧
    (encodePairs (cPrimeLists.zip compLists)).length = 1 + t * (2 + b) := by
  have h2half : 2 * (b / 2) = b := by rcases hb_even with ⟨m, hm⟩; omega
  have hzl : (cPrimeLists.zip compLists).length = t := by rw [List.length_zip, hcpl, hcol, min_self]
  have henc_len : ∀ idx (hidx : idx < t),
      (encodePair ((cPrimeLists.zip compLists)[idx]'(hzl.symm ▸ hidx))).length = 2 + b := by
    intro idx hidx
    have h := hp idx hidx
    simp only [encodePair, List.getElem_zip, List.length_cons, List.length_append, h.2.2.1, h.2.2.2.1]
    omega
  have htake_len : ∀ j ≤ t,
      (((cPrimeLists.zip compLists).take j).flatMap encodePair).length = j * (2 + b) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      rw [List.take_succ_eq_append_getElem (by omega), List.flatMap_append, List.flatMap_singleton,
        List.length_append, ih (by omega), henc_len j (by omega), Nat.succ_mul]
  have hflat_len : ((cPrimeLists.zip compLists).flatMap encodePair).length = t * (2 + b) := by
    have := htake_len t le_rfl
    have ht : (cPrimeLists.zip compLists).take t = cPrimeLists.zip compLists := by
      rw [← hzl]; exact List.take_length
    rwa [ht] at this
  have htot : (encodePairs (cPrimeLists.zip compLists)).length = 1 + t * (2 + b) := by
    simp only [encodePairs, List.length_cons, hflat_len]; omega
  refine ⟨fun pos hpos => ?_, htot⟩
  cases pos with
  | zero =>
    simp only [Nat.add_zero, encodePairs, List.getElem_cons_zero, hzl, htag]
  | succ pos =>
    have hpos_lt : pos < t * (2 + b) := by
      simp only [encodePairs, List.length_cons, hflat_len] at hpos; omega
    simp only [encodePairs, List.getElem_cons_succ]
    set idx := pos / (2 + b)
    have hidx : idx < t := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hpos_lt)
    have hrem : pos % (2 + b) < 2 + b := Nat.mod_lt pos (by omega)
    have hpos_eq : pos = idx * (2 + b) + pos % (2 + b) := by
      have := Nat.div_add_mod pos (2 + b); have := Nat.mul_comm (pos / (2 + b)) (2 + b); dsimp only [idx]; omega
    generalize hrem_def : pos % (2 + b) = rem at hrem hpos_eq
    have hsplit : (cPrimeLists.zip compLists).flatMap encodePair =
        (((cPrimeLists.zip compLists).take idx).flatMap encodePair) ++
        encodePair ((cPrimeLists.zip compLists)[idx]'(hzl.symm ▸ hidx)) ++
        (((cPrimeLists.zip compLists).drop (idx + 1)).flatMap encodePair) := by
      conv_lhs => rw [← List.take_append_drop idx (cPrimeLists.zip compLists)]
      rw [List.drop_eq_getElem_cons (hzl.symm ▸ hidx), List.flatMap_append, List.flatMap_cons, List.append_assoc]
    have hget_ep : ((cPrimeLists.zip compLists).flatMap encodePair)[pos]'(by rw [hflat_len]; exact hpos_lt) =
        (encodePair ((cPrimeLists.zip compLists)[idx]'(hzl.symm ▸ hidx)))[rem]'(by rw [henc_len idx hidx]; exact hrem) := by
      have h1 : pos < ((((cPrimeLists.zip compLists).take idx).flatMap encodePair) ++
          encodePair ((cPrimeLists.zip compLists)[idx]'(hzl.symm ▸ hidx))).length := by
        rw [List.length_append, htake_len idx (le_of_lt hidx), henc_len idx hidx]; omega
      have h2 : (((cPrimeLists.zip compLists).take idx).flatMap encodePair).length ≤ pos := by
        rw [htake_len idx (le_of_lt hidx)]; omega
      have hsub : pos - (((cPrimeLists.zip compLists).take idx).flatMap encodePair).length = rem := by
        rw [htake_len idx (le_of_lt hidx)]; omega
      simp only [hsplit]
      rw [List.getElem_append_left h1, List.getElem_append_right h2]
      congr 1
    rw [hget_ep]
    have h := hp idx hidx
    set cL := cPrimeLists[idx]'(hcpl.symm ▸ hidx)
    set oL := compLists[idx]'(hcol.symm ▸ hidx)
    have hzip : (cPrimeLists.zip compLists)[idx]'(hzl.symm ▸ hidx) = (cL, oL) := List.getElem_zip
    have hrem' : rem < (encodePair (cL, oL)).length := by
      rw [← hzip, henc_len idx hidx]; exact hrem
    have hrw_zip : (encodePair ((cPrimeLists.zip compLists)[idx]'(hzl.symm ▸ hidx)))[rem]'(by rw [henc_len idx hidx]; exact hrem) =
        (encodePair (cL, oL))[rem]'hrem' := by
      congr 1; rw [hzip]
    rw [hrw_zip, encodePair_getElem cL oL rem hrem']
    have haddr_eq : pairsA + (pos + 1) = pairsA + 1 + idx * (2 + b) + rem := by omega
    rw [haddr_eq]
    by_cases hr0 : rem = 0
    · subst hr0; simp [h.1, h.2.2.1]
    · simp only [hr0, ↓reduceDIte]
      by_cases hr1 : rem ≤ cL.length
      · simp only [hr1, ↓reduceDIte]
        have ha1 : pairsA + 1 + idx * (2 + b) + rem = pairsA + 1 + idx * (2 + b) + 1 + (rem - 1) := by omega
        rw [ha1]; exact h.2.2.2.2.1 (rem - 1) (by omega)
      · simp only [hr1, ↓reduceDIte]
        by_cases hr2 : rem = 1 + cL.length
        · simp only [hr2, ↓reduceDIte]
          have ha : pairsA + 1 + idx * (2 + b) + (1 + cL.length) = pairsA + 1 + idx * (2 + b) + 1 + b / 2 := by
            have := h.2.2.1; omega
          rw [ha, h.2.1, h.2.2.2.1]
        · simp only [hr2, ↓reduceDIte]
          have ha2 : pairsA + 1 + idx * (2 + b) + rem =
              pairsA + 1 + idx * (2 + b) + 2 + b / 2 + (rem - (2 + cL.length)) := by
            have := h.2.2.1; omega
          rw [ha2]; exact h.2.2.2.2.2 (rem - (2 + cL.length)) (by have := h.2.2.1; have := h.2.2.2.1; omega)

end MinCostFlow.ExpanderDecomp
