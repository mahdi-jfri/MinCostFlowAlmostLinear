module

public import MinCostFlow.DynSpanner.Program.GraphTranslateEmit
public import MinCostFlow.DynSpanner.Program.EmbOps

import Mathlib.Data.List.TakeDrop

/-!
# Reverse Graph Translation Primitives (`Cited.Graph` / `Walk` → `MGraph` triples / `MEmbAt`)

Implements and verifies the deterministic Word-RAM primitives used to decode the canonical
output of `Sparsify` (`cJtilde : Cited.Graph`, `kept : List ℕ`, `embJJtilde : ℕ → Walk`):

* `SparsifyOutRelocAt`: canonical memory layout for `Sparsify` output relative to `guestBase`
  (`guestBase = 0` locally, or `guestBase = hBuf + 1` under `relocStmt` relocation).
* `gtBuildKeptTriplesStmt` (`gtIdxBuildKeptTriples = 0` in `gtRevPrimProcs`): expands
  `kept : List ℕ` into `3 * kept.length` edge triples `(eOrig, tail, head)` for `dgInitFromLists`.
* `gtDecodeWalksStmt` (`gtIdxDecodeWalks = 1` in `gtRevPrimProcs`): translates `embJJtilde j`
  (`WalkAt`) into `MWalkAt` / `MEmbAt` for `citedEmbToMGraph J cJtilde kept embJJtilde`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section

def gtIdxBuildKeptTriples : ℕ := 0
def gtIdxDecodeWalks : ℕ := 1

/-! ## Canonical `Sparsify` output layout & pure decoding helpers -/

/-- Canonical `Sparsify` output in guest memory relative to `guestBase`:
at `guestBase + outPtr`, header `[pJtilde, pKept, pEmbOut]`, where `pJtilde` holds
`GraphAt cJtilde`, `pKept` holds `kept.length :: kept`, and `pEmbOut` holds `EmbAt mJ emb`, all
bounded below `retHeap`. When `guestBase = 0`, this coincides with local guest memory. -/
def SparsifyOutRelocAt (mem : ℕ → ℕ) (guestBase outPtr retHeap mJ : ℕ)
    (cJtilde : Cited.Graph) (kept : List ℕ) (emb : ℕ → Walk) : Prop :=
  outPtr + 3 ≤ retHeap ∧
  let pJtilde := mem (guestBase + outPtr)
  let pKept := mem (guestBase + outPtr + 1)
  let pEmb := mem (guestBase + outPtr + 2)
  pJtilde + cJtilde.encode.length ≤ retHeap ∧
  pKept + 1 + kept.length ≤ retHeap ∧
  pEmb + mJ ≤ retHeap ∧
  GraphAt mem (guestBase + pJtilde) cJtilde ∧
  ListAt mem (guestBase + pKept) (kept.length :: kept) ∧
  (∀ j < mJ,
    mem (guestBase + pEmb + j) + (Walk.encode (emb j)).length ≤ retHeap ∧
    WalkAt mem (guestBase + mem (guestBase + pEmb + j)) (emb j))

/-- Unrolled edge-walk length of `citedWalkSteps`. -/
lemma citedWalkSteps_length (jEs : List ℕ) (G : Cited.Graph) (kept : List ℕ) :
    ∀ (vs cs : List ℕ),
      (citedWalkSteps jEs G kept vs cs).length = min (vs.length - 1) cs.length
  | [], _ => by simp [citedWalkSteps]
  | [_], _ => by simp [citedWalkSteps]
  | _ :: _ :: _, [] => by simp [citedWalkSteps]
  | u :: v :: vs, c :: cs => by
    have ih := citedWalkSteps_length jEs G kept (v :: vs) cs
    simp only [citedWalkSteps, List.length_cons] at ih ⊢
    rw [ih]
    omega

/-- Indexing into `citedWalkSteps` for `k < min (vs.length - 1) cs.length`. -/
lemma citedWalkSteps_getElem (jEs : List ℕ) (G : Cited.Graph) (kept : List ℕ) :
    ∀ (vs cs : List ℕ) (k : ℕ) (hk : k < min (vs.length - 1) cs.length),
      (citedWalkSteps jEs G kept vs cs)[k]'(by rw [citedWalkSteps_length]; exact hk) =
        (jEs.getD (kept.getD (cs[k]'(by omega)) 0) 0,
         decide ((G.edges.getD (cs[k]'(by omega)) (0, 0)).1 = vs[k]'(by omega) ∧
                 (G.edges.getD (cs[k]'(by omega)) (0, 0)).2 = vs[k + 1]'(by omega)))
  | [], _, _, hk => by simp at hk
  | [_], _, _, hk => by simp at hk
  | _ :: _ :: _, [], _, hk => by simp at hk
  | u :: v :: vs, c :: cs, 0, _ => by simp [citedWalkSteps]
  | u :: v :: vs, c :: cs, k + 1, hk => by
    have hk' : k < min ((v :: vs).length - 1) cs.length := by simp at hk ⊢; omega
    simpa [citedWalkSteps] using citedWalkSteps_getElem jEs G kept (v :: vs) cs k hk'

/-- Construct `MWalkAt mem a P` from its length header and element-wise `(edge, dir)` pairs. -/
lemma mWalkAt_of_cells {mem : ℕ → ℕ} {a : ℕ} {P : List (ℕ × Bool)}
    (hlen : mem a = P.length)
    (hsteps : ∀ i (hi : i < P.length),
      mem (a + 1 + 2 * i) = P[i].1 ∧
      mem (a + 1 + 2 * i + 1) = if P[i].2 then 1 else 0) :
    MWalkAt mem a P := by
  intro j hj
  dsimp only [mWalkEncode] at hj ⊢
  cases j with
  | zero => simpa using hlen
  | succ j' =>
    simp only [List.length_cons, Nat.succ_lt_succ_iff, flatMap_pair_length] at hj
    rcases Nat.even_or_odd' j' with ⟨i, rfl | rfl⟩
    · have hi : i < P.length := by omega
      have hcell := (hsteps i hi).1
      rw [show a + (2 * i + 1) = a + 1 + 2 * i by omega, hcell]
      simpa using (flatMap_pair_getElem_even hi).symm
    · have hi : i < P.length := by omega
      have hcell := (hsteps i hi).2
      rw [show a + (2 * i + 1 + 1) = a + 1 + 2 * i + 1 by omega, hcell]
      simpa using (flatMap_pair_getElem_odd hi).symm

/-- Decoded walk for edge `j < jEs.length` in `citedEmbToMGraph`. -/
def citedDecWalk (jEs : List ℕ) (cJtilde : Cited.Graph) (kept : List ℕ)
    (emb : ℕ → Walk) (j : ℕ) : List (ℕ × Bool) :=
  citedWalkSteps jEs cJtilde kept (emb j).verts (emb j).edges

lemma citedEmbToMGraph_at_jEs {J : MGraph} {jEs kept : List ℕ} {cJtilde : Cited.Graph}
    {emb : ℕ → Walk} (hjE : jEs = vertsOf J.E) {j : ℕ} (hj : j < jEs.length) :
    citedEmbToMGraph J cJtilde kept emb (jEs[j]'hj) =
      citedDecWalk jEs cJtilde kept emb j := by
  have heJ : jEs[j]'hj ∈ J.E := by
    have hm : jEs[j]'hj ∈ vertsOf J.E := hjE ▸ List.getElem_mem hj
    rwa [mem_vertsOf] at hm
  have hnodup : jEs.Nodup := hjE ▸ vertsOf_nodup J.E
  dsimp only [citedEmbToMGraph, citedDecWalk]
  simp [← hjE, heJ, hnodup.idxOf_getElem j hj]

/-- Cumulative encoded `MWalkAt` word offset after decoding edges `0 .. k - 1`. -/
def citedDecPrefLen (jEs : List ℕ) (cJtilde : Cited.Graph) (kept : List ℕ)
    (emb : ℕ → Walk) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    citedDecPrefLen jEs cJtilde kept emb k +
      (mWalkEncode (citedDecWalk jEs cJtilde kept emb k)).length

lemma citedDecPrefLen_mono (jEs : List ℕ) (cJtilde : Cited.Graph) (kept : List ℕ)
    (emb : ℕ → Walk) {a b : ℕ} (hab : a ≤ b) :
    citedDecPrefLen jEs cJtilde kept emb a ≤ citedDecPrefLen jEs cJtilde kept emb b := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih =>
    rw [citedDecPrefLen]
    exact le_trans ih (Nat.le_add_right _ _)

lemma citedDecPrefLen_le_walkSum (jEs : List ℕ) (cJtilde : Cited.Graph) (kept : List ℕ)
    (emb : ℕ → Walk) (k : ℕ) :
    citedDecPrefLen jEs cJtilde kept emb k ≤
      k + 2 * ((List.range k).map fun j => (emb j).edges.length).sum := by
  induction k with
  | zero => simp [citedDecPrefLen]
  | succ k ih =>
    rw [citedDecPrefLen, mWalkEncode_length, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hlen : (citedDecWalk jEs cJtilde kept emb k).length ≤ (emb k).edges.length := by
      dsimp only [citedDecWalk]
      rw [citedWalkSteps_length]
      exact Nat.min_le_right _ _
    omega

/-! ## Word-RAM statements & module -/

/-- Build `3 * kept.length` edge triples `(eOrig, tail, head)` at `triplesOutPtr`:
`[keptBase, jEsPtr, jTailsPtr, jHeadsPtr, triplesOutPtr]`. Returns `kept.length`. -/
def gtBuildKeptTriplesStmt : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  forRange 6 (.const 0) (.reg 5)
    (.assign 7 (.load (.bin .add (.reg 0) (.bin .add (.const 1) (.reg 6)))) ;;
     .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
     .assign 9 (.load (.bin .add (.reg 2) (.reg 7))) ;;
     .assign 10 (.load (.bin .add (.reg 3) (.reg 7))) ;;
     .assign 11 (.bin .mul (.const 3) (.reg 6)) ;;
     .store (.bin .add (.reg 4) (.reg 11)) (.reg 8) ;;
     .store (.bin .add (.reg 4) (.bin .add (.reg 11) (.const 1))) (.reg 9) ;;
     .store (.bin .add (.reg 4) (.bin .add (.reg 11) (.const 2))) (.reg 10)) ;;
  .ret (.reg 5)

/-- Compute `steps := min (vLen - 1) eLen` into `r16` from `r14 = vLen`, `r15 = eLen`. -/
def gtComputeStepsStmt : Stmt :=
  .cond (.bin .lt (.const 1) (.reg 14))
    (.assign 16 (.bin .sub (.reg 14) (.const 1)) ;;
     .cond (.bin .lt (.reg 15) (.reg 16)) (.assign 16 (.reg 15)) .nop)
    (.assign 16 (.const 0))

/-- Decode `cJtilde`/`kept`/`emb` into `mEmbOutPtr` (`MEmbAt`) and `walkBufPtr` (`MWalkAt`):
`[mJ, jEsPtr, guestBase, jtildeGuestPtr, keptGuestPtr, embGuestPtr, mEmbOutPtr, walkBufPtr]`.
Returns end of written `walkBuf` (`walkBufPtr + citedDecPrefLen ... mJ`). -/
def gtDecodeWalksStmt : Stmt :=
  .assign 8 (.bin .add (.reg 2) (.bin .add (.reg 3) (.const 2))) ;;
  .assign 9 (.bin .add (.reg 2) (.bin .add (.reg 4) (.const 1))) ;;
  .assign 10 (.bin .add (.reg 2) (.reg 5)) ;;
  forRange 11 (.const 0) (.reg 0)
    (.assign 12 (.load (.bin .add (.reg 1) (.reg 11))) ;;
     .store (.bin .add (.reg 6) (.reg 12)) (.reg 7) ;;
     .assign 13 (.bin .add (.reg 2) (.load (.bin .add (.reg 10) (.reg 11)))) ;;
     .assign 14 (.load (.reg 13)) ;;
     .assign 15 (.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 14)))) ;;
     gtComputeStepsStmt ;;
     .store (.reg 7) (.reg 16) ;;
     forRange 17 (.const 0) (.reg 16)
       (.assign 18 (.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 17)))) ;;
        .assign 19 (.load (.bin .add (.reg 13) (.bin .add (.const 2) (.reg 17)))) ;;
        .assign 20 (.load (.bin .add (.reg 13) (.bin .add (.bin .add (.const 2) (.reg 14)) (.reg 17)))) ;;
        .assign 21 (.bin .mul (.const 2) (.reg 20)) ;;
        .assign 22 (.load (.bin .add (.reg 8) (.reg 21))) ;;
        .assign 23 (.load (.bin .add (.reg 8) (.bin .add (.reg 21) (.const 1)))) ;;
        .assign 24 (.bin .mul (.bin .eq (.reg 22) (.reg 18)) (.bin .eq (.reg 23) (.reg 19))) ;;
        .assign 25 (.load (.bin .add (.reg 9) (.reg 20))) ;;
        .assign 26 (.load (.bin .add (.reg 1) (.reg 25))) ;;
        .assign 27 (.bin .add (.reg 7) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 17)))) ;;
        .store (.reg 27) (.reg 26) ;;
        .store (.bin .add (.reg 27) (.const 1)) (.reg 24)) ;;
     .assign 7 (.bin .add (.reg 7) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 16))))) ;;
  .ret (.reg 7)

/-- Module of reverse graph-translation primitives (`gtIdxBuildKeptTriples = 0`, `gtIdxDecodeWalks = 1`). -/
def gtRevPrimProcs : List Stmt :=
  [gtBuildKeptTriplesStmt, gtDecodeWalksStmt]

/-! ## Contracts -/

/-- Contract for `gtBuildKeptTriplesStmt`. -/
def gtBuildKeptTriplesContract (w : ℕ) (kept jEs jTails jHeads : List ℕ) : Contract where
  pre args mem := ∃ keptBase jEsPtr jTailsPtr jHeadsPtr triplesOutPtr,
    args = [keptBase, jEsPtr, jTailsPtr, jHeadsPtr, triplesOutPtr] ∧
    16 ≤ 2 ^ w ∧
    keptBase + 1 + kept.length < 2 ^ w ∧
    jEsPtr + jEs.length < 2 ^ w ∧
    jTailsPtr + jEs.length < 2 ^ w ∧
    jHeadsPtr + jEs.length < 2 ^ w ∧
    triplesOutPtr + 3 * kept.length < 2 ^ w ∧
    jTails.length = jEs.length ∧ jHeads.length = jEs.length ∧
    (∀ idx ∈ kept, idx < jEs.length) ∧
    (∀ idx ∈ kept, jEs[idx]! < 2 ^ w ∧ jTails[idx]! < 2 ^ w ∧ jHeads[idx]! < 2 ^ w) ∧
    (∀ i < 1 + kept.length, keptBase + i < triplesOutPtr ∨ triplesOutPtr + 3 * kept.length ≤ keptBase + i) ∧
    (∀ i < jEs.length, jEsPtr + i < triplesOutPtr ∨ triplesOutPtr + 3 * kept.length ≤ jEsPtr + i) ∧
    (∀ i < jEs.length, jTailsPtr + i < triplesOutPtr ∨ triplesOutPtr + 3 * kept.length ≤ jTailsPtr + i) ∧
    (∀ i < jEs.length, jHeadsPtr + i < triplesOutPtr ∨ triplesOutPtr + 3 * kept.length ≤ jHeadsPtr + i) ∧
    ListAt mem keptBase (kept.length :: kept) ∧
    ListAt mem jEsPtr jEs ∧ ListAt mem jTailsPtr jTails ∧ ListAt mem jHeadsPtr jHeads
  post args mem ret mem' := ∃ keptBase jEsPtr jTailsPtr jHeadsPtr triplesOutPtr,
    args = [keptBase, jEsPtr, jTailsPtr, jHeadsPtr, triplesOutPtr] ∧
    ret = kept.length ∧
    (∀ i (hi : i < kept.length),
      mem' (triplesOutPtr + 3 * i) = jEs.getD kept[i] 0 ∧
      mem' (triplesOutPtr + 3 * i + 1) = jTails.getD kept[i] 0 ∧
      mem' (triplesOutPtr + 3 * i + 2) = jHeads.getD kept[i] 0) ∧
    ∀ addr, addr < triplesOutPtr ∨ triplesOutPtr + 3 * kept.length ≤ addr → mem' addr = mem addr
  cost _ _ := 75 * kept.length + 25

/-- Contract for `gtDecodeWalksStmt`. -/
def gtDecodeWalksContract (w eCap : ℕ) (J : MGraph) (jEs kept : List ℕ)
    (cJtilde : Cited.Graph) (embJJtilde : ℕ → Walk) : Contract where
  pre args mem := ∃ mJ jEsPtr guestBase jtildeG keptG embG mEmbOutPtr walkBufPtr,
    let totWalk := citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length
    args = [jEs.length, jEsPtr, guestBase, jtildeG, keptG, embG, mEmbOutPtr, walkBufPtr] ∧
    mJ = jEs.length ∧
    16 ≤ 2 ^ w ∧
    jEsPtr + jEs.length < 2 ^ w ∧
    guestBase + jtildeG + cJtilde.encode.length < 2 ^ w ∧
    guestBase + keptG + 1 + kept.length < 2 ^ w ∧
    guestBase + embG + jEs.length < 2 ^ w ∧
    mEmbOutPtr + eCap < 2 ^ w ∧
    walkBufPtr + totWalk < 2 ^ w ∧
    jEs = vertsOf J.E ∧
    (∀ e ∈ J.E, e < eCap) ∧
    (∀ k ∈ kept, k < jEs.length) ∧
    (∀ j < jEs.length,
      (embJJtilde j).verts.length < 2 ^ w ∧ (embJJtilde j).edges.length < 2 ^ w ∧
      guestBase + mem (guestBase + embG + j) + (Walk.encode (embJJtilde j)).length < 2 ^ w ∧
      (∀ c ∈ (embJJtilde j).edges, c < cJtilde.m ∧ c < kept.length) ∧
      (∀ u ∈ (embJJtilde j).verts, u < 2 ^ w)) ∧
    cJtilde.encode.all (· < 2 ^ w) ∧
    (∀ i < cJtilde.m, (cJtilde.edges[i]!).1 < 2 ^ w ∧ (cJtilde.edges[i]!).2 < 2 ^ w) ∧
    ListAt mem jEsPtr jEs ∧
    GraphAt mem (guestBase + jtildeG) cJtilde ∧
    ListAt mem (guestBase + keptG) (kept.length :: kept) ∧
    (∀ j < jEs.length, WalkAt mem (guestBase + mem (guestBase + embG + j)) (embJJtilde j)) ∧
    let dis := fun addr =>
      (addr < mEmbOutPtr ∨ mEmbOutPtr + eCap ≤ addr) ∧
      (addr < walkBufPtr ∨ walkBufPtr + totWalk ≤ addr)
    (mEmbOutPtr + eCap ≤ walkBufPtr ∨ walkBufPtr + totWalk ≤ mEmbOutPtr) ∧
    (∀ i < jEs.length, dis (jEsPtr + i)) ∧
    (∀ i < cJtilde.encode.length, dis (guestBase + jtildeG + i)) ∧
    (∀ i < 1 + kept.length, dis (guestBase + keptG + i)) ∧
    (∀ j < jEs.length, dis (guestBase + embG + j)) ∧
    (∀ j < jEs.length, ∀ i < (Walk.encode (embJJtilde j)).length,
      dis (guestBase + mem (guestBase + embG + j) + i))
  post args mem ret mem' := ∃ jEsPtr guestBase jtildeG keptG embG mEmbOutPtr walkBufPtr,
    let totWalk := citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length
    args = [jEs.length, jEsPtr, guestBase, jtildeG, keptG, embG, mEmbOutPtr, walkBufPtr] ∧
    ret = walkBufPtr + totWalk ∧
    MEmbAt mem' mEmbOutPtr J.E eCap (citedEmbToMGraph J cJtilde kept embJJtilde) ∧
    (∀ j (hj : j < jEs.length),
      let wPtr := mem' (mEmbOutPtr + jEs[j]'hj)
      walkBufPtr ≤ wPtr ∧
      wPtr + (mWalkEncode (citedDecWalk jEs cJtilde kept embJJtilde j)).length ≤ walkBufPtr + totWalk) ∧
    ∀ addr,
      (addr < mEmbOutPtr ∨ mEmbOutPtr + eCap ≤ addr) →
      (addr < walkBufPtr ∨ walkBufPtr + totWalk ≤ addr) →
      mem' addr = mem addr
  cost args _ :=
    250 * ((List.range (args.getD 0 0)).map fun j => (embJJtilde j).edges.length).sum +
    200 * args.getD 0 0 + 80

end

/-! ## Verification -/

public section

private lemma runs_cond_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T)
    (hF : v = 0 → ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  by_cases hv : v = 0
  · rcases hF hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨0, c₁, hv ▸ he, by simpa using hr₁, rfl⟩, hq, by omega⟩
  · rcases hT hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨v, c₁, he, by simp [hv]; exact hr₁, rfl⟩, hq, by omega⟩

private lemma gt_computeSteps_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {vLen eLen : ℕ} (hw16 : 16 ≤ 2 ^ w)
    (hr14 : st.regs 14 = vLen) (hr15 : st.regs 15 = eLen)
    (hv : vLen < 2 ^ w) :
    ∃ st' c,
      Runs w p ω gtComputeStepsStmt st .normal st' c ∧
      st'.regs 16 = min (vLen - 1) eLen ∧
      st'.mem = st.mem ∧ st'.pos = st.pos ∧
      (∀ r, r ≠ 16 → st'.regs r = st.regs r) ∧
      c ≤ 20 := by
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  dsimp only [gtComputeStepsStmt]
  by_cases hv1 : 1 < vLen
  · obtain ⟨o, st', c, hrun, ⟨ho, h16, hm, hp, hregs⟩, hc⟩ := runs_cond_le
      (w := w) (p := p) (ω := ω) (st := st) (k := 0) (T := 20)
      (e := .bin .lt (.const 1) (.reg 14))
      (s₁ := .assign 16 (.bin .sub (.reg 14) (.const 1)) ;;
        .cond (.bin .lt (.reg 15) (.reg 16)) (.assign 16 (.reg 15)) .nop)
      (s₂ := .assign 16 (.const 0)) (v := 1)
      (Q := fun o st' => o = .normal ∧ st'.regs 16 = min (vLen - 1) eLen ∧
        st'.mem = st.mem ∧ st'.pos = st.pos ∧ ∀ r, r ≠ 16 → st'.regs r = st.regs r)
      (Expr.eval_lt_true (Expr.eval_const h1_lt) (Expr.eval_reg_of_eq hr14) hv1 h1_lt)
      (fun _ => by
        refine runs_seq_assign_le (v := vLen - 1)
          (Expr.eval_sub (Expr.eval_reg_of_eq hr14) (Expr.eval_const h1_lt) hv) ?_
        by_cases he : eLen < vLen - 1
        · have hmin : min (vLen - 1) eLen = eLen := Nat.min_eq_right (Nat.le_of_lt he)
          refine runs_cond_le (w := w) (p := p) (ω := ω) (v := 1)
            (Q := fun o st' => o = .normal ∧ st'.regs 16 = min (vLen - 1) eLen ∧
              st'.mem = st.mem ∧ st'.pos = st.pos ∧ ∀ r, r ≠ 16 → st'.regs r = st.regs r)
            (Expr.eval_lt_true
              (Expr.eval_reg_of_eq (v := eLen) (by simp [Function.update_of_ne, hr15]))
              (Expr.eval_reg_of_eq (v := vLen - 1) (by simp [Function.update_self])) he h1_lt)
            (fun _ => runs_assign_le (v := eLen)
              (Expr.eval_reg_of_eq (v := eLen) (by simp [Function.update_of_ne, hr15]))
              ⟨rfl, by simp [Function.update_self, hmin], rfl, rfl, fun r hr => by
                simp [Function.update_of_ne hr]⟩
              (by simp [Expr.size]))
            (fun h => absurd h Nat.one_ne_zero)
        · have hmin : min (vLen - 1) eLen = vLen - 1 := Nat.min_eq_left (Nat.not_lt.mp he)
          refine runs_cond_le (w := w) (p := p) (ω := ω) (v := 0)
            (Q := fun o st' => o = .normal ∧ st'.regs 16 = min (vLen - 1) eLen ∧
              st'.mem = st.mem ∧ st'.pos = st.pos ∧ ∀ r, r ≠ 16 → st'.regs r = st.regs r)
            (Expr.eval_lt_false
              (Expr.eval_reg_of_eq (v := eLen) (by simp [Function.update_of_ne, hr15]))
              (Expr.eval_reg_of_eq (v := vLen - 1) (by simp [Function.update_self]))
              (Nat.not_lt.mp he) h1_lt)
            (fun h => False.elim (h rfl))
            (fun _ => runs_nop_le
              ⟨rfl, by simp [Function.update_self, hmin], rfl, rfl, fun r hr => by
                simp [Function.update_of_ne hr]⟩
              (by simp [Expr.size])))
      (fun h => absurd h Nat.one_ne_zero)
    subst ho
    exact ⟨st', c, hrun, h16, hm, hp, hregs, by omega⟩
  · have hmin : min (vLen - 1) eLen = 0 := by
      have hv0 : vLen - 1 = 0 := by omega
      simp [hv0]
    obtain ⟨o, st', c, hrun, ⟨ho, h16, hm, hp, hregs⟩, hc⟩ := runs_cond_le
      (w := w) (p := p) (ω := ω) (st := st) (k := 0) (T := 20)
      (e := .bin .lt (.const 1) (.reg 14))
      (s₁ := .assign 16 (.bin .sub (.reg 14) (.const 1)) ;;
        .cond (.bin .lt (.reg 15) (.reg 16)) (.assign 16 (.reg 15)) .nop)
      (s₂ := .assign 16 (.const 0)) (v := 0)
      (Q := fun o st' => o = .normal ∧ st'.regs 16 = min (vLen - 1) eLen ∧
        st'.mem = st.mem ∧ st'.pos = st.pos ∧ ∀ r, r ≠ 16 → st'.regs r = st.regs r)
      (Expr.eval_lt_false (Expr.eval_const h1_lt) (Expr.eval_reg_of_eq hr14) (Nat.not_lt.mp hv1) h1_lt)
      (fun h => False.elim (h rfl))
      (fun _ => runs_assign_le (v := 0) (Expr.eval_const h0_lt)
        ⟨rfl, by simp [Function.update_self, hmin], rfl, rfl, fun r hr => by
          simp [Function.update_of_ne hr]⟩
        (by simp [Expr.size]))
    subst ho
    exact ⟨st', c, hrun, h16, hm, hp, hregs, by omega⟩

lemma runs_seq_gtComputeSteps_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {st : State} {vLen eLen k T : ℕ} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w) (hr14 : st.regs 14 = vLen) (hr15 : st.regs 15 = eLen) (hv : vLen < 2 ^ w)
    (hrest : ∀ st', st'.regs 16 = min (vLen - 1) eLen → st'.mem = st.mem → st'.pos = st.pos →
      (∀ r, r ≠ 16 → st'.regs r = st.regs r) →
      ∃ o st'' c₂, Runs w p ω s st' o st'' c₂ ∧ Q o st'' ∧ (k + 20 + 1) + c₂ ≤ T) :
    ∃ o st'' c, Runs w p ω (.seq gtComputeStepsStmt s) st o st'' c ∧ Q o st'' ∧ k + c ≤ T := by
  rcases gt_computeSteps_runs hw16 hr14 hr15 hv with ⟨st', c₁, hr₁, h16, hm, hp, hregs, hc₁⟩
  rcases hrest st' h16 hm hp hregs with ⟨o, st'', c₂, hr₂, hq, hc₂⟩
  exact ⟨o, st'', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st', c₁, c₂, hr₁, hr₂, rfl⟩), hq, by omega⟩

theorem gtBuildKeptTriples_meetsContract {w : ℕ} {p : Program} {bRev : ℕ}
    {kept jEs jTails jHeads : List ℕ}
    (hpRev : p.HasAt bRev gtRevPrimProcs) :
    MeetsContract w p (bRev + gtIdxBuildKeptTriples)
      (gtBuildKeptTriplesContract w kept jEs jTails jHeads) := by
  refine meetsContract_of_runs
    (hpRev.get (i := gtIdxBuildKeptTriples) (by simp [gtRevPrimProcs, gtIdxBuildKeptTriples]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨keptBase, jEsPtr, jTailsPtr, jHeadsPtr, triplesOutPtr, rfl,
    hw16, hKB, hjEB, hjTB, hjHB, hTB, hLenT, hLenHd, hK_lt, hK_w,
    hdjK, hdjE, hdjT, hdjHd, hAtK, hAtE, hAtT, hAtHd⟩
  have hlt_kB : keptBase < 2 ^ w := by omega
  have hlt_jEP : jEsPtr < 2 ^ w := by omega
  have hlt_jTP : jTailsPtr < 2 ^ w := by omega
  have hlt_jHP : jHeadsPtr < 2 ^ w := by omega
  have hlt_tO : triplesOutPtr < 2 ^ w := by omega
  have hlt_kLen : kept.length < 2 ^ w := by omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [gtRevPrimProcs, gtIdxBuildKeptTriples, List.getElem_cons_zero, gtBuildKeptTriplesStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (x := keptBase) (v := kept.length)
    (by simp [Expr.eval, startState])
    (by have hAtK0 := hAtK 0 (by simp); simpa [startState] using hAtK0)) ?_
  let body : Stmt :=
    .assign 7 (.load (.bin .add (.reg 0) (.bin .add (.const 1) (.reg 6)))) ;;
    .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
    .assign 9 (.load (.bin .add (.reg 2) (.reg 7))) ;;
    .assign 10 (.load (.bin .add (.reg 3) (.reg 7))) ;;
    .assign 11 (.bin .mul (.const 3) (.reg 6)) ;;
    .store (.bin .add (.reg 4) (.reg 11)) (.reg 8) ;;
    .store (.bin .add (.reg 4) (.bin .add (.reg 11) (.const 1))) (.reg 9) ;;
    .store (.bin .add (.reg 4) (.bin .add (.reg 11) (.const 2))) (.reg 10)
  let Inv : ℕ → State → Prop := fun k s =>
    s.regs 0 = keptBase ∧ s.regs 1 = jEsPtr ∧ s.regs 2 = jTailsPtr ∧
    s.regs 3 = jHeadsPtr ∧ s.regs 4 = triplesOutPtr ∧ s.regs 5 = kept.length ∧
    s.regs 6 = k ∧
    (∀ i (hi : i < k), ∃ hik : i < kept.length,
      s.mem (triplesOutPtr + 3 * i) = jEs.getD (kept[i]'hik) 0 ∧
      s.mem (triplesOutPtr + 3 * i + 1) = jTails.getD (kept[i]'hik) 0 ∧
      s.mem (triplesOutPtr + 3 * i + 2) = jHeads.getD (kept[i]'hik) 0) ∧
    ∀ addr, addr < triplesOutPtr ∨ triplesOutPtr + 3 * kept.length ≤ addr → s.mem addr = mem addr
  have hloop : Triple w p
      (fun s => s.regs 0 = keptBase ∧ s.regs 1 = jEsPtr ∧ s.regs 2 = jTailsPtr ∧
        s.regs 3 = jHeadsPtr ∧ s.regs 4 = triplesOutPtr ∧ s.regs 5 = kept.length ∧
        ∀ addr, addr < triplesOutPtr ∨ triplesOutPtr + 3 * kept.length ≤ addr → s.mem addr = mem addr)
      (forRange 6 (.const 0) (.reg 5) body)
      (normalPost (Inv kept.length))
      (fun _ => kept.length * (55 + Expr.size (.reg 5) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 5) + 5)) := by
    refine Triple.forRange_const 55 0 kept.length (Nat.zero_le _) h1_lt (fun _ => hlt_kLen)
      (fun s hI => ⟨by simp [Expr.eval, h0_lt], by
        rcases hI with ⟨r0, r1, r2, r3, r4, r5, hfr⟩
        exact ⟨by simpa [Function.update_of_ne] using r0, by simpa [Function.update_of_ne] using r1,
          by simpa [Function.update_of_ne] using r2, by simpa [Function.update_of_ne] using r3,
          by simpa [Function.update_of_ne] using r4, by simpa [Function.update_of_ne] using r5,
          by simp, fun _ hi => (Nat.not_lt_zero _ hi).elim, hfr⟩⟩)
      (fun _ s _ _ hI => hI.2.2.2.2.2.2.1)
      (fun _ s _ _ hI => by simp [Expr.eval, hI.2.2.2.2.2.1]) ?_
    intro i _ hi_lt s ω' ⟨r0, r1, r2, r3, r4, r5, r6, hres, hfr⟩
    set idx := kept[i]'hi_lt
    have hidx_mem : idx ∈ kept := List.getElem_mem hi_lt
    have hidx_lt : idx < jEs.length := hK_lt idx hidx_mem
    have hidx_w := hK_w idx hidx_mem
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt,
      List.getElem?_eq_getElem (hLenT ▸ hidx_lt), List.getElem?_eq_getElem (hLenHd ▸ hidx_lt),
      Option.getD_some] at hidx_w
    have hi_ltw : i < 2 ^ w := by omega
    have h1i_ltw : 1 + i < 2 ^ w := by omega
    have h3i_ltw : 3 * i < 2 ^ w := by omega
    have h3i1_ltw : 3 * i + 1 < 2 ^ w := by omega
    have h3i2_ltw : 3 * i + 2 < 2 ^ w := by omega
    have hKB_i_ltw : keptBase + (1 + i) < 2 ^ w := by omega
    have hE_idx_ltw : jEsPtr + idx < 2 ^ w := by omega
    have hT_idx_ltw : jTailsPtr + idx < 2 ^ w := by omega
    have hH_idx_ltw : jHeadsPtr + idx < 2 ^ w := by omega
    have hO_0_ltw : triplesOutPtr + 3 * i < 2 ^ w := by omega
    have hO_1_ltw : triplesOutPtr + 3 * i + 1 < 2 ^ w := by omega
    have hO_2_ltw : triplesOutPtr + 3 * i + 2 < 2 ^ w := by omega
    have hmem_k : s.mem (keptBase + (1 + i)) = idx := by
      rw [hfr _ (hdjK (1 + i) (by omega))]
      simpa [Nat.add_comm 1 i] using hAtK (1 + i) (by simp; omega)
    have hmem_e : s.mem (jEsPtr + idx) = jEs[idx]'hidx_lt := by
      rw [hfr _ (hdjE idx hidx_lt)]; exact hAtE idx hidx_lt
    have hmem_t : s.mem (jTailsPtr + idx) = jTails[idx]'(hLenT ▸ hidx_lt) := by
      rw [hfr _ (hdjT idx hidx_lt)]; exact hAtT idx (hLenT ▸ hidx_lt)
    have hmem_h : s.mem (jHeadsPtr + idx) = jHeads[idx]'(hLenHd ▸ hidx_lt) := by
      rw [hfr _ (hdjHd idx hidx_lt)]; exact hAtHd idx (hLenHd ▸ hidx_lt)
    refine runs_start_le ?_
    dsimp only [body]
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := idx)
      (by simp [Expr.eval, BinOp.eval, r0, r6, h1_lt, h1i_ltw, hKB_i_ltw]) hmem_k) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := jEs[idx]'hidx_lt)
      (by simp [Expr.eval, BinOp.eval, Function.update_self, r1, hE_idx_ltw]) hmem_e) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := jTails[idx]'(hLenT ▸ hidx_lt))
      (by simp [Expr.eval, BinOp.eval, Function.update_self, r2, hT_idx_ltw])
      hmem_t) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := jHeads[idx]'(hLenHd ▸ hidx_lt))
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, r3, hH_idx_ltw]) hmem_h) ?_
    refine runs_seq_assign_le (v := 3 * i)
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, r6, h3_lt, h3i_ltw]) ?_
    refine runs_seq_store_le (x := triplesOutPtr + 3 * i) (v := jEs[idx]'hidx_lt)
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, Function.update_self, r4, hO_0_ltw])
      (by simp [Expr.eval, Function.update_of_ne]) ?_
    refine runs_seq_store_le (x := triplesOutPtr + 3 * i + 1)
      (v := jTails[idx]'(hLenT ▸ hidx_lt))
      (Expr.eval_eq_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (v := triplesOutPtr) (by simp [Function.update_of_ne, r4]))
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := 3 * i) (by simp [Function.update_self]))
            (Expr.eval_const h1_lt) h3i1_ltw)
          (by omega))
        (by omega))
      (by simp [Expr.eval, Function.update_of_ne]) ?_
    refine runs_store_le (x := triplesOutPtr + 3 * i + 2)
      (v := jHeads[idx]'(hLenHd ▸ hidx_lt))
      (Expr.eval_eq_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (v := triplesOutPtr) (by simp [Function.update_of_ne, r4]))
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := 3 * i) (by simp [Function.update_self]))
            (Expr.eval_const h2_lt) h3i2_ltw)
          (by omega))
        (by omega))
      (by simp [Expr.eval, Function.update_of_ne]) ?_ ?_
    · refine ⟨⟨by simp [Function.update_of_ne, r0], by simp [Function.update_of_ne, r1],
        by simp [Function.update_of_ne, r2], by simp [Function.update_of_ne, r3],
        by simp [Function.update_of_ne, r4], by simp [Function.update_of_ne, r5],
        by simp [Function.update_self], ?_, ?_⟩, by simp [Function.update_of_ne, r6]⟩
      · intro j hj
        by_cases hj_eq : j = i
        · subst hj_eq
          refine ⟨hi_lt, ?_, ?_, ?_⟩
          · dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self, List.getD_eq_getElem _ _ hidx_lt]
          · dsimp only
            rw [Function.update_of_ne (by omega), Function.update_self,
              List.getD_eq_getElem _ _ (hLenT ▸ hidx_lt)]
          · dsimp only
            rw [Function.update_self, List.getD_eq_getElem _ _ (hLenHd ▸ hidx_lt)]
        · have hj_lt : j < i := by omega
          rcases hres j hj_lt with ⟨hjk, hm0, hm1, hm2⟩
          refine ⟨hjk, ?_, ?_, ?_⟩
          · dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hm0
          · dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hm1
          · dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hm2
      · intro addr haddr
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hfr addr haddr
    · dsimp only [body, Expr.size]; omega
  refine runs_seq_triple_le hloop
    ⟨by simp [Function.update_of_ne, startState], by simp [Function.update_of_ne, startState],
     by simp [Function.update_of_ne, startState], by simp [Function.update_of_ne, startState],
     by simp [Function.update_of_ne, startState], by simp [Function.update_self], fun _ _ => rfl⟩ ?_
  intro st' ⟨_, _, _, _, _, hr5, _, hres', hfr'⟩
  refine runs_ret_le (v := kept.length) (by simp [Expr.eval, hr5])
    ⟨keptBase, jEsPtr, jTailsPtr, jHeadsPtr, triplesOutPtr, rfl, rfl,
      fun i hi => let h := hres' i hi; ⟨h.2.1, h.2.2.1, h.2.2.2⟩, hfr'⟩ ?_
  dsimp only [gtBuildKeptTriplesContract, Expr.size]
  omega

end

end MinCostFlow.DynSpanner.Program
