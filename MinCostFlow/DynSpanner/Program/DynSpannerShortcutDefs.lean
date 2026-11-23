module

public import MinCostFlow.DynSpanner.Program.DynSpannerRevDefs
public import MinCostFlow.DynSpanner.Walks

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Walk-Shortcutting Definitions and Pure Stack Bridge (`DynSpannerShortcutDefs`)

Defines the deterministic Word-RAM walk-shortcutting procedure `dsShortcutEmbStmt`
(`lwIdxShortcutEmb = 2`), its contract `dsShortcutEmbContract`, and the pure stack/stamp
invariants connecting `shortcutWalk` (`Walks.lean`) to the linear-time stack pass.

For each edge `e` in `eL` (with `G.IsWalk (G.tail e) (G.head e) (emb e)`):
1. Pass 1 records the walk vertices `V_0, …, V_k` into `[permPtr .. permPtr + k + 1)`.
2. Pass 2 scans `i = k - 1` down to `0`, maintaining a singly-linked stack of 4-word nodes
   `[vert, edge, dir, next]` in `[permPtr + k + 1 .. nodePtr)` and generation stamps `dsVStampBase`:
   when `V_i` is already stamped (`∈ G.walkVertices cur Q`), nodes are popped and unstamped
   until reaching `V_i` (or `0` when `V_i = V_k`); otherwise a node is pushed and `V_i` stamped.
3. Pass 3 copies the final stack `shortcutWalk G (G.tail e) (emb e)` to compact `MWalkAt` format at
   `outWalkPtr = nodePtr`, clears remaining stamps (including `V_k`), updates `mEmbPtr[e] := outWalkPtr`,
   and advances `permPtr := outWalkPtr + 1 + 2 * outLen ≤ permPtr + 7 * (k + 1)`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure index and statement bodies -/

/-- Procedure index of `dsShortcutEmbStmt` inside `levelWalkProcs bOps bRev`. -/
def lwIdxShortcutEmb : ℕ := 2

/-- Single-edge shortcutting body inside `dsShortcutEmbStmt` (`r1..r7` persistent, `r8 = idx`,
`r9 = e`, `r10 = wPtr`, `r11 = k`, advancing `r5 = permPtr`). -/
def dsShortcutEdgeStmt (bOps : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
  .assign 10 (.load (.bin .add (.reg 4) (.reg 9))) ;;
  .assign 11 (.load (.reg 10)) ;;
  -- Pass 1: record V_0 = G.tail e, ..., V_k at [permPtr .. permPtr + k + 1)
  .call 12 (bOps + dgIdxGetTail) [.reg 1, .reg 9] ;;
  .store (.reg 5) (.reg 12) ;;
  forRange 13 (.const 0) (.reg 11)
    (.assign 14 (.load (.bin .add (.reg 10)
      (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 13))))) ;;
     .assign 15 (.load (.bin .add (.reg 10)
      (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 13))))) ;;
     .cond (.reg 15)
       (.call 12 (bOps + dgIdxGetHead) [.reg 1, .reg 14])
       (.call 12 (bOps + dgIdxGetTail) [.reg 1, .reg 14]) ;;
     .store (.bin .add (.reg 5) (.bin .add (.reg 13) (.const 1))) (.reg 12)) ;;
  -- Stamp V_k and initialize empty stack at nodeBase = permPtr + k + 1
  .assign 19 (.load (.bin .add (.reg 5) (.reg 11))) ;;
  .store (.bin .add (.reg 6) (.reg 19)) (.reg 7) ;;
  .assign 16 (.bin .add (.bin .add (.reg 5) (.reg 11)) (.const 1)) ;;
  .assign 17 (.reg 16) ;;
  .assign 18 (.const 0) ;;
  -- Pass 2: backward scan i = k - 1 - j for j = 0 .. k - 1
  forRange 13 (.const 0) (.reg 11)
    (.assign 21 (.bin .sub (.bin .sub (.reg 11) (.const 1)) (.reg 13)) ;;
     .assign 12 (.load (.bin .add (.reg 5) (.reg 21))) ;;
     .cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 12))) (.reg 7))
       (.cond (.reg 18)
          (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
            (.assign 20 (.const 0)) (.assign 20 (.const 1)))
          (.assign 20 (.const 0)) ;;
        .loop (.reg 20)
          (.assign 15 (.load (.reg 18)) ;;
           .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
           .assign 18 (.load (.bin .add (.reg 18) (.const 3))) ;;
           .cond (.reg 18)
             (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
               (.assign 20 (.const 0)) (.assign 20 (.const 1)))
             (.assign 20 (.const 0))))
       (.assign 14 (.load (.bin .add (.reg 10)
          (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
        .assign 15 (.load (.bin .add (.reg 10)
          (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
        .store (.reg 17) (.reg 12) ;;
        .store (.bin .add (.reg 17) (.const 1)) (.reg 14) ;;
        .store (.bin .add (.reg 17) (.const 2)) (.reg 15) ;;
        .store (.bin .add (.reg 17) (.const 3)) (.reg 18) ;;
        .assign 18 (.reg 17) ;;
        .assign 17 (.bin .add (.reg 17) (.const 4)) ;;
        .store (.bin .add (.reg 6) (.reg 12)) (.reg 7))) ;;
  -- Pass 3: copy stack to compact MWalkAt at nodePtr, clear vStamp, update mEmbPtr[e]
  .assign 22 (.reg 17) ;;
  .assign 21 (.bin .add (.reg 17) (.const 1)) ;;
  .assign 23 (.const 0) ;;
  .loop (.reg 18)
    (.assign 15 (.load (.reg 18)) ;;
     .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
     .assign 14 (.load (.bin .add (.reg 18) (.const 1))) ;;
     .store (.reg 21) (.reg 14) ;;
     .assign 14 (.load (.bin .add (.reg 18) (.const 2))) ;;
     .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
     .assign 21 (.bin .add (.reg 21) (.const 2)) ;;
     .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
     .assign 18 (.load (.bin .add (.reg 18) (.const 3)))) ;;
  .store (.bin .add (.reg 6) (.reg 19)) (.const 0) ;;
  .store (.reg 22) (.reg 23) ;;
  .store (.bin .add (.reg 4) (.reg 9)) (.reg 22) ;;
  .assign 5 (.reg 21)

/-- `args = [b, gPtr, eListPtr, numEdges, mEmbPtr, heapPtr]`: shortcuts each walk `emb e` (`e ∈ eL`)
to `shortcutWalk G (G.tail e) (emb e)` in linear time `O(∑ (emb e).length + eL.length + 1)`,
writing compact `MWalkAt` encodings in `[heapPtr .. ret)` and storing pointers in `mEmbPtr[e]`. -/
def dsShortcutEmbStmt (bOps : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 9 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 6)) (.bin .mul (.const 9) (.reg 7)))) ;;
  .assign 10 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
  .assign 9 (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 9))) ;;
  .assign 9 (.bin .add (.reg 9)
    (.bin .add (.bin .mul (.const 3) (.reg 7))
      (.bin .mul (.const 2) (.bin .add (.reg 8) (.const 1))))) ;;
  .assign 9 (.bin .add (.reg 9)
    (.bin .add (.bin .add (.reg 8) (.const 1))
      (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 8) (.const 1)) (.reg 7))))) ;;
  .assign 6 (.bin .add (.reg 9)
    (.bin .add (.bin .mul (.const 3) (.bin .mul (.bin .add (.reg 8) (.const 1)) (.reg 6)))
      (.bin .add (.bin .mul (.const 2) (.bin .add (.reg 8) (.const 1))) (.reg 6)))) ;;
  .assign 7 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
  forRange 8 (.const 0) (.reg 3) (dsShortcutEdgeStmt bOps) ;;
  .ret (.reg 5)

lemma dsShortcutEmbStmt_noRand (bOps : ℕ) : (dsShortcutEmbStmt bOps).NoRand := by
  simp [dsShortcutEmbStmt, dsShortcutEdgeStmt, forRange, WordRAM.forUp, Stmt.NoRand]

/-! ## Frame and Contract -/

/-- Memory cells outside `dsVStampBase`, `mEmbPtr + [0, eCapEmb)`, and `[heapPtr, ret)`. -/
def dsShortcutFrameCond (L vCap eCap b eCapEmb mEmbPtr heapPtr ret addr : ℕ) : Prop :=
  (∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v) ∧
  (∀ e < eCapEmb, addr ≠ mEmbPtr + e) ∧
  (addr < heapPtr ∨ ret ≤ addr)

lemma dsShortcutFrameCond_mono {L vCap eCap b eCapEmb mEmbPtr heapPtr h1 h2 addr : ℕ}
    (hle : h1 ≤ h2) (hfr : dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr h2 addr) :
    dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr h1 addr := by
  rcases hfr with ⟨h1', h2', h3'⟩
  refine ⟨h1', h2', ?_⟩
  rcases h3' with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hle h)

/-- Upper bound on heap allocation of `dsShortcutEmbStmt`. -/
def dsShortcutHeapSpace (eL : List ℕ) (emb : MinCostFlow.Embedding) : ℕ :=
  7 * ((eL.map fun e => (emb e).length).sum + eL.length)

/-- Contract for `dsShortcutEmbStmt` (`[b, gPtr, eListPtr, numEdges, mEmbPtr, heapPtr]`). -/
def dsShortcutEmbContract (w L vCap eCap b vCapG eCapG eCapEmb : ℕ)
    (G : MGraph) (eL : List ℕ) (emb : MinCostFlow.Embedding) : Contract where
  pre args mem := ∃ gPtr eListPtr mEmbPtr heapPtr,
    let heapMax := heapPtr + dsShortcutHeapSpace eL emb
    args = [b, gPtr, eListPtr, eL.length, mEmbPtr, heapPtr] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ b ∧
    b + dsFixedSize L vCap eCap ≤ heapPtr ∧
    heapMax < 2 ^ w ∧
    gPtr + dynGraphSize vCapG eCapG < 2 ^ w ∧
    eListPtr + eL.length < 2 ^ w ∧
    mEmbPtr + eCapEmb < 2 ^ w ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    mem (b + dsGenOff) + 1 < 2 ^ w ∧
    (∀ e < eCapEmb, (∀ v < vCap, mEmbPtr + e ≠ dsVStampBase b L vCap eCap + v) ∧
      (mEmbPtr + e < heapPtr ∨ heapMax ≤ mEmbPtr + e)) ∧
    (∀ v < vCap, mem (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
    (∀ i < dynGraphSize vCapG eCapG,
      dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr heapMax (gPtr + i)) ∧
    (∀ k < eL.length,
      dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr heapMax (eListPtr + k)) ∧
    eL.Nodup ∧ ListAt mem eListPtr eL ∧
    DynGraphAt mem gPtr vCapG eCapG G ∧ G.IsValid ∧
    (∀ v ∈ G.V, v < vCap) ∧
    (∀ e ∈ eL, e ∈ G.E ∧ e < eCapEmb ∧ G.IsWalk (G.tail e) (G.head e) (emb e) ∧
      MWalkAt mem (mem (mEmbPtr + e)) (emb e) ∧
      mem (mEmbPtr + e) + 1 + 2 * (emb e).length < 2 ^ w ∧
      ∀ addr, mem (mEmbPtr + e) ≤ addr → addr < mem (mEmbPtr + e) + 1 + 2 * (emb e).length →
        dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr heapMax addr)
  post args mem ret mem' := ∃ gPtr eListPtr mEmbPtr heapPtr,
    args = [b, gPtr, eListPtr, eL.length, mEmbPtr, heapPtr] ∧
    heapPtr ≤ ret ∧
    ret ≤ heapPtr + dsShortcutHeapSpace eL emb ∧
    (∀ v < vCap, mem' (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
    (∀ e ∈ eL,
      let pi := shortcutWalk G (G.tail e) (emb e)
      heapPtr ≤ mem' (mEmbPtr + e) ∧
      mem' (mEmbPtr + e) + 1 + 2 * pi.length ≤ ret ∧
      MWalkAt mem' (mem' (mEmbPtr + e)) pi) ∧
    ∀ addr, dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr ret addr →
      mem' addr = mem addr
  cost _ _ := 400 * (eL.map fun e => (emb e).length).sum + 300 * eL.length + 180

/-! ## Pure Stack / Stamp Helpers -/

/-- Prefix of `Q` popped by `suffixFrom G target cur Q` before hitting `target` (or the end). -/
def popPrefix (G : MGraph) (target cur : ℕ) : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => []
  | x :: xs => if cur = target then [] else x :: popPrefix G target (G.dst x) xs

lemma popPrefix_length_add_suffixFrom (G : MGraph) (target cur : ℕ) (Q : List (ℕ × Bool)) :
    (popPrefix G target cur Q).length + (suffixFrom G target cur Q).length = Q.length := by
  induction Q generalizing cur with
  | nil => simp [popPrefix, suffixFrom]
  | cons x xs ih =>
    simp only [popPrefix, suffixFrom]
    split_ifs
    · simp
    · simp only [List.length_cons]
      have := ih (G.dst x)
      omega

/-- Vertex along walk `P` starting at `u` at position `i ≤ P.length`. -/
def vertAt (G : MGraph) (u : ℕ) (P : List (ℕ × Bool)) (i : ℕ) : ℕ :=
  if i = 0 then u else match P[i - 1]? with | some x => G.dst x | none => u

lemma vertAt_zero (G : MGraph) (u : ℕ) (P : List (ℕ × Bool)) : vertAt G u P 0 = u := rfl

lemma vertAt_succ (G : MGraph) (u : ℕ) {P : List (ℕ × Bool)} {i : ℕ} (hi : i < P.length) :
    vertAt G u P (i + 1) = G.dst (P[i]'hi) := by
  simp [vertAt, hi]

/-- Endpoint predicate on a walk starting at `cur` and terminating at `vEnd`. -/
def EndsAt (G : MGraph) (cur : ℕ) : List (ℕ × Bool) → ℕ → Prop
  | [], vEnd => cur = vEnd
  | x :: xs, vEnd => EndsAt G (G.dst x) xs vEnd

lemma endsAt_of_isWalk {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk u v P) : EndsAt G u P v := by
  induction hW with
  | nil _ => rfl
  | cons _ _ _ ih => exact ih

lemma vertAt_length_eq_of_isWalk {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P → vertAt G u P P.length = v
  | _, _, [], .nil _ => rfl
  | _, _, [x], .cons _ _ (.nil _) => by simp [vertAt]
  | _, v, _ :: y :: xs, .cons _ _ hW => by
    have ih := vertAt_length_eq_of_isWalk hW
    simp only [List.length_cons, vertAt, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      List.getElem?_cons_succ] at ih ⊢
    rw [List.getElem?_eq_getElem (by simp)] at ih ⊢
    exact ih

/-- Singly-linked list of 4-word stack nodes `[vert, edge, dir, next]` (`0` = nil). -/
def StackListIn (G : MGraph) (nodeLo nodeHi : ℕ) (mem : ℕ → ℕ)
    (head cur : ℕ) : List (ℕ × Bool) → Prop
  | [] => head = 0
  | x :: xs =>
      nodeLo ≤ head ∧ head + 4 ≤ nodeHi ∧
      mem head = cur ∧
      mem (head + 1) = x.1 ∧
      mem (head + 2) = (if x.2 then 1 else 0) ∧
      StackListIn G nodeLo nodeHi mem (mem (head + 3)) (G.dst x) xs

lemma StackListIn.of_agree {G : MGraph} {nodeLo nodeHi : ℕ} {mem mem' : ℕ → ℕ}
    (hagree : ∀ a, nodeLo ≤ a → a < nodeHi → mem' a = mem a) :
    ∀ {head cur : ℕ} {xs : List (ℕ × Bool)},
      StackListIn G nodeLo nodeHi mem head cur xs →
      StackListIn G nodeLo nodeHi mem' head cur xs
  | _, _, [], rfl => rfl
  | head, cur, _ :: _, ⟨hlo, hhi, h0, h1, h2, hrest⟩ => by
    refine ⟨hlo, hhi, (hagree head hlo (by omega)).trans h0,
      (hagree (head + 1) (by omega) (by omega)).trans h1,
      (hagree (head + 2) (by omega) (by omega)).trans h2, ?_⟩
    rw [hagree (head + 3) (by omega) hhi]
    exact StackListIn.of_agree hagree hrest

lemma StackListIn.mono_hi {G : MGraph} {nodeLo h1 h2 : ℕ} {mem : ℕ → ℕ}
    (hle : h1 ≤ h2) :
    ∀ {head cur : ℕ} {xs : List (ℕ × Bool)},
      StackListIn G nodeLo h1 mem head cur xs →
      StackListIn G nodeLo h2 mem head cur xs
  | _, _, [], rfl => rfl
  | _, _, _ :: _, ⟨hlo, hhi, h0, h1', h2', hrest⟩ =>
    ⟨hlo, le_trans hhi hle, h0, h1', h2', StackListIn.mono_hi hle hrest⟩

/-- Generation stamp invariant for vertices currently on `S = G.walkVertices cur Q`. -/
def VStampInv (mem : ℕ → ℕ) (vStampPtr vCap stampVal gen0 : ℕ) (S : List ℕ) : Prop :=
  ∀ v < vCap, (v ∈ S → mem (vStampPtr + v) = stampVal) ∧
    (v ∉ S → mem (vStampPtr + v) ≤ gen0)

lemma endsAt_suffixFrom_of_mem {G : MGraph} {target cur vEnd : ℕ} :
    ∀ {Q : List (ℕ × Bool)},
      target ∈ G.walkVertices cur Q → EndsAt G cur Q vEnd →
      EndsAt G target (suffixFrom G target cur Q) vEnd
  | [], hmem, he => by
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hmem
    simp only [suffixFrom, EndsAt]
    change cur = vEnd at he
    exact hmem ▸ he
  | x :: xs, hmem, he => by
    simp only [suffixFrom]
    split_ifs with hct
    · rwa [← hct]
    · simp only [MGraph.walkVertices, List.mem_cons] at hmem
      have hmem' : target ∈ G.walkVertices (G.dst x) xs :=
        hmem.resolve_left (fun h => hct h.symm)
      exact endsAt_suffixFrom_of_mem hmem' he

lemma isWalk_drop_vertAt {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)} (hW : G.IsWalk u v P) :
    ∀ i ≤ P.length, G.IsWalk (vertAt G u P i) v (P.drop i) := by
  induction hW with
  | nil u₀ =>
    intro i hi
    simp only [List.length_nil, Nat.le_zero] at hi
    subst hi
    simpa [vertAt] using MGraph.IsWalk.nil u₀
  | @cons u₀ _ x xs he hsrc hW' ih =>
    intro i hi
    cases i with
    | zero => simpa [vertAt] using MGraph.IsWalk.cons he hsrc hW'
    | succ k =>
      have hk : k ≤ xs.length := Nat.le_of_succ_le_succ (by simpa using hi)
      have hsub := ih k hk
      have hve : vertAt G u₀ (x :: xs) (k + 1) = vertAt G (G.dst x) xs k := by
        cases k with
        | zero => simp [vertAt]
        | succ m =>
          simp only [vertAt, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
            List.getElem?_cons_succ]
          rw [List.getElem?_eq_getElem (by simp at hk; omega)]
      rw [hve]
      simpa using hsub

lemma walkVertices_lt_vCap {G : MGraph} {vCap : ℕ} (hVal : G.IsValid) (hvG : ∀ v ∈ G.V, v < vCap) :
    ∀ {cur vEnd : ℕ} {Q : List (ℕ × Bool)},
      cur ∈ G.V → G.IsWalk cur vEnd Q → ∀ v ∈ G.walkVertices cur Q, v < vCap
  | cur, _, [], hcur, .nil _, v, hv => by
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hv
    exact hv ▸ hvG cur hcur
  | cur, _, x :: xs, hcur, .cons he _ hW, v, hv => by
    simp only [MGraph.walkVertices, List.mem_cons] at hv
    have hdstV : G.dst x ∈ G.V := by
      rcases x with ⟨e, d⟩
      cases d <;> [exact (hVal e he).1; exact (hVal e he).2]
    rcases hv with rfl | hmem
    · exact hvG _ hcur
    · exact walkVertices_lt_vCap hVal hvG hdstV hW v hmem

lemma isWalk_mem_dst_V {G : MGraph} (hVal : G.IsValid) {x : ℕ × Bool} (he : x.1 ∈ G.E) :
    G.dst x ∈ G.V := by
  rcases x with ⟨e, d⟩
  cases d <;> [exact (hVal e he).1; exact (hVal e he).2]

lemma vertAt_mem_V {G : MGraph} (hVal : G.IsValid) {u v : ℕ} {P : List (ℕ × Bool)}
    (hu : u ∈ G.V) (hW : G.IsWalk u v P) :
    ∀ i ≤ P.length, vertAt G u P i ∈ G.V := by
  intro i hi
  cases i with
  | zero => simpa [vertAt] using hu
  | succ k =>
    have hk : k < P.length := by omega
    rw [vertAt_succ G u hk]
    exact (isWalk_mem_V_tail_head hVal hu hW _ (List.getElem_mem hk)).2

lemma suffixFrom_len_le (G : MGraph) (target cur : ℕ) :
    ∀ Q : List (ℕ × Bool), (suffixFrom G target cur Q).length ≤ Q.length
  | [] => by simp [suffixFrom]
  | x :: xs => by
    simp only [suffixFrom]
    split_ifs
    · exact le_rfl
    · exact Nat.le_succ_of_le (suffixFrom_len_le G target (G.dst x) xs)

lemma shortcutStep_len_le_succ (G : MGraph) (u : ℕ) (x : ℕ × Bool) (Q : List (ℕ × Bool)) :
    (shortcutStep G u x Q).length ≤ Q.length + 1 := by
  simp only [shortcutStep]
  split_ifs
  · exact Nat.le_succ_of_le (suffixFrom_len_le G u (G.dst x) Q)
  · simp

lemma rangeCost_shortcut_step {f : ℕ → ℕ} (C1 C2 : ℕ) :
    ∀ k, (∀ j < k, f (j + 1) ≤ f j + 1) →
    rangeCost (fun j => C1 + C2 * (f j + 1 - f (j + 1))) 0 k ≤
      C1 * k + C2 * (k + f 0) := by
  suffices h : ∀ k lo, (∀ j, lo ≤ j → j < lo + k → f (j + 1) ≤ f j + 1) →
      rangeCost (fun j => C1 + C2 * (f j + 1 - f (j + 1))) lo (lo + k) + C2 * f (lo + k) =
        C1 * k + C2 * (k + f lo) by
    intro k hle
    have := h k 0 (fun j _ hj => hle j (by omega))
    rw [Nat.zero_add] at this
    omega
  intro k
  induction k with
  | zero => intro lo _; simp [rangeCost]
  | succ k ih =>
    intro lo hle
    rw [rangeCost_step (by omega)]
    have ih' := ih (lo + 1) (fun j hj1 hj2 => hle j (by omega) (by omega))
    have hstep := hle lo le_rfl (by omega)
    have hsub : f lo + 1 - f (lo + 1) + f (lo + 1) = f lo + 1 := Nat.sub_add_cancel hstep
    rw [show lo + (k + 1) = lo + 1 + k by omega] at *
    calc C1 + C2 * (f lo + 1 - f (lo + 1)) +
          rangeCost (fun j => C1 + C2 * (f j + 1 - f (j + 1))) (lo + 1) (lo + 1 + k) +
          C2 * f (lo + 1 + k)
        = C1 + C2 * (f lo + 1 - f (lo + 1)) +
          (rangeCost (fun j => C1 + C2 * (f j + 1 - f (j + 1))) (lo + 1) (lo + 1 + k) +
            C2 * f (lo + 1 + k)) := by ring
      _ = C1 + C2 * (f lo + 1 - f (lo + 1)) + (C1 * k + C2 * (k + f (lo + 1))) := by rw [ih']
      _ = C1 * (k + 1) + C2 * k + C2 * (f lo + 1 - f (lo + 1) + f (lo + 1)) := by ring
      _ = C1 * (k + 1) + C2 * k + C2 * (f lo + 1) := by rw [hsub]
      _ = C1 * (k + 1) + C2 * (k + 1 + f lo) := by ring

lemma dsShortcutHeapSpace_take_succ (eL : List ℕ) (emb : MinCostFlow.Embedding) {k : ℕ}
    (hk : k < eL.length) :
    dsShortcutHeapSpace (eL.take (k + 1)) emb =
      dsShortcutHeapSpace (eL.take k) emb + 7 * ((emb (eL[k]'hk)).length + 1) := by
  simp only [dsShortcutHeapSpace, List.take_succ_eq_append_getElem hk, List.map_append,
    List.map_singleton, List.sum_append, List.sum_singleton, List.length_append,
    List.length_singleton]
  ring

lemma dsShortcutHeapSpace_take_le (eL : List ℕ) (emb : MinCostFlow.Embedding) (k : ℕ) :
    dsShortcutHeapSpace (eL.take k) emb ≤ dsShortcutHeapSpace eL emb := by
  obtain ⟨t, ht⟩ := List.take_prefix k eL
  have h1 : (eL.take k).length ≤ eL.length := by simp
  have h2 : ((eL.take k).map fun e => (emb e).length).sum ≤
      (eL.map fun e => (emb e).length).sum := by
    conv_rhs => rw [← ht, List.map_append, List.sum_append]
    exact Nat.le_add_right _ _
  dsimp only [dsShortcutHeapSpace]
  omega

lemma rangeCost_shortcut_outer (eL : List ℕ) (emb : MinCostFlow.Embedding) :
    rangeCost (fun k => match eL[k]? with | some e => 400 * (emb e).length + 300 | none => 0)
      0 eL.length = 400 * (eL.map fun e => (emb e).length).sum + 300 * eL.length := by
  rw [rangeCost_zero_eq_range]
  induction eL with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.getElem?_cons_zero,
      List.sum_cons]
    have hmap : (List.map Nat.succ (List.range xs.length)).map
        (fun k => match (x :: xs)[k]? with | some e => 400 * (emb e).length + 300 | none => 0) =
        (List.range xs.length).map
          (fun k => match xs[k]? with | some e => 400 * (emb e).length + 300 | none => 0) := by
      simp [List.map_map, Function.comp_def]
    rw [hmap, ih]
    ring

lemma shortcutWalk_drop_step {G : MGraph} {u : ℕ} {P : List (ℕ × Bool)} {j : ℕ}
    (hj : j < P.length) :
    let i := P.length - 1 - j
    have hi : i < P.length := by omega
    shortcutWalk G (vertAt G u P (P.length - (j + 1))) (P.drop (P.length - (j + 1))) =
      shortcutStep G (vertAt G u P i) (P[i]'hi)
        (shortcutWalk G (vertAt G u P (P.length - j)) (P.drop (P.length - j))) := by
  intro i hi
  have hsub1 : P.length - (j + 1) = i := by omega
  have hsub2 : P.length - j = i + 1 := by omega
  rw [hsub1, hsub2, List.drop_eq_getElem_cons hi, shortcutWalk, ← vertAt_succ G u hi]

lemma isWalk_getElem_src {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)} (hW : G.IsWalk u v P) :
    ∀ i (hi : i < P.length), (P[i]'hi).1 ∈ G.E ∧ G.src (P[i]'hi) = vertAt G u P i := by
  induction hW with
  | nil _ => intro _ hi; simp at hi
  | @cons u₀ _ x xs he hsrc hW' ih =>
    intro i hi
    cases i with
    | zero => simpa [vertAt] using ⟨he, hsrc⟩
    | succ k =>
      have hk : k < xs.length := Nat.lt_of_succ_lt_succ hi
      have hsub := ih k hk
      have hve : vertAt G u₀ (x :: xs) (k + 1) = vertAt G (G.dst x) xs k := by
        cases k with
        | zero => simp [vertAt]
        | succ m =>
          simp only [vertAt, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
            List.getElem?_cons_succ]
          rw [List.getElem?_eq_getElem (by omega)]
      rwa [hve]

lemma suffixFrom_isWalk_of_mem {G : MGraph} {target vEnd : ℕ} :
    ∀ {cur : ℕ} {Q : List (ℕ × Bool)},
      G.IsWalk cur vEnd Q → target ∈ G.walkVertices cur Q →
      G.IsWalk target vEnd (suffixFrom G target cur Q)
  | cur, [], .nil _, hmem => by
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hmem
    simpa [suffixFrom, hmem] using MGraph.IsWalk.nil target
  | cur, x :: xs, .cons he hsrc hW', hmem => by
    simp only [suffixFrom]
    split_ifs with hct
    · exact hct ▸ .cons he hsrc hW'
    · simp only [MGraph.walkVertices, List.mem_cons] at hmem
      exact suffixFrom_isWalk_of_mem hW' (hmem.resolve_left (fun h => hct h.symm))

end

end MinCostFlow.DynSpanner.Program
