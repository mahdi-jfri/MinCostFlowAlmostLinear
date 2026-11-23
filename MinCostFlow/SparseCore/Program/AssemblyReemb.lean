module

public import MinCostFlow.SparseCore.Program.AssemblyStatement
public import MinCostFlow.SparseCore.Program.AssemblyEmpty
public import MinCostFlow.SparseCore.LSFInit

/-!
# Re-embedded edge list extension and layout framing (`AssemblyReemb`)

The solver's cycle query uses an indexed max-heap whose keys depend on each candidate edge's
own-level embedding. When an update (`op 0`) runs on a level, the heap maintainer needs the list of
surviving off-spanner edges whose embedding changed in each branch (`reembList`).

This file extends `sparseCoreOrdMachineContractKF`:
* `BranchOutReembAt`: appends `2 * k` words `[reembPtr_j, reembLen_j]` immediately after the
  `1 + 4 * k` words of `BranchOutAt` (`heap + 1 + 4 * k + 2 * j`), so every memory state satisfying
  `BranchOutReembAt` also satisfies `BranchOutAt` at the exact same address `heap`.
* `sparseCoreOrdMachineContractKFR`: `sparseCoreOrdMachineContractKF` whose `op 0` postcondition
  strengthens `BranchOutAt` to `BranchOutReembAt` for a per-branch report function `reemb`.
* `SparseCoreOrdProgramUniformReemb`, `SparseCoreOrdProgramUniformAuto` (`R` before `L`, for
  limb-count-independent LSF initializers `lsfInit : ℕ → LSFInit`), and
  `SparseCoreOrdProgramUniformReembAuto`.
* `dsRep_implements_kf_of_kfr`: any program meeting `KFR` automatically meets `KF`.
* Memory-agreement helpers `readList_of_agree`, `smallBatchAt_of_agree`, `ordEditsAt_of_agree`,
  `ordListAt_of_agree`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## Memory-agreement helpers -/

/-- `readList` depends only on `[a, a + n)`. -/
theorem readList_of_agree {mem₁ mem₂ : ℕ → ℕ} {a n : ℕ}
    (h : ∀ x, a ≤ x → x < a + n → mem₂ x = mem₁ x) :
    readList mem₂ a n = readList mem₁ a n := by
  apply List.ext_getElem (by simp [readList_length])
  intro i hi _
  rw [readList_getElem, readList_getElem]
  rw [readList_length] at hi
  exact h (a + i) (by omega) (by omega)

/-- `ListAt` depends only on `[a, a + xs.length)`. -/
theorem listAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (hL : ListAt mem₁ a xs)
    (h : ∀ x, a ≤ x → x < a + xs.length → mem₂ x = mem₁ x) :
    ListAt mem₂ a xs := by
  intro i hi
  rw [h (a + i) (by omega) (by omega)]
  exact hL i hi

/-- `UpdateAt` depends only on `[a, a + len)`. -/
theorem updateAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (hU : UpdateAt mem₁ a G u len)
    (h : ∀ x, a ≤ x → x < a + len → mem₂ x = mem₁ x) :
    UpdateAt mem₂ a G u len := by
  cases u with
  | insert e x y =>
    exact ⟨hU.1, listAt_of_agree hU.2 fun z hz1 hz2 => h z hz1 (by simp [hU.1] at hz2 ⊢; omega)⟩
  | delete e =>
    exact ⟨hU.1, listAt_of_agree hU.2 fun z hz1 hz2 => h z hz1 (by simp [hU.1] at hz2 ⊢; omega)⟩
  | split v v' St Sh =>
    rcases hU with ⟨Lt, Lh, hnd1, hnd2, ht, hh, hlen, hLA⟩ | ⟨Lt, Lh, hnd1, hnd2, ht, hh, hlen, hLA⟩
    · left
      refine ⟨Lt, Lh, hnd1, hnd2, ht, hh, hlen, listAt_of_agree hLA fun z hz1 hz2 => h z hz1 ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil] at hz2; omega
    · right
      refine ⟨Lt, Lh, hnd1, hnd2, ht, hh, hlen, listAt_of_agree hLA fun z hz1 hz2 => h z hz1 ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil] at hz2; omega

/-- `BatchBodyAt` depends only on `[a, a + words)`. -/
theorem batchBodyAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {words : ℕ}
    (hB : BatchBodyAt mem₁ a G U words)
    (h : ∀ x, a ≤ x → x < a + words → mem₂ x = mem₁ x) :
    BatchBodyAt mem₂ a G U words := by
  induction U generalizing a G words with
  | nil => exact hB
  | cons u us ih =>
    rcases hB with ⟨len, hlen, hU, hrest⟩
    exact ⟨len, hlen,
      updateAt_of_agree hU (fun x hx1 hx2 => h x hx1 (by omega)),
      ih hrest (fun x hx1 hx2 => h x (by omega) (by omega))⟩

/-- `SmallBatchAt` depends only on `[a, a + words)`. -/
theorem smallBatchAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {words : ℕ}
    (hB : SmallBatchAt mem₁ a G U words)
    (h : ∀ x, a ≤ x → x < a + words → mem₂ x = mem₁ x) :
    SmallBatchAt mem₂ a G U words := by
  have hw : 1 ≤ words := hB.1.1
  exact ⟨⟨hw, (h a le_rfl (by omega)).trans hB.1.2.1,
    batchBodyAt_of_agree hB.1.2.2 (fun x hx1 hx2 => h x (by omega) (by omega))⟩, hB.2⟩

private theorem decodeOrdEdit_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ}
    (h : ∀ x, a ≤ x → x < a + (decodeOrdEdit mem₁ a).2 → mem₂ x = mem₁ x) :
    decodeOrdEdit mem₂ a = decodeOrdEdit mem₁ a := by
  unfold decodeOrdEdit at h ⊢
  by_cases h0 : mem₁ a = 0
  · simp only [h0, ↓reduceIte] at h
    have ha0 : mem₂ a = 0 := (h a le_rfl (by omega)).trans h0
    have ha1 : mem₂ (a + 1) = mem₁ (a + 1) := h (a + 1) (by omega) (by omega)
    simp only [h0, ha0, ha1, ↓reduceIte]
  · by_cases h12 : mem₁ a = 1 ∨ mem₁ a = 2
    · simp only [h0, h12, ↓reduceIte] at h
      have ha0 : mem₂ a = mem₁ a := h a le_rfl (by omega)
      have ha1 : mem₂ (a + 1) = mem₁ (a + 1) := h (a + 1) (by omega) (by omega)
      have ha2 : mem₂ (a + 2) = mem₁ (a + 2) := h (a + 2) (by omega) (by omega)
      have ha3 : mem₂ (a + 3) = mem₁ (a + 3) := h (a + 3) (by omega) (by omega)
      have hrl : readList mem₂ (a + 4) (mem₁ (a + 3)) = readList mem₁ (a + 4) (mem₁ (a + 3)) :=
        readList_of_agree fun x hx1 hx2 => h x (by omega) (by omega)
      simp only [ha0, h0, h12, ha1, ha2, ha3, hrl, ↓reduceIte]
    · by_cases h3 : mem₁ a = 3
      · simp [h3] at h
        have ha0 : mem₂ a = 3 := (h a le_rfl (by omega)).trans h3
        have ha1 : mem₂ (a + 1) = mem₁ (a + 1) := h (a + 1) (by omega) (by omega)
        have ha2 : mem₂ (a + 2) = mem₁ (a + 2) := h (a + 2) (by omega) (by omega)
        have ha3 : mem₂ (a + 3) = mem₁ (a + 3) := h (a + 3) (by omega) (by omega)
        simp [ha0, h3, ha1, ha2, ha3]
      · simp only [h0, h12, h3, ↓reduceIte] at h
        have ha0 : mem₂ a = mem₁ a := h a le_rfl (by omega)
        have ha1 : mem₂ (a + 1) = mem₁ (a + 1) := h (a + 1) (by omega) (by omega)
        have ha2 : mem₂ (a + 2) = mem₁ (a + 2) := h (a + 2) (by omega) (by omega)
        simp only [ha0, h0, h12, h3, ha1, ha2, ↓reduceIte]

private theorem decodeOrdEdits_of_agree {mem₁ mem₂ : ℕ → ℕ} {cnt a : ℕ}
    (h : ∀ x, a ≤ x → x < a + (decodeOrdEdits mem₁ cnt a).2.sum → mem₂ x = mem₁ x) :
    decodeOrdEdits mem₂ cnt a = decodeOrdEdits mem₁ cnt a := by
  induction cnt generalizing a with
  | zero => rfl
  | succ cnt ih =>
    have hsum : (decodeOrdEdits mem₁ (cnt + 1) a).2.sum =
        (decodeOrdEdit mem₁ a).2 + (decodeOrdEdits mem₁ cnt (a + (decodeOrdEdit mem₁ a).2)).2.sum := by
      simp [decodeOrdEdits]
    have hd := decodeOrdEdit_of_agree (mem₁ := mem₁) (mem₂ := mem₂) (a := a)
      (fun x hx1 hx2 => h x hx1 (by omega))
    have hrest := ih (a := a + (decodeOrdEdit mem₁ a).2)
      (fun x hx1 hx2 => h x (by omega) (by omega))
    simp only [decodeOrdEdits, hd, hrest]

/-- `OrdEditsAt` depends only on `[a, a + words)`. -/
theorem ordEditsAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {ed : List OrdEdit} {words : ℕ}
    (hE : OrdEditsAt mem₁ a ed words)
    (h : ∀ x, a ≤ x → x < a + words → mem₂ x = mem₁ x) :
    OrdEditsAt mem₂ a ed words := by
  rcases hE with ⟨hread, hlen, hsmall⟩
  have ha0 : mem₂ a = mem₁ a := h a le_rfl (by omega)
  have hdec : decodeOrdEdits mem₂ (mem₂ a) (a + 1) = decodeOrdEdits mem₁ (mem₁ a) (a + 1) := by
    rw [ha0]
    exact decodeOrdEdits_of_agree fun x hx1 hx2 => h x (by omega) (by omega)
  refine ⟨?_, ?_, hsmall⟩
  · unfold readOrdEdits; rw [hdec]; exact hread
  · rw [hdec]; exact hlen

private theorem readOrdRecords_of_agree {mem₁ mem₂ : ℕ → ℕ} {cnt a : ℕ}
    (h : ∀ x, a ≤ x → x < a + ordRecordsWords (readOrdRecords mem₁ cnt a) → mem₂ x = mem₁ x) :
    readOrdRecords mem₂ cnt a = readOrdRecords mem₁ cnt a := by
  induction cnt generalizing a with
  | zero => rfl
  | succ cnt ih =>
    have hws : ordRecordsWords (readOrdRecords mem₁ (cnt + 1) a) =
        2 + mem₁ (a + 1) + ordRecordsWords (readOrdRecords mem₁ cnt (a + 2 + mem₁ (a + 1))) := by
      simp [readOrdRecords, ordRecordsWords, readList_length]
    have ha0 := h a le_rfl (by omega)
    have ha1 := h (a + 1) (by omega) (by omega)
    have hrl := readList_of_agree (mem₁ := mem₁) (mem₂ := mem₂) (a := a + 2) (n := mem₁ (a + 1))
      (fun x hx1 hx2 => h x (by omega) (by omega))
    have hrest := ih (a := a + 2 + mem₁ (a + 1)) (fun x hx1 hx2 => h x (by omega) (by omega))
    simp only [readOrdRecords, ha0, ha1, hrl, hrest]

/-- `OrdListAt` depends only on `[a, a + words)`. -/
theorem ordListAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {ord : ℕ → List End} {words : ℕ}
    (hO : OrdListAt mem₁ a ord words)
    (h : ∀ x, a ≤ x → x < a + words → mem₂ x = mem₁ x) :
    OrdListAt mem₂ a ord words := by
  rcases hO with ⟨hnd, hread, hlen⟩
  have hlen' : words = 1 + ordRecordsWords (readOrdRecords mem₁ (mem₁ a) (a + 1)) := hlen
  have ha0 : mem₂ a = mem₁ a := h a le_rfl (by omega)
  have hrec : readOrdRecordsAt mem₂ a = readOrdRecordsAt mem₁ a := by
    unfold readOrdRecordsAt
    rw [ha0]
    exact readOrdRecords_of_agree fun x hx1 hx2 => h x (by omega) (by omega)
  exact ⟨hrec ▸ hnd, by unfold readOrd; rw [hrec]; exact hread, by rw [hrec]; exact hlen⟩

/-- `SmallBatchAt` transfers across a contiguous copy from `src` to `dst`. -/
theorem smallBatchAt_shift {mem₁ mem₂ : ℕ → ℕ} {src dst : ℕ} {G : MGraph} {U : List Update} {words : ℕ}
    (hB : SmallBatchAt mem₁ src G U words)
    (h : ∀ i < words, mem₂ (dst + i) = mem₁ (src + i)) :
    SmallBatchAt mem₂ dst G U words := by
  have hw : 1 ≤ words := hB.1.1
  have hlist : ∀ {a b : ℕ} {xs : List ℕ}, ListAt mem₁ a xs →
      (∀ i < xs.length, mem₂ (b + i) = mem₁ (a + i)) → ListAt mem₂ b xs := fun hL hc i hi => by
    rw [hc i hi]; exact hL i hi
  have hupd : ∀ {a b : ℕ} {H : MGraph} {u : Update} {len : ℕ}, UpdateAt mem₁ a H u len →
      (∀ i < len, mem₂ (b + i) = mem₁ (a + i)) → UpdateAt mem₂ b H u len := by
    intro a b H u len hU hc
    cases u with
    | insert e x y =>
      exact ⟨hU.1, hlist hU.2 fun i hi => hc i (by simp [hU.1] at hi ⊢; omega)⟩
    | delete e =>
      exact ⟨hU.1, hlist hU.2 fun i hi => hc i (by simp [hU.1] at hi ⊢; omega)⟩
    | split v v' St Sh =>
      rcases hU with ⟨Lt, Lh, hnd1, hnd2, ht, hh, hlen, hLA⟩ | ⟨Lt, Lh, hnd1, hnd2, ht, hh, hlen, hLA⟩
      · left; exact ⟨Lt, Lh, hnd1, hnd2, ht, hh, hlen, hlist hLA fun i hi =>
          hc i (by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega)⟩
      · right; exact ⟨Lt, Lh, hnd1, hnd2, ht, hh, hlen, hlist hLA fun i hi =>
          hc i (by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega)⟩
  have hbody : ∀ {U : List Update} {a b : ℕ} {H : MGraph} {w : ℕ}, BatchBodyAt mem₁ a H U w →
      (∀ i < w, mem₂ (b + i) = mem₁ (a + i)) → BatchBodyAt mem₂ b H U w := by
    intro U
    induction U with
    | nil => intro _ _ _ _ h1 _; exact h1
    | cons u us ih =>
      intro a b H w h1 hc
      rcases h1 with ⟨len, hlen, hU, hrest⟩
      exact ⟨len, hlen, hupd hU (fun i hi => hc i (by omega)),
        ih hrest (fun i hi => by simpa [Nat.add_assoc] using hc (len + i) (by omega))⟩
  have h0' : mem₂ dst = mem₁ src := by simpa using h 0 (by omega)
  exact ⟨⟨hw, h0'.trans hB.1.2.1,
    hbody hB.1.2.2 fun i hi => by simpa [Nat.add_assoc] using h (1 + i) (by omega)⟩, hB.2⟩

/-- `OrdEditsAt` transfers across a contiguous copy from `src` to `dst`. -/
theorem ordEditsAt_shift {mem₁ mem₂ : ℕ → ℕ} {src dst : ℕ} {ed : List OrdEdit} {words : ℕ}
    (hE : OrdEditsAt mem₁ src ed words)
    (h : ∀ i < words, mem₂ (dst + i) = mem₁ (src + i)) :
    OrdEditsAt mem₂ dst ed words := by
  have hrl : ∀ {a b n : ℕ}, (∀ i < n, mem₂ (b + i) = mem₁ (a + i)) →
      readList mem₂ b n = readList mem₁ a n := by
    intro a b n hc
    apply List.ext_getElem (by simp [readList_length])
    intro i hi _
    rw [readList_getElem, readList_getElem]; rw [readList_length] at hi; exact hc i hi
  have hdec1 : ∀ {a b : ℕ}, (∀ i < (decodeOrdEdit mem₁ a).2, mem₂ (b + i) = mem₁ (a + i)) →
      decodeOrdEdit mem₂ b = decodeOrdEdit mem₁ a := by
    intro a b hc
    unfold decodeOrdEdit at hc ⊢
    by_cases h0 : mem₁ a = 0
    · simp only [h0, ↓reduceIte] at hc
      have h0' : mem₂ b = mem₁ a := by simpa using hc 0 (by omega)
      have hb0 : mem₂ b = 0 := h0'.trans h0
      have hb1 : mem₂ (b + 1) = mem₁ (a + 1) := hc 1 (by omega)
      simp only [h0, hb0, hb1, ↓reduceIte]
    · by_cases h12 : mem₁ a = 1 ∨ mem₁ a = 2
      · simp only [h0, h12, ↓reduceIte] at hc
        have hb0 : mem₂ b = mem₁ a := by simpa using hc 0 (by omega)
        have hb1 : mem₂ (b + 1) = mem₁ (a + 1) := hc 1 (by omega)
        have hb2 : mem₂ (b + 2) = mem₁ (a + 2) := hc 2 (by omega)
        have hb3 : mem₂ (b + 3) = mem₁ (a + 3) := hc 3 (by omega)
        have hrl' : readList mem₂ (b + 4) (mem₁ (a + 3)) = readList mem₁ (a + 4) (mem₁ (a + 3)) :=
          hrl fun i hi => by simpa [Nat.add_assoc] using hc (4 + i) (by omega)
        simp only [hb0, h0, h12, hb1, hb2, hb3, hrl', ↓reduceIte]
      · by_cases h3 : mem₁ a = 3
        · simp [h3] at hc
          have h0' : mem₂ b = mem₁ a := by simpa using hc 0 (by omega)
          have hb0 : mem₂ b = 3 := h0'.trans h3
          have hb1 : mem₂ (b + 1) = mem₁ (a + 1) := hc 1 (by omega)
          have hb2 : mem₂ (b + 2) = mem₁ (a + 2) := hc 2 (by omega)
          have hb3 : mem₂ (b + 3) = mem₁ (a + 3) := hc 3 (by omega)
          simp [hb0, h3, hb1, hb2, hb3]
        · simp only [h0, h12, h3, ↓reduceIte] at hc
          have hb0 : mem₂ b = mem₁ a := by simpa using hc 0 (by omega)
          have hb1 : mem₂ (b + 1) = mem₁ (a + 1) := hc 1 (by omega)
          have hb2 : mem₂ (b + 2) = mem₁ (a + 2) := hc 2 (by omega)
          simp only [hb0, h0, h12, h3, hb1, hb2, ↓reduceIte]
  have hdecs : ∀ {cnt a b : ℕ}, (∀ i < (decodeOrdEdits mem₁ cnt a).2.sum, mem₂ (b + i) = mem₁ (a + i)) →
      decodeOrdEdits mem₂ cnt b = decodeOrdEdits mem₁ cnt a := by
    intro cnt
    induction cnt with
    | zero => intro _ _ _; rfl
    | succ cnt ih =>
      intro a b hc
      have hsum : (decodeOrdEdits mem₁ (cnt + 1) a).2.sum =
          (decodeOrdEdit mem₁ a).2 + (decodeOrdEdits mem₁ cnt (a + (decodeOrdEdit mem₁ a).2)).2.sum := by
        simp [decodeOrdEdits]
      have hd := hdec1 (a := a) (b := b) fun i hi => hc i (by omega)
      have hrest := ih (a := a + (decodeOrdEdit mem₁ a).2) (b := b + (decodeOrdEdit mem₁ a).2)
        fun i hi => by simpa [Nat.add_assoc] using hc ((decodeOrdEdit mem₁ a).2 + i) (by omega)
      simp only [decodeOrdEdits, hd, hrest]
  rcases hE with ⟨hread, hlen, hsmall⟩
  have hb0 : mem₂ dst = mem₁ src := by simpa using h 0 (by omega)
  have hdec : decodeOrdEdits mem₂ (mem₂ dst) (dst + 1) = decodeOrdEdits mem₁ (mem₁ src) (src + 1) := by
    rw [hb0]
    exact hdecs fun i hi => by simpa [Nat.add_assoc] using h (1 + i) (by omega)
  exact ⟨by unfold readOrdEdits; rw [hdec]; exact hread, by rw [hdec]; exact hlen, hsmall⟩

/-! ## Re-embedded edge list extension of `BranchOutAt` and `sparseCoreOrdMachineContractKF` -/

/-- `BranchOutAt` together with the per-branch list of re-embedded edges (`reembList`). For each
branch `j < k`, the two words at `heap + 1 + 4 * k + 2 * j` and
`heap + 2 + 4 * k + 2 * j` hold `[reembPtr_j, reembLen_j]` with
`readList mem reembPtr_j reembLen_j = reemb j`. -/
def BranchOutReembAt (mem : ℕ → ℕ) (heap k : ℕ) (G_old : ℕ → MGraph)
    (U_S : ℕ → List Update) (ord_old ord_new : ℕ → ℕ → List End)
    (reemb : ℕ → List ℕ) : Prop :=
  BranchOutAt mem heap k G_old U_S ord_old ord_new ∧
  ∀ j < k, readList mem (mem (heap + 1 + 4 * k + 2 * j))
    (mem (heap + 2 + 4 * k + 2 * j)) = reemb j

/-- Per-branch re-embedded edge list function attached to a `SparseCoreRestartTool`: given a state
`s`, an update batch `U`, and the new order `ord'`, returns for each branch `j` the list of edges
whose embedding changed in that step. -/
abbrev ToolReembFn (tool : SparseCoreRestartTool) : Type :=
  tool.State → List Update → (ℕ → List End) → ℕ → List ℕ

/-- Per-branch re-embedded edge list for the bundle-tree tool: `[]` on an empty state, and
`brReemb (st.trees j) U st.ord ord'` on a nonempty state. -/
def bundleToolReemb {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    (brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ) :
    ToolReembFn (sparseCoreProgTool lsfInit C_lsst depth impl) :=
  fun st U ord' j =>
    if st.isNonempty then brReemb (st.trees j) U st.ord ord' else []

/-- Extension of `sparseCoreOrdMachineContractKF` whose Update (`op 0`) postcondition also writes
the per-branch `reembList` immediately after `BranchOutAt` (`BranchOutReembAt`). -/
noncomputable def sparseCoreOrdMachineContractKFR {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreRestartTool) (reemb : ToolReembFn tool)
    (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (SparseCoreOrdAbs tool) :=
  let D := sparseCoreOrdMachineContractKF fmt L tool initialGraph k M N vCap eCap capExp P
    allocation
  { D with
    post := fun i a args mem a' mem' => match i with
      | 0 => D.post 0 a args mem a' mem' ∧
          ∀ j < k, readList mem' (mem' (heapArg args + 1 + 4 * k + 2 * j))
            (mem' (heapArg args + 2 + 4 * k + 2 * j)) =
            reemb a.st (ordUpdateBatch a args mem) (ordUpdateOrder a args mem) j
      | i => D.post i a args mem a' mem' }

/-- Any implementation of `sparseCoreOrdMachineContractKFR` automatically implements
`sparseCoreOrdMachineContractKF` with the same representation, constants, and allocation. -/
theorem dsRep_implements_kf_of_kfr {w : ℕ} {fmt : Num.Format w} {L : ℕ}
    {tool : SparseCoreRestartTool} {reemb : ToolReembFn tool}
    {initialGraph : MGraph} {k M N vCap eCap capExp : ℕ}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)}
    (h : R.Implements w p init op
      (sparseCoreOrdMachineContractKFR fmt L tool reemb initialGraph k M N vCap eCap capExp P
        allocation)) :
    R.Implements w p init op
      (sparseCoreOrdMachineContractKF fmt L tool initialGraph k M N vCap eCap capExp P
        allocation) := by
  refine ⟨h.1, h.2.1, fun i b s x args mem pos ω hargs hhead hrep hpre hfoot hz hsp => ?_⟩
  obtain ⟨body, hbody, o, st', c, hrun, s', x', hrep', hpost, hresp, hcost⟩ :=
    h.2.2 i b s x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
  refine ⟨body, hbody, o, st', c, hrun, s', x', hrep', ?_, hresp, hcost⟩
  cases i with
  | zero => exact hpost.1
  | succ _ => exact hpost

/-- Uniform statement for `sparseCoreOrdMachineContractKFR` (including `reembList` on `op 0`),
with `wordExp` depending only on `capExp` (before `limbMul`). -/
def SparseCoreOrdProgramUniformReemb (C_lsst : ℝ) (lsfInit : ℕ → ℕ → LSFInit)
    (impl : SparsifyImpl)
    (brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ)
    (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w) (L : ℕ),
        ∃ R : DSRep (SparseCoreOrdAbs
            (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)),
          R.Local ∧ ∀ (G : MGraph) (k M N vCap eCap : ℕ),
            fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
            R.Implements w p init op
              (sparseCoreOrdMachineContractKFR fmt L
                (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                (bundleToolReemb (brReemb depth))
                G k M N vCap eCap capExp P allocation)

/-- `R`-before-`L` uniform statement for a limb-count-independent LSF initializer
`lsfInitAuto : ℕ → LSFInit` (parameterized only by precision `fmt.precision`), with `reembList`
reported on `op 0` and `wordExp` independent of `limbMul`. -/
def SparseCoreOrdProgramUniformReembAuto (C_lsst : ℝ) (lsfInitAuto : ℕ → LSFInit)
    (impl : SparsifyImpl)
    (brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ)
    (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w),
        ∃ R : DSRep (SparseCoreOrdAbs
            (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)),
          R.Local ∧ ∀ (L : ℕ) (G : MGraph) (k M N vCap eCap : ℕ),
            fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
            R.Implements w p init op
              (sparseCoreOrdMachineContractKFR fmt L
                (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                (bundleToolReemb (brReemb depth))
                G k M N vCap eCap capExp P allocation)

/-- `R`-before-`L` uniform statement for `sparseCoreOrdMachineContractKF`. -/
def SparseCoreOrdProgramUniformAuto (C_lsst : ℝ) (lsfInitAuto : ℕ → LSFInit)
    (impl : SparsifyImpl) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w),
        ∃ R : DSRep (SparseCoreOrdAbs
            (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)),
          R.Local ∧ ∀ (L : ℕ) (G : MGraph) (k M N vCap eCap : ℕ),
            fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
            R.Implements w p init op
              (sparseCoreOrdMachineContractKF fmt L
                (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                G k M N vCap eCap capExp P allocation)

/-- `SparseCoreOrdProgramUniformReemb` immediately implies `SparseCoreOrdProgramUniform`. -/
theorem sparseCoreOrdProgramUniform_of_reemb {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit}
    {impl : SparsifyImpl}
    {brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (h : SparseCoreOrdProgramUniformReemb C_lsst lsfInit impl brReemb p init op) :
    SparseCoreOrdProgramUniform C_lsst lsfInit impl p init op := fun capExp => by
  obtain ⟨wordExp, hw⟩ := h capExp
  refine ⟨wordExp, fun limbMul => ?_⟩
  obtain ⟨P, allocation, hwe, hP⟩ := hw limbMul
  refine ⟨P, allocation, hwe, fun depth w fmt L => ?_⟩
  obtain ⟨R, hloc, hR⟩ := hP depth w fmt L
  exact ⟨R, hloc, fun G k M N vCap eCap hfmt hcap =>
    dsRep_implements_kf_of_kfr (hR G k M N vCap eCap hfmt hcap)⟩

/-- `SparseCoreOrdProgramUniformReembAuto` immediately implies `SparseCoreOrdProgramUniformAuto`. -/
theorem sparseCoreOrdProgramUniformAuto_of_reemb {C_lsst : ℝ} {lsfInitAuto : ℕ → LSFInit}
    {impl : SparsifyImpl}
    {brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (h : SparseCoreOrdProgramUniformReembAuto C_lsst lsfInitAuto impl brReemb p init op) :
    SparseCoreOrdProgramUniformAuto C_lsst lsfInitAuto impl p init op := fun capExp => by
  obtain ⟨wordExp, hw⟩ := h capExp
  refine ⟨wordExp, fun limbMul => ?_⟩
  obtain ⟨P, allocation, hwe, hP⟩ := hw limbMul
  refine ⟨P, allocation, hwe, fun depth w fmt => ?_⟩
  obtain ⟨R, hloc, hR⟩ := hP depth w fmt
  exact ⟨R, hloc, fun L G k M N vCap eCap hfmt hcap =>
    dsRep_implements_kf_of_kfr (hR L G k M N vCap eCap hfmt hcap)⟩

/-- Polynomial upper bound on the walk-length stretch `⌈impl.γ_ℓ m⌉` of a sparsifier
implementation, allowing the branch restart space polynomial to be fixed from `impl` alone. -/
def SparsifyPolyStretch (impl : SparsifyImpl) : Prop :=
  ∃ Cγ cγ : ℕ, ∀ m : ℕ, Nat.ceil (impl.γ_ℓ m) ≤ Cγ * (m + 2) ^ cγ

/-! ## Word-size exponent for P10 readout/update -/

/-- Minimum word-size exponent `wordExp` as a function of `capExp` sufficient for P10's update
condition `(vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w` whenever `vCap + eCap + 2 ≤ (M + N + 2) ^ capExp`,
`tCap ≤ 2 * (vCap + eCap + 2) ^ 2`, and
`L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)`.
At `capExp = 3`, `asmP10WordExp 3 = 24 ≤ 39`. -/
def asmP10WordExp (capExp : ℕ) : ℕ :=
  4 * capExp + 2 + Nat.log 2 (9 * (capExp + sparseCoreReadout2LimbConst + 1))

theorem asmP10WordExp_at_3 : asmP10WordExp 3 = 24 := by decide

theorem asmP10WordExp_ge_four (capExp : ℕ) : 4 ≤ asmP10WordExp capExp := by
  have h1 : 10 ≤ Nat.log 2 (9 * (capExp + sparseCoreReadout2LimbConst + 1)) := by
    rw [Nat.le_log_iff_pow_le (by decide : 1 < 2) (by unfold sparseCoreReadout2LimbConst; omega)]
    unfold sparseCoreReadout2LimbConst; omega
  unfold asmP10WordExp; omega

theorem asmP10WordExp_ge_two_mul (capExp : ℕ) : 2 * capExp ≤ asmP10WordExp capExp := by
  unfold asmP10WordExp; omega

private theorem succ_le_two_pow : ∀ k : ℕ, k + 1 ≤ 2 ^ k
  | 0 => le_rfl
  | k + 1 => by
    have ih := succ_le_two_pow k
    rw [Nat.pow_succ]
    omega

/-- **P10 word-size bound from `SparseCoreCapHyp` and `asmP10WordExp`**: for every `M`, `N`, `L`
and every `wordExp ≥ asmP10WordExp capExp`, the contract word bound
`(M + N + 2) ^ wordExp * (L + 1) < 2 ^ w`, the capacity bound, the tree-edge capacity bound
`tCap ≤ 2 * (vCap + eCap + 2) ^ 2`, and the readout-2 limb bound
`L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)` imply
`(vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w`. -/
theorem p10Word_of_wordExp {capExp limbMul w L M N vCap eCap tCap L_w : ℕ}
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (htCap : tCap ≤ 2 * (vCap + eCap + 2) ^ 2)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1))
    {wordExp : ℕ} (hwe : asmP10WordExp capExp ≤ wordExp)
    (hw : (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w) :
    (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w := by
  set B := M + N + 2
  have hB2 : 2 ≤ B := by omega
  have hBpow1 : 1 ≤ B ^ capExp := Nat.one_le_pow _ _ (by omega)
  have hBpow_le_sq : B ^ capExp ≤ (B ^ capExp) ^ 2 := by
    simpa [sq] using Nat.le_mul_of_pos_right (B ^ capExp) hBpow1
  have hcap_sq : (vCap + eCap + 2) ^ 2 ≤ (B ^ capExp) ^ 2 := Nat.pow_le_pow_left hcap.1 2
  have hvt : vCap + tCap + 2 ≤ 3 * (B ^ capExp) ^ 2 := by
    have hv : vCap + 2 ≤ B ^ capExp := le_trans (by omega) hcap.1
    omega
  have hvt_sq : (vCap + tCap + 2) ^ 2 ≤ 9 * B ^ (4 * capExp) := by
    calc (vCap + tCap + 2) ^ 2
        ≤ (3 * (B ^ capExp) ^ 2) ^ 2 := Nat.pow_le_pow_left hvt 2
      _ = 9 * B ^ (4 * capExp) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
          ring_nf
  have hlogB : Nat.log 2 B + 1 ≤ B :=
    le_trans (succ_le_two_pow (Nat.log 2 B)) (Nat.pow_log_le_self 2 (by omega))
  have hLw1 : L_w + 1 ≤ (capExp + sparseCoreReadout2LimbConst + 1) * B * (L + 1) := by
    have h1 : L_w + 1 ≤ (L + 1) + (capExp + sparseCoreReadout2LimbConst) * B := by
      have := Nat.mul_le_mul_left (capExp + sparseCoreReadout2LimbConst) hlogB
      omega
    have h2 : L + 1 ≤ B * (L + 1) := Nat.le_mul_of_pos_left (L + 1) (by omega)
    have h3 : (capExp + sparseCoreReadout2LimbConst) * B ≤
        (capExp + sparseCoreReadout2LimbConst) * B * (L + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
    calc L_w + 1
        ≤ (L + 1) + (capExp + sparseCoreReadout2LimbConst) * B := h1
      _ ≤ B * (L + 1) + (capExp + sparseCoreReadout2LimbConst) * B * (L + 1) :=
          Nat.add_le_add h2 h3
      _ = (capExp + sparseCoreReadout2LimbConst + 1) * B * (L + 1) := by ring
  set C := 9 * (capExp + sparseCoreReadout2LimbConst + 1)
  have hC_lt : C ≤ B ^ (Nat.log 2 C + 1) :=
    le_trans (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) C))
      (Nat.pow_le_pow_left hB2 _)
  have hprod : (vCap + tCap + 2) ^ 2 * (L_w + 1) ≤ B ^ (asmP10WordExp capExp) * (L + 1) := by
    calc (vCap + tCap + 2) ^ 2 * (L_w + 1)
        ≤ (9 * B ^ (4 * capExp)) * ((capExp + sparseCoreReadout2LimbConst + 1) * B * (L + 1)) :=
          Nat.mul_le_mul hvt_sq hLw1
      _ = C * (B ^ (4 * capExp + 1) * (L + 1)) := by
          dsimp only [C]; rw [pow_succ]; ring
      _ ≤ B ^ (Nat.log 2 C + 1) * (B ^ (4 * capExp + 1) * (L + 1)) :=
          Nat.mul_le_mul_right _ hC_lt
      _ = B ^ ((Nat.log 2 C + 1) + (4 * capExp + 1)) * (L + 1) := by
          rw [← mul_assoc, ← pow_add]
      _ = B ^ (asmP10WordExp capExp) * (L + 1) := by
          have hexp : Nat.log 2 C + 1 + (4 * capExp + 1) = asmP10WordExp capExp := by
            unfold asmP10WordExp; dsimp only [C]; omega
          rw [hexp]
  have hexp_le : B ^ (asmP10WordExp capExp) * (L + 1) ≤ B ^ wordExp * (L + 1) :=
    Nat.mul_le_mul_right (L + 1) (Nat.pow_le_pow_right (by omega) hwe)
  exact lt_of_le_of_lt (le_trans hprod hexp_le) hw

/-- Capacity-indexed uniform statement (`τ`, `phi`, `foot` chosen once before `L, G, k, M, N, vCap, eCap`;
`rep` indexed by the immutable level constants `(L, vCap, eCap)`), with `reembList` on `op 0` and
`wordExp` independent of `limbMul`. -/
def SparseCoreOrdProgramUniformReembCap (C_lsst : ℝ) (lsfInitAuto : ℕ → LSFInit)
    (impl : SparsifyImpl)
    (brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ)
    (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w),
        1 ≤ depth →
        ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
          ∀ (L vCap eCap : ℕ),
            ∃ rep : ℕ → SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl) →
                τ → (ℕ → ℕ) → Prop,
              let R : DSRep (SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)) :=
                ⟨τ, rep, phi, foot⟩
              R.Local ∧ ∀ (G : MGraph) (k M N : ℕ),
                fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                depth ≤ M + N + k + L →
                (∀ j < k, IsValidLSFInitFor (lsfInitAuto fmt.precision) C_lsst k j) →
                G.n ≤ G.m + 1 →
                R.Implements w p init op
                  (sparseCoreOrdMachineContractKFR fmt L
                    (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                    (bundleToolReemb (brReemb depth))
                    G k M N vCap eCap capExp P allocation)

/-- Capacity-indexed uniform statement for `sparseCoreOrdMachineContractKF` (`τ`, `phi`, `foot`
uniform over `L, G, k, M, N, vCap, eCap`, and `wordExp` independent of `limbMul`). -/
def SparseCoreOrdProgramUniformCap (C_lsst : ℝ) (lsfInitAuto : ℕ → LSFInit)
    (impl : SparsifyImpl) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w),
        1 ≤ depth →
        ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
          ∀ (L vCap eCap : ℕ),
            ∃ rep : ℕ → SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl) →
                τ → (ℕ → ℕ) → Prop,
              let R : DSRep (SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)) :=
                ⟨τ, rep, phi, foot⟩
              R.Local ∧ ∀ (G : MGraph) (k M N : ℕ),
                fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                depth ≤ M + N + k + L →
                (∀ j < k, IsValidLSFInitFor (lsfInitAuto fmt.precision) C_lsst k j) →
                G.n ≤ G.m + 1 →
                R.Implements w p init op
                  (sparseCoreOrdMachineContractKF fmt L
                    (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                    G k M N vCap eCap capExp P allocation)

theorem sparseCoreOrdProgramUniformCap_of_reemb {C_lsst : ℝ} {lsfInitAuto : ℕ → LSFInit}
    {impl : SparsifyImpl}
    {brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (h : SparseCoreOrdProgramUniformReembCap C_lsst lsfInitAuto impl brReemb p init op) :
    SparseCoreOrdProgramUniformCap C_lsst lsfInitAuto impl p init op := fun capExp => by
  obtain ⟨wordExp, hw⟩ := h capExp
  refine ⟨wordExp, fun limbMul => ?_⟩
  obtain ⟨P, allocation, hwe, hP⟩ := hw limbMul
  refine ⟨P, allocation, hwe, fun depth w fmt hdepth => ?_⟩
  obtain ⟨τ, phi, foot, hτ⟩ := hP depth w fmt hdepth
  refine ⟨τ, phi, foot, fun L vCap eCap => ?_⟩
  obtain ⟨rep, hloc, hR⟩ := hτ L vCap eCap
  exact ⟨rep, hloc, fun G k M N hfmt hcap hdle hInit hGn =>
    dsRep_implements_kf_of_kfr (hR G k M N hfmt hcap hdle hInit hGn)⟩

end MinCostFlow.SparseCore.Program
