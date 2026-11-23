module

public import MinCostFlow.LinkCut.Gen.Cut
public import MinCostFlow.LinkCut.ForestModelSplice

/-!
# How many entries an operation pushes on the index

Each tree operation notes the roots it creates on the index stack. Find-ready later pops
entries one by one, so the potential pays a constant per entry. This file bounds the number of
entries an operation adds by twice the number of splices that the model counts, plus a small
constant. A note pushes at most one entry, a detach of a right child at most two, and each
splice of an expose does one detach.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen

variable {α σ τ : Type*}

theorem noteList_length_le (S : List ℕ) (x : ℕ) : (noteList S x).length ≤ S.length + 1 := by
  unfold noteList; split_ifs <;> simp

theorem drNotes_length_le (s : SplayState α σ τ) (x : ℕ) (S : List ℕ) :
    (drNotes s x S).length ≤ S.length + 2 := by
  unfold drNotes
  have h1 := noteList_length_le S x
  have h2 := noteList_length_le (noteList S x) (s.nodes x).right
  split_ifs <;> omega

theorem dcNotes_length_le (s : SplayState α σ τ) (x : ℕ) (S : List ℕ) :
    (dcNotes s x S).length ≤ S.length + 3 := by
  unfold dcNotes
  have h1 := noteList_length_le S x
  have h2 := noteList_length_le (noteList S x) (s.nodes x).left
  have h3 := noteList_length_le (noteList (noteList S x) (s.nodes x).left) (s.nodes x).right
  split_ifs <;> omega

theorem exposeLoopNotes_length_le (P : LctPayload α σ τ) :
    ∀ (k : ℕ) (st : LctState α σ τ) (last : ℕ) (S : List ℕ),
      (exposeLoopNotes P st k last S).length ≤ S.length + 2 * (lctExposeLoop P st k last).2.2.2
  | 0, _, _, _ => by simp [exposeLoopNotes, lctExposeLoop]
  | k + 1, st, last, S => by
    by_cases hp : (st.splay.nodes last).ppar = 0
    · simp [exposeLoopNotes, lctExposeLoop, hp]
    have ih := exposeLoopNotes_length_le P k (lctExposeStep P st last).1
      (st.splay.nodes last).ppar
      (drNotes (SplayState.splay P st.splay (2 * st.n + 1) (st.splay.nodes last).ppar)
        (st.splay.nodes last).ppar S)
    have hd := drNotes_length_le (SplayState.splay P st.splay (2 * st.n + 1)
      (st.splay.nodes last).ppar) (st.splay.nodes last).ppar S
    have hl : (lctExposeLoop P st (k + 1) last).2.2.2 =
        1 + (lctExposeLoop P (lctExposeStep P st last).1 k (st.splay.nodes last).ppar).2.2.2 := by
      simp [lctExposeLoop, hp]; rfl
    have hn : exposeLoopNotes P st (k + 1) last S = exposeLoopNotes P (lctExposeStep P st last).1 k
        (st.splay.nodes last).ppar (drNotes (SplayState.splay P st.splay (2 * st.n + 1)
          (st.splay.nodes last).ppar) (st.splay.nodes last).ppar S) := by
      simp [exposeLoopNotes, hp]
    rw [hl, hn]
    omega

/-- An expose adds at most two entries per splice it counts. -/
theorem exposeNotes_length_le (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ)
    (S : List ℕ) :
    (exposeNotes P st v S).length ≤ S.length + 2 * (lctExposeCost P st v).2.2 := by
  have h1 := exposeLoopNotes_length_le P (2 * st.n + 1) (exposeStart P st v) v
    (drNotes (SplayState.splay P st.splay (2 * st.n + 1) v) v S)
  have h2 := drNotes_length_le (SplayState.splay P st.splay (2 * st.n + 1) v) v S
  have h3 : (lctExposeCost P st v).2.2 =
      1 + (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).2.2.2 := rfl
  unfold exposeNotes
  rw [h3]
  omega

theorem rerootExposeNotes_length_le (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ)
    (S : List ℕ) :
    (rerootExposeNotes P st u v S).length ≤ S.length + 2 * (lctPathSummaryCost P st u v).2.2.2 := by
  have h1 := exposeNotes_length_le P st u S
  have h2 := exposeNotes_length_le P (lctReroot P st u) v (exposeNotes P st u S)
  have h3 : (lctPathSummaryCost P st u v).2.2.2 =
      (lctExposeCost P st u).2.2 + (lctExposeCost P (lctReroot P st u) v).2.2 := rfl
  unfold rerootExposeNotes
  rw [h3]
  omega

theorem linkNotes_length_le (P : LctPayload α σ τ) (st : LctState α σ τ) {u v : ℕ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hf : st.freeHead ≠ 0) (e : α) (S : List ℕ) :
    (linkNotes P st u v S).length ≤ S.length + 2 * (lctLinkCost P st u v e).2.2 := by
  have h1 := exposeNotes_length_le P st v S
  have h2 := exposeNotes_length_le P (lctReroot P st v) u (exposeNotes P st v S)
  have h3 := noteList_length_le (exposeNotes P (lctReroot P st v) u (exposeNotes P st v S))
    st.freeHead
  have hfh : (lctRerootCost P (lctRerootCost P st v).1 u).1.freeHead = st.freeHead := by
    rw [lctRerootCost_freeHead, lctRerootCost_freeHead]
  have h4 : (lctLinkCost P st u v e).2.2 =
      (lctExposeCost P st v).2.2 + (lctExposeCost P (lctReroot P st v) u).2.2 + 1 := by
    unfold lctLinkCost
    rw [ite_eq_right (by simp [hu, hv, huv, hf])]
    simp only [hfh, beq_iff_eq, hf, ite_false]
    rfl
  unfold linkNotes
  rw [ite_eq_right (by tauto), h4]
  omega

theorem cutNotes_length_le (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ)
    (S : List ℕ) :
    (cutNotes P st u v S).length ≤ S.length + 2 * (lctCutCost P st u v).2.2 + 3 := by
  unfold cutNotes
  split_ifs with hg hc
  · omega
  · have h1 := rerootExposeNotes_length_le P st u v S
    have h2 := dcNotes_length_le (SplayState.splay P (cutPd P st u v) (2 * st.n + 1)
      (cutNe P st u v)) (cutNe P st u v) (rerootExposeNotes P st u v S)
    have h3 : (lctPathSummaryCost P st u v).2.2.2 ≤ (lctCutCost P st u v).2.2 := by
      unfold lctCutCost
      rw [ite_eq_right (by simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]; tauto)]
      dsimp only
      split_ifs <;> dsimp only [lctPathSummaryCost] <;> omega
    omega
  · have h1 := rerootExposeNotes_length_le P st u v S
    have h3 : (lctPathSummaryCost P st u v).2.2.2 ≤ (lctCutCost P st u v).2.2 := by
      unfold lctCutCost
      rw [ite_eq_right (by simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]; tauto)]
      dsimp only
      split_ifs <;> dsimp only [lctPathSummaryCost] <;> omega
    omega

end MinCostFlow.LinkCut.PathProg
