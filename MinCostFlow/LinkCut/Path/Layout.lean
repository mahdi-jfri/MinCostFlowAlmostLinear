module

public import MinCostFlow.LinkCut.Gen.Layout
public import MinCostFlow.MinRatio.PathPayloadAdapter
public import MinCostFlow.MinRatio.PathPayloadLayout

/-!
# The node layout of the Section 6 path payload

Inside the tree, every number of the path payload is kept in `K` limbs of `h` bits, in the
layouts of `MinRatio/PathPayloadLayout.lean`: an edge value is four layout words followed by
`PathEdgeAt` (a header word, a direction word and four blocks, `2 + 4 K` words), a summary is `PathSummaryAt` (`3 K + 1`
words), and a tag is `PathTagAt` (`2 K` words). The width `K` is a parameter: the tree may keep
numbers wider than the `L`-limb blocks of the interface, because the values computed on the way
need not fit where the start and the end state do.

A block's value depends only on its own cells, so a copy of a block holds the same value
(`pathLayout`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen

theorem pathIntAt_move {m m' : ℕ → ℕ} {a b h K : ℕ} {z : ℤ} (hz : PathIntAt m a h K z)
    (hag : ∀ i < K, m' (b + i) = m (a + i)) : PathIntAt m' b h K z :=
  hz.congr hag

theorem pathEdgeAt_move {m m' : ℕ → ℕ} {a b h K : ℕ} {v : Option PathEdgeValue}
    (hv : PathEdgeAt m a h K v) (hag : ∀ i < 2 + 4 * K, m' (b + i) = m (a + i)) :
    PathEdgeAt m' b h K v := by
  cases v with
  | none =>
    change m' b = 0
    have := hag 0 (by omega)
    simp only [Nat.add_zero] at this
    rw [this]; exact hv
  | some v =>
    obtain ⟨hk, hd, hg, hl, hf, hr⟩ := hv
    have e : ∀ j, j < 2 + 4 * K → m' (b + j) = m (a + j) := hag
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := e 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact hk
    · rw [e 1 (by omega)]; exact hd
    · exact pathIntAt_move hg fun i hi => by
        rw [show b + 2 + i = b + (2 + i) by omega, e _ (by omega), show a + (2 + i) = a + 2 + i
          by omega]
    · exact pathIntAt_move hl fun i hi => by
        rw [show b + 2 + K + i = b + (2 + K + i) by omega, e _ (by omega),
          show a + (2 + K + i) = a + 2 + K + i by omega]
    · exact pathIntAt_move hf fun i hi => by
        rw [show b + 2 + 2 * K + i = b + (2 + 2 * K + i) by omega, e _ (by omega),
          show a + (2 + 2 * K + i) = a + 2 + 2 * K + i by omega]
    · exact pathIntAt_move hr fun i hi => by
        rw [show b + 2 + 3 * K + i = b + (2 + 3 * K + i) by omega, e _ (by omega),
          show a + (2 + 3 * K + i) = a + 2 + 3 * K + i by omega]

theorem pathSummaryAt_move {m m' : ℕ → ℕ} {a b h K : ℕ} {s : PathSummary}
    (hs : PathSummaryAt m a h K s) (hag : ∀ i < 3 * K + 1, m' (b + i) = m (a + i)) :
    PathSummaryAt m' b h K s := by
  obtain ⟨hg, hl, hd⟩ := hs
  have e : ∀ j, j < 3 * K + 1 → m' (b + j) = m (a + j) := hag
  refine ⟨pathIntAt_move hg fun i hi => e i (by omega),
    pathIntAt_move hl fun i hi => by
      rw [show b + K + i = b + (K + i) by omega, e _ (by omega),
        show a + (K + i) = a + K + i by omega], ?_⟩
  have e2 : m' (b + 2 * K) = m (a + 2 * K) := e _ (by omega)
  cases hz : s.detector with
  | none =>
    simp only [hz] at hd ⊢
    rw [e2]; exact hd
  | some z =>
    simp only [hz] at hd ⊢
    refine ⟨by rw [e2]; exact hd.1, pathIntAt_move hd.2 fun i hi => ?_⟩
    rw [show b + 2 * K + 1 + i = b + (2 * K + 1 + i) by omega, e _ (by omega),
      show a + (2 * K + 1 + i) = a + 2 * K + 1 + i by omega]

theorem pathTagAt_move {m m' : ℕ → ℕ} {a b h K : ℕ} {t : PathTag}
    (ht : PathTagAt m a h K t) (hag : ∀ i < 2 * K, m' (b + i) = m (a + i)) :
    PathTagAt m' b h K t :=
  ⟨pathIntAt_move ht.1 fun i hi => hag i (by omega),
    pathIntAt_move ht.2 fun i hi => by
      rw [show b + K + i = b + (K + i) by omega, hag _ (by omega),
        show a + (K + i) = a + K + i by omega]⟩

theorem pathEdgeAt_unique {m : ℕ → ℕ} {a h K : ℕ} {v v' : Option PathEdgeValue}
    (hv : PathEdgeAt m a h K v) (hv' : PathEdgeAt m a h K v') : v = v' := by
  cases v with
  | none =>
    cases v' with
    | none => rfl
    | some e => exact absurd (hv'.1.symm.trans hv) (by decide)
  | some e =>
    cases v' with
    | none => exact absurd (hv.1.symm.trans hv') (by decide)
    | some e' =>
      obtain ⟨-, hd, hg, hl, hf, hr⟩ := hv
      obtain ⟨-, hd', hg', hl', hf', hr'⟩ := hv'
      have hfw : e.forward = e'.forward := by
        have := hd.symm.trans hd'
        by_cases h1 : e.forward <;> by_cases h2 : e'.forward <;> simp_all
      rw [PathEdgeValue.ext_iff.mpr ⟨hfw, hg.unique hg', hl.unique hl', hf.unique hf',
        hr.unique hr'⟩]

theorem pathSummaryAt_unique {m : ℕ → ℕ} {a h K : ℕ} {s s' : PathSummary}
    (hs : PathSummaryAt m a h K s) (hs' : PathSummaryAt m a h K s') : s = s' := by
  obtain ⟨hg, hl, hd⟩ := hs
  obtain ⟨hg', hl', hd'⟩ := hs'
  have hdet : s.detector = s'.detector := by
    cases hz : s.detector with
    | none =>
      cases hz' : s'.detector with
      | none => rfl
      | some z' =>
        simp only [hz] at hd; simp only [hz'] at hd'
        exact absurd (hd'.1.symm.trans hd) (by decide)
    | some z =>
      cases hz' : s'.detector with
      | none =>
        simp only [hz] at hd; simp only [hz'] at hd'
        exact absurd (hd.1.symm.trans hd') (by decide)
      | some z' =>
        simp only [hz] at hd; simp only [hz'] at hd'
        rw [hd.2.unique hd'.2]
  exact PathSummary.ext (hg.unique hg') (hl.unique hl') hdet

theorem pathTagAt_unique {m : ℕ → ℕ} {a h K : ℕ} {t t' : PathTag}
    (ht : PathTagAt m a h K t) (ht' : PathTagAt m a h K t') : t = t' :=
  PathTag.ext (ht.1.unique ht'.1) (ht.2.unique ht'.2)

/-- A value block of the path payload: four layout words (the record width `13 + 9 K`, the
value width `6 + 4 K`, the tag width `2 K`, and `K`), then the edge value. The programs read
`K` and the widths from these words, so their text does not depend on `K`. -/
def PathValAt (m : ℕ → ℕ) (a h K : ℕ) (v : Option PathEdgeValue) : Prop :=
  m a = 13 + 9 * K ∧ m (a + 1) = 6 + 4 * K ∧ m (a + 2) = 2 * K ∧ m (a + 3) = K ∧
    PathEdgeAt m (a + 4) h K v

theorem pathValAt_move {m m' : ℕ → ℕ} {a b h K : ℕ} {v : Option PathEdgeValue}
    (hv : PathValAt m a h K v) (hag : ∀ i < 6 + 4 * K, m' (b + i) = m (a + i)) :
    PathValAt m' b h K v := by
  obtain ⟨h0, h1, h2, h3, he⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, pathEdgeAt_move he fun i hi => ?_⟩
  · have := hag 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact h0
  · rw [hag 1 (by omega)]; exact h1
  · rw [hag 2 (by omega)]; exact h2
  · rw [hag 3 (by omega)]; exact h3
  · rw [show b + 4 + i = b + (4 + i) by omega, hag _ (by omega),
      show a + (4 + i) = a + 4 + i by omega]

theorem pathValAt_unique {m : ℕ → ℕ} {a h K : ℕ} {v v' : Option PathEdgeValue}
    (hv : PathValAt m a h K v) (hv' : PathValAt m a h K v') : v = v' :=
  pathEdgeAt_unique hv.2.2.2.2 hv'.2.2.2.2

/-- The node layout of the path payload, with numbers in `K` limbs of `h` bits. -/
def pathLayout (h K : ℕ) : NodeLayout (Option PathEdgeValue) PathSummary PathTag where
  valW := 6 + 4 * K
  sumW := 3 * K + 1
  tagW := 2 * K
  ValAt m a v := PathValAt m a h K v
  SumAt m a s := PathSummaryAt m a h K s
  TagAt m a t := PathTagAt m a h K t
  val_move _ _ _ _ _ hv hag := pathValAt_move hv hag
  sum_move _ _ _ _ _ hs hag := pathSummaryAt_move hs hag
  tag_move _ _ _ _ _ ht hag := pathTagAt_move ht hag
  val_hdr _ _ _ hv := ⟨by rw [hv.1]; omega, hv.2.1, hv.2.2.1⟩
  val_three := by omega

end MinCostFlow.LinkCut.Path
