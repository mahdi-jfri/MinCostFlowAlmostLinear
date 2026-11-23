module

public import MinCostFlow.DynSpanner.Program.StateLayout

/-!
# The levels above `j` after the step

After a rebuild of level `j`, the levels `i > j` of the new state are empty: `inDom i = ∅` and
`S_i = ∅`. The step does not touch the per-edge or per-vertex words of these levels. It only
writes `0` to the generation words `domGen[i]` and `sGen[i]` (`dsZeroRangeStmt`). This file shows
that this is enough. When `domGen[i] = 0`, no stamp can match it, so the level clauses of
`DynSpannerStateAt` hold with an empty domain and empty reverse lists
(`levelDom_of_gen_zero`). When `sGen[i] = 0`, the same holds for `S_i` and its list
(`levelS_of_gen_zero`). Each lemma needs only that the old stamps are at most the global
generation word, which the old invariant gives.

The levels below `j` keep their words. `LevelDomAt` and `LevelSAt` name the two level clauses;
`levelDomAt_restrict` shows that the `inDom` clause survives the shrinking of `E(G)`, and
`LevelDomAt.of_agree`, `LevelSAt.of_agree` show that the clauses survive any write outside the
level arrays, the generation word and the heap cells of the metadata.
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

@[expose] public section

/-- The `inDom` clause of `DynSpannerStateAt` for one level `i` whose word `domGen[i]` is `0`.
The domain, the set `inDom i` and the reverse lists are then empty, and the embedding of the
level can be anything. -/
theorem levelDom_of_gen_zero {L vCap eCap b : ℕ} {mem : ℕ → ℕ} {x : DynSpannerMeta L}
    {st : DynSpannerState L} (i : Fin (L + 1))
    (hgen : mem (dsDomGenBase b L vCap eCap + i.1) = 0)
    (hedge : ∀ e < eCap,
      mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ mem (b + dsGenOff))
    (hrev : ∀ v < vCap,
      mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff))
    (hdomx : x.memInDom i = ∅) (hrevx : ∀ v, x.revLists i v = [])
    (hdom : st.inDom i = ∅) :
    mem (dsDomGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff) ∧
    (∀ e < eCap,
      mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ mem (b + dsGenOff) ∧
      ((0 < mem (dsDomGenBase b L vCap eCap + i.1) ∧
        mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
          mem (dsDomGenBase b L vCap eCap + i.1)) ↔ e ∈ x.memInDom i)) ∧
    (∀ e ∈ x.memInDom i, e < eCap) ∧
    st.inDom i = x.memInDom i ∩ st.G.E ∧
    (∀ e ∈ st.inDom i,
      let ptr := mem (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)
      MWalkAt mem ptr (st.Pi_level i e) ∧
      RangeInHeapFoot x ptr (ptr + (mWalkEncode (st.Pi_level i e)).length)) ∧
    (∀ v < vCap,
      mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
      (x.revLists i v).Nodup ∧
      (∀ e ∈ x.revLists i v, e < eCap ∧ e ∈ x.memInDom i) ∧
      (if 0 < mem (dsDomGenBase b L vCap eCap + i.1) ∧
          mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
            mem (dsDomGenBase b L vCap eCap + i.1)
       then LinkedListIn (heapFoot x) mem
              (mem (dsRevHeadBase b L vCap eCap + i.1 * vCap + v)) (x.revLists i v)
       else x.revLists i v = [])) := by
  -- With `domGen[i] = 0`, the test `0 < domGen[i]` fails, so no stamp matches.
  refine ⟨by rw [hgen]; exact Nat.zero_le _, fun e he => ⟨hedge e he, ?_⟩, ?_, ?_, ?_,
    fun v hv => ⟨hrev v hv, ?_, ?_, ?_⟩⟩
  · simp [hgen, hdomx]
  · simp [hdomx]
  · simp [hdom, hdomx]
  · simp [hdom]
  · simp [hrevx v]
  · simp [hrevx v]
  · simp [hgen, hrevx v]

/-- The `S` clause of `DynSpannerStateAt` for one level `i` whose word `sGen[i]` is `0`. The set
`S_i` and its list are then empty. -/
theorem levelS_of_gen_zero {L vCap eCap b : ℕ} {mem : ℕ → ℕ} {x : DynSpannerMeta L}
    {st : DynSpannerState L} (i : Fin (L + 1))
    (hgen : mem (dsSGenBase b L vCap eCap + i.1) = 0)
    (hvs : ∀ v < vCap,
      mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff))
    (hsx : x.sLists i = []) (hS : st.S_level i = ∅) :
    mem (dsSGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff) ∧
    (∀ v ∈ st.S_level i, v < vCap) ∧
    (∀ v < vCap,
      mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
      ((0 < mem (dsSGenBase b L vCap eCap + i.1) ∧
        mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ st.S_level i)) ∧
    (x.sLists i).Nodup ∧
    (∀ v, v ∈ x.sLists i ↔ v ∈ st.S_level i) ∧
    (if 0 < mem (dsSGenBase b L vCap eCap + i.1)
     then LinkedListIn (heapFoot x) mem
            (mem (dsSHeadBase b L vCap eCap + i.1)) (x.sLists i)
     else x.sLists i = []) := by
  -- With `sGen[i] = 0`, the test `0 < sGen[i]` fails, so no vertex is marked.
  refine ⟨by rw [hgen]; exact Nat.zero_le _, by simp [hS], fun v hv => ⟨hvs v hv, ?_⟩, ?_, ?_,
    ?_⟩
  · simp [hgen, hS]
  · simp [hsx]
  · simp [hsx, hS]
  · simp [hgen, hsx]

/-- The `inDom` clause of `DynSpannerStateAt` for one level `i`, as a named proposition. It is
the same formula as in `DynSpannerStateAt`, so the two can be exchanged by unfolding. -/
def LevelDomAt (L vCap eCap b : ℕ) (mem : ℕ → ℕ) (x : DynSpannerMeta L)
    (st : DynSpannerState L) (i : Fin (L + 1)) : Prop :=
  mem (dsDomGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff) ∧
  (∀ e < eCap,
    mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ mem (b + dsGenOff) ∧
    ((0 < mem (dsDomGenBase b L vCap eCap + i.1) ∧
      mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
        mem (dsDomGenBase b L vCap eCap + i.1)) ↔ e ∈ x.memInDom i)) ∧
  (∀ e ∈ x.memInDom i, e < eCap) ∧
  st.inDom i = x.memInDom i ∩ st.G.E ∧
  (∀ e ∈ st.inDom i,
    let ptr := mem (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)
    MWalkAt mem ptr (st.Pi_level i e) ∧
    RangeInHeapFoot x ptr (ptr + (mWalkEncode (st.Pi_level i e)).length)) ∧
  (∀ v < vCap,
    mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
    (x.revLists i v).Nodup ∧
    (∀ e ∈ x.revLists i v, e < eCap ∧ e ∈ x.memInDom i) ∧
    (if 0 < mem (dsDomGenBase b L vCap eCap + i.1) ∧
        mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsDomGenBase b L vCap eCap + i.1)
     then LinkedListIn (heapFoot x) mem
            (mem (dsRevHeadBase b L vCap eCap + i.1 * vCap + v)) (x.revLists i v)
     else x.revLists i v = []))

/-- A level below `j` keeps its words in the step, while the graph loses edges (the updates are
deletions and splits, so `E(G') ⊆ E(G)`). The model then sets `inDom i := inDom i ∩ E(G')` and
keeps `Π_i`. The clause of the level still holds with the same memory and metadata: the stamps
did not change, and intersecting with `E(G')` gives the same set from both sides, because
`inDom i = memInDom i ∩ E(G)` and `E(G') ⊆ E(G)`. -/
theorem levelDomAt_restrict {L vCap eCap b : ℕ} {mem : ℕ → ℕ} {x : DynSpannerMeta L}
    {st st' : DynSpannerState L} {i : Fin (L + 1)} (h : LevelDomAt L vCap eCap b mem x st i)
    (hG : st'.G.E ⊆ st.G.E) (hdom : st'.inDom i = st.inDom i ∩ st'.G.E)
    (hPi : st'.Pi_level i = st.Pi_level i) :
    LevelDomAt L vCap eCap b mem x st' i := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, ?_, fun e he => ?_, h6⟩
  · -- `(memInDom ∩ E(G)) ∩ E(G') = memInDom ∩ E(G')` since `E(G') ⊆ E(G)`.
    rw [hdom, h4, Finset.inter_assoc, Finset.inter_eq_right.mpr hG]
  · have he' : e ∈ st.inDom i := (Finset.mem_inter.mp (hdom ▸ he)).1
    rw [hPi]
    exact h5 e he'

private lemma idx_lt {L i c x : ℕ} (hi : i ≤ L) (hx : x < c) : i * c + x < (L + 1) * c := by
  have := Nat.mul_le_mul_right c (show i + 1 ≤ L + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- The clause of a level only reads the words of the level arrays (from `domGen` up to
`sGen`), the global generation word, and the heap cells of the metadata. So it survives any
change of memory that keeps these cells. -/
theorem LevelDomAt.of_agree {L vCap eCap b : ℕ} {mem mem' : ℕ → ℕ} {x : DynSpannerMeta L}
    {st : DynSpannerState L} {i : Fin (L + 1)} (h : LevelDomAt L vCap eCap b mem x st i)
    (hag : ∀ addr, ((dsDomGenBase b L vCap eCap ≤ addr ∧ addr < dsSGenBase b L vCap eCap) ∨
      addr = b + dsGenOff ∨ heapFoot x addr) → mem' addr = mem addr) :
    LevelDomAt L vCap eCap b mem' x st i := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hi := i.2
  have hE : dsEdgeDomGenBase b L vCap eCap = dsDomGenBase b L vCap eCap + (L + 1) := rfl
  have hP : dsPiPtrBase b L vCap eCap = dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap := rfl
  have hR : dsRevGenBase b L vCap eCap = dsPiPtrBase b L vCap eCap + (L + 1) * eCap := rfl
  have hRH : dsRevHeadBase b L vCap eCap = dsRevGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hS : dsSGenBase b L vCap eCap = dsRevHeadBase b L vCap eCap + (L + 1) * vCap := rfl
  have hgen : mem' (b + dsGenOff) = mem (b + dsGenOff) := hag _ (Or.inr (Or.inl rfl))
  have hdg : mem' (dsDomGenBase b L vCap eCap + i.1) = mem (dsDomGenBase b L vCap eCap + i.1) :=
    hag _ (Or.inl ⟨by omega, by omega⟩)
  refine ⟨by rw [hgen, hdg]; exact h1, fun e he => ?_, h3, h4, fun e he => ?_, fun v hv => ?_⟩
  · have hlt := idx_lt (c := eCap) (show i.1 ≤ L by omega) he
    have hw : mem' (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
        mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) :=
      hag _ (Or.inl ⟨by omega, by omega⟩)
    rw [hgen, hdg, hw]
    exact h2 e he
  · have heC : e < eCap := h3 e (by rw [h4] at he; exact (Finset.mem_inter.mp he).1)
    have hlt := idx_lt (c := eCap) (show i.1 ≤ L by omega) heC
    have hw : mem' (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) =
        mem (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) :=
      hag _ (Or.inl ⟨by omega, by omega⟩)
    obtain ⟨hW, hR'⟩ := h5 e he
    simp only at hW hR' ⊢
    rw [hw]
    refine ⟨hW.of_agree fun addr h1 h2 => hag addr (Or.inr (Or.inr (hR' addr h1 ?_))), hR'⟩
    rw [mWalkEncode_length]
    omega
  · have hlt := idx_lt (c := vCap) (show i.1 ≤ L by omega) hv
    have hw : mem' (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
        mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) :=
      hag _ (Or.inl ⟨by omega, by omega⟩)
    have hw2 : mem' (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) =
        mem (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) :=
      hag _ (Or.inl ⟨by omega, by omega⟩)
    obtain ⟨g1, g2, g3, g4⟩ := h6 v hv
    refine ⟨by rw [hw, hgen]; exact g1, g2, g3, ?_⟩
    rw [hdg, hw, hw2]
    split_ifs at g4 ⊢ <;>
      first
        | exact g4.of_agree fun a ha => hag a (Or.inr (Or.inr ha))
        | exact g4

/-- The `S` clause of `DynSpannerStateAt` for one level `i`, as a named proposition. -/
def LevelSAt (L vCap eCap b : ℕ) (mem : ℕ → ℕ) (x : DynSpannerMeta L)
    (st : DynSpannerState L) (i : Fin (L + 1)) : Prop :=
  mem (dsSGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff) ∧
  (∀ v ∈ st.S_level i, v < vCap) ∧
  (∀ v < vCap,
    mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
    ((0 < mem (dsSGenBase b L vCap eCap + i.1) ∧
      mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
        mem (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ st.S_level i)) ∧
  (x.sLists i).Nodup ∧
  (∀ v, v ∈ x.sLists i ↔ v ∈ st.S_level i) ∧
  (if 0 < mem (dsSGenBase b L vCap eCap + i.1)
   then LinkedListIn (heapFoot x) mem
          (mem (dsSHeadBase b L vCap eCap + i.1)) (x.sLists i)
   else x.sLists i = [])

/-- The `S` clause of a level only reads the words from `sGen` up to `sBit`, the global
generation word, and the heap cells of the metadata. -/
theorem LevelSAt.of_agree {L vCap eCap b : ℕ} {mem mem' : ℕ → ℕ} {x : DynSpannerMeta L}
    {st : DynSpannerState L} {i : Fin (L + 1)} (h : LevelSAt L vCap eCap b mem x st i)
    (hag : ∀ addr, ((dsSGenBase b L vCap eCap ≤ addr ∧ addr < dsSBitBase b L vCap eCap) ∨
      addr = b + dsGenOff ∨ heapFoot x addr) → mem' addr = mem addr) :
    LevelSAt L vCap eCap b mem' x st i := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hi := i.2
  have hV : dsVSGenBase b L vCap eCap = dsSGenBase b L vCap eCap + (L + 1) := rfl
  have hH : dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hB : dsSBitBase b L vCap eCap = dsSHeadBase b L vCap eCap + (L + 1) := rfl
  have hgen : mem' (b + dsGenOff) = mem (b + dsGenOff) := hag _ (Or.inr (Or.inl rfl))
  have hsg : mem' (dsSGenBase b L vCap eCap + i.1) = mem (dsSGenBase b L vCap eCap + i.1) :=
    hag _ (Or.inl ⟨by omega, by omega⟩)
  have hsh : mem' (dsSHeadBase b L vCap eCap + i.1) = mem (dsSHeadBase b L vCap eCap + i.1) :=
    hag _ (Or.inl ⟨by omega, by omega⟩)
  refine ⟨by rw [hgen, hsg]; exact h1, h2, fun v hv => ?_, h4, h5, ?_⟩
  · have hlt := idx_lt (c := vCap) (show i.1 ≤ L by omega) hv
    have hw : mem' (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
        mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) :=
      hag _ (Or.inl ⟨by omega, by omega⟩)
    rw [hw, hgen, hsg]
    exact h3 v hv
  · rw [hsg, hsh]
    split_ifs at h6 ⊢ <;>
      first
        | exact h6.of_agree fun a ha => hag a (Or.inr (Or.inr ha))
        | exact h6

/-- A level above `j` after the step: once `domGen[i]` is `0` and the other words of the level
are kept, the clause holds with an empty domain and empty reverse lists, for any new metadata
and state that make them empty. The bounds on the stamps come from the old clause. -/
theorem levelDomAt_clear {L vCap eCap b : ℕ} {mem mem' : ℕ → ℕ} {x x' : DynSpannerMeta L}
    {st st' : DynSpannerState L} {i : Fin (L + 1)} (h : LevelDomAt L vCap eCap b mem x st i)
    (hz : mem' (dsDomGenBase b L vCap eCap + i.1) = 0)
    (hag : ∀ addr, ((dsEdgeDomGenBase b L vCap eCap ≤ addr ∧ addr < dsSGenBase b L vCap eCap) ∨
      addr = b + dsGenOff) → mem' addr = mem addr)
    (hdomx : x'.memInDom i = ∅) (hrevx : ∀ v, x'.revLists i v = []) (hdom : st'.inDom i = ∅) :
    LevelDomAt L vCap eCap b mem' x' st' i := by
  obtain ⟨_, h2, _, _, _, h6⟩ := h
  have hi := i.2
  have hP : dsPiPtrBase b L vCap eCap = dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap := rfl
  have hR : dsRevGenBase b L vCap eCap = dsPiPtrBase b L vCap eCap + (L + 1) * eCap := rfl
  have hRH : dsRevHeadBase b L vCap eCap = dsRevGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hS : dsSGenBase b L vCap eCap = dsRevHeadBase b L vCap eCap + (L + 1) * vCap := rfl
  have hgen : mem' (b + dsGenOff) = mem (b + dsGenOff) := hag _ (Or.inr rfl)
  refine levelDom_of_gen_zero i hz (fun e he => ?_) (fun v hv => ?_) hdomx hrevx hdom
  · have hlt := idx_lt (c := eCap) (show i.1 ≤ L by omega) he
    rw [hag _ (Or.inl ⟨by omega, by omega⟩), hgen]
    exact (h2 e he).1
  · have hlt := idx_lt (c := vCap) (show i.1 ≤ L by omega) hv
    rw [hag _ (Or.inl ⟨by omega, by omega⟩), hgen]
    exact (h6 v hv).1

/-- The `S` clause with the list cells in any footprint `foot` inside the heap cells of the new
metadata gives `LevelSAt`. This is the form of the post of `dsUpdateSLevelsStmt`, whose new list
cells lie in the old heap cells or in the heap range it used. -/
theorem levelSAt_of_foot {L vCap eCap b : ℕ} {mem : ℕ → ℕ} {x : DynSpannerMeta L}
    {st : DynSpannerState L} {i : Fin (L + 1)} {foot : ℕ → Prop} {sl : List ℕ}
    (h1 : mem (dsSGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff))
    (h2 : ∀ v ∈ st.S_level i, v < vCap)
    (h3 : ∀ v < vCap,
      mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
      ((0 < mem (dsSGenBase b L vCap eCap + i.1) ∧
        mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ st.S_level i))
    (h4 : sl.Nodup) (h5 : ∀ v, v ∈ sl ↔ v ∈ st.S_level i)
    (h6 : if 0 < mem (dsSGenBase b L vCap eCap + i.1)
      then LinkedListIn foot mem (mem (dsSHeadBase b L vCap eCap + i.1)) sl
      else sl = [])
    (hfoot : ∀ a, foot a → heapFoot x a) (hsl : x.sLists i = sl) :
    LevelSAt L vCap eCap b mem x st i := by
  subst hsl
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split_ifs at h6 ⊢ <;>
    first
      | exact h6.mono hfoot
      | exact h6

end

end MinCostFlow.DynSpanner.Program
