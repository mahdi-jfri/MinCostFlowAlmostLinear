module

public import MinCostFlow.LastLevelProgram.IndexGraph
public import MinCostFlow.Num.Encoding
import Mathlib.Tactic

/-!
# Canonical memory for a fixed-point tree query

The oracle for Definition 5.8 (pages 19–20) needs one precise machine
input for a graph and its numeric vectors. Put the four arrays in
compact edge order and leave the output regions and the heap zeroed.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord Num

/-- The first cell of the compact lengths table. -/
@[expose] def queryLengths (G : MGraph) : ℕ := 2 * G.m

/-- The first cell of the compact weights table. -/
@[expose] def queryWeights (G : MGraph) (L : ℕ) : ℕ := queryLengths G + G.m * L

/-- The first cell of the original-edge result table. -/
@[expose] def queryOriginals (G : MGraph) (L : ℕ) : ℕ := queryWeights G L + G.m * L

/-- The first cell of the bridge result table. -/
@[expose] def queryBridges (G : MGraph) (L : ℕ) : ℕ := queryOriginals G L + G.n

/-- The first cell of the two-word result header. -/
@[expose] def queryHeader (G : MGraph) (L : ℕ) : ℕ := queryBridges G L + 2 * G.n

/-- The first cell available to the LSST workspace. -/
@[expose] def queryHeap (G : MGraph) (L : ℕ) : ℕ := queryHeader G L + 2

private def blockLimb (L : ℕ) (values : ℕ → ℤ) (offset : ℕ) : ℕ :=
  (encodeLimbs 1 L (values (offset / L))).getD (offset % L) 0

/-- Canonical input memory for positive lengths and weights with one-bit
limbs. The vectors are supplied as unscaled integer numerators. -/
def queryMemory (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) (a : ℕ) : ℕ :=
  if a < G.m then (indexedGraph G).tail a
  else if a < queryLengths G then (indexedGraph G).head (a - G.m)
  else if a < queryWeights G L then blockLimb L (len ∘ edgeName G) (a - queryLengths G)
  else if a < queryOriginals G L then blockLimb L (wt ∘ edgeName G) (a - queryWeights G L)
  else 0

private theorem blockLimb_at (L : ℕ) (values : ℕ → ℤ) (i j : ℕ) (hj : j < L) :
    blockLimb L values (i * L + j) =
      (encodeLimbs 1 L (values i))[j]'(by simpa using hj) := by
  have hL : 0 < L := (Nat.zero_le j).trans_lt hj
  have hdiv : (i * L + j) / L = i := by
    rw [Nat.mul_comm i L, Nat.mul_add_div hL, Nat.div_eq_of_lt hj, add_zero]
  have hmod : (i * L + j) % L = j := by
    rw [Nat.mul_comm i L, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  simp [blockLimb, hdiv, hmod, hj]

/-- Endpoints are stored in the two required compact arrays. -/
theorem queryMemory_endpoints (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) (i : ℕ)
    (hi : i < G.m) :
    queryMemory G L len wt i = (indexedGraph G).tail i ∧
      queryMemory G L len wt (G.m + i) = (indexedGraph G).head i := by
  refine ⟨ite_eq_left hi, ?_⟩
  have h1 : ¬ G.m + i < G.m := by omega
  have h2 : G.m + i < queryLengths G := by unfold queryLengths; omega
  simp [queryMemory, h1, h2]

/-- The canonical length and weight blocks store their signed encodings. -/
theorem queryMemory_blocks (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) (i : ℕ)
    (hi : i < G.m) :
    ListAt (queryMemory G L len wt) (queryLengths G + i * L)
      (encodeLimbs 1 L (len (edgeName G i))) ∧
    ListAt (queryMemory G L len wt) (queryWeights G L + i * L)
      (encodeLimbs 1 L (wt (edgeName G i))) := by
  have hmul : i * L + L ≤ G.m * L := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  constructor
  · intro j hj
    have hj' : j < L := by simpa using hj
    have hb₁ : ¬ queryLengths G + i * L + j < G.m := by unfold queryLengths; omega
    have hb₂ : ¬ queryLengths G + i * L + j < queryLengths G := by omega
    have hb₃ : queryLengths G + i * L + j < queryWeights G L := by unfold queryWeights; omega
    have he : queryLengths G + i * L + j - queryLengths G = i * L + j := by omega
    simp only [queryMemory, hb₁, hb₂, hb₃, ↓reduceIte, he]
    exact blockLimb_at L (len ∘ edgeName G) i j hj'
  · intro j hj
    have hj' : j < L := by simpa using hj
    have hb₁ : ¬ queryWeights G L + i * L + j < G.m := by unfold queryWeights queryLengths; omega
    have hb₂ : ¬ queryWeights G L + i * L + j < queryLengths G := by unfold queryWeights; omega
    have hb₃ : ¬ queryWeights G L + i * L + j < queryWeights G L := by omega
    have hb₄ : queryWeights G L + i * L + j < queryOriginals G L := by unfold queryOriginals; omega
    have he : queryWeights G L + i * L + j - queryWeights G L = i * L + j := by omega
    simp only [queryMemory, hb₁, hb₂, hb₃, hb₄, ↓reduceIte, he]
    exact blockLimb_at L (wt ∘ edgeName G) i j hj'

/-- The canonical allocation starts with a zero workspace. -/
theorem queryMemory_zero_suffix (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) :
    ZeroFrom (queryMemory G L len wt) (queryOriginals G L) := by
  intro a ha
  unfold queryOriginals queryWeights queryLengths at ha
  simp [queryMemory, queryOriginals, queryWeights, queryLengths,
    show ¬ a < G.m by omega, show ¬ a < 2 * G.m by omega,
    show ¬ a < 2 * G.m + G.m * L by omega,
    show ¬ a < 2 * G.m + G.m * L + G.m * L by omega]

/-- In particular, the workspace starts at zero. -/
theorem queryMemory_zero (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) :
    ZeroFrom (queryMemory G L len wt) (queryHeap G L) := by
  intro a ha
  apply queryMemory_zero_suffix
  unfold queryHeap queryHeader queryBridges at ha
  omega

private theorem blockLimb_lt (L : ℕ) (v : ℕ → ℤ) (a : ℕ) :
    blockLimb L v a < 2 := by
  simp only [blockLimb, List.getD_eq_getElem?_getD]
  cases h : (encodeLimbs 1 L (v (a / L)))[a % L]? with
  | none => decide
  | some x =>
    have hx := encodeLimbs_lt 1 L (v (a / L)) x (List.mem_of_getElem? h)
    simpa [base] using hx

/-- Every canonical input cell fits the guest word. Compact endpoint
indices are bounded by the vertex count, and encoded limbs are bits. -/
theorem queryMemory_fits {G : MGraph} (hG : (indexedGraph G).Valid)
    (L : ℕ) (len wt : ℕ → ℤ) {B : ℕ} (hn : G.n ≤ B) (hB : 2 ≤ B) (a : ℕ) :
    queryMemory G L len wt a < B := by
  unfold queryMemory
  split
  · rename_i ha
    exact (hG.2 a ha).1.trans_le hn
  · rename_i ha
    split
    · rename_i hh
      have hi : a - G.m < G.m := by unfold queryLengths at hh; omega
      exact (hG.2 _ hi).2.trans_le hn
    · split
      · exact (blockLimb_lt _ _ _).trans_le hB
      · split
        · exact (blockLimb_lt _ _ _).trans_le hB
        · omega

/-- The packed arrays and a zero suffix give exactly the canonical
guest memory. This allows preparation in a fresh host region. -/
theorem queryMemory_eq_of_arrays (G : MGraph) {L : ℕ} (hL : 0 < L)
    (len wt : ℕ → ℤ) (mem : ℕ → ℕ)
    (ht : ∀ i < G.m, mem i = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (G.m + i) = (indexedGraph G).head i)
    (hl : ∀ i < G.m, ListAt mem (queryLengths G + i * L)
      (encodeLimbs 1 L (len (edgeName G i))))
    (hv : ∀ i < G.m, ListAt mem (queryWeights G L + i * L)
      (encodeLimbs 1 L (wt (edgeName G i))))
    (hz : ZeroFrom mem (queryOriginals G L)) :
    mem = queryMemory G L len wt := by
  have block (v : ℕ → ℤ) (b : ℕ)
      (hat : ∀ i < G.m, ListAt mem (b + i * L) (encodeLimbs 1 L (v i)))
      (a : ℕ) (ha : b ≤ a) (hend : a < b + G.m * L) :
      mem a = blockLimb L v (a - b) := by
    let i := (a - b) / L
    let j := (a - b) % L
    have hi : i < G.m := (Nat.div_lt_iff_lt_mul hL).mpr (by omega)
    have hj : j < L := Nat.mod_lt _ hL
    have hsplit : i * L + j = a - b := by
      simpa [i, j, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div (a - b) L
    have hadd : b + i * L + j = a := by omega
    rw [← hsplit, blockLimb_at _ _ _ _ hj, ← hadd]
    exact hat i hi j (by simpa using hj)
  funext a
  unfold queryMemory
  split
  · exact ht a ‹a < G.m›
  · split
    · have hlt : a - G.m < G.m := by
        have h := ‹a < queryLengths G›
        unfold queryLengths at h
        omega
      simpa only [show G.m + (a - G.m) = a by omega] using hh _ hlt
    · split
      · exact block (len ∘ edgeName G) _ hl a (by omega) ‹a < queryWeights G L›
      · split
        · exact block (wt ∘ edgeName G) _ hv a (by omega) ‹a < queryOriginals G L›
        · exact hz a (by omega)

/-- The relocation copies only the input prefix. Cells following a
staged prefix can hold other allocations without affecting its readout. -/
theorem queryMemory_prefix_of_arrays (G : MGraph) {L src : ℕ} (hL : 0 < L)
    (len wt : ℕ → ℤ) (mem : ℕ → ℕ)
    (ht : ∀ i < G.m, mem (src+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (src+(G.m+i)) = (indexedGraph G).head i)
    (hl : ∀ i < G.m, ListAt mem (src+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i))))
    (hv : ∀ i < G.m, ListAt mem (src+queryWeights G L+i*L)
      (encodeLimbs 1 L (wt (edgeName G i)))) :
    ∀ i < queryOriginals G L, mem (src+i) = queryMemory G L len wt i := by
  let input := fun i => if i < queryOriginals G L then mem (src+i) else 0
  have ht' (i : ℕ) (hi : i < G.m) : input i = (indexedGraph G).tail i := by
    have h : i < queryOriginals G L := by
      unfold queryOriginals queryWeights queryLengths
      omega
    simpa only [input, ite_eq_left h] using ht i hi
  have hh' (i : ℕ) (hi : i < G.m) : input (G.m+i) = (indexedGraph G).head i := by
    have h : G.m+i < queryOriginals G L := by
      unfold queryOriginals queryWeights queryLengths
      omega
    simpa only [input, ite_eq_left h] using hh i hi
  have hl' (i : ℕ) (hi : i < G.m) : ListAt input (queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i))) := by
    intro j hj
    have hj' : j < L := by simpa using hj
    have hm := Nat.mul_le_mul_right L hi
    rw [Nat.succ_mul] at hm
    have h : queryLengths G+i*L+j < queryOriginals G L := by
      unfold queryOriginals queryWeights
      omega
    change input (queryLengths G+i*L+j) = _
    rw [show input (queryLengths G+i*L+j) = mem (src+(queryLengths G+i*L+j)) from ite_eq_left h]
    simpa only [Nat.add_assoc] using hl i hi j hj
  have hv' (i : ℕ) (hi : i < G.m) : ListAt input (queryWeights G L+i*L)
      (encodeLimbs 1 L (wt (edgeName G i))) := by
    intro j hj
    have hj' : j < L := by simpa using hj
    have hm := Nat.mul_le_mul_right L hi
    rw [Nat.succ_mul] at hm
    have h : queryWeights G L+i*L+j < queryOriginals G L := by
      unfold queryOriginals
      omega
    change input (queryWeights G L+i*L+j) = _
    rw [show input (queryWeights G L+i*L+j) = mem (src+(queryWeights G L+i*L+j)) from ite_eq_left h]
    simpa only [Nat.add_assoc] using hv i hi j hj
  have hz : ZeroFrom input (queryOriginals G L) := by
    intro i hi
    exact ite_eq_right (not_lt.mpr hi)
  have he := queryMemory_eq_of_arrays G hL len wt input ht' hh' hl' hv' hz
  intro i hi
  simpa only [input, ite_eq_left hi] using congrFun he i

end MinCostFlow.LastLevelProgram
