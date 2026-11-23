module

public import MinCostFlow.LastLevelProgram.PackValues
public import MinCostFlow.LastLevelProgram.NameTreeStretch
public import MinCostFlow.Machine.WideWord.LSSTProgram

/-!
# Calling Theorem 2.2 on the packed last-level graph

The endpoint and numeric packing passes supply the four arrays for the
verified LSST program. The call reads the original fixed-point values
through the compact edge-name map.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord

private def readBridgePairs (mem : ℕ → ℕ) (base : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | n + 1 => (mem base, mem (base + 1)) :: readBridgePairs mem (base + 2) n

private theorem readBridgePairs_eq {mem : ℕ → ℕ} (base : ℕ) (pairs : List (ℕ × ℕ))
    (hat : ListAt mem base (pairs.flatMap fun q => [q.1, q.2])) :
    readBridgePairs mem base pairs.length = pairs := by
  induction pairs generalizing base with
  | nil => rfl
  | cons q rest ih =>
    have h0 : mem base = q.1 := by
      simpa using hat 0 (by simp)
    have h1 : mem (base + 1) = q.2 := by
      simpa using hat 1 (by simp)
    have htail : ListAt mem (base + 2) (rest.flatMap fun p => [p.1, p.2]) := by
      intro i hi
      have h := hat (i + 2) (by simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons]; omega)
      simpa only [List.flatMap_cons, List.cons_append, List.nil_append,
        List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 2] using h
    simp only [List.length_cons, readBridgePairs, h0, h1, ih _ htail, Prod.eta]

/-- Decode a compact tree directly from the LSST output header and arrays. -/
def treeFromOutput (H : MGraph) (mem : ℕ → ℕ) (orig bridges output : ℕ) : MGraph :=
  let G := indexedGraph H
  let edges := List.ofFn fun i : Fin (mem output) => mem (orig + i)
  let pairs := readBridgePairs mem bridges (mem (output + 1))
  decodedTree H.n H.m G.tail G.head edges pairs

/-- Reading the counted original-edge array supplies the exact list
used by the compact tree decoder. -/
theorem treeFromOutput_originals (G : MGraph) (mem : ℕ → ℕ) (orig bridges output : ℕ) :
    ∃ (edges : List ℕ) (pairs : List (ℕ × ℕ)),
      edges.length = mem output ∧ pairs.length = mem (output + 1) ∧
      ListAt mem orig edges ∧
      treeFromOutput G mem orig bridges output =
        decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head edges pairs := by
  have hlength (base count : ℕ) : (readBridgePairs mem base count).length = count := by
    induction count generalizing base with
    | zero => rfl
    | succ n ih => simp [readBridgePairs, ih]
  refine ⟨List.ofFn (fun i : Fin (mem output) => mem (orig + i)),
    readBridgePairs mem bridges (mem (output + 1)), List.length_ofFn, hlength _ _, ?_, rfl⟩
  intro i hi
  simp

/-- The original-edge list is determined by the LSST output memory. -/
theorem originalEdges_eq_of_output {mem : ℕ → ℕ} {orig output : ℕ} {edges : List ℕ}
    (hlen : mem output = edges.length) (hat : ListAt mem orig edges) :
    (List.ofFn fun i : Fin (mem output) => mem (orig + i)) = edges := by
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hi'
    rw [List.getElem_ofFn]
    exact hat i hi'

/-- The decoded tree in the running-time theorem is the tree read from the
output cells. Hence the low-stretch claim transfers to the decoded memory. -/
theorem treeFromOutput_eq (H : MGraph) (mem : ℕ → ℕ) (orig bridges output : ℕ)
    (edges : List ℕ) (pairs : List (ℕ × ℕ))
    (he : mem output = edges.length) (hp : mem (output + 1) = pairs.length)
    (heAt : ListAt mem orig edges)
    (hpAt : ListAt mem bridges (pairs.flatMap fun q => [q.1, q.2])) :
    treeFromOutput H mem orig bridges output =
      decodedTree H.n H.m (indexedGraph H).tail (indexedGraph H).head edges pairs := by
  unfold treeFromOutput
  rw [originalEdges_eq_of_output he heAt, hp, readBridgePairs_eq bridges pairs hpAt]

/-- The output of Theorem 2.2 (page 7) decodes to the same tree after
moving its header and arrays by a common base. -/
theorem treeFromOutput_translate (H : MGraph) (mem moved : ℕ → ℕ)
    (base bound orig bridges output : ℕ) (edges : List ℕ) (pairs : List (ℕ × ℕ))
    (he : mem output = edges.length) (hp : mem (output + 1) = pairs.length)
    (heAt : ListAt mem orig edges)
    (hpAt : ListAt mem bridges (pairs.flatMap fun q => [q.1, q.2]))
    (ho : output + 1 < bound) (heBound : orig + edges.length ≤ bound)
    (hpBound : bridges + (pairs.flatMap fun q => [q.1, q.2]).length ≤ bound)
    (hmem : ∀ a < bound, moved (base + a) = mem a) :
    treeFromOutput H moved (base + orig) (base + bridges) (base + output) =
      treeFromOutput H mem orig bridges output := by
  rw [treeFromOutput_eq H mem orig bridges output edges pairs he hp heAt hpAt]
  apply treeFromOutput_eq H moved (base + orig) (base + bridges) (base + output) edges pairs
  · exact (hmem output (by omega)).trans he
  · rw [Nat.add_assoc, hmem (output + 1) ho, hp]
  · intro i hi
    rw [Nat.add_assoc, hmem (orig + i) (by omega)]
    exact heAt i hi
  · intro i hi
    rw [Nat.add_assoc, hmem (bridges + i) (by omega)]
    exact hpAt i hi

/-- Theorem 2.2 (page 7) on a packed named graph. The length and weight
premises describe the copies made by the two numeric packing passes.
The guarantee is for the named tree read from the returned memory. -/
theorem packedTreeCall_runs :
    ∃ (Q : Program) (c₀ : ℕ) (K : ℝ), 1 ≤ c₀ ∧
      (∀ b, ∀ s ∈ lsstModule Q b 1, s.NoRand) ∧
      ∀ (b : ℕ) (p : Program) (H : MGraph)
        (L P tails heads lens weights orig bridges output heap pos : ℕ)
        (mem lensIn weightsIn : ℕ → ℕ) (lenIn weightIn : ℕ) (ω : ℕ → Bool),
        let G := indexedGraph H
        let sim := lsstLSimMin c₀ G.n G.m L 1
        let w := max 5 (Nat.log 2 (heap + lsstSpace Q K G.n G.m sim 1) + 1)
        let ℓ := fun e => Num.fixVal lensIn (lenIn + e * L) 1 L P
        let v := fun e => Num.fixVal weightsIn (weightIn + e * L) 1 L P
        p.HasAt b (lsstModule Q b 1) → H.IsValid → H.V.Nonempty → 1 ≤ L →
        tails + H.m ≤ heap → heads + H.m ≤ heap →
        lens + H.m * L ≤ heap → weights + H.m * L ≤ heap →
        orig + H.n ≤ heap → bridges + 2 * H.n ≤ heap → output + 2 ≤ heap →
        DisjointRanges orig H.n bridges (2 * H.n) →
        DisjointRanges orig H.n output 2 →
        DisjointRanges bridges (2 * H.n) output 2 →
        (∀ i < H.m, mem (tails + i) = G.tail i ∧ mem (heads + i) = G.head i) →
        (∀ i < H.m, ∀ j < L,
          mem (lens + i * L + j) = lensIn (lenIn + edgeName H i * L + j)) →
        (∀ i < H.m, ∀ j < L,
          mem (weights + i * L + j) = weightsIn (weightIn + edgeName H i * L + j)) →
        (∀ i < H.m, Num.Valid lensIn (lenIn + edgeName H i * L) 1 L ∧ 0 < ℓ (edgeName H i)) →
        (∀ i < H.m, Num.Valid weightsIn (weightIn + edgeName H i * L) 1 L ∧ 0 < v (edgeName H i)) →
        ZeroFrom mem heap →
        ∃ (st : State) (cost : ℕ) (edges : List ℕ) (pairs : List (ℕ × ℕ)),
          Runs w p ω (lsstEntryProc b 1)
            (startState [G.n, G.m, tails, heads, lens, weights, L, sim,
              orig, bridges, output, heap] mem pos)
            (.returned 0) st cost ∧
          st.mem output = edges.length ∧ st.mem (output + 1) = pairs.length ∧
          edges.length ≤ H.n ∧ pairs.length ≤ H.n ∧
          ListAt st.mem orig edges ∧
          ListAt st.mem bridges (pairs.flatMap fun q => [q.1, q.2]) ∧
          LSF.IsLSST H ℓ v ((4 * max K 1 + 5) * Real.log (↑H.n + 2)^2)
            (restoreTreeNames H (treeFromOutput H st.mem orig bridges output)) ∧
          (∀ a < heap, (a < orig ∨ orig + H.n ≤ a) →
            (a < bridges ∨ bridges + 2 * H.n ≤ a) →
            (a < output ∨ output + 2 ≤ a) → st.mem a = mem a) ∧
          (cost : ℝ) ≤ 16000 * ((H.m + H.n + 1 : ℕ) : ℝ) *
            lsstOverheadFactor Q c₀ K H.n H.m L := by
  obtain ⟨Q, c₀, K, hc₀, hdet, _, hcall⟩ := theorem_2_2_program_linear
  refine ⟨Q, c₀, K, hc₀, hdet, ?_⟩
  intro b p H L P tails heads lens weights orig bridges output heap pos mem lensIn weightsIn
    lenIn weightIn ω G sim w ℓ v hp hH hV hL ht hh hl hv ho hb hhdr hob hoh hbh he hlen hwt
    hvalidLen hvalidWt hz
  have htailAt : ListAt mem tails (List.ofFn fun i : Fin G.m => G.tail i) := by
    intro i hi
    have hmi : i < H.m := by simpa only [List.length_ofFn, G, indexedGraph] using hi
    simpa only [List.getElem_ofFn] using (he i hmi).1
  have hheadAt : ListAt mem heads (List.ofFn fun i : Fin G.m => G.head i) := by
    intro i hi
    have hmi : i < H.m := by simpa only [List.length_ofFn, G, indexedGraph] using hi
    simpa only [List.getElem_ofFn] using (he i hmi).2
  have hlenAt : ∀ i < G.m, Num.Valid mem (lens + i * L) 1 L ∧
      Num.fixVal mem (lens + i * L) 1 L P = ℓ (edgeName H i) ∧ 0 < ℓ (edgeName H i) := by
    intro i hi
    obtain ⟨hvalid, hpos⟩ := hvalidLen i hi
    obtain ⟨hvalid', hvalue⟩ := packedValue_eq (P := P) (hlen i hi) hvalid
    exact ⟨hvalid', hvalue, hpos⟩
  have hwtAt : ∀ i < G.m, Num.Valid mem (weights + i * L) 1 L ∧
      Num.fixVal mem (weights + i * L) 1 L P = v (edgeName H i) ∧ 0 < v (edgeName H i) := by
    intro i hi
    obtain ⟨hvalid, hpos⟩ := hvalidWt i hi
    obtain ⟨hvalid', hvalue⟩ := packedValue_eq (P := P) (hwt i hi) hvalid
    exact ⟨hvalid', hvalue, hpos⟩

  obtain ⟨st, cost, edges, pairs, hr, hcountE, hcountB, hsizeE, hsizeB,
    hEdges, hPairs, hTree, hFrame, hCost⟩ :=
    hcall b p G (v ∘ edgeName H) (ℓ ∘ edgeName H) P tails heads lens weights L
      orig bridges output heap mem pos ω hp (indexedGraph_valid hH hV) hL
      ht hh hl hv ho hb hhdr hob hoh hbh htailAt hheadAt hlenAt hwtAt hz
  refine ⟨st, cost, edges, pairs, hr, hcountE, hcountB, hsizeE, hsizeB, hEdges,
    hPairs, ?_, hFrame, hCost.2⟩
  rw [treeFromOutput_eq H st.mem orig bridges output edges pairs hcountE hcountB hEdges hPairs]
  exact restoreTreeNames_isLSST hH hTree

/-- All successful executions from the same prepared query on the same
tape expose the same named tree. -/
theorem packedTreeOutput_unique {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {body : Stmt} {start st₁ st₂ : State} {o₁ o₂ : Outcome} {c₁ c₂ : ℕ}
    (h₁ : Runs w p ω body start o₁ st₁ c₁) (h₂ : Runs w p ω body start o₂ st₂ c₂)
    (H : MGraph) (orig bridges output : ℕ) :
    restoreTreeNames H (treeFromOutput H st₁.mem orig bridges output) =
      restoreTreeNames H (treeFromOutput H st₂.mem orig bridges output) := by
  rw [(h₁.det h₂).2.1]

end MinCostFlow.LastLevelProgram
