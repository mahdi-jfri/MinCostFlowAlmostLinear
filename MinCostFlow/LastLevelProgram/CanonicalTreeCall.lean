module

public import MinCostFlow.LastLevelProgram.QueryMemory
public import MinCostFlow.LastLevelProgram.TreeCall
import Mathlib.Tactic

/-!
# The LSST run on canonical fixed-point inputs

For any fitting positive integer numerators, Theorem 2.2 (page 7)
runs on the canonical query memory. Its output supplies a named tree
for the multiplicative-weights oracle of Definition 5.8 (pages 19–20).
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord Num

/-- The canonical query's arguments, register defaults, and packed
prefix fit at the guest width selected by Theorem 2.2 (page 7). -/
theorem canonicalTreeCall_wordBounds (Q : Program) (c₀ : ℕ) (K : ℝ)
    (hc : 1 ≤ c₀) (G : MGraph) (L : ℕ) (hL : 1 ≤ L) (mem : ℕ → ℕ) :
    let heap := queryHeap G L
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let w := max 5 (Nat.log 2 (heap + lsstSpace Q K G.n G.m sim 1) + 1)
    let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
      queryOriginals G L, queryBridges G L, queryHeader G L, heap]
    G.n < 2 ^ w ∧ 2 ≤ 2 ^ w ∧ queryOriginals G L < 2 ^ w ∧
      ∀ r, (startState args mem 0).regs r < 2 ^ w := by
  intro heap sim w args
  have hspace : heap + lsstSpace Q K G.n G.m sim 1 < 2 ^ w :=
    (lsst_param_selection Q c₀ K hc (indexedGraph G) L heap hL).2.2.2.2.2
  have hheap : heap < 2 ^ w := (Nat.le_add_right _ _).trans_lt hspace
  have hn : G.n < 2 ^ w := by
    have h : G.n ≤ lsstSpace Q K G.n G.m sim 1 := by
      unfold lsstSpace
      omega
    omega
  have hsim : sim < 2 ^ w := by
    have h : sim ≤ (2 + 3 * (4 * G.m)) * sim :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h' : (2 + 3 * (4 * G.m)) * sim ≤ lsstSpace Q K G.n G.m sim 1 := by
      unfold lsstSpace
      omega
    omega
  have hlimb : L < 2 ^ w := by
    apply lt_of_le_of_lt _ hsim
    apply le_trans _ (le_max_left _ _)
    unfold kWidthOf
    omega
  have hbit : 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by dsimp [w]; omega : 1 ≤ w)
  have hprefix : queryOriginals G L < 2 ^ w := by
    dsimp [heap, queryHeap, queryHeader, queryBridges] at hheap
    omega
  refine ⟨hn, hbit, hprefix, ?_⟩
  intro r
  change args.getD r 0 < _
  simp only [List.getD_eq_getElem?_getD]
  cases h : args[r]? with
  | none => exact Nat.two_pow_pos _
  | some a =>
    have ha := List.mem_of_getElem? h
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at ha
    dsimp [heap, queryHeap, queryHeader, queryBridges, queryOriginals, queryWeights,
      queryLengths] at hheap ⊢
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      try dsimp [heap, queryHeap, queryHeader, queryBridges, queryOriginals, queryWeights, queryLengths]
      omega

/-- A canonical standalone run supplies the named low-stretch tree for
integer numerators at a common fractional precision. -/
theorem canonicalTreeCall_runs :
    ∃ (Q : Program) (c₀ : ℕ) (K : ℝ), 1 ≤ c₀ ∧
      ∀ (G : MGraph) (L P : ℕ) (len wt : ℕ → ℤ),
        G.IsValid → G.V.Nonempty → 1 ≤ L →
        (∀ e ∈ G.E, 0 < len e ∧ Fits 1 L (len e)) →
        (∀ e ∈ G.E, 0 < wt e ∧ Fits 1 L (wt e)) →
        let H := indexedGraph G
        let p : Program := ⟨lsstModule Q 0 1⟩
        let heap := queryHeap G L
        let sim := lsstLSimMin c₀ H.n H.m L 1
        let w := max 5 (Nat.log 2 (heap + lsstSpace Q K H.n H.m sim 1) + 1)
        let orig := queryOriginals G L
        let bridge := queryBridges G L
        let header := queryHeader G L
        let args := [H.n, H.m, 0, H.m, queryLengths G, queryWeights G L, L, sim,
          orig, bridge, header, heap]
        ∃ st cost,
          Runs w p (fun _ => false) (lsstEntryProc 0 1)
            (startState args (queryMemory G L len wt) 0) (.returned 0) st cost ∧
          LSF.IsLSST H.toMGraph ((fun e => (len e : ℝ) / (2 : ℝ)^P) ∘ edgeName G)
            ((fun e => (wt e : ℝ) / (2 : ℝ)^P) ∘ edgeName G)
            ((4 * max K 1 + 5) * Real.log (↑G.n + 2)^2)
            (treeFromOutput G st.mem orig bridge header) ∧
          LSF.IsLSST G (fun e => (len e : ℝ) / (2 : ℝ)^P) (fun e => (wt e : ℝ) / (2 : ℝ)^P)
            ((4 * max K 1 + 5) * Real.log (↑G.n + 2)^2)
            (restoreTreeNames G (treeFromOutput G st.mem orig bridge header)) ∧
          (cost : ℝ) ≤ 16000 * ((G.m + G.n + 1 : ℕ) : ℝ) *
            lsstOverheadFactor Q c₀ K G.n G.m L ∧
          st.mem header ≤ G.n ∧ st.mem (header + 1) ≤ G.n ∧
          (∀ (base : ℕ) (moved : ℕ → ℕ),
            (∀ a < 2 ^ w, moved (base + a) = st.mem a) →
            treeFromOutput G moved (base + orig) (base + bridge) (base + header) =
              treeFromOutput G st.mem orig bridge header) := by
  obtain ⟨Q, c₀, K, hc, _, _, hcall⟩ := theorem_2_2_program_linear
  refine ⟨Q, c₀, K, hc, ?_⟩
  intro G L P len wt hG hV hL hLent hWt H p heap sim w orig bridge header args
  let mem := queryMemory G L len wt
  have hp : p.HasAt 0 (lsstModule Q 0 1) := by
    intro i hi
    simp [p]
  have hlengths (i : ℕ) (hi : i < G.m) :
      Num.Valid mem (queryLengths G + i * L) 1 L ∧
      Num.fixVal mem (queryLengths G + i * L) 1 L P = (len (edgeName G i) : ℝ) / (2 : ℝ)^P := by
    have hat := (queryMemory_blocks G L len wt i hi).1
    refine ⟨valid_encodeLimbs hat, ?_⟩
    rw [Num.fixVal, intVal_encodeLimbs hat ((hLent _ (edgeName_mem hi)).2)]
  have hweights (i : ℕ) (hi : i < G.m) :
      Num.Valid mem (queryWeights G L + i * L) 1 L ∧
      Num.fixVal mem (queryWeights G L + i * L) 1 L P = (wt (edgeName G i) : ℝ) / (2 : ℝ)^P := by
    have hat := (queryMemory_blocks G L len wt i hi).2
    refine ⟨valid_encodeLimbs hat, ?_⟩
    rw [Num.fixVal, intVal_encodeLimbs hat (hWt _ (edgeName_mem hi)).2]
  have hlengthPos (i : ℕ) (hi : i < G.m) :
      0 < Num.fixVal mem (queryLengths G + i * L) 1 L P := by
    rw [(hlengths i hi).2]
    exact div_pos (by exact_mod_cast (hLent _ (edgeName_mem hi)).1) (by positivity)
  have hweightPos (i : ℕ) (hi : i < G.m) :
      0 < Num.fixVal mem (queryWeights G L + i * L) 1 L P := by
    rw [(hweights i hi).2]
    exact div_pos (by exact_mod_cast (hWt _ (edgeName_mem hi)).1) (by positivity)
  let ℓ := fun e => (len e : ℝ) / (2 : ℝ)^P
  let v := fun e => (wt e : ℝ) / (2 : ℝ)^P
  have htail : ListAt mem 0 (List.ofFn fun i : Fin H.m => H.tail i) := by
    intro i hi
    have hi' : i < G.m := by simpa only [List.length_ofFn, H, indexedGraph] using hi
    simpa only [List.getElem_ofFn, Nat.zero_add] using (queryMemory_endpoints G L len wt i hi').1
  have hhead : ListAt mem G.m (List.ofFn fun i : Fin H.m => H.head i) := by
    intro i hi
    have hi' : i < G.m := by simpa only [List.length_ofFn, H, indexedGraph] using hi
    simpa only [List.getElem_ofFn] using (queryMemory_endpoints G L len wt i hi').2
  have hout := hcall 0 p H (v ∘ edgeName G) (ℓ ∘ edgeName G) P
    0 G.m (queryLengths G) (queryWeights G L) L orig bridge header heap mem 0 (fun _ => false)
    hp (indexedGraph_valid hG hV) hL
    (by dsimp [H, indexedGraph, heap, queryHeap, queryHeader, queryBridges, queryOriginals, queryWeights, queryLengths]; omega)
    (by dsimp [H, indexedGraph, heap, queryHeap, queryHeader, queryBridges, queryOriginals, queryWeights, queryLengths]; omega)
    (by dsimp [H, indexedGraph, heap, queryHeap, queryHeader, queryBridges, queryOriginals, queryWeights, queryLengths]; omega)
    (by dsimp [H, indexedGraph, heap, queryHeap, queryHeader, queryBridges, queryOriginals, queryWeights, queryLengths]; omega)
    (by dsimp [H, indexedGraph, heap, orig, queryHeap, queryHeader, queryBridges]; omega)
    (by dsimp [H, indexedGraph, heap, bridge, queryHeap, queryHeader]; omega)
    le_rfl
    (Or.inl le_rfl) (Or.inl (Nat.le_add_right _ _)) (Or.inl le_rfl)
    htail hhead
    (fun i hi => ⟨(hlengths i hi).1, (hlengths i hi).2,
      by simpa only [(hlengths i hi).2, Function.comp_apply, ℓ] using hlengthPos i hi⟩)
    (fun i hi => ⟨(hweights i hi).1, (hweights i hi).2,
      by simpa only [(hweights i hi).2, Function.comp_apply, v] using hweightPos i hi⟩)
    (queryMemory_zero G L len wt)
  obtain ⟨st, cost, edges, pairs, hr, he, hb, heLen, hbLen, heAt, hbAt, htree, _, hcost⟩ := hout
  refine ⟨st, cost, hr, ?_, ?_, hcost.2, he.symm ▸ heLen, hb.symm ▸ hbLen, ?_⟩
  · rw [treeFromOutput_eq G st.mem orig bridge header edges pairs he hb heAt hbAt]
    exact htree
  · rw [treeFromOutput_eq G st.mem orig bridge header edges pairs he hb heAt hbAt]
    exact restoreTreeNames_isLSST hG htree

  · intro base moved hmem
    have hheap : heap < 2 ^ w := by
      apply (Nat.le_add_right heap _).trans_lt
      exact (Nat.lt_pow_succ_log_self (by decide) _).trans_le
        (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
    have hpairs (ps : List (ℕ × ℕ)) :
        (ps.flatMap fun q => [q.1, q.2]).length = 2 * ps.length := by
      induction ps with
      | nil => rfl
      | cons p ps ih => simp [ih, Nat.mul_succ]
    refine treeFromOutput_translate G st.mem moved base (2 ^ w) orig bridge header edges pairs
      he hb heAt hbAt ?_ ?_ ?_ hmem
    · dsimp [heap, queryHeap] at hheap
      dsimp [header]
      omega
    · dsimp [heap, queryHeap, queryHeader, queryBridges, orig] at hheap ⊢
      dsimp [H, indexedGraph] at heLen
      omega
    · rw [hpairs]
      dsimp [heap, queryHeap, queryHeader, bridge] at hheap ⊢
      dsimp [H, indexedGraph] at hbLen
      omega

end MinCostFlow.LastLevelProgram
