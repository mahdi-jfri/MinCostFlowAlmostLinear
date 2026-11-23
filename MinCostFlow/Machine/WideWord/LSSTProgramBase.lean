module

public import MinCostFlow.Machine.WideWord.LSSTSimDecode
public import MinCostFlow.Machine.WideWord.LSSTEncodeGAug
public import MinCostFlow.Machine.WideWord.LSSTGraph
public import MinCostFlow.Machine.WideWord.LSSTWeights
public import MinCostFlow.Machine.WideWord.LSSTReduction
import MinCostFlow.LowStretch.ProgClusterSetupLs
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Program Assembly Base, Parameter Selection, and Contract for Theorem 2.2

This file defines the complete deterministic WordRAM entry procedure `lsstEntryProc` and module
`lsstModule`, establishes `lsstModule_length`, `lsstModule_noRand`, `Program.HasAt` extraction
lemmas for every submodule, graph/word-size/cost/space parameter bounds (`wordSize_bound_of_weights`,
`lsstLSimMin`, `anCostBound`, `lsstSpace`, `lsstCost`), the host-level contract `lsstContract`, and
the star-branch correctness theorem `lsst_star_runs`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Module layout and entry procedure -/

def idxLSSTEntry : ℕ := 0
def lsstGraphBase (b : ℕ) : ℕ := b + 1
def lsstWeightsBase (b : ℕ) : ℕ := b + 7
def lsstPackBase (b : ℕ) : ℕ := b + 58
def lsstWrapBase (b : ℕ) : ℕ := b + 59
def lsstEncodeBase (b : ℕ) : ℕ := b + 61
def lsstSimBase (b : ℕ) : ℕ := b + 66

/-- Top-level deterministic WordRAM entry procedure implementing Theorem 2.2.
Arguments (`regs 0..11`):
`[n, m, tailArr, headArr, lenArr, wtArr, L, L_sim, outOrigPtr, outBridgePtr, outHdrPtr, heap]`. -/
def lsstEntryProc (b h : ℕ) : Stmt :=
  .call 20 (lsstGraphBase b + idxScanNonloops) [.reg 1, .reg 2, .reg 3, .reg 11] ;;
  .cond (.reg 20)
    -- General branch (`1 ≤ nlLen`): CSR -> VertIdx -> BfsBridges -> Weights -> EncodeGAug -> SimDecode
    (.assign 21 (.bin .add (.reg 11) (.reg 1)) ;;
     .call 22 (lsstGraphBase b + idxBuildCSR) [.reg 0, .reg 20, .reg 11, .reg 2, .reg 3, .reg 21] ;;
     .assign 23 (.load (.reg 21)) ;;
     .assign 24 (.load (.bin .add (.reg 21) (.const 1))) ;;
     .assign 25 (.bin .add (.reg 21) (.const 2)) ;;
     .assign 26 (.bin .add (.reg 25) (.reg 0)) ;;
     .assign 27 (.bin .add (.reg 26) (.reg 0)) ;;
     .assign 28 (.bin .add (.reg 27) (.bin .add (.reg 0) (.const 1))) ;;
     .assign 29 (.load (.reg 25)) ;;
     .call 45 (lsstGraphBase b + idxBuildVertIdx) [.reg 23, .reg 25, .reg 22] ;;
     .assign 30 (.bin .add (.reg 22) (.reg 0)) ;;
     .assign 31 (.bin .add (.reg 30) (.reg 0)) ;;
     .call 32 (lsstGraphBase b + idxBfsBridges)
       [.reg 0, .reg 27, .reg 28, .reg 23, .reg 25, .reg 30, .reg 31] ;;
     .assign 33 (.bin .add (.reg 31) (.bin .mul (.const 2) (.reg 0))) ;;
     .assign 34 (.bin .add (.reg 33) (.reg 20)) ;;
     .assign 35 (.bin .add (.reg 34) (.const 1)) ;;
     .assign 36 (.bin .add (.reg 35) (.bin .mul (.reg 20) (.reg 7))) ;;
     .call 37 (lsstWeightsBase b + idxWeightsEntry)
       [.reg 20, .reg 11, .reg 4, .reg 5, .reg 23, .reg 6, .reg 33, .reg 35, .reg 34, .reg 36] ;;
     .assign 38 (.load (.reg 34)) ;;
     .assign 39 (.bin .add (.reg 37) (.bin .mul (.const 2) (.reg 20))) ;;
     .call 40 (lsstEncodeBase b + idxEncodeGAug)
       [.reg 20, .reg 11, .reg 2, .reg 3, .reg 22, .reg 33, .reg 35, .reg 38, .reg 23,
         .reg 32, .reg 30, .reg 7, .const (2 ^ h), .reg 37, .reg 39] ;;
     .assign 41 (.bin .add (.reg 40) (.reg 32)) ;;
     .assign 42 (.bin .add (.const 2) (.bin .mul (.const 3) (.reg 41))) ;;
     .assign 43 (.bin .add (.reg 39) (.bin .mul (.reg 42) (.reg 7))) ;;
     .call 45 (lsstEncodeBase b + idxSimDecode)
       [.reg 23, .reg 41, .reg 40, .reg 32, .reg 30, .reg 24, .reg 26, .reg 29, .reg 39,
         .reg 7, .const h, .const (2 ^ h), .reg 37, .reg 8, .reg 9, .reg 10, .reg 43] ;;
     .ret (.const 0))
    -- Star branch (`nlLen = 0`): all edges are self-loops
    (.store (.reg 10) (.const 0) ;;
     .call 21 (lsstGraphBase b + idxStarPairs) [.reg 0, .reg 9] ;;
     .store (.bin .add (.reg 10) (.const 1)) (.reg 21) ;;
     .ret (.const 0))

theorem lsstEntryProc_noRand (b h : ℕ) : (lsstEntryProc b h).NoRand := by
  dsimp only [lsstEntryProc, Stmt.NoRand]
  simp

/-- Full relocated WordRAM module implementing Theorem 2.2 from a guest `[AN19]` program `Q_AN`. -/
def lsstModule (Q_AN : Program) (b h : ℕ) : List Stmt :=
  [lsstEntryProc b h] ++
  graphModule (lsstGraphBase b) ++
  weightsModule (lsstWeightsBase b) h ++
  Num.packWordModule (lsstPackBase b) h ++
  wrapperModule (lsstSimBase b + 1) (lsstSimBase b + 19) ++
  encodeDecodeModule (lsstSimBase b + 1) (lsstPackBase b) (lsstWrapBase b)
    (lsstSimBase b) (lsstEncodeBase b) ++
  compile Q_AN (lsstSimBase b)

theorem lsstModule_length (Q_AN : Program) (b h : ℕ) :
    (lsstModule Q_AN b h).length = 87 + Q_AN.procs.length := by
  simp only [lsstModule, List.length_append, List.length_cons, List.length_nil,
    graphModule_length, weightsModule_length, wrapperModule_length,
    encodeDecodeModule_length, compile_length]
  change 1 + 6 + 51 + [Num.packWordBody h].length + 2 + 5 + (21 + Q_AN.procs.length) =
    87 + Q_AN.procs.length
  simp only [List.length_cons, List.length_nil]
  omega

theorem lsstModule_noRand (Q_AN : Program) (b h : ℕ) :
    ∀ s ∈ lsstModule Q_AN b h, s.NoRand := by
  intro s hs
  simp only [lsstModule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((((((rfl | hs) | hs) | hs) | hs) | hs) | hs)
  · exact lsstEntryProc_noRand b h
  · exact graphModule_noRand _ _ hs
  · exact weightsModule_noRand _ _ _ hs
  · simp only [Num.packWordModule, List.mem_cons, List.not_mem_nil, or_false] at hs
    rw [hs]; exact Num.packWordBody_noRand _ _
  · exact wrapperModule_noRand _ _ _ hs
  · exact encodeDecodeModule_noRand _ _ _ _ _ _ hs
  · exact compile_noRand _ _ _ hs

/-! ### `HasAt` extraction helpers -/

lemma hasAt_append_left {p : Program} {b : ℕ} {A B : List Stmt} (hp : p.HasAt b (A ++ B)) :
    p.HasAt b A := fun i hi => by
  have h := hp i (by rw [List.length_append]; omega)
  simpa [List.getElem_append_left hi] using h

lemma hasAt_append_right {p : Program} {b : ℕ} {A B : List Stmt} (hp : p.HasAt b (A ++ B)) :
    p.HasAt (b + A.length) B := fun i hi => by
  have h := hp (A.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (Nat.le_add_right _ _)] at h
  simp only [Nat.add_sub_cancel_left] at h
  rw [Nat.add_assoc]
  exact h

private def lsstTail (Q_AN : Program) (b h : ℕ) : List Stmt :=
  graphModule (lsstGraphBase b) ++
  weightsModule (lsstWeightsBase b) h ++
  Num.packWordModule (lsstPackBase b) h ++
  wrapperModule (lsstSimBase b + 1) (lsstSimBase b + 19) ++
  encodeDecodeModule (lsstSimBase b + 1) (lsstPackBase b) (lsstWrapBase b)
    (lsstSimBase b) (lsstEncodeBase b) ++
  compile Q_AN (lsstSimBase b)

private lemma hasAt_rest1 {p Q_AN : Program} {b h : ℕ}
    (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.HasAt (b + 1) (lsstTail Q_AN b h) := by
  have h0 : p.HasAt b ([lsstEntryProc b h] ++ lsstTail Q_AN b h) := by
    simpa only [lsstModule, lsstTail, List.append_assoc] using hp
  simpa only [List.length_cons, List.length_nil, Nat.zero_add] using hasAt_append_right h0

lemma lsst_hasAt_entry {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.procs[b + idxLSSTEntry]? = some (lsstEntryProc b h) := by
  have h := hp 0 (by simp [lsstModule])
  simpa [lsstModule, idxLSSTEntry] using h

lemma lsst_hasAt_graph {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.HasAt (lsstGraphBase b) (graphModule (lsstGraphBase b)) := by
  have h1 := hasAt_rest1 hp
  have h2 := hasAt_append_left (by simpa only [lsstTail, List.append_assoc] using h1)
  simpa only [lsstGraphBase] using h2

lemma lsst_hasAt_weights {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.HasAt (lsstWeightsBase b) (weightsModule (lsstWeightsBase b) h) := by
  have h1 := hasAt_append_right (by simpa only [lsstTail, List.append_assoc] using hasAt_rest1 hp)
  rw [graphModule_length] at h1
  have h2 := hasAt_append_left (by simpa only [List.append_assoc] using h1)
  simpa only [lsstWeightsBase, Nat.add_assoc] using h2

lemma lsst_hasAt_pack {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.HasAt (lsstPackBase b) (Num.packWordModule (lsstPackBase b) h) := by
  have h1 := hasAt_append_right (by simpa only [lsstTail, List.append_assoc] using hasAt_rest1 hp)
  have h2 := hasAt_append_right (by simpa only [List.append_assoc] using h1)
  rw [graphModule_length, weightsModule_length] at h2
  have h3 := hasAt_append_left (by simpa only [List.append_assoc] using h2)
  simpa only [lsstPackBase, Nat.add_assoc] using h3

lemma lsst_hasAt_wrap {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.HasAt (lsstWrapBase b) (wrapperModule (lsstSimBase b + 1) (lsstSimBase b + 19)) := by
  have h1 := hasAt_append_right (by simpa only [lsstTail, List.append_assoc] using hasAt_rest1 hp)
  have h2 := hasAt_append_right (by simpa only [List.append_assoc] using h1)
  have h3 := hasAt_append_right (by simpa only [List.append_assoc] using h2)
  have hlenp : (Num.packWordModule (lsstPackBase b) h).length = 1 := rfl
  rw [graphModule_length, weightsModule_length, hlenp] at h3
  have h4 := hasAt_append_left (by simpa only [List.append_assoc] using h3)
  simpa only [lsstWrapBase, Nat.add_assoc] using h4

lemma lsst_hasAt_encode {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.HasAt (lsstEncodeBase b)
      (encodeDecodeModule (lsstSimBase b + 1) (lsstPackBase b) (lsstWrapBase b)
        (lsstSimBase b) (lsstEncodeBase b)) := by
  have h1 := hasAt_append_right (by simpa only [lsstTail, List.append_assoc] using hasAt_rest1 hp)
  have h2 := hasAt_append_right (by simpa only [List.append_assoc] using h1)
  have h3 := hasAt_append_right (by simpa only [List.append_assoc] using h2)
  have h4 := hasAt_append_right (by simpa only [List.append_assoc] using h3)
  have hlenp : (Num.packWordModule (lsstPackBase b) h).length = 1 := rfl
  rw [graphModule_length, weightsModule_length, hlenp, wrapperModule_length] at h4
  have h5 := hasAt_append_left (by simpa only [List.append_assoc] using h4)
  simpa only [lsstEncodeBase, Nat.add_assoc] using h5

lemma lsst_hasAt_sim {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.HasAt (lsstSimBase b) (compile Q_AN (lsstSimBase b)) := by
  have h1 := hasAt_append_right (by simpa only [lsstTail, List.append_assoc] using hasAt_rest1 hp)
  have h2 := hasAt_append_right (by simpa only [List.append_assoc] using h1)
  have h3 := hasAt_append_right (by simpa only [List.append_assoc] using h2)
  have h4 := hasAt_append_right (by simpa only [List.append_assoc] using h3)
  have h5 := hasAt_append_right (by simpa only [List.append_assoc] using h4)
  have hlenp : (Num.packWordModule (lsstPackBase b) h).length = 1 := rfl
  rw [graphModule_length, weightsModule_length, hlenp, wrapperModule_length,
    encodeDecodeModule_length] at h5
  simpa only [lsstSimBase, Nat.add_assoc] using h5

lemma lsst_hasAt_arith {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.HasAt (lsstSimBase b + 1) (arithModule (lsstSimBase b + 1)) :=
  arithModule_hasAt_of_compile (lsst_hasAt_sim hp)

/-! ### Graph cardinality and list bounds -/

lemma nonloopEdges_length_le (G : IndexedGraph) : (nonloopEdges G).length ≤ G.m := by
  dsimp only [nonloopEdges]
  exact (List.length_filter_le _ _).trans (by simp [List.length_range])

lemma activeVertsList_length_le (G : IndexedGraph) : (activeVertsList G).length ≤ G.n := by
  dsimp only [activeVertsList]
  exact (List.length_filter_le _ _).trans (by simp [List.length_range])

lemma inactiveVertsList_length_le (n : ℕ) (V : List ℕ) : (inactiveVertsList n V).length ≤ n := by
  dsimp only [inactiveVertsList]
  exact (List.length_filter_le _ _).trans (by simp [List.length_range])

lemma active_add_inactive_le (G : IndexedGraph) :
    (activeVertsList G).length + (inactiveVertsList G.n (activeVertsList G)).length ≤ G.n := by
  set V := activeVertsList G
  set I := inactiveVertsList G.n V
  have hV_nd : V.Nodup := activeVertsList_nodup G
  have hI_nd : I.Nodup := inactiveVertsList_nodup G.n V
  have hdisj : Disjoint V.toFinset I.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxV hxI
    rw [List.mem_toFinset] at hxV hxI
    dsimp only [I, inactiveVertsList] at hxI
    rw [List.mem_filter] at hxI
    simp at hxI
    exact hxI.2 hxV
  have hsub : V.toFinset ∪ I.toFinset ⊆ (List.range G.n).toFinset := by
    intro x hx
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset] at hx
    rw [List.mem_toFinset]
    rcases hx with hxV | hxI
    · exact (List.mem_filter.mp hxV).1
    · exact (List.mem_filter.mp hxI).1
  have hcard : (V.toFinset ∪ I.toFinset).card ≤ (List.range G.n).toFinset.card :=
    Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hV_nd,
    List.toFinset_card_of_nodup hI_nd, List.toFinset_card_of_nodup List.nodup_range,
    List.length_range] at hcard
  exact hcard

lemma activeVertsList_ge_two_of_nl {G : IndexedGraph} (hG : G.Valid)
    (hnl : (nonloopEdges G).length ≠ 0) : 2 ≤ (activeVertsList G).length := by
  have hne : nonloopEdges G ≠ [] := by
    intro hnil; apply hnl; simp [hnil]
  obtain ⟨e, he_nl⟩ := List.exists_mem_of_ne_nil _ hne
  have he_lt : e < G.m := List.mem_range.mp (List.mem_filter.mp he_nl).1
  have hne_end : G.tail e ≠ G.head e := by
    have hf := (List.mem_filter.mp he_nl).2
    simpa [bne] using hf
  have htail : G.tail e ∈ activeVertsList G :=
    mem_activeVertsList_iff.mpr ⟨(hG.2 e he_lt).1, e, he_nl, Or.inl rfl⟩
  have hhead : G.head e ∈ activeVertsList G :=
    mem_activeVertsList_iff.mpr ⟨(hG.2 e he_lt).2, e, he_nl, Or.inr rfl⟩
  have hsub : [G.tail e, G.head e].toFinset ⊆ (activeVertsList G).toFinset := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (activeVertsList_nodup G)] at hc
  have h2 : ([G.tail e, G.head e] : List ℕ).Nodup := by
    simp [List.nodup_cons, hne_end]
  rw [List.toFinset_card_of_nodup h2, List.length_cons, List.length_cons, List.length_nil] at hc
  exact hc

lemma nonloop_ends_mem_active {G : IndexedGraph} (hG : G.Valid) {e : ℕ} (he : e ∈ nonloopEdges G) :
    G.tail e ∈ activeVertsList G ∧ G.head e ∈ activeVertsList G := by
  have he_lt : e < G.m := List.mem_range.mp (List.mem_filter.mp he).1
  exact ⟨mem_activeVertsList_iff.mpr ⟨(hG.2 e he_lt).1, e, he, Or.inl rfl⟩,
    mem_activeVertsList_iff.mpr ⟨(hG.2 e he_lt).2, e, he, Or.inr rfl⟩⟩

/-! ### Parameters, `[AN19]` word-size bounds, and cost/space definitions -/

lemma kWidthOf_mono {a b L : ℕ} (hab : a ≤ b) : kWidthOf a L ≤ kWidthOf b L := by
  dsimp only [kWidthOf]
  have hlog : Nat.log 2 (4 * a + 2) ≤ Nat.log 2 (4 * b + 2) := Nat.log_mono_right (by omega)
  omega

lemma kWidthOf_ge_five (nlCnt L : ℕ) (hL : 1 ≤ L) : 5 ≤ kWidthOf nlCnt L := by
  dsimp only [kWidthOf]
  have hlog : 1 ≤ Nat.log 2 (4 * nlCnt + 2) := Nat.log_pos (by norm_num) (by omega)
  omega

/-- Explicit upper bound on `[AN19]`'s runtime `cost` on `G_aug` (at most `4 * m` edges),
carrying `Cited.logLogFactor` and `Cited.weightFactor`. -/
noncomputable def anCostBound (K_AN : ℝ) (n m L_sim h : ℕ) : ℕ :=
  Nat.ceil (max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
    (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))))

/-- Explicit upper bound on `WordRAM.wordSize c_AN G_aug.encode`. -/
def w'Max (c_AN _n m L h : ℕ) : ℕ :=
  c_AN * (Nat.log 2 (6 + 16 * m) + kWidthOf m L * h + 3)

/-- Minimum simulation limb count `L_sim` required by `lsstEntryProc`. -/
def lsstLSimMin (c_AN n m L h : ℕ) : ℕ :=
  max (kWidthOf m L) (w'Max c_AN n m L h)

/-- Scratch memory above `heap` used by `lsstModule`. -/
noncomputable def lsstSpace (Q_AN : Program) (K_AN : ℝ) (n m L_sim h : ℕ) : ℕ :=
  (4 + 9 * n + 4 * m + m * L_sim) + weightsSpace m L_sim + 2 * m +
    (2 + 3 * (4 * m)) * L_sim +
    simDecodeSpace Q_AN (2 * m) (4 * m) L_sim h (anCostBound K_AN n m L_sim h)

/-- Total machine cost bound of `lsstModule`. -/
noncomputable def lsstCost (Q_AN : Program) (K_AN : ℝ) (c_AN n m L L_sim h : ℕ) : ℕ :=
  scanNonloopsCost m + starPairsCost n +
  buildCSRCost n m + buildVertIdxCost n + bfsBridgesCost n m + weightsCost m L +
  (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
  simDecodeCost Q_AN (w'Max c_AN n m L h) (2 * m) (4 * m) n L_sim (anCostBound K_AN n m L_sim h) +
  500

lemma lsstLSimMin_bounds {c_AN n m L L_sim h : ℕ} (hc : 1 ≤ c_AN) (hh : 1 ≤ h)
    (hsim : lsstLSimMin c_AN n m L h ≤ L_sim) :
    kWidthOf m L ≤ L_sim ∧ w'Max c_AN n m L h ≤ L_sim * h ∧
      Nat.log 2 (6 + 16 * m) + 1 ≤ L_sim * h := by
  have hk_le : kWidthOf m L ≤ L_sim := le_trans (le_max_left _ _) hsim
  have hw_le : w'Max c_AN n m L h ≤ L_sim := le_trans (le_max_right _ _) hsim
  have hw_lh : w'Max c_AN n m L h ≤ L_sim * h :=
    le_trans hw_le (Nat.le_mul_of_pos_right L_sim hh)
  have h1 : Nat.log 2 (6 + 16 * m) + 1 ≤ w'Max c_AN n m L h := by
    dsimp only [w'Max]
    have hmul : Nat.log 2 (6 + 16 * m) + kWidthOf m L * h + 3 ≤
        c_AN * (Nat.log 2 (6 + 16 * m) + kWidthOf m L * h + 3) :=
      Nat.le_mul_of_pos_left _ hc
    omega
  exact ⟨hk_le, hw_lh, le_trans h1 hw_lh⟩

private lemma foldr_max_le {xs : List ℕ} {M : ℕ} (h : ∀ v ∈ xs, v ≤ M) :
    xs.foldr max 0 ≤ M := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun v hv => h v (List.mem_cons_of_mem a hv))

lemma wordSize_one_le {c_AN : ℕ} (hc : 1 ≤ c_AN) (input : List ℕ) :
    1 ≤ WordRAM.wordSize c_AN input ∧ ∀ v ∈ input, v < 2 ^ WordRAM.wordSize c_AN input := by
  have h1 : 1 ≤ WordRAM.wordSize c_AN input := by
    dsimp only [WordRAM.wordSize]
    exact Nat.mul_pos hc (Nat.succ_pos _)
  refine ⟨h1, fun v hv => ?_⟩
  have hfold : v ≤ input.foldr max 0 := by
    clear hc h1
    induction input with
    | nil => cases hv
    | cons a t ih =>
      simp only [List.mem_cons] at hv
      simp only [List.foldr_cons]
      rcases hv with rfl | ht
      · exact le_max_left _ _
      · exact le_trans (ih ht) (le_max_right _ _)
  have hpow : input.length + input.foldr max 0 + 2 <
      2 ^ (Nat.log 2 (input.length + input.foldr max 0 + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hle_exp : Nat.log 2 (input.length + input.foldr max 0 + 2) + 1 ≤ WordRAM.wordSize c_AN input := by
    dsimp only [WordRAM.wordSize]
    exact Nat.le_mul_of_pos_left _ hc
  have hpow2 : 2 ^ (Nat.log 2 (input.length + input.foldr max 0 + 2) + 1) ≤
      2 ^ WordRAM.wordSize c_AN input :=
    Nat.pow_le_pow_right (by norm_num) hle_exp
  omega

lemma wordSize_bound_of_weights {G : IndexedGraph} {V_list B : List ℕ} {mult w_orig : ℕ → ℕ}
    {c_AN L h : ℕ} (hV_len : V_list.length ≤ 2 * (nonloopEdges G).length)
    (hB_len : B.length ≤ V_list.length)
    (hmult_sum : ((nonloopEdges G).map mult).sum ≤ 2 * (nonloopEdges G).length)
    (hw : ∀ e ∈ nonloopEdges G, w_orig e < 2 ^ (kWidthOf (nonloopEdges G).length L * h - 1)) :
    let nl := nonloopEdges G
    let m₁ := (nl.map mult).sum
    let G_aug := buildGAug G V_list B mult w_orig
    m₁ ≤ 2 * G.m ∧
      m₁ + B.length ≤ 4 * G.m ∧
      G_aug.encode.length ≤ 2 + 3 * (4 * G.m) ∧
      WordRAM.wordSize c_AN G_aug.encode ≤ w'Max c_AN G.n G.m L h := by
  intro nl m₁ G_aug
  have hnl_m : (nonloopEdges G).length ≤ G.m := nonloopEdges_length_le G
  have hm₁_sum : ((nonloopEdges G).map mult).sum = m₁ := rfl
  have hm₁_le : m₁ ≤ 2 * G.m := le_trans hmult_sum (by omega)
  have hV_2m : V_list.length ≤ 2 * G.m := le_trans hV_len (by omega)
  have hB_2m : B.length ≤ 2 * G.m := le_trans hB_len hV_2m
  have hm_aug_le : m₁ + B.length ≤ 4 * G.m := by omega
  have henc_len : G_aug.encode.length ≤ 2 + 3 * (4 * G.m) := by
    dsimp only [G_aug]
    rw [gAug_encode_length]
    omega
  refine ⟨hm₁_le, hm_aug_le, henc_len, ?_⟩
  set K := kWidthOf (nonloopEdges G).length L
  have hK_le : K ≤ kWidthOf G.m L := kWidthOf_mono hnl_m
  have hall_vals : ∀ v ∈ G_aug.encode, v ≤ 4 * G.m + 2 ^ (K * h) + 2 := by
    intro v hv
    dsimp only [G_aug, Cited.WGraph.encode, buildGAug, Cited.WGraph.m] at hv
    simp only [List.mem_cons, List.mem_flatMap, List.mem_append, List.mem_map] at hv
    rcases hv with rfl | rfl | ⟨⟨a, b, wt⟩, hmem, htri⟩
    · exact le_trans hV_2m (le_trans (by omega : 2 * G.m ≤ 4 * G.m)
        (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    · have hlen_copy : ((nonloopEdges G).flatMap fun e => List.replicate (mult e)
          (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)).length = m₁ := by
        rw [List.length_flatMap]
        have hr : List.map (fun e => (List.replicate (mult e)
            (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)).length) (nonloopEdges G) =
            (nonloopEdges G).map mult := by
          simp [List.length_replicate]
        rw [hr, hm₁_sum]
      rw [List.length_append, hlen_copy, List.length_map]
      exact le_trans (by omega : m₁ + B.length ≤ 4 * G.m)
        (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    · simp only [List.not_mem_nil, or_false] at htri
      have ha_bound : a ≤ 2 * G.m ∧ b ≤ 2 * G.m ∧ wt ≤ 2 ^ (K * h) := by
        rcases hmem with ⟨e, _, hrep⟩ | ⟨b0, hb0, hbp⟩
        · simp only [List.mem_replicate, Prod.mk.injEq] at hrep
          rcases hrep with ⟨hne, rfl, rfl, rfl⟩
          have he_nl : e ∈ nonloopEdges G := ‹_›
          have hwe := le_of_lt (hw e he_nl)
          have hpow_le : 2 ^ (K * h - 1) ≤ 2 ^ (K * h) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
          exact ⟨le_trans List.idxOf_le_length hV_2m, le_trans List.idxOf_le_length hV_2m,
            le_trans hwe hpow_le⟩
        · simp only [Prod.mk.injEq] at hbp
          rcases hbp with ⟨rfl, rfl, rfl⟩
          exact ⟨Nat.zero_le _, le_trans List.idxOf_le_length hV_2m, Nat.one_le_pow _ _ (by norm_num)⟩
      rcases htri with rfl | rfl | rfl <;> omega
  have hfold_le : G_aug.encode.foldr max 0 ≤ 4 * G.m + 2 ^ (K * h) + 2 :=
    foldr_max_le hall_vals
  set A := G_aug.encode.length + G_aug.encode.foldr max 0 + 2
  have hA_ne : A ≠ 0 := by omega
  have hA_le : A ≤ (6 + 16 * G.m) + 2 ^ (K * h) := by omega
  set p1 := Nat.log 2 (6 + 16 * G.m) + 1
  have hp1 : 6 + 16 * G.m < 2 ^ p1 :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hA_lt_pow : A < 2 ^ (max p1 (K * h) + 1) := by
    have h1 : 2 ^ p1 ≤ 2 ^ max p1 (K * h) := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : 2 ^ (K * h) ≤ 2 ^ max p1 (K * h) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    rw [Nat.pow_succ]
    omega
  have hlog_lt : Nat.log 2 A < max p1 (K * h) + 1 := Nat.log_lt_of_lt_pow hA_ne hA_lt_pow
  have hlog_le : Nat.log 2 A ≤ max p1 (K * h) := Nat.lt_succ_iff.mp hlog_lt
  dsimp only [WordRAM.wordSize, w'Max]
  refine Nat.mul_le_mul_left c_AN ?_
  have hmax : max p1 (K * h) ≤ p1 + K * h := Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  have hKh : K * h ≤ kWidthOf G.m L * h := Nat.mul_le_mul_right h hK_le
  have hstep : Nat.log 2 A + 1 ≤ Nat.log 2 (6 + 16 * G.m) + kWidthOf G.m L * h + 3 := by
    dsimp only [p1] at hlog_le hmax
    linarith only [hlog_le, hmax, hKh]
  exact hstep

theorem cited_c_pos_of_lsst :
    ∃ (P_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      1 ≤ c_AN ∧
      ∀ (G : Cited.WGraph), G.graph.IsValid → G.graph.IsLoopless → G.IsConnected →
        (∀ e ∈ G.edges, 1 ≤ e.2.2) →
        ∃ out cost,
          WordRAM.RunsTo (WordRAM.wordSize c_AN G.encode) P_AN G.encode (fun _ => false) out cost ∧
            G.IsSpanningTree out ∧
            G.totalStretch out ≤ K_AN * G.m * Cited.logLogFactor G.n ∧
            (cost : ℝ) ≤ K_AN * (G.m + 1) * (Cited.logLogFactor G.n + Cited.weightFactor G.n G.maxWeight) := by
  rcases MinCostFlow.LowStretch.lowStretchSpanningTree_lsst with ⟨P_AN, c_AN, K_AN, hspec⟩
  have hc_pos : 1 ≤ c_AN := by
    by_contra hc0
    have hc_eq : c_AN = 0 := by omega
    subst hc_eq
    let G0 : Cited.WGraph :=
      { n := 1, edges := [] }
    have hv : G0.graph.IsValid := fun _ he => by simp [G0, Cited.WGraph.graph] at he
    have hl : G0.graph.IsLoopless := fun _ he => by simp [G0, Cited.WGraph.graph] at he
    have hconn : G0.IsConnected := ⟨by decide, fun u hu v hv' => by
      simp [G0] at hu hv'
      subst hu hv'
      exact ⟨[], Cited.WGraph.IsWalkIn.nil 0⟩⟩
    obtain ⟨out, cost, ⟨fuel, hrun⟩, _⟩ := hspec G0 hv hl hconn (fun _ h => by simp [G0] at h) (fun _ => false)
    have henc : G0.encode.length = 2 := by simp [G0, Cited.WGraph.encode]
    have hw0 : WordRAM.wordSize 0 G0.encode = 0 := by simp [WordRAM.wordSize]
    rw [hw0] at hrun
    simp only [WordRAM.run] at hrun
    have hnone : WordRAM.exec 0 P_AN (fun _ => false) fuel
        (.call 0 0 [.const G0.encode.length])
        { mem := WordRAM.initMem G0.encode, regs := fun _ => 0, pos := 0 } = none := by
      cases fuel with
      | zero => simp [WordRAM.exec]
      | succ f =>
        have heval : WordRAM.evalArgs 0 { mem := WordRAM.initMem G0.encode, regs := fun _ => 0, pos := 0 }
            [.const G0.encode.length] = none := by
          simp [WordRAM.evalArgs, Expr.eval, henc]
        simp [WordRAM.exec, heval]
    rw [hnone] at hrun
    cases hrun
  exact ⟨P_AN, c_AN, K_AN, hc_pos, fun G hv hl hc he => hspec G hv hl hc he (fun _ => false)⟩

lemma anCost_le_bound {K_AN : ℝ} {n₀ n m₀ m L_sim h cost W : ℕ}
    (hn0 : 2 ≤ n₀) (hn : n₀ ≤ n) (hm : m₀ ≤ 4 * m) (hW : W ≤ 2 ^ (L_sim * h))
    (hcost : (cost : ℝ) ≤ K_AN * ((m₀ : ℝ) + 1) *
      (Cited.logLogFactor n₀ + Cited.weightFactor n₀ W)) :
    cost ≤ anCostBound K_AN n m L_sim h := by
  have h1 : 1 < Real.log ((n₀ : ℝ) + 2) := MinCostFlow.LSF.one_lt_log_add_two (by omega)
  have hlog_n0_pos : 0 < Real.log ((n₀ : ℝ) + 2) := by linarith
  have hlog_mono : Real.log ((n₀ : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n₀ + 2 ≤ n + 2))
  have hll_n0_nn : 0 ≤ Real.log (Real.log ((n₀ : ℝ) + 2)) := (Real.log_pos h1).le
  have hll_mono : Real.log (Real.log ((n₀ : ℝ) + 2)) ≤ Real.log (Real.log ((n : ℝ) + 2)) :=
    Real.log_le_log hlog_n0_pos hlog_mono
  have hlogLog_le : Cited.logLogFactor n₀ ≤ Cited.logLogFactor n := by
    dsimp only [Cited.logLogFactor]
    exact mul_le_mul hlog_mono hll_mono hll_n0_nn (by linarith)
  have hlogLog_nn : 0 ≤ Cited.logLogFactor n₀ := by
    dsimp only [Cited.logLogFactor]
    exact mul_nonneg hlog_n0_pos.le hll_n0_nn
  have hw2_ge1 : (1 : ℝ) ≤ (W : ℝ) + 2 := by exact_mod_cast (by omega : 1 ≤ W + 2)
  have hlogW_nn : 0 ≤ Real.log ((W : ℝ) + 2) := Real.log_nonneg hw2_ge1
  have hllW_nn : 0 ≤ Real.log (Real.log ((W : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
  have hlogW_mono : Real.log ((W : ℝ) + 2) ≤ Real.log (((2 ^ (L_sim * h) : ℕ) : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hW 2)
  have hllW_mono : Real.log (Real.log ((W : ℝ) + 2) + 2) ≤
      Real.log (Real.log (((2 ^ (L_sim * h) : ℕ) : ℝ) + 2) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hwf_le : Cited.weightFactor n₀ W ≤ Cited.weightFactor n (2 ^ (L_sim * h)) := by
    dsimp only [Cited.weightFactor]
    exact mul_le_mul hlog_mono hllW_mono hllW_nn (by linarith)
  have hwf_nn : 0 ≤ Cited.weightFactor n₀ W := by
    dsimp only [Cited.weightFactor]
    exact mul_nonneg hlog_n0_pos.le hllW_nn
  have hm_le : (m₀ : ℝ) + 1 ≤ ((4 * m : ℕ) : ℝ) + 1 := by
    have : (m₀ : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast hm
    linarith
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) + 1 := by positivity
  have hsum_le : Cited.logLogFactor n₀ + Cited.weightFactor n₀ W ≤
      Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)) := add_le_add hlogLog_le hwf_le
  have hsum_nn : 0 ≤ Cited.logLogFactor n₀ + Cited.weightFactor n₀ W := add_nonneg hlogLog_nn hwf_nn
  have hpart1 : K_AN * ((m₀ : ℝ) + 1) ≤ max K_AN 0 * (((4 * m : ℕ) : ℝ) + 1) := by
    rcases le_total K_AN 0 with hK0 | hK0
    · have lhs_le0 : K_AN * ((m₀ : ℝ) + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK0 hm_nn
      have rhs_ge0 : 0 ≤ max K_AN 0 * (((4 * m : ℕ) : ℝ) + 1) :=
        mul_nonneg (le_max_right _ _) (by positivity)
      linarith
    · exact mul_le_mul (le_max_left _ _) hm_le hm_nn (le_max_right _ _)
  have hreal_le : (cost : ℝ) ≤ max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
      (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) := by
    have hmul : K_AN * ((m₀ : ℝ) + 1) * (Cited.logLogFactor n₀ + Cited.weightFactor n₀ W) ≤
        max K_AN 0 * (((4 * m : ℕ) : ℝ) + 1) *
          (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) := by
      rcases le_total K_AN 0 with hK0 | hK0
      · have h1' : K_AN * ((m₀ : ℝ) + 1) * (Cited.logLogFactor n₀ + Cited.weightFactor n₀ W) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hK0 hm_nn) hsum_nn
        have h2' : 0 ≤ max K_AN 0 * (((4 * m : ℕ) : ℝ) + 1) *
            (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) :=
          mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) (le_trans hsum_nn hsum_le)
        linarith
      · exact mul_le_mul hpart1 hsum_le hsum_nn (mul_nonneg (le_max_right _ _) (by positivity))
    exact le_trans hcost hmul
  exact Nat.cast_le.mp (le_trans hreal_le (Nat.le_ceil _))

lemma weightsSpace_mono {a₁ a₂ K₁ K₂ : ℕ} (ha : a₁ ≤ a₂) (hK : K₁ ≤ K₂) :
    weightsSpace a₁ K₁ ≤ weightsSpace a₂ K₂ := by
  have hdiv : Num.integerDivideSpace (2 * K₁) ≤ Num.integerDivideSpace (2 * K₂) := by
    dsimp only [Num.integerDivideSpace, Num.unsignedDivideSpace]
    nlinarith
  dsimp only [weightsSpace]
  exact Nat.add_le_add (by omega) (Nat.mul_le_mul ha (Nat.add_le_add (by omega) (by omega)))

lemma weightsCost_mono {a₁ a₂ L : ℕ} (ha : a₁ ≤ a₂) :
    weightsCost a₁ L ≤ weightsCost a₂ L := by
  have hk : kWidthOf a₁ L ≤ kWidthOf a₂ L := kWidthOf_mono ha
  have hstep : weightStepCost (kWidthOf a₁ L) ≤ weightStepCost (kWidthOf a₂ L) := by
    dsimp only [weightStepCost]
    nlinarith
  dsimp only [weightsCost]
  nlinarith

lemma decodeOutCost_mono {o₁ o₂ i₁ i₂ L_sim : ℕ} (ho : o₁ ≤ o₂) (hi : i₁ ≤ i₂) :
    decodeOutCost o₁ i₁ L_sim ≤ decodeOutCost o₂ i₂ L_sim := by
  dsimp only [decodeOutCost]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ ho) (Nat.mul_le_mul_left 45 hi)) le_rfl

lemma simDecodeSpace_mono {Q : Program} {v₁ v₂ m₁ m₂ L_sim h c₁ c₂ : ℕ}
    (hv : v₁ ≤ v₂) (hm : m₁ ≤ m₂) (hc : c₁ ≤ c₂) :
    simDecodeSpace Q v₁ m₁ L_sim h c₁ ≤ simDecodeSpace Q v₂ m₂ L_sim h c₂ := by
  dsimp only [simDecodeSpace]
  have h1 : (1 + v₁) * L_sim ≤ (1 + v₂) * L_sim := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 + 3 * m₁) * (L_sim * 2 ^ h + L_sim) ≤ (2 + 3 * m₂) * (L_sim * 2 ^ h + L_sim) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : simScale Q * L_sim * 2 ^ h * (c₁ + (2 + 3 * m₁) + 1) ≤
      simScale Q * L_sim * 2 ^ h * (c₂ + (2 + 3 * m₂) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

lemma simDecodeCost_mono {Q : Program} {w'₁ w'₂ v₁ v₂ m₁ m₂ i₁ i₂ L_sim c₁ c₂ : ℕ}
    (hw' : w'₁ ≤ w'₂) (hv : v₁ ≤ v₂) (hm : m₁ ≤ m₂) (hi : i₁ ≤ i₂) (hc : c₁ ≤ c₂) :
    simDecodeCost Q w'₁ v₁ m₁ i₁ L_sim c₁ ≤ simDecodeCost Q w'₂ v₂ m₂ i₂ L_sim c₂ := by
  dsimp only [simDecodeCost]
  have h1 : (95 * L_sim + 115) * (2 + 3 * m₁) ≤ (95 * L_sim + 115) * (2 + 3 * m₂) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : simScale Q * L_sim * w'₁ * (c₁ + (2 + 3 * m₁) + 1) ≤
      simScale Q * L_sim * w'₂ * (c₂ + (2 + 3 * m₂) + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hw') (by omega)
  have h3 : (70 * L_sim + 80) * (v₁ - 1) ≤ (70 * L_sim + 80) * (v₂ - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : decodeOutCost (v₁ - 1) i₁ L_sim ≤ decodeOutCost (v₂ - 1) i₂ L_sim :=
    decodeOutCost_mono (by omega) hi
  omega

/-- Overhead factor multiplying `16000 * (m + n + 1)` in the linear-time bound for Theorem 2.2:
collects `L_sim`, `w'`, `simScale Q_AN`, `Cited.logLogFactor`, and `Cited.weightFactor`. -/
noncomputable def lsstOverheadFactor (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (n m L : ℕ) : ℝ :=
  let L_sim := lsstLSimMin c_AN n m L 1
  let W' := w'Max c_AN n m L 1
  (L_sim : ℝ) ^ 2 +
    (simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ) *
      (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) + 1)

private lemma lsstCost_base_nat_le (m n L K L_sim : ℕ)
    (h1K : 1 ≤ K) (hLK : L ≤ K) (hK : K ≤ L_sim) :
    scanNonloopsCost m + starPairsCost n + buildCSRCost n m +
      buildVertIdxCost n + bfsBridgesCost n m +
      ((m + 1) * (weightStepCost K + 140 * K + 600) + m * (42 * L + 200) + 300) +
      (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
      ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
        decodeOutCost (2 * m - 1) n L_sim + 200) + 500 ≤
      16000 * ((m + n + 1) * (L_sim * L_sim)) := by
  set M := m + n + 1
  set L2 := L_sim * L_sim
  set Z := M * L2
  have h1L : 1 ≤ L_sim := le_trans h1K hK
  have h1L2 : 1 ≤ L2 := Nat.mul_pos h1L h1L
  have hL_L2 : L_sim ≤ L2 := Nat.le_mul_of_pos_right L_sim h1L
  have hK_L2 : K ≤ L2 := le_trans hK hL_L2
  have hK2_L2 : K * K ≤ L2 := Nat.mul_le_mul hK hK
  have hL0_L2 : L ≤ L2 := le_trans (le_trans hLK hK) hL_L2
  have h1M : 1 ≤ M := by omega
  have h1Z : 1 ≤ Z := Nat.mul_pos h1M h1L2
  have mulML {a b c d : ℕ} (ha : a ≤ c * M) (hb : b ≤ d * L2) : a * b ≤ (c * d) * Z := by
    calc a * b ≤ (c * M) * (d * L2) := Nat.mul_le_mul ha hb
      _ = (c * d) * Z := by dsimp only [Z]; ring
  have hpre :
      scanNonloopsCost m + starPairsCost n + buildCSRCost n m +
        buildVertIdxCost n + bfsBridgesCost n m ≤ 580 * Z := by
    have hlin :
        scanNonloopsCost m + starPairsCost n + buildCSRCost n m +
          buildVertIdxCost n + bfsBridgesCost n m ≤ 580 * M := by
      dsimp only [scanNonloopsCost, starPairsCost, buildCSRCost, buildVertIdxCost, bfsBridgesCost, M]
      omega
    calc _ ≤ 580 * M := hlin
      _ = 580 * M * 1 := (Nat.mul_one _).symm
      _ ≤ 580 * M * L2 := Nat.mul_le_mul_left _ h1L2
      _ = 580 * Z := by dsimp only [Z]; ring
  have hwt1 : (m + 1) * (weightStepCost K + 140 * K + 600) ≤ 9540 * Z := by
    have hp : weightStepCost K + 140 * K + 600 ≤ 9540 * L2 := by
      dsimp only [weightStepCost]
      calc 2800 * K * K + 4200 * K + 1800 + 140 * K + 600
          = 2800 * (K * K) + 4340 * K + 2400 := by ring
        _ ≤ 2800 * L2 + 4340 * L2 + 2400 * L2 :=
            Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hK2_L2)
              (Nat.mul_le_mul_left _ hK_L2)) (Nat.le_mul_of_pos_right 2400 h1L2)
        _ = 9540 * L2 := by ring
    simpa using mulML (c := 1) (d := 9540) (by omega) hp
  have hwt2 : m * (42 * L + 200) ≤ 242 * Z := by
    have hp : 42 * L + 200 ≤ 242 * L2 :=
      calc 42 * L + 200 ≤ 42 * L2 + 200 * L2 :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hL0_L2) (Nat.le_mul_of_pos_right 200 h1L2)
        _ = 242 * L2 := by ring
    simpa using mulML (c := 1) (d := 242) (by omega) hp
  have h4mL : (4 * m) * (70 * L_sim + 110) ≤ 720 * Z := by
    have hp : 70 * L_sim + 110 ≤ 180 * L2 :=
      calc 70 * L_sim + 110 ≤ 70 * L2 + 110 * L2 :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hL_L2) (Nat.le_mul_of_pos_right 110 h1L2)
        _ = 180 * L2 := by ring
    exact mulML (c := 4) (d := 180) (by omega) hp
  have henc : (95 * L_sim + 115) * (2 + 3 * (4 * m)) ≤ 2520 * Z := by
    rw [Nat.mul_comm]
    have hp : 95 * L_sim + 115 ≤ 210 * L2 :=
      calc 95 * L_sim + 115 ≤ 95 * L2 + 115 * L2 :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hL_L2) (Nat.le_mul_of_pos_right 115 h1L2)
        _ = 210 * L2 := by ring
    exact mulML (c := 12) (d := 210) (by omega) hp
  have h70m : (70 * L_sim + 80) * (2 * m - 1) ≤ 300 * Z := by
    rw [Nat.mul_comm]
    have hp : 70 * L_sim + 80 ≤ 150 * L2 :=
      calc 70 * L_sim + 80 ≤ 70 * L2 + 80 * L2 :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hL_L2) (Nat.le_mul_of_pos_right 80 h1L2)
        _ = 150 * L2 := by ring
    exact mulML (c := 2) (d := 150) (by omega) hp
  have hdec : decodeOutCost (2 * m - 1) n L_sim ≤ 315 * Z := by
    dsimp only [decodeOutCost]
    have hda : (2 * m - 1) * (25 * L_sim + 80) ≤ 210 * Z := by
      have hp : 25 * L_sim + 80 ≤ 105 * L2 :=
        calc 25 * L_sim + 80 ≤ 25 * L2 + 80 * L2 :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hL_L2) (Nat.le_mul_of_pos_right 80 h1L2)
          _ = 105 * L2 := by ring
      exact mulML (c := 2) (d := 105) (by omega) hp
    have hdb : 45 * n ≤ 45 * Z := by
      have := mulML (a := n) (b := 1) (c := 1) (d := 1) (by omega) (by simpa using h1L2)
      linarith only [this]
    have hdc : 60 ≤ 60 * Z := Nat.le_mul_of_pos_right 60 h1Z
    omega
  have hmZ : 110 * m ≤ 110 * Z := by
    have := mulML (a := m) (b := 1) (c := 1) (d := 1) (by omega) (by simpa using h1L2)
    linarith only [this]
  have hLZ : 50 * L_sim ≤ 50 * Z := by
    have := mulML (a := 1) (b := L_sim) (c := 1) (d := 1) (by simpa using h1M) (by simpa using hL_L2)
    linarith only [this]
  have h300 : 300 ≤ 300 * Z := Nat.le_mul_of_pos_right 300 h1Z
  have h120 : 120 ≤ 120 * Z := Nat.le_mul_of_pos_right 120 h1Z
  have h200 : 200 ≤ 200 * Z := Nat.le_mul_of_pos_right 200 h1Z
  have h500 : 500 ≤ 500 * Z := Nat.le_mul_of_pos_right 500 h1Z
  omega

/-- Total step count `lsstCost` at `h = 1` is at most `16000 * (m + n + 1) * F(n, m, L)`. -/
theorem lsstCost_le_linear_factor (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    {n m L : ℕ} (hn : 1 ≤ n) :
    (lsstCost Q_AN K_AN c_AN n m L (lsstLSimMin c_AN n m L 1) 1 : ℝ) ≤
      16000 * ((m + n + 1 : ℕ) : ℝ) * lsstOverheadFactor Q_AN c_AN K_AN n m L := by
  set L_sim := lsstLSimMin c_AN n m L 1
  set W' := w'Max c_AN n m L 1
  set C_an := anCostBound K_AN n m L_sim 1
  set M := m + n + 1
  have hK_le : kWidthOf m L ≤ L_sim := le_max_left _ _
  have h1K : 1 ≤ kWidthOf m L := by dsimp only [kWidthOf]; omega
  have hLK : L ≤ kWidthOf m L := by dsimp only [kWidthOf]; omega
  have hbase_nat := lsstCost_base_nat_le m n L (kWidthOf m L) L_sim h1K hLK hK_le
  have hbase_real :
      ((scanNonloopsCost m + starPairsCost n + buildCSRCost n m +
        buildVertIdxCost n + bfsBridgesCost n m + weightsCost m L +
        (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
        ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
          decodeOutCost (2 * m - 1) n L_sim + 200) + 500 : ℕ) : ℝ) ≤
        16000 * (M : ℝ) * (L_sim : ℝ) ^ 2 := by
    have hnat' :
        scanNonloopsCost m + starPairsCost n + buildCSRCost n m +
          buildVertIdxCost n + bfsBridgesCost n m + weightsCost m L +
          (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
          ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
            decodeOutCost (2 * m - 1) n L_sim + 200) + 500 ≤
          16000 * ((m + n + 1) * (L_sim * L_sim)) := by
      simpa only [weightsCost] using hbase_nat
    have hreal := (Nat.cast_le (α := ℝ)).mpr hnat'
    push_cast [sq] at hreal ⊢
    have hassoc :
        (16000 : ℝ) * ((↑m + ↑n + 1) * (↑L_sim * ↑L_sim)) =
          16000 * (M : ℝ) * (↑L_sim * ↑L_sim) := by
      dsimp only [M]; push_cast; ring
    linarith only [hreal, hassoc]
  have hlog_n : 1 < Real.log ((n : ℝ) + 2) := by
    have h16 : (5 / 6 : ℝ) ≤ Real.exp (-(1 / 6 : ℝ)) := by
      linarith only [Real.add_one_le_exp (-(1 / 6 : ℝ))]
    have hexp16 : Real.exp (1 / 6 : ℝ) ≤ 6 / 5 := by
      have hinv : Real.exp (1 / 6 : ℝ) = (Real.exp (-(1 / 6 : ℝ)))⁻¹ := by
        rw [← Real.exp_neg, neg_neg]
      rw [hinv]
      calc (Real.exp (-(1 / 6 : ℝ)))⁻¹ ≤ (5 / 6 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h16
        _ = 6 / 5 := by norm_num
    have hexp1 : Real.exp 1 < 3 := by
      have hpow : (Real.exp (1 / 6 : ℝ)) ^ 6 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hpow_le : Real.exp 1 ≤ (6 / 5 : ℝ) ^ 6 := by
        rw [← hpow]
        exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hexp16 6
      linarith only [hpow_le]
    have hexp : Real.exp 1 < (n : ℝ) + 2 := by
      have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith only [hexp1, h1n]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log ((n : ℝ) + 2) := Real.log_lt_log (Real.exp_pos 1) hexp
  have hloglog_nn : 0 ≤ Cited.logLogFactor n := by
    dsimp only [Cited.logLogFactor]
    exact mul_nonneg (by linarith only [hlog_n]) (Real.log_nonneg (by linarith only [hlog_n]))
  have hwt_nn : 0 ≤ Cited.weightFactor n (2 ^ L_sim) := by
    dsimp only [Cited.weightFactor]
    have h1 : (1 : ℝ) ≤ ((2 ^ L_sim : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow L_sim 2 (by decide)
    have hlogW : 0 ≤ Real.log (((2 ^ L_sim : ℕ) : ℝ) + 2) := Real.log_nonneg (by linarith only [h1])
    exact mul_nonneg (by linarith only [hlog_n]) (Real.log_nonneg (by linarith only [hlogW]))
  have hF_nn : 0 ≤ Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim) :=
    add_nonneg hloglog_nn hwt_nn
  have hC_an :
      (C_an : ℝ) <
        max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
          (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) + 1 := by
    dsimp only [C_an, anCostBound]
    rw [Nat.mul_one]
    exact Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) hF_nn)
  have hCan_lin :
      ((C_an + (2 + 3 * (4 * m)) + 1 : ℕ) : ℝ) ≤
        16 * (M : ℝ) *
          (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) + 1) := by
    have hKmax : max K_AN 0 ≤ max K_AN 1 := max_le_max_left K_AN (by norm_num)
    have hm4 : ((4 * m : ℕ) + 1 : ℝ) ≤ 4 * (M : ℝ) := by
      have : 4 * m + 1 ≤ 4 * M := by omega
      exact_mod_cast this
    have hprod :
        max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
          (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) ≤
          4 * (M : ℝ) *
            (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim))) := by
      calc max K_AN 0 * ((4 * m : ℕ) + 1 : ℝ) *
              (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim))
          ≤ max K_AN 1 * (4 * (M : ℝ)) *
              (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hKmax hm4 (by positivity) (le_trans (by norm_num) (le_max_right K_AN 1)))
              hF_nn
        _ = 4 * (M : ℝ) *
              (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim))) := by ring
    have hm16 : 12 * (m : ℝ) + 4 ≤ 16 * (M : ℝ) := by
      have : 12 * m + 4 ≤ 16 * M := by omega
      exact_mod_cast this
    have h4_le16 :
        4 * (M : ℝ) * (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim))) ≤
          16 * (M : ℝ) * (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim))) := by
      have h1 : 0 ≤ (M : ℝ) := by positivity
      have h2 : 0 ≤ max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) :=
        mul_nonneg (le_trans (by norm_num) (le_max_right K_AN 1)) hF_nn
      have : 4 * (M : ℝ) ≤ 16 * (M : ℝ) := by linarith only [h1]
      exact mul_le_mul_of_nonneg_right this h2
    have hsum :
        ((C_an + (2 + 3 * (4 * m)) + 1 : ℕ) : ℝ) ≤
          4 * (M : ℝ) * (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim))) +
            16 * (M : ℝ) := by
      push_cast at hm4 ⊢
      linarith only [hC_an, hprod, hm16]
    linarith only [hsum, h4_le16]
  have hsim_real :
      ((simScale Q_AN * L_sim * W' * (C_an + (2 + 3 * (4 * m)) + 1) : ℕ) : ℝ) ≤
        16000 * (M : ℝ) *
          ((simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ) *
            (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) + 1)) := by
    set S := (simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ)
    set T := max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) + 1
    have hs_nn : 0 ≤ S := by positivity
    have hT_nn : 0 ≤ T := add_nonneg (mul_nonneg (le_trans (by norm_num) (le_max_right K_AN 1)) hF_nn) (by norm_num)
    have hM_nn : 0 ≤ (M : ℝ) := by positivity
    calc ((simScale Q_AN * L_sim * W' * (C_an + (2 + 3 * (4 * m)) + 1) : ℕ) : ℝ)
        = S * ((C_an + (2 + 3 * (4 * m)) + 1 : ℕ) : ℝ) := by dsimp only [S]; push_cast; ring
      _ ≤ S * (16 * (M : ℝ) * T) := mul_le_mul_of_nonneg_left hCan_lin hs_nn
      _ = 16 * (M : ℝ) * (S * T) := by ring
      _ ≤ 16000 * (M : ℝ) * (S * T) :=
          mul_le_mul_of_nonneg_right (by linarith only [hM_nn]) (mul_nonneg hs_nn hT_nn)
  have hsplit :
      (lsstCost Q_AN K_AN c_AN n m L L_sim 1 : ℝ) =
        ((scanNonloopsCost m + starPairsCost n + buildCSRCost n m +
          buildVertIdxCost n + bfsBridgesCost n m + weightsCost m L +
          (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
          ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
            decodeOutCost (2 * m - 1) n L_sim + 200) + 500 : ℕ) : ℝ) +
          ((simScale Q_AN * L_sim * W' * (C_an + (2 + 3 * (4 * m)) + 1) : ℕ) : ℝ) := by
    have hnat_eq :
        lsstCost Q_AN K_AN c_AN n m L L_sim 1 =
          (scanNonloopsCost m + starPairsCost n + buildCSRCost n m +
            buildVertIdxCost n + bfsBridgesCost n m + weightsCost m L +
            (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
            ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
              decodeOutCost (2 * m - 1) n L_sim + 200) + 500) +
            simScale Q_AN * L_sim * W' * (C_an + (2 + 3 * (4 * m)) + 1) := by
      dsimp only [lsstCost, simDecodeCost]
      ring
    exact_mod_cast hnat_eq
  dsimp only [lsstOverheadFactor]
  rw [hsplit]
  have heq_rhs :
      16000 * (M : ℝ) *
          ((L_sim : ℝ) ^ 2 +
            (simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ) *
              (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) + 1)) =
        16000 * (M : ℝ) * (L_sim : ℝ) ^ 2 +
          16000 * (M : ℝ) *
            ((simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ) *
              (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) + 1)) := by
    ring
  change (scanNonloopsCost m + starPairsCost n + buildCSRCost n m +
        buildVertIdxCost n + bfsBridgesCost n m + weightsCost m L +
        (110 * m + (4 * m) * (70 * L_sim + 110) + 50 * L_sim + 120) +
        ((95 * L_sim + 115) * (2 + 3 * (4 * m)) + (70 * L_sim + 80) * (2 * m - 1) +
          decodeOutCost (2 * m - 1) n L_sim + 200) + 500 : ℕ) +
      ((simScale Q_AN * L_sim * W' * (C_an + (2 + 3 * (4 * m)) + 1) : ℕ) : ℝ) ≤
    16000 * (M : ℝ) *
      ((L_sim : ℝ) ^ 2 +
        (simScale Q_AN : ℝ) * (L_sim : ℝ) * (W' : ℝ) *
          (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ L_sim)) + 1))
  linarith only [hbase_real, hsim_real, heq_rhs]

/-! ### Top-level contract `lsstContract` -/

noncomputable def lsstContract (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (w h : ℕ) : Contract where
  pre args mem :=
    ∃ (G : IndexedGraph) (v ℓ : ℕ → ℝ) (P_fp : ℕ)
      (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ),
      args = [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
        outOrigPtr, outBridgePtr, outHdrPtr, heap] ∧
      1 ≤ c_AN ∧ G.Valid ∧ 1 ≤ h ∧ 3 * h + 2 ≤ w ∧ 1 ≤ L ∧
      lsstLSimMin c_AN G.n G.m L h ≤ L_sim ∧
      tailArr + G.m ≤ heap ∧ headArr + G.m ≤ heap ∧
      lenArr + G.m * L ≤ heap ∧ wtArr + G.m * L ≤ heap ∧
      outOrigPtr + G.n ≤ heap ∧ outBridgePtr + 2 * G.n ≤ heap ∧ outHdrPtr + 2 ≤ heap ∧
      DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n) ∧
      DisjointRanges outOrigPtr G.n outHdrPtr 2 ∧
      DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2 ∧
      ListAt mem tailArr (List.ofFn fun i : Fin G.m => G.tail i) ∧
      ListAt mem headArr (List.ofFn fun i : Fin G.m => G.head i) ∧
      (∀ e < G.m, Num.Valid mem (lenArr + e * L) h L ∧
        Num.fixVal mem (lenArr + e * L) h L P_fp = ℓ e ∧ 0 < ℓ e) ∧
      (∀ e < G.m, Num.Valid mem (wtArr + e * L) h L ∧
        Num.fixVal mem (wtArr + e * L) h L P_fp = v e ∧ 0 < v e) ∧
      ZeroFrom mem heap ∧
      heap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w
  post args mem ret mem' :=
    ∃ (G : IndexedGraph) (v ℓ : ℕ → ℝ) (_P_fp : ℕ)
      (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
      (origEdges : List ℕ) (bridgePairs : List (ℕ × ℕ)),
      args = [G.n, G.m, tailArr, headArr, lenArr, wtArr, L, L_sim,
        outOrigPtr, outBridgePtr, outHdrPtr, heap] ∧
      ret = 0 ∧
      mem' outHdrPtr = origEdges.length ∧
      mem' (outHdrPtr + 1) = bridgePairs.length ∧
      origEdges.length ≤ G.n ∧
      bridgePairs.length ≤ G.n ∧
      ListAt mem' outOrigPtr origEdges ∧
      ListAt mem' outBridgePtr (bridgePairs.flatMap fun p => [p.1, p.2]) ∧
      MinCostFlow.LSF.IsLSST G.toMGraph ℓ v
        ((4 * max K_AN 1 + 5) * Real.log (↑G.n + 2) ^ 2)
        (decodedTree G.n G.m G.tail G.head origEdges bridgePairs) ∧
      (∀ a < heap,
        (a < outOrigPtr ∨ outOrigPtr + G.n ≤ a) →
        (a < outBridgePtr ∨ outBridgePtr + 2 * G.n ≤ a) →
        (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → mem' a = mem a) ∧
      ZeroFrom mem' (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h)
  cost args _ :=
    lsstCost Q_AN K_AN c_AN (args.getD 0 0) (args.getD 1 0) (args.getD 6 0) (args.getD 7 0) h

end MinCostFlow.WideWord
