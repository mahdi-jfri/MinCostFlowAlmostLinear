module

public import MinCostFlow.Machine.WideWord.LSSTProgramBase
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Verification Stages of the Theorem 2.2 WordRAM Program

This file provides reusable helpers and the first two stages of verifying `lsstModule`:
- `runs_seq_call_runs_step`: sequential composition of a direct `Runs ... (.returned _)` call
  proof with a continuation.
- `lsst_procs_weights`, `lsst_procs_encodeGAug`, `lsst_procs_simDecode`: procedure table lookups
  within `lsstModule Q_AN b h`.
- `LSSTInRegs`, `lsstInRegs_upd`, `lsstInRegs_of_eq`: preservation of caller registers `0..11`.
- `lsst_star_runs`: verification of the self-loop star branch `(nonloopEdges G).length = 0`.
- `lsst_graph_stage_runs`: verification of CSR construction, vertex-index map, and bridge BFS.
- `disjointRanges_mono`: monotonicity helper for `DisjointRanges`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Direct-run call sequencing and module lookups -/

lemma runs_seq_call_runs_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f cBound : ℕ}
    {argsE : List Expr} {body s₂ : Stmt} {st : State} {vs : List ℕ} {vret : ℕ}
    {st1 : State} {c1 k T : ℕ} {Q : Outcome → State → Prop}
    (hproc : p.procs[f]? = some body)
    (heval : evalArgs w st argsE = some vs)
    (hrun1 : Runs w p ω body (startState vs st.mem st.pos) (.returned vret) st1 c1)
    (hc1 : c1 ≤ cBound)
    (hnext : ∀ st' : State, st'.mem = st1.mem → st'.regs = Function.update st.regs r vret →
      ∃ o st'' c, Runs w p ω s₂ st' o st'' c ∧ Q o st'' ∧ (k + (argsSize argsE + cBound + 2)) + c ≤ T) :
    ∃ o st'' c, Runs w p ω (.call r f argsE ;; s₂) st o st'' c ∧ Q o st'' ∧ k + c ≤ T := by
  let st_after : State := { st1 with regs := Function.update st.regs r vret }
  have hcall : Runs w p ω (.call r f argsE) st .normal st_after (argsSize argsE + c1 + 1) :=
    runs_call_iff.mpr ⟨vs, body, .returned vret, st1, c1, heval, hproc, hrun1, rfl, rfl, rfl⟩
  obtain ⟨o, st'', c2, hrun2, hq, hle⟩ := hnext st_after rfl rfl
  refine ⟨o, st'', (argsSize argsE + c1 + 1) + c2 + 1,
    runs_seq_iff.mpr (Or.inr ⟨st_after, argsSize argsE + c1 + 1, c2, hcall, hrun2, rfl⟩), hq, ?_⟩
  omega

lemma lsst_procs_weights {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.procs[lsstWeightsBase b + idxWeightsEntry]? = some (weightsProc (lsstWeightsBase b)) := by
  have hw := lsst_hasAt_weights hp
  have := hw 0 (by rw [weightsModule_length]; omega)
  simpa [weightsModule, idxWeightsEntry] using this

lemma lsst_procs_encodeGAug {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.procs[lsstEncodeBase b + idxEncodeGAug]? =
      some (encodeGAugProc (lsstSimBase b + 1) (lsstEncodeBase b)) := by
  have he := lsst_hasAt_encode hp
  have := he 2 (by rw [encodeDecodeModule_length]; omega)
  simpa [encodeDecodeModule, idxEncodeGAug] using this

lemma lsst_procs_simDecode {p Q_AN : Program} {b h : ℕ} (hp : p.HasAt b (lsstModule Q_AN b h)) :
    p.procs[lsstEncodeBase b + idxSimDecode]? =
      some (simDecodeProc (lsstWrapBase b) (lsstSimBase b) (lsstEncodeBase b)) := by
  have he := lsst_hasAt_encode hp
  have := he 4 (by rw [encodeDecodeModule_length]; omega)
  simpa [encodeDecodeModule, idxSimDecode] using this

lemma disjointRanges_mono {a₁ s₁ a₂ s₂ s₁' s₂' : ℕ}
    (hd : DisjointRanges a₁ s₁ a₂ s₂) (hs1 : s₁' ≤ s₁) (hs2 : s₂' ≤ s₂) :
    DisjointRanges a₁ s₁' a₂ s₂' := by
  rcases hd with h1 | h1
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-! ### Caller-register preservation bundle (`regs 0..11`) -/

structure LSSTInRegs (s : State) (n m tailArr headArr lenArr wtArr L L_sim
    outOrigPtr outBridgePtr outHdrPtr heap : ℕ) : Prop where
  r0 : s.regs 0 = n
  r1 : s.regs 1 = m
  r2 : s.regs 2 = tailArr
  r3 : s.regs 3 = headArr
  r4 : s.regs 4 = lenArr
  r5 : s.regs 5 = wtArr
  r6 : s.regs 6 = L
  r7 : s.regs 7 = L_sim
  r8 : s.regs 8 = outOrigPtr
  r9 : s.regs 9 = outBridgePtr
  r10 : s.regs 10 = outHdrPtr
  r11 : s.regs 11 = heap

lemma lsstInRegs_upd {s st' : State} {n m tailArr headArr lenArr wtArr L L_sim
    outOrigPtr outBridgePtr outHdrPtr heap r v : ℕ}
    (hrg : LSSTInRegs s n m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap)
    (hreg : st'.regs = Function.update s.regs r v) (hr : 20 ≤ r) :
    LSSTInRegs st' n m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap :=
  ⟨by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r0,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r1,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r2,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r3,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r4,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r5,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r6,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r7,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r8,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r9,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r10,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r11⟩

lemma lsstInRegs_of_eq {s st' : State} {n m tailArr headArr lenArr wtArr L L_sim
    outOrigPtr outBridgePtr outHdrPtr heap : ℕ}
    (hrg : LSSTInRegs s n m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap)
    (hreg : st'.regs = s.regs) :
    LSSTInRegs st' n m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap :=
  ⟨by rw [hreg]; exact hrg.r0, by rw [hreg]; exact hrg.r1, by rw [hreg]; exact hrg.r2,
   by rw [hreg]; exact hrg.r3, by rw [hreg]; exact hrg.r4, by rw [hreg]; exact hrg.r5,
   by rw [hreg]; exact hrg.r6, by rw [hreg]; exact hrg.r7, by rw [hreg]; exact hrg.r8,
   by rw [hreg]; exact hrg.r9, by rw [hreg]; exact hrg.r10, by rw [hreg]; exact hrg.r11⟩

/-! ### Non-existential postcondition bundle and Star branch (`nl.length = 0`) -/

def LSSTPost (K_AN : ℝ) (G : IndexedGraph) (v ℓ : ℕ → ℝ)
    (outOrigPtr outBridgePtr outHdrPtr heap : ℕ) (mem_orig : ℕ → ℕ)
    (o : Outcome) (mem' : ℕ → ℕ) : Prop :=
  ∃ (origEdges : List ℕ) (bridgePairs : List (ℕ × ℕ)),
    o = .returned 0 ∧
    mem' outHdrPtr = origEdges.length ∧
    mem' (outHdrPtr + 1) = bridgePairs.length ∧
    origEdges.length ≤ G.n ∧
    bridgePairs.length ≤ G.n ∧
    (∀ e ∈ origEdges, e < G.m) ∧
    origEdges.length + bridgePairs.length ≤ G.n - 1 ∧
    ListAt mem' outOrigPtr origEdges ∧
    ListAt mem' outBridgePtr (bridgePairs.flatMap fun p => [p.1, p.2]) ∧
    MinCostFlow.LSF.IsLSST G.toMGraph ℓ v
      ((4 * max K_AN 1 + 5) * Real.log (↑G.n + 2) ^ 2)
      (decodedTree G.n G.m G.tail G.head origEdges bridgePairs) ∧
    (∀ a < heap,
      (a < outOrigPtr ∨ outOrigPtr + G.n ≤ a) →
      (a < outBridgePtr ∨ outBridgePtr + 2 * G.n ≤ a) →
      (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → mem' a = mem_orig a)

lemma lsst_star_runs_ret {w b : ℕ} {P : Program} {ω : ℕ → Bool}
    {mem_orig : ℕ → ℕ} {st : State} {k T : ℕ}
    (K_AN : ℝ)
    (hGraph : P.HasAt (lsstGraphBase b) (graphModule (lsstGraphBase b)))
    (G : IndexedGraph) (v ℓ : ℕ → ℝ)
    (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
    (hG : G.Valid) (hw5 : 5 ≤ w)
    (_hoo_le : outOrigPtr + G.n ≤ heap) (hob_le : outBridgePtr + 2 * G.n ≤ heap)
    (hoh_le : outHdrPtr + 2 ≤ heap)
    (hd_ob : DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n))
    (_hd_oh : DisjointRanges outOrigPtr G.n outHdrPtr 2)
    (hd_bh : DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2)
    (hv_pos : ∀ e < G.m, 0 < v e)
    (hheap_w : heap + G.m < 2 ^ w)
    (hrg : LSSTInRegs st G.n G.m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap)
    (hfr_scan : ∀ a < heap, st.mem a = mem_orig a)
    (hnl0 : (nonloopEdges G).length = 0)
    (retE : Expr) (retVal : ℕ)
    (hret_ev : ∀ s : State, s.regs 11 = heap → s.regs 1 = G.m → Expr.eval w s retE = some retVal)
    (hret_sz : retE.size ≤ 3)
    (hk : k + (starPairsCost G.n + 30) ≤ T) :
    ∃ o st' c,
      Runs w P ω
        (.store (.reg 10) (.const 0) ;;
         .call 21 (lsstGraphBase b + idxStarPairs) [.reg 0, .reg 9] ;;
         .store (.bin .add (.reg 10) (.const 1)) (.reg 21) ;;
         .ret retE)
        st o st' c ∧
      (o = .returned retVal ∧
        LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig (.returned 0) st'.mem ∧
        ∀ a, heap ≤ a → st'.mem a = st.mem a) ∧
      k + c ≤ T := by
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h16_w : 16 ≤ 2 ^ w :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 4 ≤ w))
  have hheap_lt_w : heap < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hheap_w
  have hn_w : G.n < 2 ^ w := by
    have : G.n ≤ 2 * G.n := by omega
    have := lt_of_le_of_lt hob_le hheap_lt_w
    omega
  have hob_w : outBridgePtr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hob_le) hheap_lt_w
  have hob_pairs_w : outBridgePtr + 2 * (G.n - 1) < 2 ^ w := by
    have : 2 * (G.n - 1) ≤ 2 * G.n := by omega
    exact lt_of_le_of_lt (by omega) (lt_of_le_of_lt hob_le hheap_lt_w)
  have hoh0_w : outHdrPtr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hoh_le) hheap_lt_w
  have hoh1_w : outHdrPtr + 1 < 2 ^ w := lt_of_le_of_lt (by omega) hheap_lt_w
  have hn1_w : G.n - 1 < 2 ^ w := lt_of_le_of_lt (by omega) hn_w
  have hw0 : 0 < 2 ^ w := Nat.lt_trans Nat.zero_lt_one hw1
  have hsp_mc : MeetsContract w P (lsstGraphBase b + idxStarPairs) (starPairsContract w) :=
    starPairs_meetsContract (hasAt_csrAuxModule hGraph)
  refine runs_seq_store_step (Expr.eval_reg_of_eq hrg.r10) (Expr.eval_const hw0) rfl fun s1 hm1 hr1 _ => ?_
  have hrg1 := lsstInRegs_of_eq hrg hr1
  have hs1_hdr0 : s1.mem outHdrPtr = 0 := by rw [hm1, Function.update_self]
  have hs1_pres : ∀ a < heap, a ≠ outHdrPtr → s1.mem a = mem_orig a := fun a ha hne => by
    rw [hm1, Function.update_of_ne hne, hfr_scan a ha]
  have hpre_sp : (starPairsContract w).pre [G.n, outBridgePtr] s1.mem :=
    ⟨G.n, outBridgePtr, rfl, h16_w, hob_pairs_w⟩
  refine runs_seq_call_step hsp_mc
    (evalArgs_cons (Expr.eval_reg_of_eq hrg1.r0) (evalArgs_cons (Expr.eval_reg_of_eq hrg1.r9) (evalArgs_nil _ _)))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> assumption)
    hpre_sp rfl (rfl : _ = starPairsCost G.n) fun v_sp mem_sp s2 hp_sp hm2 hr2 => ?_
  rcases hp_sp with ⟨n_sp, outP_sp, heq_sp, hv_sp, hlist_sp, hfr_sp⟩
  simp only [List.cons.injEq, and_true] at heq_sp
  rcases heq_sp with ⟨en_sp, eo_sp⟩
  rw [← en_sp] at hv_sp hlist_sp
  rw [← en_sp, ← eo_sp] at hfr_sp
  rw [← eo_sp] at hlist_sp
  have hrg2 := lsstInRegs_upd hrg1 hr2 (by decide)
  have hs2_21 : s2.regs 21 = G.n - 1 := by rw [hr2, Function.update_self, hv_sp]
  have hs2_hdr0 : s2.mem outHdrPtr = 0 := by
    have hne : outHdrPtr < outBridgePtr ∨ outBridgePtr + 2 * (G.n - 1) ≤ outHdrPtr := by
      rcases hd_bh with h1 | h1
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    rw [hm2, hfr_sp outHdrPtr hne, hs1_hdr0]
  refine runs_seq_store_step
    (Expr.eval_add (Expr.eval_reg_of_eq hrg2.r10) (Expr.eval_const hw1) hoh1_w)
    (Expr.eval_reg_of_eq hs2_21) rfl fun s3 hm3 hr3 _ => ?_
  let pairs := List.map (fun i => (0, i + 1)) (List.range (G.n - 1))
  have hs3_hdr0 : s3.mem outHdrPtr = 0 := by
    rw [hm3, Function.update_of_ne (by omega), hs2_hdr0]
  have hs3_hdr1 : s3.mem (outHdrPtr + 1) = pairs.length := by
    rw [hm3, Function.update_self]
    simp [pairs, List.length_map, List.length_range]
  have hs3_orig : ListAt s3.mem outOrigPtr ([] : List ℕ) := fun i hi => by simp at hi
  have hs3_bridge : ListAt s3.mem outBridgePtr (pairs.flatMap fun p => [p.1, p.2]) := by
    refine hlist_sp.congr fun q hq1 hq2 => ?_
    have hflat_len : (pairs.flatMap fun p => [p.1, p.2]).length = 2 * (G.n - 1) := by
      dsimp only [pairs]
      induction (G.n - 1) with
      | zero => simp
      | succ k ih =>
        simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.length_append,
          List.length_cons, List.length_nil] at ih ⊢
        omega
    rw [hflat_len] at hq2
    have hne : q ≠ outHdrPtr + 1 := by
      rcases hd_bh with h1 | h1 <;> omega
    rw [hm3, Function.update_of_ne hne, hm2]
  have hs3_frame : ∀ a < heap,
      (a < outOrigPtr ∨ outOrigPtr + G.n ≤ a) →
      (a < outBridgePtr ∨ outBridgePtr + 2 * G.n ≤ a) →
      (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → s3.mem a = mem_orig a := by
    intro a ha hao hab hah
    have hne1 : a ≠ outHdrPtr + 1 := by rcases hah with h1 | h1 <;> omega
    have hne0 : a ≠ outHdrPtr := by rcases hah with h1 | h1 <;> omega
    have hab' : a < outBridgePtr ∨ outBridgePtr + 2 * (G.n - 1) ≤ a := by
      rcases hab with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by omega)
    rw [hm3, Function.update_of_ne hne1, hm2, hfr_sp a hab', hs1_pres a ha hne0]
  have hloop : ∀ e ∈ G.toMGraph.E, G.toMGraph.tail e = G.toMGraph.head e := by
    intro e he
    have he_m : e < G.m := Finset.mem_range.mp he
    by_contra hne
    have he_nl : e ∈ nonloopEdges G :=
      List.mem_filter.mpr ⟨List.mem_range.mpr he_m, by simp [bne]; exact hne⟩
    have hpos : 0 < (nonloopEdges G).length := List.length_pos_of_mem he_nl
    omega
  have hvis : ∀ e ∈ G.toMGraph.E, 0 < v e := fun e he => by
    have he_m : e < G.m := Finset.mem_range.mp he
    exact hv_pos e he_m
  have hlsst : MinCostFlow.LSF.IsLSST G.toMGraph ℓ v
      ((4 * max K_AN 1 + 5) * Real.log (↑G.n + 2) ^ 2)
      (decodedTree G.n G.m G.tail G.head [] pairs) :=
    lsst_star_no_nonloop hG hvis hloop (le_max_right K_AN 1)
  have hs3_ge_heap : ∀ a, heap ≤ a → s3.mem a = st.mem a := by
    intro a ha
    have hne1 : a ≠ outHdrPtr + 1 := by omega
    have hne0 : a ≠ outHdrPtr := by omega
    have hab' : a < outBridgePtr ∨ outBridgePtr + 2 * (G.n - 1) ≤ a := by
      have : outBridgePtr + 2 * (G.n - 1) ≤ heap := by
        have : 2 * (G.n - 1) ≤ 2 * G.n := by omega
        omega
      exact Or.inr (by omega)
    rw [hm3, Function.update_of_ne hne1, hm2, hfr_sp a hab', hm1, Function.update_of_ne hne0]
  have hs3_11 : s3.regs 11 = heap := by rw [hr3]; exact hrg2.r11
  have hs3_1 : s3.regs 1 = G.m := by rw [hr3]; exact hrg2.r1
  refine runs_ret_le (hret_ev s3 hs3_11 hs3_1) ?_ ?_
  · refine ⟨rfl, ⟨[], pairs, rfl, hs3_hdr0, hs3_hdr1, by simp,
      by simp [pairs], by simp, by simp [pairs],
      hs3_orig, hs3_bridge, hlsst, hs3_frame⟩, hs3_ge_heap⟩
  · dsimp only [Expr.size, argsSize] at hret_sz ⊢
    omega

lemma lsst_star_runs {w b : ℕ} {P : Program} {ω : ℕ → Bool}
    {mem_orig : ℕ → ℕ} {st : State} {k T : ℕ}
    (K_AN : ℝ)
    (hGraph : P.HasAt (lsstGraphBase b) (graphModule (lsstGraphBase b)))
    (G : IndexedGraph) (v ℓ : ℕ → ℝ)
    (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
    (hG : G.Valid) (hw5 : 5 ≤ w)
    (hoo_le : outOrigPtr + G.n ≤ heap) (hob_le : outBridgePtr + 2 * G.n ≤ heap)
    (hoh_le : outHdrPtr + 2 ≤ heap)
    (hd_ob : DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n))
    (hd_oh : DisjointRanges outOrigPtr G.n outHdrPtr 2)
    (hd_bh : DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2)
    (hv_pos : ∀ e < G.m, 0 < v e)
    (hheap_w : heap + G.m < 2 ^ w)
    (hrg : LSSTInRegs st G.n G.m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap)
    (hfr_scan : ∀ a < heap, st.mem a = mem_orig a)
    (hnl0 : (nonloopEdges G).length = 0)
    (hk : k + (starPairsCost G.n + 30) ≤ T) :
    ∃ o st' c,
      Runs w P ω
        (.store (.reg 10) (.const 0) ;;
         .call 21 (lsstGraphBase b + idxStarPairs) [.reg 0, .reg 9] ;;
         .store (.bin .add (.reg 10) (.const 1)) (.reg 21) ;;
         .ret (.const 0))
        st o st' c ∧
      (LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig o st'.mem ∧
        ∀ a, heap ≤ a → st'.mem a = st.mem a) ∧
      k + c ≤ T := by
  obtain ⟨o, st', c, hrun, ⟨rfl, hpost, hge⟩, hc⟩ :=
    lsst_star_runs_ret K_AN hGraph G v ℓ tailArr headArr lenArr wtArr L L_sim
      outOrigPtr outBridgePtr outHdrPtr heap hG hw5 hoo_le hob_le hoh_le
      hd_ob hd_oh hd_bh hv_pos hheap_w hrg hfr_scan hnl0
      (.const 0) 0 (fun _ _ _ => Expr.eval_const (Nat.two_pow_pos w)) (by decide) hk
  exact ⟨.returned 0, st', c, hrun, ⟨hpost, hge⟩, hc⟩

/-! ### General branch stage 1: CSR, vertex-index map, and bridge BFS -/

private lemma csrAdjacencySpec_congr_lt {G : IndexedGraph} {mem₁ mem₂ : ℕ → ℕ}
    {offPtr adjPtr limit : ℕ}
    (hG : G.Valid)
    (hspec : CSRAdjacencySpec G mem₁ offPtr adjPtr)
    (hoff : offPtr + G.n < limit)
    (hadj : adjPtr + 2 * (nonloopEdges G).length ≤ limit)
    (hmem : ∀ a < limit, mem₂ a = mem₁ a) :
    CSRAdjacencySpec G mem₂ offPtr adjPtr := by
  rcases hspec with ⟨h0, hmono, hlast, hfw, hbk⟩
  have hle_last : ∀ u ≤ G.n, mem₁ (offPtr + u) ≤ 2 * (nonloopEdges G).length := by
    intro u hu
    induction hm : G.n - u generalizing u with
    | zero =>
      have : u = G.n := by omega
      subst this
      exact le_of_eq hlast
    | succ d ih =>
      have hu_lt : u < G.n := by omega
      exact le_trans (hmono u hu_lt) (ih (u + 1) (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem _ (by omega)]; exact h0
  · intro u hu
    rw [hmem _ (by omega), hmem _ (by omega)]
    exact hmono u hu
  · rw [hmem _ hoff]; exact hlast
  · intro u hu p hp1 hp2
    rw [hmem _ (by omega)] at hp1
    rw [hmem _ (by omega)] at hp2
    have hp_lt : p < 2 * (nonloopEdges G).length := lt_of_lt_of_le hp2 (hle_last (u + 1) hu)
    rcases hfw u hu p hp1 hp2 with ⟨e, he, ⟨rfl, hh⟩ | ⟨rfl, ht⟩⟩
    · refine ⟨e, he, Or.inl ⟨rfl, ?_⟩⟩
      rw [hmem _ (by omega)]; exact hh
    · refine ⟨e, he, Or.inr ⟨rfl, ?_⟩⟩
      rw [hmem _ (by omega)]; exact ht
  · intro e he
    have hm_e : e < G.m := (mem_nonloopEdges_iff.mp he).1
    have ht_lt : G.tail e < G.n := (hG.2 e hm_e).1
    have hh_lt : G.head e < G.n := (hG.2 e hm_e).2
    rcases hbk e he with ⟨⟨p1, hp1a, hp1b, hpe1⟩, ⟨p2, hp2a, hp2b, hpe2⟩⟩
    refine ⟨⟨p1, ?_, ?_, ?_⟩, ⟨p2, ?_, ?_, ?_⟩⟩
    · rw [hmem _ (by omega)]; exact hp1a
    · rw [hmem _ (by omega)]; exact hp1b
    · have hp_lt : p1 < 2 * (nonloopEdges G).length := lt_of_lt_of_le hp1b (hle_last (G.tail e + 1) ht_lt)
      rw [hmem _ (by omega)]; exact hpe1
    · rw [hmem _ (by omega)]; exact hp2a
    · rw [hmem _ (by omega)]; exact hp2b
    · have hp_lt : p2 < 2 * (nonloopEdges G).length := lt_of_lt_of_le hp2b (hle_last (G.head e + 1) hh_lt)
      rw [hmem _ (by omega)]; exact hpe2

lemma lsst_graph_stage_runs {w h b : ℕ} {P Q_AN : Program} {ω : ℕ → Bool}
    {mem_orig : ℕ → ℕ} {st : State} {k T : ℕ} {Q_post : Outcome → State → Prop}
    (K_AN : ℝ)
    (hGraph : P.HasAt (lsstGraphBase b) (graphModule (lsstGraphBase b)))
    (G : IndexedGraph) (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
    (hG : G.Valid) (h1 : 1 ≤ h) (hw : 3 * h + 2 ≤ w)
    (hnl_ne : (nonloopEdges G).length ≠ 0)
    (ht_lt : tailArr + G.m ≤ heap) (hh_lt : headArr + G.m ≤ heap)
    (hheap_space : heap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w)
    (htail_at : ListAt st.mem tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhead_at : ListAt st.mem headArr (List.ofFn fun i : Fin G.m => G.head i))
    (hnl_at : ListAt st.mem heap (nonloopEdges G))
    (hz_csr : ZeroFrom st.mem (heap + G.m))
    (hpres : ∀ a < heap, st.mem a = mem_orig a)
    (hrg : LSSTInRegs st G.n G.m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap)
    (hr20 : st.regs 20 = (nonloopEdges G).length)
    (tail : Stmt := .ret (.const 0))
    (hrest : ∀ s_bfs (B : List ℕ) (newHeap vListPtr inactPtr bPtr bfsHeap : ℕ),
      let V_list := activeVertsList G
      let inact := inactiveVertsList G.n V_list
      let h3 := bfsHeap + 2 * G.n
      newHeap = heap + G.m + 3 + 5 * G.n + 2 * (nonloopEdges G).length →
      vListPtr = heap + G.m + 2 →
      inactPtr = vListPtr + G.n →
      bPtr = newHeap + G.n →
      bfsHeap = bPtr + G.n →
      B.length ≤ V_list.length →
      LSSTInRegs s_bfs G.n G.m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap →
      s_bfs.regs 20 = (nonloopEdges G).length →
      s_bfs.regs 22 = newHeap →
      s_bfs.regs 23 = V_list.length →
      s_bfs.regs 24 = inact.length →
      s_bfs.regs 26 = inactPtr →
      s_bfs.regs 29 = V_list.headD 0 →
      s_bfs.regs 30 = bPtr →
      s_bfs.regs 31 = bfsHeap →
      s_bfs.regs 32 = B.length →
      ListAt s_bfs.mem heap (nonloopEdges G) →
      ListAt s_bfs.mem inactPtr inact →
      ListAt s_bfs.mem bPtr B →
      (∀ u ∈ V_list, s_bfs.mem (newHeap + u) = V_list.idxOf u) →
      (∀ v' : ℕ → ℝ, (∀ e < G.m, 0 < v' e) →
        IsBridgeVerts
          (MinCostFlow.LSF.weightedCopyGraph
            { G.toMGraph with E := (nonloopEdges G).toFinset } v')
          V_list.toFinset (V_list.headD 0) B) →
      ZeroFrom s_bfs.mem h3 →
      (∀ a < heap, s_bfs.mem a = mem_orig a) →
      ∃ o st' c,
        Runs w P ω
          (.assign 33 (.bin .add (.reg 31) (.bin .mul (.const 2) (.reg 0))) ;;
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
           tail)
          s_bfs o st' c ∧ Q_post o st' ∧
          (k + (buildCSRCost G.n (nonloopEdges G).length + buildVertIdxCost G.n +
            bfsBridgesCost G.n (nonloopEdges G).length + 80)) + c ≤ T) :
    ∃ o st' c,
      Runs w P ω
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
         tail)
        st o st' c ∧ Q_post o st' ∧ k + c ≤ T := by
  have hw5 : 5 ≤ w := by omega
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h2_w : 2 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ w))
  have h16_w : 16 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 4 ≤ w))
  set nl := nonloopEdges G
  set V_list := activeVertsList G
  set inact := inactiveVertsList G.n V_list
  set csrHeap := heap + G.m
  set newHeap := csrHeap + 3 + 5 * G.n + 2 * nl.length
  set vListPtr := csrHeap + 2
  set inactPtr := vListPtr + G.n
  set offPtr := inactPtr + G.n
  set adjPtr := offPtr + (G.n + 1)
  set bPtr := newHeap + G.n
  set bfsHeap := bPtr + G.n
  set h3 := bfsHeap + 2 * G.n
  have hnl_le : nl.length ≤ G.m := nonloopEdges_length_le G
  have hV_le : V_list.length ≤ G.n := activeVertsList_length_le G
  have hI_le : inact.length ≤ G.n := inactiveVertsList_length_le G.n V_list
  have hV_ge2 : 2 ≤ V_list.length := activeVertsList_ge_two_of_nl hG hnl_ne
  have hsp_ge : 4 + 9 * G.n + 4 * G.m ≤ lsstSpace Q_AN K_AN G.n G.m L_sim h := by
    dsimp only [lsstSpace]
    omega
  have hh3_w : h3 < 2 ^ w := by
    have : h3 ≤ heap + (4 + 9 * G.n + 4 * G.m) := by
      dsimp only [h3, bfsHeap, bPtr, newHeap, csrHeap]
      omega
    exact lt_of_le_of_lt this (lt_of_le_of_lt (by omega) hheap_space)
  have hcsr_w : csrHeap < 2 ^ w := by dsimp only [h3, bfsHeap, bPtr, newHeap, csrHeap] at hh3_w ⊢; omega
  have hcsr1_w : csrHeap + 1 < 2 ^ w := by dsimp only [h3, bfsHeap, bPtr, newHeap, csrHeap] at hh3_w ⊢; omega
  have hvList_w : vListPtr < 2 ^ w := by dsimp only [vListPtr, h3, bfsHeap, bPtr, newHeap, csrHeap] at hh3_w ⊢; omega
  have hinactP_w : inactPtr < 2 ^ w := by dsimp only [inactPtr, vListPtr, h3, bfsHeap, bPtr, newHeap, csrHeap] at hh3_w ⊢; omega
  have hoffP_w : offPtr < 2 ^ w := by dsimp only [offPtr, inactPtr, vListPtr, h3, bfsHeap, bPtr, newHeap, csrHeap] at hh3_w ⊢; omega
  have hadjP_w : adjPtr < 2 ^ w := by dsimp only [adjPtr, offPtr, inactPtr, vListPtr, h3, bfsHeap, bPtr, newHeap, csrHeap] at hh3_w ⊢; omega
  have hn1_w : G.n + 1 < 2 ^ w := by dsimp only [h3, bfsHeap, bPtr, newHeap, csrHeap] at hh3_w ⊢; omega
  have hnewHeap_w : newHeap < 2 ^ w := by dsimp only [h3, bfsHeap, bPtr, newHeap, csrHeap] at hh3_w ⊢; omega
  have hbPtr_w : bPtr < 2 ^ w := by dsimp only [bPtr, h3, bfsHeap, newHeap, csrHeap] at hh3_w ⊢; omega
  have hbfsHeap_w : bfsHeap < 2 ^ w := by dsimp only [bfsHeap, bPtr, h3] at hh3_w ⊢; omega
  have hn_w : G.n < 2 ^ w := by omega
  have hm_w : G.m < 2 ^ w := by omega
  have hnl_w : nl.length < 2 ^ w := lt_of_le_of_lt hnl_le hm_w
  have hV_w : V_list.length < 2 ^ w := lt_of_le_of_lt hV_le hn_w
  have hI_w : inact.length < 2 ^ w := lt_of_le_of_lt hI_le hn_w
  have hheap_w : heap < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hcsr_w
  have ht_w : tailArr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) ht_lt) hheap_w
  have hh_w : headArr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hh_lt) hheap_w
  have hcsr_mc : MeetsContract w P (lsstGraphBase b + idxBuildCSR) (buildCSRContract G w) :=
    buildCSR_meetsContract (hasAt_buildCSR hGraph)
  have hvi_mc : MeetsContract w P (lsstGraphBase b + idxBuildVertIdx) (buildVertIdxContract G.n V_list w) :=
    buildVertIdx_meetsContract (hasAt_csrAuxModule hGraph)
  have hbfs_mc : MeetsContract w P (lsstGraphBase b + idxBfsBridges) (bfsBridgesContract G V_list w) := by
    have hbfs := bfsBridges_meetsContract (G := G) (V_list := V_list) (w := w) hGraph
    simpa only [lsstGraphBase] using hbfs
  -- Step 1: reg 21 := heap + m = csrHeap
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hrg.r11) (Expr.eval_reg_of_eq hrg.r1) hcsr_w)
    rfl fun s1 hm1 _ hr1 => ?_
  have hrg1 := lsstInRegs_upd hrg hr1 (by decide)
  have hs1_20 : s1.regs 20 = nl.length := by rw [hr1, Function.update_of_ne (by decide)]; exact hr20
  have hs1_21 : s1.regs 21 = csrHeap := by rw [hr1, Function.update_self]
  -- Step 2: call buildCSR
  have hpre_csr : (buildCSRContract G w).pre [G.n, nl.length, heap, tailArr, headArr, csrHeap] s1.mem := by
    rw [hm1]
    exact ⟨heap, tailArr, headArr, csrHeap, rfl, hG, h16_w,
      (by dsimp only [csrHeap]; linarith only [hnl_le]),
      le_trans ht_lt (Nat.le_add_right _ _), le_trans hh_lt (Nat.le_add_right _ _),
      by dsimp only [csrHeap, newHeap] at hnewHeap_w ⊢; omega,
      hnl_at, htail_at, hhead_at, hz_csr⟩
  refine runs_seq_call_step hcsr_mc
    (evalArgs_cons (Expr.eval_reg_of_eq hrg1.r0)
      (evalArgs_cons (Expr.eval_reg_of_eq hs1_20)
        (evalArgs_cons (Expr.eval_reg_of_eq hrg1.r11)
          (evalArgs_cons (Expr.eval_reg_of_eq hrg1.r2)
            (evalArgs_cons (Expr.eval_reg_of_eq hrg1.r3)
              (evalArgs_cons (Expr.eval_reg_of_eq hs1_21) (evalArgs_nil _ _)))))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    hpre_csr rfl (rfl : _ = buildCSRCost G.n nl.length) fun ret_csr mem_csr s2 hp_csr hm2 hr2 => ?_
  rcases hp_csr with ⟨nlA_c, tA_c, hA_c, h_c, heq_csr, hret_csr, hm_V, hm_I, hlist_V, hlist_I,
    hcsr_spec, hz_new, hfr_csr⟩
  simp only [List.cons.injEq, and_true] at heq_csr
  rcases heq_csr with ⟨_, _, enl_c, et_c, eh_c, ehp_c⟩
  rw [← ehp_c] at hret_csr hm_V hm_I hlist_V hlist_I hcsr_spec hz_new hfr_csr
  have hrg2 := lsstInRegs_upd hrg1 hr2 (by decide)
  have hs2_20 : s2.regs 20 = nl.length := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_20
  have hs2_21 : s2.regs 21 = csrHeap := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_21
  have hs2_22 : s2.regs 22 = newHeap := by
    rw [hr2, Function.update_self, hret_csr]
  have hs2_nl : ListAt s2.mem heap nl := by
    rw [hm2]
    exact hnl_at.congr fun q hq1 hq2 => by rw [hfr_csr q (by omega), hm1]
  have hs2_lt_heap : ∀ a < heap, s2.mem a = mem_orig a := fun a ha => by
    rw [hm2, hfr_csr a (by omega), hm1, hpres a ha]
  -- Steps 3..9: load Vcnt, inactLen, compute vListPtr, inactPtr, offPtr, adjPtr, r₀
  refine runs_seq_assign_step
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hs2_21) (hm2 ▸ hm_V))
    rfl fun s3 hm3 _ hr3 => ?_
  have hrg3 := lsstInRegs_upd hrg2 hr3 (by decide)
  have hs3_20 : s3.regs 20 = nl.length := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_20
  have hs3_21 : s3.regs 21 = csrHeap := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_21
  have hs3_22 : s3.regs 22 = newHeap := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_22
  have hs3_23 : s3.regs 23 = V_list.length := by rw [hr3, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hs3_21) (Expr.eval_const hw1) hcsr1_w)
      (hm3 ▸ hm2 ▸ hm_I))
    rfl fun s4 hm4 _ hr4 => ?_
  have hrg4 := lsstInRegs_upd hrg3 hr4 (by decide)
  have hs4_20 : s4.regs 20 = nl.length := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_20
  have hs4_21 : s4.regs 21 = csrHeap := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_21
  have hs4_22 : s4.regs 22 = newHeap := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_22
  have hs4_23 : s4.regs 23 = V_list.length := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_23
  have hs4_24 : s4.regs 24 = inact.length := by rw [hr4, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs4_21) (Expr.eval_const h2_w) hvList_w)
    rfl fun s5 hm5 _ hr5 => ?_
  have hrg5 := lsstInRegs_upd hrg4 hr5 (by decide)
  have hs5_20 : s5.regs 20 = nl.length := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_20
  have hs5_22 : s5.regs 22 = newHeap := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_22
  have hs5_23 : s5.regs 23 = V_list.length := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_23
  have hs5_24 : s5.regs 24 = inact.length := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_24
  have hs5_25 : s5.regs 25 = vListPtr := by rw [hr5, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs5_25) (Expr.eval_reg_of_eq hrg5.r0) hinactP_w)
    rfl fun s6 hm6 _ hr6 => ?_
  have hrg6 := lsstInRegs_upd hrg5 hr6 (by decide)
  have hs6_20 : s6.regs 20 = nl.length := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_20
  have hs6_22 : s6.regs 22 = newHeap := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_22
  have hs6_23 : s6.regs 23 = V_list.length := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_23
  have hs6_24 : s6.regs 24 = inact.length := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_24
  have hs6_25 : s6.regs 25 = vListPtr := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_25
  have hs6_26 : s6.regs 26 = inactPtr := by rw [hr6, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs6_26) (Expr.eval_reg_of_eq hrg6.r0) hoffP_w)
    rfl fun s7 hm7 _ hr7 => ?_
  have hrg7 := lsstInRegs_upd hrg6 hr7 (by decide)
  have hs7_20 : s7.regs 20 = nl.length := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_20
  have hs7_22 : s7.regs 22 = newHeap := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_22
  have hs7_23 : s7.regs 23 = V_list.length := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_23
  have hs7_24 : s7.regs 24 = inact.length := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_24
  have hs7_25 : s7.regs 25 = vListPtr := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_25
  have hs7_26 : s7.regs 26 = inactPtr := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_26
  have hs7_27 : s7.regs 27 = offPtr := by rw [hr7, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs7_27)
      (Expr.eval_add (Expr.eval_reg_of_eq hrg7.r0) (Expr.eval_const hw1) hn1_w) hadjP_w)
    rfl fun s8 hm8 _ hr8 => ?_
  have hrg8 := lsstInRegs_upd hrg7 hr8 (by decide)
  have hs8_20 : s8.regs 20 = nl.length := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_20
  have hs8_22 : s8.regs 22 = newHeap := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_22
  have hs8_23 : s8.regs 23 = V_list.length := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_23
  have hs8_24 : s8.regs 24 = inact.length := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_24
  have hs8_25 : s8.regs 25 = vListPtr := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_25
  have hs8_26 : s8.regs 26 = inactPtr := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_26
  have hs8_27 : s8.regs 27 = offPtr := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_27
  have hs8_28 : s8.regs 28 = adjPtr := by rw [hr8, Function.update_self]
  have hs8_mem : s8.mem = s2.mem := hm8.trans (hm7.trans (hm6.trans (hm5.trans (hm4.trans hm3))))
  have hr₀_eq_mem : s8.mem vListPtr = V_list.headD 0 := by
    rw [hs8_mem, hm2]
    have h0 := hlist_V.getElem (i := 0) (by linarith only [hV_ge2])
    rw [Nat.add_zero] at h0
    rw [h0, headD_eq_getElem_zero V_list (by linarith only [hV_ge2])]
  refine runs_seq_assign_step
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hs8_25) hr₀_eq_mem)
    rfl fun s9 hm9 _ hr9 => ?_
  have hrg9 := lsstInRegs_upd hrg8 hr9 (by decide)
  have hs9_20 : s9.regs 20 = nl.length := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_20
  have hs9_22 : s9.regs 22 = newHeap := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_22
  have hs9_23 : s9.regs 23 = V_list.length := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_23
  have hs9_24 : s9.regs 24 = inact.length := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_24
  have hs9_25 : s9.regs 25 = vListPtr := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_25
  have hs9_26 : s9.regs 26 = inactPtr := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_26
  have hs9_27 : s9.regs 27 = offPtr := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_27
  have hs9_28 : s9.regs 28 = adjPtr := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_28
  have hs9_29 : s9.regs 29 = V_list.headD 0 := by rw [hr9, Function.update_self]
  have hs9_mem : s9.mem = s2.mem := hm9.trans hs8_mem
  have hV_lt_n : ∀ u ∈ V_list, u < G.n := fun u hu => (mem_activeVertsList_iff.mp hu).1
  -- Step 10: call buildVertIdx
  have hpre_vi : (buildVertIdxContract G.n V_list w).pre [V_list.length, vListPtr, newHeap] s9.mem := by
    rw [hs9_mem, hm2]
    exact ⟨vListPtr, newHeap, rfl, h16_w, activeVertsList_nodup G, hV_lt_n,
      (by dsimp only [vListPtr, newHeap, csrHeap]; linarith only [hV_le]), hbPtr_w, hlist_V⟩
  refine runs_seq_call_step hvi_mc
    (evalArgs_cons (Expr.eval_reg_of_eq hs9_23)
      (evalArgs_cons (Expr.eval_reg_of_eq hs9_25)
        (evalArgs_cons (Expr.eval_reg_of_eq hs9_22) (evalArgs_nil _ _))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
    hpre_vi rfl (rfl : _ = buildVertIdxCost G.n) fun _ mem_vi s10 hp_vi hm10 hr10 => ?_
  rcases hp_vi with ⟨vp_i, vi_i, heq_vi, _, hvidx_spec, hfr_vi⟩
  simp only [List.cons.injEq, true_and, and_true] at heq_vi
  rcases heq_vi with ⟨evp_i, evi_i⟩
  rw [← evi_i] at hvidx_spec hfr_vi
  have hrg10 := lsstInRegs_upd hrg9 hr10 (by decide)
  have hs10_20 : s10.regs 20 = nl.length := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_20
  have hs10_22 : s10.regs 22 = newHeap := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_22
  have hs10_23 : s10.regs 23 = V_list.length := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_23
  have hs10_24 : s10.regs 24 = inact.length := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_24
  have hs10_25 : s10.regs 25 = vListPtr := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_25
  have hs10_26 : s10.regs 26 = inactPtr := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_26
  have hs10_27 : s10.regs 27 = offPtr := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_27
  have hs10_28 : s10.regs 28 = adjPtr := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_28
  have hs10_29 : s10.regs 29 = V_list.headD 0 := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_29
  -- Steps 11..12: assign bPtr and bfsHeap
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs10_22) (Expr.eval_reg_of_eq hrg10.r0) hbPtr_w)
    rfl fun s11 hm11 _ hr11 => ?_
  have hrg11 := lsstInRegs_upd hrg10 hr11 (by decide)
  have hs11_20 : s11.regs 20 = nl.length := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_20
  have hs11_22 : s11.regs 22 = newHeap := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_22
  have hs11_23 : s11.regs 23 = V_list.length := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_23
  have hs11_24 : s11.regs 24 = inact.length := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_24
  have hs11_25 : s11.regs 25 = vListPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_25
  have hs11_26 : s11.regs 26 = inactPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_26
  have hs11_27 : s11.regs 27 = offPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_27
  have hs11_28 : s11.regs 28 = adjPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_28
  have hs11_29 : s11.regs 29 = V_list.headD 0 := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_29
  have hs11_30 : s11.regs 30 = bPtr := by rw [hr11, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs11_30) (Expr.eval_reg_of_eq hrg11.r0) hbfsHeap_w)
    rfl fun s12 hm12 _ hr12 => ?_
  have hrg12 := lsstInRegs_upd hrg11 hr12 (by decide)
  have hs12_20 : s12.regs 20 = nl.length := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_20
  have hs12_22 : s12.regs 22 = newHeap := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_22
  have hs12_23 : s12.regs 23 = V_list.length := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_23
  have hs12_24 : s12.regs 24 = inact.length := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_24
  have hs12_25 : s12.regs 25 = vListPtr := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_25
  have hs12_26 : s12.regs 26 = inactPtr := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_26
  have hs12_27 : s12.regs 27 = offPtr := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_27
  have hs12_28 : s12.regs 28 = adjPtr := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_28
  have hs12_29 : s12.regs 29 = V_list.headD 0 := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_29
  have hs12_30 : s12.regs 30 = bPtr := by rw [hr12, Function.update_of_ne (by decide)]; exact hs11_30
  have hs12_31 : s12.regs 31 = bfsHeap := by rw [hr12, Function.update_self]
  have hs12_mem : s12.mem = mem_vi := hm12.trans (hm11.trans hm10)
  -- Check preconditions for bfsBridges
  have hpre_bfs : (bfsBridgesContract G V_list w).pre
      [G.n, offPtr, adjPtr, V_list.length, vListPtr, bPtr, bfsHeap] s12.mem := by
    rw [hs12_mem]
    refine ⟨offPtr, adjPtr, vListPtr, bPtr, bfsHeap, rfl, hG, h16_w, rfl,
      by intro hnil; simp [hnil] at hV_ge2,
      (by dsimp only [offPtr, inactPtr, vListPtr, newHeap, bPtr, bfsHeap, csrHeap]; linarith only),
      (by dsimp only [adjPtr, offPtr, inactPtr, vListPtr, newHeap, bPtr, bfsHeap, csrHeap]; linarith only),
      (by dsimp only [vListPtr, newHeap, bPtr, bfsHeap, csrHeap]; linarith only [hV_le]),
      (by dsimp only [bPtr, bfsHeap]; linarith only [hV_le]),
      fun a ha1 ha2 ha3 ha4 => by dsimp only [bPtr, vListPtr, newHeap, csrHeap] at ha1 ha4; linarith only [ha1, ha4, hV_le],
      fun a ha1 ha2 ha3 ha4 => by dsimp only [bPtr, offPtr, inactPtr, vListPtr, newHeap, csrHeap] at ha1 ha4; linarith only [ha1, ha4],
      fun a ha1 ha2 ha3 ha4 => by dsimp only [bPtr, adjPtr, offPtr, inactPtr, vListPtr, newHeap, csrHeap] at ha1 ha4; linarith only [ha1, ha4],
      hh3_w,
      hlist_V.congr fun q hq1 hq2 => by
        rw [hfr_vi q (Or.inl (by dsimp only [vListPtr, newHeap, csrHeap] at hq2 ⊢; linarith only [hq2, hV_le])), hs9_mem, hm2],
      ?_,
      fun q hq => by
        rw [hfr_vi q (Or.inr (by dsimp only [bfsHeap, bPtr] at hq ⊢; linarith only [hq])), hs9_mem, hm2]
        exact hz_new q (by dsimp only [bfsHeap, bPtr, newHeap, csrHeap] at hq ⊢; linarith only [hq])⟩
    · exact csrAdjacencySpec_congr_lt hG hcsr_spec (limit := newHeap)
        (by dsimp only [offPtr, inactPtr, vListPtr, newHeap, csrHeap]; linarith only)
        (by dsimp only [adjPtr, offPtr, inactPtr, vListPtr, newHeap, csrHeap]; linarith only)
        fun a ha => by rw [hfr_vi a (Or.inl ha), hs9_mem, hm2]
  -- Step 13: call bfsBridges
  refine runs_seq_call_step hbfs_mc
    (evalArgs_cons (Expr.eval_reg_of_eq hrg12.r0)
      (evalArgs_cons (Expr.eval_reg_of_eq hs12_27)
        (evalArgs_cons (Expr.eval_reg_of_eq hs12_28)
          (evalArgs_cons (Expr.eval_reg_of_eq hs12_23)
            (evalArgs_cons (Expr.eval_reg_of_eq hs12_25)
              (evalArgs_cons (Expr.eval_reg_of_eq hs12_30)
                (evalArgs_cons (Expr.eval_reg_of_eq hs12_31) (evalArgs_nil _ _))))))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    hpre_bfs rfl (rfl : _ = bfsBridgesCost G.n nl.length) fun _ mem_bfs s13 hp_bfs hm13 hr13 => ?_
  rcases hp_bfs with ⟨o_b, a_b, v_b, bp_b, hp_b, heq_bfs, B, hret_b, hB_le, hB_at, hz_bfs, hfr_bfs, hBr⟩
  simp only [List.cons.injEq, and_true] at heq_bfs
  rcases heq_bfs with ⟨_, _, _, _, _, ebp_b, ehp_b⟩
  rw [← ebp_b] at hB_at hfr_bfs
  rw [← ehp_b] at hz_bfs hfr_bfs
  have hrg13 := lsstInRegs_upd hrg12 hr13 (by decide)
  have hs13_20 : s13.regs 20 = nl.length := by rw [hr13, Function.update_of_ne (by decide)]; exact hs12_20
  have hs13_22 : s13.regs 22 = newHeap := by rw [hr13, Function.update_of_ne (by decide)]; exact hs12_22
  have hs13_23 : s13.regs 23 = V_list.length := by rw [hr13, Function.update_of_ne (by decide)]; exact hs12_23
  have hs13_24 : s13.regs 24 = inact.length := by rw [hr13, Function.update_of_ne (by decide)]; exact hs12_24
  have hs13_26 : s13.regs 26 = inactPtr := by rw [hr13, Function.update_of_ne (by decide)]; exact hs12_26
  have hs13_29 : s13.regs 29 = V_list.headD 0 := by rw [hr13, Function.update_of_ne (by decide)]; exact hs12_29
  have hs13_30 : s13.regs 30 = bPtr := by rw [hr13, Function.update_of_ne (by decide)]; exact hs12_30
  have hs13_31 : s13.regs 31 = bfsHeap := by rw [hr13, Function.update_of_ne (by decide)]; exact hs12_31
  have hs13_32 : s13.regs 32 = B.length := by rw [hr13, Function.update_self, hret_b]
  have hs13_mem_bPtr : ∀ a < bPtr, s13.mem a = mem_vi a := fun a ha => by
    rw [hm13, hfr_bfs a (Or.inl ha), hs12_mem]
  have hs13_nl : ListAt s13.mem heap nl :=
    hs2_nl.congr fun q hq1 hq2 => by
      have hqb : q < bPtr := by dsimp only [bPtr, newHeap, csrHeap] at hq2 ⊢; linarith only [hq2, hnl_le]
      have hqn : q < newHeap := by dsimp only [newHeap, csrHeap] at hq2 ⊢; linarith only [hq2, hnl_le]
      rw [hs13_mem_bPtr q hqb, hfr_vi q (Or.inl hqn), hs9_mem]
  have hs13_inact : ListAt s13.mem inactPtr inact :=
    hlist_I.congr fun q hq1 hq2 => by
      have hqb : q < bPtr := by dsimp only [bPtr, newHeap, csrHeap, inactPtr, vListPtr] at hq2 ⊢; linarith only [hq2, hI_le]
      have hqn : q < newHeap := by dsimp only [newHeap, csrHeap, inactPtr, vListPtr] at hq2 ⊢; linarith only [hq2, hI_le]
      rw [hs13_mem_bPtr q hqb, hfr_vi q (Or.inl hqn), hs9_mem, hm2]
  have hs13_vidx : ∀ u ∈ V_list, s13.mem (newHeap + u) = V_list.idxOf u := fun u hu => by
    have hqb : newHeap + u < bPtr := by have := hV_lt_n u hu; dsimp only [bPtr]; linarith only [this]
    rw [hs13_mem_bPtr _ hqb]
    exact hvidx_spec u hu
  have hs13_B : ListAt s13.mem bPtr B := by rw [hm13]; exact hB_at
  have hs13_zero : ZeroFrom s13.mem h3 := by rw [hm13]; exact hz_bfs
  have hs13_pres : ∀ a < heap, s13.mem a = mem_orig a := fun a ha => by
    have hqb : a < bPtr := by dsimp only [bPtr, newHeap, csrHeap]; linarith only [ha]
    have hqn : a < newHeap := by dsimp only [newHeap, csrHeap]; linarith only [ha]
    rw [hs13_mem_bPtr a hqb, hfr_vi a (Or.inl hqn), hs9_mem, hs2_lt_heap a ha]
  obtain ⟨o, st', c, hrun_s, hq_s, hc_s⟩ :=
    hrest s13 B newHeap vListPtr inactPtr bPtr bfsHeap rfl rfl rfl rfl rfl hB_le
      hrg13 hs13_20 hs13_22 hs13_23 hs13_24 hs13_26 hs13_29 hs13_30 hs13_31 hs13_32
      hs13_nl hs13_inact hs13_B hs13_vidx hBr hs13_zero hs13_pres
  refine ⟨o, st', _, hrun_s, hq_s, ?_⟩
  simp only [Expr.size, argsSize] at hc_s ⊢
  linarith only [hc_s]

end MinCostFlow.WideWord
