module

public import MinCostFlow.Scaling.DemandScanProgram
public import MinCostFlow.Scaling.ShiftedInputLayout
public import WordRAM.CopyWords
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Building all shifted demands from the encoded input

The general-flow reduction of Lemma C.1 of Chen et al., arXiv:2203.00671v2,
initializes the signed demand table from the original demands, then scans
each input edge once. This procedure copies the statement's demand block
and runs the proved demand scan. It computes exactly `buildShiftedDemands`,
allocates `2*n+6*m` cells including scratch, and costs at most
`700*m+40*n+200` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[inputAddress,heap]`. -/
def buildDemandsBody (copy scan : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 8) (.reg 3))) ;;
  .call 5 copy [.reg 4, .reg 1, .bin .mul (.const 2) (.reg 2)] ;;
  .assign 6 (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 2))) ;;
  .call 7 scan [.bin .add (.reg 0) (.const 2), .reg 3, .reg 1, .reg 6] ;;
  .ret (.reg 7)

/-- Demand initialization, copying, and the full demand scan. -/
def buildDemandsModule (b : ℕ) : List Stmt :=
  buildDemandsBody (b + 1) (b + 2) :: copyWords :: demandScanModule (b + 2)

/-- All initial demand magnitudes are bounded by `B`, all lower capacities
by `L`, and the word budget covers their full edge scan. -/
def buildDemandsContract (w : ℕ) (I : Instance) (hv : I.IsValid) (B L : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, h] ∧ ListAt mem a I.encode ∧
      a + I.encode.length ≤ h ∧ (∀ v : Fin I.n, (I.d v).natAbs ≤ B) ∧
      (∀ e : Fin I.m, (I.edge e).lower.natAbs ≤ L) ∧
      B + 2 * I.m * L < 2 ^ w ∧ 8 < 2 ^ w)
    (fun args _ mem' => SignedTableAt mem' (heapArg args) (FlowReduction.buildShiftedDemands I hv))
    (fun _ _ => 700 * I.m + 40 * I.n + 200) (fun _ _ => 2 * I.n + 6 * I.m)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 * I.n + 6 * I.m }

/-- Initialization and the complete demand scan have no random instructions. -/
theorem buildDemandsModule_noRand (b : ℕ) :
    ∀ body ∈ buildDemandsModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [buildDemandsBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · simp only [copyWords, forRange, forUp, Stmt.NoRand, and_self]
    · exact demandScanModule_noRand _ body hb

/-- The full procedure initializes and updates precisely the model demand
table, with explicit linear time and exact space. -/
theorem buildDemands_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (buildDemandsModule b)) (I : Instance) (hv : I.IsValid) (B L : ℕ) :
    MeetsContract w p b (buildDemandsContract w I hv B L) := by
  have hcopy : p.HasAt (b + 1) [copyWords] := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [buildDemandsModule, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.add_zero] using hp 1 (by simp [buildDemandsModule])
  have hscan : p.HasAt (b + 2) (demandScanModule (b + 2)) := by
    intro i hi
    have h := hp (i + 1 + 1) (by simp only [buildDemandsModule, List.length_cons]; omega)
    have hi' : b + (i + 1 + 1) = b + 2 + i := by omega
    rw [hi'] at h
    simpa only [buildDemandsModule, List.getElem_cons_succ] using h
  have hkC := copyWords_meetsContract (w := w) hcopy
  have hkS := demandScan_meetsContract (w := w) hscan I hv
    (fun v => I.d v) (List.finRange I.m) B L
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hd, hl, hbudget, hw⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (2 * I.n + 6 * I.m) < 2 ^ w at hspace
  have hlength := instance_encode_length I hv
  have hheader := instance_header_at I mem a hat
  have hN := hheader.1
  have hM := hheader.2
  have hedge := instance_edges_at I mem a hat
  have hdemand := instance_demands_at I mem a hat
  have hdemandlen : (I.demand.flatMap encodeInt).length = 2 * I.n := by
    rw [integers_encode_length, hv.2]
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hn : I.n < 2 ^ w := by omega
  have hm : I.m < 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have ha2 : a + 2 < 2 ^ w := by omega
  have h8m : 8 * I.m < 2 ^ w := by omega
  have hsource : a + 2 + 8 * I.m < 2 ^ w := by omega
  have h2n : 2 * I.n < 2 ^ w := by omega
  have htableend : heap + 2 * I.n < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  apply runs_start_le
  unfold buildDemandsBody
  refine runs_seq_assign_le (v := I.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := I.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := a + 2 + 8 * I.m) (by eval_expr) ?_
  refine runs_seq_call_le hkC (vs := [a + 2 + 8 * I.m, heap, 2 * I.n]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨a + 2 + 8 * I.m, heap, 2 * I.n, rfl, hone, by omega, by omega, Or.inr (by omega)⟩
  · intro _ memC posC hpostC
    obtain ⟨src, dst, len, hargs, _, hcopied, hframeC⟩ := hpostC
    have hs : src = a + 2 + 8 * I.m := by
      have hh := congrArg (fun xs : List ℕ => xs.getD 0 0) hargs
      simpa only [List.getD_cons_zero] using hh.symm
    have hd' : dst = heap := by
      have hh := congrArg (fun xs : List ℕ => xs.getD 1 0) hargs
      simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
    have hl' : len = 2 * I.n := by
      have hh := congrArg (fun xs : List ℕ => xs.getD 2 0) hargs
      simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
    subst src; subst dst; subst len
    change (∀ i < 2 * I.n, memC (heap + i) = mem (a + 2 + 8 * I.m + i)) at hcopied
    change (∀ x, x < heap ∨ heap + 2 * I.n ≤ x → memC x = mem x) at hframeC
    have htableC : SignedTableAt memC heap (fun v : Fin I.n => I.d v) := by
      have hblock := copyWords_listAt hdemand hdemandlen hcopied
      intro v
      have hv' : v.val < I.demand.length := by rw [hv.2]; exact v.isLt
      exact integers_pair_at I.demand memC heap hblock ⟨v.val, hv'⟩
    have hedgeC : ListAt memC (a + 2) ((List.finRange I.m).map I.edge |>.flatMap Edge.encode) := by
      rw [instance_edges_finRange]
      apply hedge.of_agree_below (h₀ := heap)
      · rw [edges_encode_length]
        change a + 2 + 8 * I.m ≤ heap
        omega
      · intro x hx
        exact hframeC x (Or.inl hx)
    have hzeroC : ZeroFrom memC (heap + 2 * I.n) := by
      intro x hx
      exact (hframeC x (Or.inr hx)).trans (hzero x (by omega))
    refine runs_seq_assign_le (v := heap + 2 * I.n) (by eval_expr) ?_
    refine runs_seq_call_le hkS (vs := [a + 2, I.m, heap, heap + 2 * I.n]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨a + 2, heap, heap + 2 * I.n, ?_, hedgeC, htableC, ?_, le_rfl,
        hd, (fun e _ => hl e), ?_, hzeroC, ?_, hw⟩
      · simp only [List.length_finRange]
      · simp only [List.length_finRange]
        omega
      · simpa only [List.length_finRange] using hbudget
      · simp only [List.length_finRange]
        omega
    · intro out memS posS hpostS
      obtain ⟨hout, htableS, hzeroS, hframeS⟩ := hpostS
      change out = heap + 2 * I.n + 6 * (List.finRange I.m).length at hout
      rw [List.length_finRange] at hout
      change SignedTableAt memS heap (FlowReduction.buildShiftedDemands I hv) at htableS
      change (∀ x < heap + 2 * I.n, x < heap ∨ heap + 2 * I.n ≤ x → memS x = memC x) at hframeS
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + (2 * I.n + 6 * I.m) ∧
          (∀ x < heap, memS x = mem x) ∧ ZeroFrom memS out ∧
          SignedTableAt memS heap (FlowReduction.buildShiftedDemands I hv)) ∧
          out = heap + 2 * I.n + 6 * I.m
        refine ⟨⟨by omega, by omega, ?_, hzeroS, htableS⟩, hout⟩
        intro x hx
        exact (hframeS x (by omega) (Or.inl hx)).trans (hframeC x (Or.inl hx))
      · simp only [buildDemandsContract, heapContract, demandScanContract, copyWordsContract,
          List.length_finRange, argsSize_cons, argsSize_nil, Expr.size_load,
          Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega

/-- Every valid encoded instance has initial demand and lower-capacity
bounds and a host width satisfying all procedure premises together. -/
theorem exists_buildDemands_pre (I : Instance) (hv : I.IsValid) :
    ∃ w B L, (∀ x ∈ [0, I.encode.length], x < 2 ^ w) ∧
      (buildDemandsContract w I hv B L).pre [0, I.encode.length] (initMem I.encode) := by
  let B := ((List.ofFn fun v : Fin I.n => I.d v).map Int.natAbs).foldr max 0
  let L := (List.ofFn fun e : Fin I.m => (I.edge e).lower.natAbs).foldr max 0
  have hd : ∀ v : Fin I.n, (I.d v).natAbs ≤ B := by
    intro v
    exact Link.elem_le_foldr_max (List.mem_map.mpr ⟨I.d v, List.mem_ofFn.mpr ⟨v, rfl⟩, rfl⟩)
  have hl : ∀ e : Fin I.m, (I.edge e).lower.natAbs ≤ L := by
    intro e
    exact Link.elem_le_foldr_max (List.mem_ofFn.mpr ⟨e, rfl⟩)
  let w := wordSize 1 [I.encode.length + 2 * I.n + 6 * I.m + B + 2 * I.m * L + 10]
  have hlarge : I.encode.length + 2 * I.n + 6 * I.m + B + 2 * I.m * L + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, B, L, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  · exact ⟨⟨0, I.encode.length, rfl, listAt_initMem _, by omega, hd, hl, by omega, by omega⟩,
      zeroFrom_initMem _, by change I.encode.length + (2 * I.n + 6 * I.m) < 2 ^ w; omega⟩

/-- The complete module occupies exactly 9 procedure slots. -/
theorem buildDemandsModule_length (b : ℕ) : (buildDemandsModule b).length = 9 := rfl

end MinCostFlow.Scaling.Machine
