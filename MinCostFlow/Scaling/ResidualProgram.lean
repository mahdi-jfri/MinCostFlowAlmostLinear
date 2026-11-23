module

public import MinCostFlow.Scaling.ResidualEdgesProgram
public import MinCostFlow.Scaling.WordPairProgram
public import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Constructing the complete residual circulation

Appendix C of Chen et al., arXiv:2203.00671v2, uses the residual graph in
both scaling loops and the general-flow reduction. This procedure writes
its header, scans all forward slots, then scans all reverse slots. Its
output is exactly `Circulation.residual`, with zero-capacity slots retained.
It allocates `2+10*m` cells, preserves both inputs, and costs at most
`600*m+200` machine steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[circulationAddress,flowAddress,heap]`. -/
def residualBody (header forward reverse : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 header [.reg 3, .bin .add (.reg 4) (.reg 4), .reg 2] ;;
  .call 6 forward [.bin .add (.reg 0) (.const 2), .reg 1, .reg 4, .reg 5] ;;
  .call 7 reverse [.bin .add (.reg 0) (.const 2), .reg 1, .reg 4, .reg 6] ;;
  .ret (.reg 7)

/-- Residual construction, header writing, and both directed scans. -/
def residualModule (b : ℕ) : List Stmt :=
  residualBody (b + 1) (b + 2) (b + 4) :: wordPairBody ::
    (residualEdgesModule false (b + 2) ++ residualEdgesModule true (b + 4))

/-- Edgewise feasible integral input values suffice for the exact residual
construction. Both source arrays lie below the fresh output. -/
def residualContract (w : ℕ) (J : Circulation) (f : Fin J.m → ℤ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a flow heap, args = [a, flow, heap] ∧
      ListAt mem a J.solverWords ∧ ListAt mem flow (List.ofFn fun e => (f e).toNat) ∧
      a + J.solverWords.length ≤ heap ∧ flow + J.m ≤ heap ∧
      (∀ e, 0 ≤ f e ∧ f e ≤ J.capacity e) ∧
      (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (J.residual f).solverWords)
    (fun _ _ => 600 * J.m + 200) (fun _ _ => 2 + 10 * J.m)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 + 10 * J.m }

/-- Every procedure of residual construction has no random instructions. -/
theorem residualModule_noRand (b : ℕ) : ∀ body ∈ residualModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [residualBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact wordPairBody_noRand
    · rcases List.mem_append.mp hb with hb | hb
      · exact residualEdgesModule_noRand _ _ body hb
      · exact residualEdgesModule_noRand _ _ body hb

/-- The complete procedure computes exactly the model residual graph,
with exact allocation and explicit linear cost on every random tape. -/
theorem residual_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (residualModule b)) (J : Circulation) (f : Fin J.m → ℤ) :
    MeetsContract w p b (residualContract w J f) := by
  have htail := hasAt_tail hp
  have hheader : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [wordPairModule, Nat.add_zero, List.getElem_cons_zero] using htail.head
  have hparts : p.HasAt (b + 2)
      (residualEdgesModule false (b + 2) ++ residualEdgesModule true (b + 4)) := by
    simpa only [Nat.add_assoc] using hasAt_tail htail
  have hforward := hasAt_append_left hparts
  have hreverse : p.HasAt (b + 4) (residualEdgesModule true (b + 4)) := by
    simpa only [residualEdgesModule_length, Nat.add_assoc] using hasAt_append_right hparts
  have hkH := wordPair_meetsContract (w := w) hheader
  have hkF := residualEdges_meetsContract (w := w) false hforward J f (List.finRange J.m)
  have hkR := residualEdges_meetsContract (w := w) true hreverse J f (List.finRange J.m)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, flow, heap, rfl, hat, hflow, hend, hflowend, hf, hinput, hw⟩,
    hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (2 + 10 * J.m) < 2 ^ w at hspace
  have hsize := J.solverWords_length
  have hN : mem a = J.n := by
    simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using hat 0 (by rw [hsize]; omega)
  have hM : mem (a + 1) = J.m := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using hat 1 (by rw [hsize]; omega)
  have hedge : ListAt mem (a + 2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have hh := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using hh
  have hflow' : ListAt mem flow ((List.finRange J.m).map fun e => (f e).toNat) := by
    rwa [← List.ofFn_eq_map]
  have hrecordWords : ∀ e ∈ List.finRange J.m, ∀ x ∈ J.solverEdgeWords e, x < 2 ^ w := by
    intro e _ x hx
    exact hinput x (J.solverEdgeWord_mem e hx)
  have ha : a < 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have ha2 : a + 2 < 2 ^ w := by omega
  have hflowword : flow < 2 ^ w := by omega
  have hheap : heap < 2 ^ w := by omega
  have hn : J.n < 2 ^ w := hinput _ (List.mem_cons_self)
  have hm : J.m < 2 ^ w := by omega
  have h2m : J.m + J.m < 2 ^ w := by omega
  have hheap2 : heap + 2 < 2 ^ w := by omega
  apply runs_start_le
  unfold residualBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkH (vs := [J.n, J.m + J.m, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨_, _, heap, rfl⟩, hzero, hheap2⟩
  · intro heapH memH posH hpostH
    obtain ⟨⟨_, _, hframeH, hzeroH, hheaderH⟩, hptrH⟩ := hpostH
    change heapH = heap + 2 at hptrH
    change (∀ x < heap, memH x = mem x) at hframeH
    change ZeroFrom memH heapH at hzeroH
    change ListAt memH heap [J.n, J.m + J.m] at hheaderH
    have hheapH : heapH < 2 ^ w := by omega
    have hedgeH := hedge.of_agree_below (h₀ := heap)
      (by rw [J.solverEdgeRecords_length, List.length_finRange]; omega) hframeH
    have hflowH := hflow'.of_agree_below (h₀ := heap)
      (by simpa only [List.length_map, List.length_finRange] using hflowend) hframeH
    refine runs_seq_call_le hkF (vs := [a + 2, flow, J.m, heapH]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨a + 2, flow, heapH, ?_, hedgeH, hflowH, ?_, ?_,
        (fun e _ => hf e), hrecordWords, hw⟩, hzeroH, ?_⟩
      · simp only [List.length_finRange]
      · simp only [List.length_finRange]
        omega
      · simp only [List.length_finRange]
        omega
      · change heapH + 5 * (List.finRange J.m).length < 2 ^ w
        simp only [List.length_finRange]
        omega
    · intro heapF memF posF hpostF
      obtain ⟨⟨_, _, hframeF, hzeroF, hforwardF⟩, hptrF⟩ := hpostF
      change heapF = heapH + 5 * (List.finRange J.m).length at hptrF
      rw [List.length_finRange] at hptrF
      change (∀ x < heapH, memF x = memH x) at hframeF
      change ZeroFrom memF heapF at hzeroF
      change ListAt memF heapH ((List.finRange J.m).flatMap (residualEdgeWords J f false)) at hforwardF
      have hheapF : heapF < 2 ^ w := by omega
      have hedgeF := hedgeH.of_agree_below (h₀ := heapH)
        (by rw [J.solverEdgeRecords_length, List.length_finRange]; omega) hframeF
      have hflowF := hflowH.of_agree_below (h₀ := heapH)
        (by simp only [List.length_map, List.length_finRange]; omega) hframeF
      refine runs_seq_call_le hkR (vs := [a + 2, flow, J.m, heapF]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · refine ⟨⟨a + 2, flow, heapF, ?_, hedgeF, hflowF, ?_, ?_,
          (fun e _ => hf e), hrecordWords, hw⟩, hzeroF, ?_⟩
        · simp only [List.length_finRange]
        · simp only [List.length_finRange]
          omega
        · simp only [List.length_finRange]
          omega
        · change heapF + 5 * (List.finRange J.m).length < 2 ^ w
          simp only [List.length_finRange]
          omega
      · intro out memR posR hpostR
        obtain ⟨⟨_, _, hframeR, hzeroR, hreverseR⟩, hout⟩ := hpostR
        change out = heapF + 5 * (List.finRange J.m).length at hout
        rw [List.length_finRange] at hout
        change (∀ x < heapF, memR x = memF x) at hframeR
        change ZeroFrom memR out at hzeroR
        change ListAt memR heapF ((List.finRange J.m).flatMap (residualEdgeWords J f true)) at hreverseR
        have houtword : out < 2 ^ w := by omega
        have hheaderR : ListAt memR heap [J.n, J.m + J.m] := by
          apply hheaderH.of_agree_below (h₀ := heapH) (by change heap + 2 ≤ heapH; omega)
          intro x hx
          exact (hframeR x (by omega)).trans (hframeF x hx)
        have hforwardR : ListAt memR heapH ((List.finRange J.m).flatMap (residualEdgeWords J f false)) :=
          hforwardF.of_agree_below (h₀ := heapF)
            (by rw [residualRecords_length, List.length_finRange]; omega) hframeR
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap + (2 + 10 * J.m) ∧
            (∀ x < heap, memR x = mem x) ∧ ZeroFrom memR out ∧
            ListAt memR heap (J.residual f).solverWords) ∧ out = heap + 2 + 10 * J.m
          refine ⟨⟨by omega, by omega, ?_, hzeroR, ?_⟩, by omega⟩
          · intro x hx
            exact (hframeR x (by omega)).trans ((hframeF x (by omega)).trans (hframeH x hx))
          · rw [residual_solverWords]
            have heF : (List.ofFn (residualEdgeWords J f false)).flatten =
                (List.finRange J.m).flatMap (residualEdgeWords J f false) := by
              rw [List.flatMap, ← List.ofFn_eq_map]
            have heR : (List.ofFn (residualEdgeWords J f true)).flatten =
                (List.finRange J.m).flatMap (residualEdgeWords J f true) := by
              rw [List.flatMap, ← List.ofFn_eq_map]
            rw [heF, heR]
            apply (listAt_append (l₁ := [J.n, J.m + J.m])).mpr
            refine ⟨hheaderR, ?_⟩
            have hstart : heap + [J.n, J.m + J.m].length = heapH := by change heap + 2 = heapH; omega
            rw [hstart]
            apply listAt_append.mpr
            refine ⟨hforwardR, ?_⟩
            rw [residualRecords_length, List.length_finRange]
            have hstartF : heapH + 5 * J.m = heapF := by omega
            rwa [hstartF]
        · simp only [residualContract, heapContract, wordPairContract, residualEdgesContract,
            List.length_finRange, argsSize_cons, argsSize_nil, Expr.size_load,
            Expr.size_bin, Expr.size_reg, Expr.size_const]
          omega

/-- The complete residual constructor uses six procedure slots. -/
theorem residualModule_length (b : ℕ) : (residualModule b).length = 6 := rfl

end MinCostFlow.Scaling.Machine
