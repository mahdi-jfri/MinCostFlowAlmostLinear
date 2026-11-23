module

public import MinCostFlow.Scaling.VertexEncounterProgram
import WordRAM.Tactic

/-!
# Scanning a stored endpoint list

The vertex-compression function scans endpoints in order and assigns labels
only on first encounters. This procedure reads a strided endpoint table and
calls the proved encounter primitive. Its table occupies a separate region
after the endpoint records. It computes `VertexLabels.scan`, preserves all
memory outside the label block, and costs at most `80*length+8`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Vertex indices stored in a strided table. -/
def EndpointsAt {n : ℕ} (mem : ℕ → ℕ) (a stride : ℕ) (vs : List (Fin n)) : Prop :=
  ∀ i (hi : i < vs.length), mem (a + stride * i) = (vs[i]'hi).val

/-- Split the first endpoint from its remaining strided table. -/
theorem endpointsAt_cons {n : ℕ} (mem : ℕ → ℕ) (a stride : ℕ)
    (v : Fin n) (vs : List (Fin n)) :
    EndpointsAt mem a stride (v :: vs) ↔
      mem a = v.val ∧ EndpointsAt mem (a + stride) stride vs := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hh := h 0 (by simp)
      change mem (a + stride * 0) = v.val at hh
      simpa only [Nat.mul_zero, Nat.add_zero] using hh
    · intro i hi
      have hh := h (i + 1) (by simp only [List.length_cons]; omega)
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hh
  · intro h i hi
    cases i with
    | zero => simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] using h.1
    | succ i =>
      have hh := h.2 i (by simp only [List.length_cons] at hi; omega)
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hh

/-- Arguments `[source,length,stride,labels,count]`; `encounter` is the
constant-cost endpoint primitive and `self` the recursive scan. -/
def vertexScanBody (self encounter : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 4))
    (.assign 5 (.load (.reg 0)) ;;
      .call 6 encounter [.reg 3, .reg 4, .reg 5] ;;
      .call 7 self [.bin .add (.reg 0) (.reg 2), .bin .sub (.reg 1) (.const 1),
        .reg 2, .reg 3, .reg 6] ;;
      .ret (.reg 7))

/-- Recursive endpoint scan and its one-cell update primitive. -/
def vertexScanModule (b : ℕ) : List Stmt :=
  [vertexScanBody b (b + 1), vertexEncounterBody]

/-- The endpoint scan updates only its label table. -/
def vertexScanContract (w : ℕ) {n : ℕ} (s : VertexLabels n) (vs : List (Fin n)) : Contract where
  pre args mem := ∃ a stride labels,
    args = [a, vs.length, stride, labels, s.count] ∧ EndpointsAt mem a stride vs ∧
      LabelsAt mem labels s ∧ s.Valid ∧ a + stride * vs.length < labels ∧
      labels + n < 2 ^ w ∧ s.count + vs.length + 1 < 2 ^ w
  post args mem out mem' := out = (s.scan vs).count ∧
    LabelsAt mem' (args.getD 3 0) (s.scan vs) ∧
    ∀ x, x < args.getD 3 0 ∨ args.getD 3 0 + n ≤ x → mem' x = mem x
  cost _ _ := 80 * vs.length + 8

/-- Both endpoint scan procedures have no random instructions. -/
theorem vertexScanModule_noRand (b : ℕ) : ∀ body ∈ vertexScanModule b, body.NoRand := by
  simp only [vertexScanModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [vertexScanBody, Stmt.NoRand, and_self], vertexEncounterBody_noRand⟩

/-- The recursive scan realizes the finite endpoint-label function with a
linear machine cost and a frame outside the label block. -/
theorem vertexScan_meetsContract {w b n : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (vertexScanModule b)) (vs : List (Fin n)) (s : VertexLabels n) :
    MeetsContract w p b (vertexScanContract w s vs) := by
  have henc : p.HasAt (b + 1) vertexEncounterModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [vertexEncounterModule, vertexScanModule, Nat.add_zero,
      List.getElem_cons_succ, List.getElem_cons_zero] using hp 1 (by simp [vertexScanModule])
  induction vs generalizing s with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, stride, labels, rfl, _, hlabels, _, _, _, _⟩ := hpre
    have hcount : s.count < 2 ^ w := hwords s.count (by simp)
    apply runs_start_le
    unfold vertexScanBody
    wram_step
    · refine runs_ret_le (by eval_expr) ?_ ?_
      · exact ⟨rfl, hlabels, fun _ _ => rfl⟩
      · simp only [vertexScanContract, List.length_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp only [List.length_nil, eq_self, not_true_eq_false] at hcond
  | cons v vs ih =>
    have hk := vertexEncounter_meetsContract (w := w) henc s v
    have hr := ih (s.encounter v)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, stride, labels, rfl, hendpoints, hlabels, hvalid, hbefore, hspace, hcount⟩ := hpre
    obtain ⟨hhead, htail⟩ := (endpointsAt_cons mem a stride v vs).mp hendpoints
    have hvlt := v.isLt
    have ha : a < 2 ^ w := hwords a (by simp)
    have hstride : stride < 2 ^ w := hwords stride (by simp)
    have hlabelword : labels < 2 ^ w := hwords labels (by simp)
    have hcountword : s.count < 2 ^ w := hwords s.count (by simp)
    have hlenword : (v :: vs).length < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hvword : v.val < 2 ^ w := by omega
    have hnewcount := s.encounter_count_le v
    have hadd : a + stride < labels := by
      simp only [List.length_cons, Nat.mul_succ] at hbefore
      omega
    have htailbefore : a + stride + stride * vs.length < labels := by
      simp only [List.length_cons, Nat.mul_succ] at hbefore
      omega
    apply runs_start_le
    unfold vertexScanBody
    wram_step
    · simp at hcond
    · refine runs_seq_assign_le (v := v.val) (by eval_expr) ?_
      refine runs_seq_call_le hk (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨labels, rfl, hlabels, hvalid, hspace, by omega⟩
      · intro count mem1 pos1 hpost
        obtain ⟨hresult, htable, hframe⟩ := hpost
        change count = (s.encounter v).count at hresult
        have hcount1 : count < 2 ^ w := by omega
        have hsource : EndpointsAt mem1 (a + stride) stride vs := by
          intro i hi
          have hindex : a + stride + stride * i < labels := by
            have hmul := Nat.mul_le_mul_left stride (Nat.le_of_lt hi)
            omega
          have hne : a + stride + stride * i ≠ labels + v.val := by omega
          have hf := hframe _ hne
          change mem1 (a + stride + stride * i) = mem (a + stride + stride * i) at hf
          exact hf.trans (htail i hi)
        refine runs_seq_call_le hr (by eval_expr) ?_ ?_ ?_
        · wram_words
        · change ∃ a' stride' labels',
            [a + stride, (v :: vs).length - 1, stride, labels, (s.encounter v).count] =
              [a', vs.length, stride', labels', (s.encounter v).count] ∧
            EndpointsAt mem1 a' stride' vs ∧ LabelsAt mem1 labels' (s.encounter v) ∧
            (s.encounter v).Valid ∧ a' + stride' * vs.length < labels' ∧
            labels' + n < 2 ^ w ∧ (s.encounter v).count + vs.length + 1 < 2 ^ w
          exact ⟨a + stride, stride, labels, by simp only [List.length_cons, Nat.add_sub_cancel],
            hsource, htable, s.encounter_valid hvalid v, htailbefore, hspace, by simp only [List.length_cons] at hcount; omega⟩
        · intro out mem2 pos2 hpost2
          obtain ⟨hout, htable2, hframe2⟩ := hpost2
          change out = ((s.encounter v).scan vs).count at hout
          have houtbound := (s.encounter v).scan_count_le vs
          have houtword : out < 2 ^ w := by simp only [List.length_cons] at hcount; omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · refine ⟨hout, htable2, ?_⟩
            intro x hx
            change x < labels ∨ labels + n ≤ x at hx
            have hf2 := hframe2 x hx
            have hne : x ≠ labels + v.val := by
              rcases hx with hx | hx <;> omega
            exact hf2.trans (hframe x hne)
          · simp only [vertexScanContract, vertexEncounterContract, List.length_cons,
              Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
              argsSize_cons, argsSize_nil]
            omega

/-- The empty scan has a valid zero-table instance whenever that block fits. -/
theorem vertexScan_pre_empty {w n : ℕ} (hn : 1 + n < 2 ^ w) :
    (vertexScanContract w (VertexLabels.empty n) []).pre [0, 0, 0, 1, 0] (fun _ => 0) := by
  refine ⟨0, 0, 1, rfl, ?_, ?_, VertexLabels.empty_valid n, ?_, hn, ?_⟩
  · intro i hi; cases hi
  · intro _; rfl
  · change (0 : ℕ) < 1; exact Nat.zero_lt_succ _
  · change 0 + 0 + 1 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
