module

public import MinCostFlow.Scaling.VertexScanProgram
import WordRAM.Tactic

/-!
# Replacing stored endpoints by their compressed labels

After endpoint labels have been computed, vertex compression replaces each
endpoint `v` by `label[v]-1`. This in-place strided scan performs that update.
The label block is disjoint from and above the endpoint records. Only the
selected endpoint cells can change. The program has no random instructions
and costs at most `64*length+8`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,length,stride,labels]`. -/
def endpointRemapBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 4 (.load (.reg 0)) ;;
      .assign 5 (.load (.bin .add (.reg 3) (.reg 4))) ;;
      .store (.reg 0) (.bin .sub (.reg 5) (.const 1)) ;;
      .call 6 self [.bin .add (.reg 0) (.reg 2), .bin .sub (.reg 1) (.const 1), .reg 2, .reg 3] ;;
      .ret (.const 0))

/-- The remapping loop occupies one recursive procedure. -/
def endpointRemapModule (b : ℕ) : List Stmt := [endpointRemapBody b]

/-- Exact endpoint values after remapping, and a frame on every other cell. -/
def endpointRemapContract (w : ℕ) {n : ℕ} (s : VertexLabels n) (vs : List (Fin n)) : Contract where
  pre args mem := ∃ a stride labels,
    args = [a, vs.length, stride, labels] ∧ EndpointsAt mem a stride vs ∧ LabelsAt mem labels s ∧
      0 < stride ∧ a + stride * vs.length < labels ∧ labels + n < 2 ^ w ∧
      ∀ v, s.table v < 2 ^ w
  post args mem out mem' := out = 0 ∧
    (∀ i (hi : i < vs.length), mem' (args.getD 0 0 + args.getD 2 0 * i) = s.table (vs[i]'hi) - 1) ∧
    ∀ x, (∀ i < vs.length, x ≠ args.getD 0 0 + args.getD 2 0 * i) → mem' x = mem x
  cost _ _ := 64 * vs.length + 8

/-- Endpoint remapping is deterministic. -/
theorem endpointRemapBody_noRand (b : ℕ) : (endpointRemapBody b).NoRand := by
  simp only [endpointRemapBody, Stmt.NoRand, and_self]

/-- The machine scan replaces each endpoint by its zero-based table label,
keeps all other cells fixed, and has a linear worst-case cost. -/
theorem endpointRemap_meetsContract {w b n : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (endpointRemapModule b)) (vs : List (Fin n)) (s : VertexLabels n) :
    MeetsContract w p b (endpointRemapContract w s vs) := by
  induction vs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, stride, labels, rfl, _, _, _, _, _, _⟩ := hpre
    apply runs_start_le
    unfold endpointRemapBody
    wram_step
    · refine runs_ret_le (by eval_expr) ?_ ?_
      · exact ⟨rfl, (by intro i hi; cases hi), fun _ _ => rfl⟩
      · simp only [endpointRemapContract, List.length_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp only [List.length_nil, eq_self, not_true_eq_false] at hcond
  | cons v vs ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, stride, labels, rfl, hends, hlabels, hstridepos, hbefore, hlabelsEnd, hvalues⟩ := hpre
    obtain ⟨hhead, htail⟩ := (endpointsAt_cons mem a stride v vs).mp hends
    have hvlt := v.isLt
    have ha : a < 2 ^ w := hwords a (by simp)
    have hlenword : (v :: vs).length < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hstride : stride < 2 ^ w := hwords stride (by simp)
    have hlabelsWord : labels < 2 ^ w := hwords labels (by simp)
    have hvword : v.val < 2 ^ w := by omega
    have hloadaddr : labels + v.val < 2 ^ w := by omega
    have hvalue : s.table v < 2 ^ w := hvalues v
    have hlookup : mem (labels + v.val) = s.table v := hlabels v
    have htailend : a + stride + stride * vs.length < labels := by
      simp only [List.length_cons, Nat.mul_succ] at hbefore
      omega
    have hadd : a + stride < 2 ^ w := by omega
    have hsrc : a < labels := by
      simp only [List.length_cons, Nat.mul_succ] at hbefore
      omega
    apply runs_start_le
    unfold endpointRemapBody
    wram_step
    · simp at hcond
    · refine runs_seq_assign_le (v := v.val) (by eval_expr) ?_
      refine runs_seq_assign_le (v := s.table v) (by eval_expr) ?_
      wram_step
      have hnewlabels : LabelsAt (Function.update mem a (s.table v - 1)) labels s := by
        intro u
        rw [Function.update_of_ne (by omega : labels + u.val ≠ a)]
        exact hlabels u
      have hnewends : EndpointsAt (Function.update mem a (s.table v - 1)) (a + stride) stride vs := by
        intro i hi
        rw [Function.update_of_ne (by have hh := Nat.zero_le (stride * i); omega : a + stride + stride * i ≠ a)]
        exact htail i hi
      refine runs_seq_call_le ih (vs := [a + stride, (v :: vs).length - 1, stride, labels]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨a + stride, stride, labels, (by simp only [List.length_cons, Nat.add_sub_cancel]), hnewends, hnewlabels, hstridepos,
          htailend, hlabelsEnd, hvalues⟩
      · intro out mem1 pos1 hpost
        obtain ⟨hout, hnewvalues, hframe⟩ := hpost
        change out = 0 at hout
        have houtword : out < 2 ^ w := by omega
        change (∀ i (hi : i < vs.length), mem1 (a + stride + stride * i) = s.table (vs[i]'hi) - 1) at hnewvalues
        change ∀ x, (∀ i < vs.length, x ≠ a + stride + stride * i) →
          mem1 x = Function.update mem a (s.table v - 1) x at hframe
        refine runs_ret_le (by eval_expr) ?_ ?_
        · refine ⟨rfl, ?_, ?_⟩
          · change ∀ i (hi : i < (v :: vs).length), mem1 (a + stride * i) = s.table ((v :: vs)[i]'hi) - 1
            intro i hi
            cases i with
            | zero =>
              have hf := hframe a (by intro i _; have hh := Nat.zero_le (stride * i); omega)
              simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, Function.update_self] using hf
            | succ i =>
              have hi' : i < vs.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
              have hh := hnewvalues i hi'
              simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hh
          · intro x hx
            change ∀ i < (v :: vs).length, x ≠ a + stride * i at hx
            have hne : x ≠ a := by simpa only [Nat.mul_zero, Nat.add_zero] using hx 0 (by simp)
            have htailne : ∀ i < vs.length, x ≠ a + stride + stride * i := by
              intro i hi
              have hh := hx (i + 1) (by simp only [List.length_cons]; omega)
              simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
            exact (hframe x htailne).trans (Function.update_of_ne hne _ _)
        · simp only [endpointRemapContract, List.length_cons, Expr.size_bin, Expr.size_reg,
            Expr.size_const, Expr.size_load, argsSize_cons, argsSize_nil]
          omega

end MinCostFlow.Scaling.Machine
