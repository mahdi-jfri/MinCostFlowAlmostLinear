module

public import MinCostFlow.Scaling.EndpointLabelsProgram
public import MinCostFlow.Scaling.EndpointRemapProgram
public import MinCostFlow.Scaling.CompressionMemory
public import WordRAM.CopyWords
import WordRAM.Tactic
import WordRAM.Entry

/-!
# The circulation vertex-compression procedure

The procedure reserves the output graph, computes endpoint labels in fresh
memory after it, copies the original records with the shared copy procedure,
and remaps the tail and head tables. It finally writes the new vertex-count
header. The output is exactly `Circulation.compress`, at the old heap.
Labels remain as scratch after the graph. The cost is at most `500*m+500`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,heap]`, with entries for label allocation, copying,
and endpoint remapping supplied by their procedure indices. -/
def compressionBody (labels copy remap : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 3 (.bin .add (.const 2) (.bin .mul (.const 5) (.reg 2))) ;;
  .assign 4 (.bin .add (.reg 1) (.reg 3)) ;;
  .call 5 labels [.reg 0, .reg 4] ;;
  .call 6 copy [.reg 0, .reg 1, .reg 3] ;;
  .call 7 remap [.bin .add (.reg 1) (.const 2), .reg 2, .const 5,
    .bin .add (.reg 4) (.const 2)] ;;
  .call 8 remap [.bin .add (.reg 1) (.const 3), .reg 2, .const 5,
    .bin .add (.reg 4) (.const 2)] ;;
  .store (.reg 1) (.load (.reg 4)) ;;
  .ret (.reg 5)

/-- Compression, three labeling entries, the copy entry, and one remapping entry. -/
def compressionModule (b : ℕ) : List Stmt :=
  [compressionBody (b + 1) (b + 4) (b + 5)] ++ endpointLabelsModule (b + 1) ++
    [copyWords, endpointRemapBody (b + 5)]

/-- The compressed graph starts at the old heap. Label scratch follows it,
and the returned pointer is exactly after that scratch. -/
def compressionContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, h] ∧ ListAt mem a J.solverWords ∧
      a + J.solverWords.length ≤ h ∧ ∀ x ∈ J.solverWords, x < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) J.compress.solverWords)
    (fun _ _ => 500 * J.m + 500) (fun _ _ => J.solverWords.length + J.n + 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + J.solverWords.length + 2 + J.n }

/-- Compression and all its helper procedures have no random instructions. -/
theorem compressionModule_noRand (b : ℕ) : ∀ body ∈ compressionModule b, body.NoRand := by
  intro body hbody
  rcases List.mem_append.mp hbody with h | h
  · rcases List.mem_append.mp h with h | h
    · have he := List.mem_singleton.mp h
      subst body
      simp only [compressionBody, Stmt.NoRand, and_self]
    · exact endpointLabelsModule_noRand _ body h
  · rcases List.mem_cons.mp h with he | h
    · subst body
      simp only [copyWords, forRange, forUp, Stmt.NoRand, and_self]
    · have he := List.mem_singleton.mp h
      subst body
      exact endpointRemapBody_noRand _

/-- The complete compression module computes its round-1 model with explicit
linear cost, exact space, and the shared heap frame. -/
theorem compression_meetsContract {w b : ℕ} {p : Program} (hw : 8 < 2 ^ w)
    (hp : p.HasAt b (compressionModule b)) (J : Circulation) :
    MeetsContract w p b (compressionContract w J) := by
  have hlabels : p.HasAt (b + 1) (endpointLabelsModule (b + 1)) := by
    intro i hi
    have h := hp (i + 1) (by
      change i + 1 < 6
      change i < 3 at hi
      omega)
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
    rcases hi3 with rfl | rfl | rfl <;>
      simpa only [compressionModule, endpointLabelsModule, vertexScanModule,
        List.singleton_append, List.cons_append, List.nil_append, List.getElem_cons_succ,
        List.getElem_cons_zero, Nat.add_assoc] using h
  have hcopy : p.procs[b + 4]? = some copyWords := by
    have h := hp 4 (by change 4 < 6; decide)
    simpa only [compressionModule, endpointLabelsModule, vertexScanModule,
      List.singleton_append, List.cons_append, List.nil_append, List.getElem_cons_succ,
      List.getElem_cons_zero] using h
  have hremap : p.HasAt (b + 5) (endpointRemapModule (b + 5)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    have h := hp 5 (by change 5 < 6; decide)
    simpa only [compressionModule, endpointLabelsModule, vertexScanModule, endpointRemapModule,
      List.singleton_append, List.cons_append, List.nil_append, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using h
  have hkL := endpointLabels_meetsContract hw hlabels J
  have hcopyModule : p.HasAt (b + 4) [copyWords] := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [Nat.add_zero, List.getElem_cons_zero] using hcopy
  have hkC := copyWords_meetsContract (w := w) hcopyModule
  have hkT := endpointRemap_meetsContract (by omega : 1 < 2 ^ w) hremap (List.ofFn J.tail) J.endpointLabels
  have hkH := endpointRemap_meetsContract (by omega : 1 < 2 ^ w) hremap (List.ofFn J.head) J.endpointLabels
  have hentry : p.procs[b]? = some (compressionBody (b + 1) (b + 4) (b + 5)) := by
    have hh := hp 0 (by change 0 < 6; decide)
    simpa only [compressionModule, endpointLabelsModule, vertexScanModule,
      List.singleton_append, List.cons_append, List.nil_append, List.getElem_cons_zero, Nat.add_zero] using hh
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hinputend, hinputwords⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (J.solverWords.length + J.n + 2) < 2 ^ w at hspace
  have ha : a < 2 ^ w := hwords a (by simp)
  have hhword : heap < 2 ^ w := hwords heap (by simp)
  have hsize := J.solverWords_length
  have hm : mem (a + 1) = J.m := by
    have hh := hat 1 (by simp only [Circulation.solverWords, List.length_cons]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using hh
  have hmword : J.m < 2 ^ w := by omega
  have hlenword : J.solverWords.length < 2 ^ w := by omega
  have h5m : 5 * J.m < 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have hout2 : heap + 2 < 2 ^ w := by omega
  have hout3 : heap + 3 < 2 ^ w := by omega
  have hscratch : heap + J.solverWords.length < 2 ^ w := by omega
  have hlabela : heap + J.solverWords.length + 2 < 2 ^ w := by omega
  have hlabelend : heap + J.solverWords.length + 2 + J.n < 2 ^ w := by omega
  have hcounts := J.endpointLabels_count_le
  have hlabelvalues : ∀ v, J.endpointLabels.table v < 2 ^ w := by
    intro v
    have hh := J.endpointLabels_valid.1 v
    omega
  apply runs_start_le
  unfold compressionBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.solverWords.length) (by rw [hsize]; eval_expr) ?_
  wram_step
  refine runs_seq_call_le hkL (by eval_expr) ?_ ?_ ?_
  · wram_words
  · change (∃ a' h', [a, heap + J.solverWords.length] = [a', h'] ∧
        ListAt mem a' J.solverWords ∧ a' + J.solverWords.length ≤ h' ∧
        ∀ x ∈ J.solverWords, x < 2 ^ w) ∧
      ZeroFrom mem (heap + J.solverWords.length) ∧
      heap + J.solverWords.length + (J.n + 2) < 2 ^ w
    exact ⟨⟨a, heap + J.solverWords.length, rfl, hat, by omega, hinputwords⟩,
      (fun x hx => hzero x (by omega)), by omega⟩
  · intro finalHeap memL posL hpostL
    obtain ⟨⟨_, _, hframeL, hzeroL, hcountL, htableL⟩, hptrL⟩ := hpostL
    change finalHeap = heap + J.solverWords.length + 2 + J.n at hptrL
    change (∀ x < heap + J.solverWords.length, memL x = mem x) at hframeL
    change ZeroFrom memL finalHeap at hzeroL
    change memL (heap + J.solverWords.length) = J.endpointLabels.count at hcountL
    change LabelsAt memL (heap + J.solverWords.length + 2) J.endpointLabels at htableL
    have hfinalword : finalHeap < 2 ^ w := by omega
    have hatL : ListAt memL a J.solverWords := by
      intro i hi
      exact (hframeL _ (by omega)).trans (hat i hi)
    refine runs_seq_call_le hkC (vs := [a, heap, J.solverWords.length]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨a, heap, J.solverWords.length, rfl, by omega, by omega, by omega, Or.inr hinputend⟩
    · intro copied memC posC hpostC
      obtain ⟨src, dst, len, hargs, _, hcwords, hframeC⟩ := hpostC
      have hsrc : src = a := by have hh := congrArg (fun xs : List ℕ => xs.getD 0 0) hargs; simpa using hh.symm
      have hdst : dst = heap := by have hh := congrArg (fun xs : List ℕ => xs.getD 1 0) hargs; simpa using hh.symm
      have hlen : len = J.solverWords.length := by have hh := congrArg (fun xs : List ℕ => xs.getD 2 0) hargs; simpa using hh.symm
      subst src; subst dst; subst len
      have hcopied := copyWords_listAt hatL rfl hcwords
      have htableC : LabelsAt memC (heap + J.solverWords.length + 2) J.endpointLabels := by
        intro v
        exact (hframeC _ (Or.inr (by omega))).trans (htableL v)
      have ht := solver_tails_at J memC heap hcopied
      have hh := solver_heads_at J memC heap hcopied
      refine runs_seq_call_le hkT (vs := [heap + 2, J.m, 5, heap + J.solverWords.length + 2]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨heap + 2, 5, heap + J.solverWords.length + 2, by simp only [List.length_ofFn],
          ht, htableC, by decide, by simp only [List.length_ofFn]; omega, hlabelend, hlabelvalues⟩
      · intro _ memT posT hpostT
        obtain ⟨_, htvalues, htframe⟩ := hpostT
        change (∀ i (hi : i < (List.ofFn J.tail).length), memT (heap + 2 + 5 * i) =
          J.endpointLabels.table ((List.ofFn J.tail)[i]'hi) - 1) at htvalues
        change (∀ x, (∀ i < (List.ofFn J.tail).length, x ≠ heap + 2 + 5 * i) → memT x = memC x) at htframe
        have htableT : LabelsAt memT (heap + J.solverWords.length + 2) J.endpointLabels := by
          intro v
          have hf := htframe (heap + J.solverWords.length + 2 + v.val)
            (by intro i hi; simp only [List.length_ofFn] at hi; omega)
          exact hf.trans (htableC v)
        have hheadsT : EndpointsAt memT (heap + 3) 5 (List.ofFn J.head) := by
          intro i hi
          exact (htframe (heap + 3 + 5 * i) (by intro k _; omega)).trans (hh i hi)
        refine runs_seq_call_le hkH (vs := [heap + 3, J.m, 5, heap + J.solverWords.length + 2]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨heap + 3, 5, heap + J.solverWords.length + 2, by simp only [List.length_ofFn],
            hheadsT, htableT, by decide, by simp only [List.length_ofFn]; omega, hlabelend, hlabelvalues⟩
        · intro _ memH posH hpostH
          obtain ⟨_, hhvalues, hhframe⟩ := hpostH
          change (∀ i (hi : i < (List.ofFn J.head).length), memH (heap + 3 + 5 * i) =
            J.endpointLabels.table ((List.ofFn J.head)[i]'hi) - 1) at hhvalues
          change (∀ x, (∀ i < (List.ofFn J.head).length, x ≠ heap + 3 + 5 * i) → memH x = memT x) at hhframe
          have houtside : ∀ x, x < heap ∨ heap + J.solverWords.length ≤ x → memH x = memL x := by
            intro x hx
            have hht := hhframe x (by intro i hi; simp only [List.length_ofFn] at hi; rcases hx with hx | hx <;> omega)
            have htt := htframe x (by intro i hi; simp only [List.length_ofFn] at hi; rcases hx with hx | hx <;> omega)
            exact hht.trans (htt.trans (hframeC x hx))
          have hcountH : memH (heap + J.solverWords.length) = J.endpointLabels.count :=
            (houtside _ (Or.inr le_rfl)).trans hcountL
          have hcountword : J.endpointLabels.count < 2 ^ w := by omega
          refine runs_seq_store_le (by eval_expr) (v := J.endpointLabels.count) (by eval_expr) ?_
          refine runs_ret_le (v := finalHeap) (by eval_expr) ?_ ?_
          · change (heap ≤ finalHeap ∧ finalHeap ≤ heap + (J.solverWords.length + J.n + 2) ∧
              (∀ x < heap, Function.update memH heap J.endpointLabels.count x = mem x) ∧
              ZeroFrom (Function.update memH heap J.endpointLabels.count) finalHeap ∧
              ListAt (Function.update memH heap J.endpointLabels.count) heap J.compress.solverWords) ∧
              finalHeap = heap + J.solverWords.length + 2 + J.n
            refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, hptrL⟩
            · intro x hx
              rw [Function.update_of_ne (by omega : x ≠ heap)]
              exact (houtside x (Or.inl hx)).trans (hframeL x (by omega))
            · intro x hx
              rw [Function.update_of_ne (by omega : x ≠ heap)]
              exact (houtside x (Or.inr (by omega))).trans (hzeroL x hx)
            · apply compressed_solverWords_at J heap memC memT memH hcopied
              · intro e
                have hh := htvalues e.val (by simpa only [List.length_ofFn] using e.isLt)
                have he : (List.ofFn J.tail)[e.val] = J.tail e := by
                  rw [List.getElem_ofFn]
                rw [he] at hh
                exact hh
              · intro x hx
                apply htframe x
                intro i hi
                exact hx ⟨i, by simpa only [List.length_ofFn] using hi⟩
              · intro e
                have hh := hhvalues e.val (by simpa only [List.length_ofFn] using e.isLt)
                have he : (List.ofFn J.head)[e.val] = J.head e := by
                  rw [List.getElem_ofFn]
                rw [he] at hh
                exact hh
              · intro x hx
                apply hhframe x
                intro i hi
                exact hx ⟨i, by simpa only [List.length_ofFn] using hi⟩
          · simp only [compressionContract, heapContract, endpointLabelsContract,
              endpointRemapContract, copyWordsContract, List.length_ofFn,
              Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load, argsSize_cons, argsSize_nil]
            omega

/-- A canonical input and fresh heap satisfy every compression precondition
at multiplier two of the circulation encoding, including the empty graph. -/
theorem compression_pre_canonical (J : Circulation) :
    let w := wordSize 2 J.solverWords
    8 < 2 ^ w ∧ (∀ x ∈ [0, J.solverWords.length], x < 2 ^ w) ∧
      (compressionContract w J).pre [0, J.solverWords.length] (initMem J.solverWords) := by
  have hmax : J.n ≤ J.solverWords.foldr max 0 := by
    change J.n ≤ max J.n _
    exact le_max_left _ _
  have hlen : 2 ≤ J.solverWords.length := by rw [J.solverWords_length]; omega
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  have hB : 4 ≤ B := by dsimp only [B]; omega
  have hp := pow_lt_two_pow_wordSize (by decide : 1 ≤ 2) J.solverWords
  change B ^ 2 < 2 ^ wordSize 2 J.solverWords at hp
  have hpow : 2 * B ≤ B ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right B (by omega : 2 ≤ B)
  have h16 : 16 ≤ B ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul hB hB
  have hsmall : J.solverWords.length + (J.solverWords.length + J.n + 2) ≤ 2 * B := by
    dsimp only [B]
    omega
  have hspace : J.solverWords.length + (J.solverWords.length + J.n + 2) <
      2 ^ wordSize 2 J.solverWords := lt_of_le_of_lt (hsmall.trans hpow) hp
  refine ⟨by omega, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  · refine ⟨⟨0, J.solverWords.length, rfl, listAt_initMem J.solverWords,
      (by omega), ?_⟩, zeroFrom_initMem J.solverWords, hspace⟩
    intro x hx
    exact lt_two_pow_wordSize_of_mem (by decide) hx

end MinCostFlow.Scaling.Machine
