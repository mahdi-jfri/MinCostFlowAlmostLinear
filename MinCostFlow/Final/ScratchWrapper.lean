module

public import MinCostFlow.Final.ScratchCanonicalSolver
public import MinCostFlow.Scaling.CanonicalWrapperProgram
import MinCostFlow.Scaling.DeterministicExecution
import WordRAM.Link
import WordRAM.Entry
import WordRAM.Tactic

/-!
# Relocating a solver with its scratch contract

The scaling reduction on page 15 calls the bounded circulation solver
in fresh guest memory. The wrapper preserves the caller's memory below
the heap and copies back the guest's canonical optimal flow.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- A relocated canonical solver body returns the model's fixed output
function. Its body cost is at most `(Q.regBound+6)*T(n,m)`, and it preserves
memory outside the guest region. Input copying and the call wrapper are
accounted for by the enclosing procedure. -/
theorem scratch_relocated_run
    {guestWidth hostWidth h b pos : ℕ} {Q P : Program} {f : ℕ}
    {T S : ℕ → ℕ → ℕ} {ω : ℕ → Bool}
    (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T S))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : ScratchCanonicalInput guestWidth T S J)
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ hostWidth) (hspace : h + 1 + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hfour : 4 ≤ 2 ^ hostWidth) (mem : ℕ → ℕ)
    (hmem : ∀ a < 2 ^ guestWidth, mem (h + 1 + a) = initMem J.solverWords a) :
    ∃ body o st cost, Q.procs[f]? = some body ∧
      Runs hostWidth P ω (relocStmt Q.regBound b body)
        (canonicalHostState Q J guestWidth h pos mem) o st cost ∧
      cost ≤ (Q.regBound + 6) * T J.n J.m ∧
      J.readSolverFlow st.mem (h + 1 + J.solverWords.length) =
        scratchCanonicalSolverAt guestWidth Q f T S hproc J ∧
      (∀ a, a < h + 1 ∨ h + 1 + 2 ^ guestWidth ≤ a → st.mem a = mem a) := by
  obtain ⟨body, o, stQ, costQ, hb, hr, hc, hout⟩ :=
    scratchCanonicalSolverAt_has_run guestWidth Q f T S hproc J hin
  have hnrand := hdet body (List.mem_of_getElem? hb)
  have hrtape := runs_of_deterministic hdet
    (ω' := subBits hostWidth guestWidth pos ω) hnrand hr
  obtain ⟨fuel, hfuel⟩ := hrtape
  have hregs : ∀ r < Q.regBound,
      (canonicalHostState Q J guestWidth h pos mem).regs r =
        (startState [0, J.solverWords.length] (initMem J.solverWords) 0).regs r := by
    intro r hr
    simp only [canonicalHostState, startState, ite_eq_right (by omega : r ≠ Q.regBound),
      ite_eq_right (by omega : r ≠ Q.regBound + 1)]
  have hgregs : ∀ r, (startState [0, J.solverWords.length] (initMem J.solverWords) 0).regs r <
      2 ^ guestWidth := by
    intro r
    rcases r with _ | r
    · exact hin.1 0 (List.mem_cons_self)
    · rcases r with _ | r
      · exact hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
      · simp only [startState, List.getD_cons_succ, List.getD_nil]
        exact Nat.two_pow_pos _
  have hgmem : ∀ a, initMem J.solverWords a < 2 ^ guestWidth := by
    intro a
    simp only [initMem, List.getD_eq_getElem?_getD]
    cases hx : J.solverWords[a]? with
    | none => exact Nat.two_pow_pos _
    | some x => exact hin.words_fit x (List.mem_of_getElem? hx)
  have hbase : (canonicalHostState Q J guestWidth h pos mem).regs Q.regBound = h + 1 := by
    simp only [canonicalHostState, ↓reduceIte]
  have hW : (canonicalHostState Q J guestWidth h pos mem).regs (Q.regBound + 1) = 2 ^ guestWidth := by
    simp only [canonicalHostState, ite_eq_right (by omega : Q.regBound + 1 ≠ Q.regBound), ↓reduceIte]
  have hreloc := Link.runs_relocStmt hmodule hw hspace hfour fuel body
    (startState [0, J.solverWords.length] (initMem J.solverWords) 0)
    (canonicalHostState Q J guestWidth h pos mem) 0 o stQ costQ
    (Link.regBound_le_of_mem (List.mem_of_getElem? hb)) hbase hW hregs hgregs hgmem hmem
    (by simp only [startState, Nat.zero_mul])
    (by simp only [canonicalHostState, Nat.zero_mul, Nat.add_zero]) hfuel
  obtain ⟨stH, costH, _, hrun, hcost, _, _, _, _, _, _, hmemory, hframe, _, _⟩ := hreloc
  refine ⟨body, o, stH, costH, hb, hrun,
    hcost.trans (Nat.mul_le_mul_left _ hc), ?_, hframe⟩
  have hbound := hin.output_fits
  rw [hout]
  funext e
  have he := hmemory (J.solverWords.length + e.val) (by have hh := e.isLt; omega)
  change (stH.mem (h + 1 + J.solverWords.length + e.val) : ℤ) =
    (stQ.mem (J.solverWords.length + e.val) : ℤ)
  rw [Nat.add_assoc, he]

/-- All call arguments fit when the canonical guest input fits and the
fresh guest region ends strictly inside host memory. -/
theorem scratchCallArgs_words {Q : Program} {J : Circulation}
    {guestWidth hostWidth h : ℕ} {T S : ℕ → ℕ → ℕ}
    (hin : ScratchCanonicalInput guestWidth T S J) (hw : guestWidth ≤ hostWidth)
    (hspace : h + 1 + 2 ^ guestWidth < 2 ^ hostWidth) :
    ∀ a ∈ canonicalCallArgs Q J guestWidth h, a < 2 ^ hostWidth := by
  intro a ha
  have hpositive : 0 < 2 ^ guestWidth := Nat.two_pow_pos _
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    have hlen : J.solverWords.length < 2 ^ hostWidth :=
      lt_of_lt_of_le (hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
        (Nat.pow_le_pow_right (by decide) hw)
    rcases r with _ | r
    · simp only [List.getD_cons_zero]; omega
    · rcases r with _ | r
      · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hlen
      · simp only [List.getD_cons_succ, List.getD_nil]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega

/-- A prepared relocated call, before the wrapper copies its output.
The guest region already contains the canonical input followed by zeros. -/
def scratchCallContract (guestWidth : ℕ) (Q : Program) (f : ℕ)
    (T S : ℕ → ℕ → ℕ) (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T S))
    (J : Circulation) (h : ℕ) : Contract where
  pre args mem := args = canonicalCallArgs Q J guestWidth h ∧
    ∀ a < 2 ^ guestWidth, mem (h + 1 + a) = initMem J.solverWords a
  post _ mem _ mem' :=
    J.readSolverFlow mem' (h + 1 + J.solverWords.length) =
      scratchCanonicalSolverAt guestWidth Q f T S hproc J ∧
    ∀ a, a < h + 1 ∨ h + 1 + 2 ^ guestWidth ≤ a → mem' a = mem a
  cost _ _ := (Q.regBound + 6) * T J.n J.m

/-- A body placed at the relocated solver index meets the ordinary call
contract, with exactly the canonical model output and the relocation cost. -/
theorem scratchCall_meetsContract
    {guestWidth hostWidth h b : ℕ} {Q P : Program} {f : ℕ}
    {T S : ℕ → ℕ → ℕ}
    (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T S))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : ScratchCanonicalInput guestWidth T S J)
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ hostWidth) (hspace : h + 1 + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hfour : 4 ≤ 2 ^ hostWidth) :
    MeetsContract hostWidth P (b + 1 + f)
      (scratchCallContract guestWidth Q f T S hproc J h) := by
  intro args mem pos ω _ hpre
  obtain ⟨rfl, hmem⟩ := hpre
  obtain ⟨body, o, st, cost, hb, hr, hc, hout, hframe⟩ :=
    scratch_relocated_run hproc hdet J hin hmodule hw hspace hfour mem hmem
  refine ⟨relocStmt Q.regBound b body, hmodule f body hb, o, st, cost, ?_,
    ⟨hout, hframe⟩, hc⟩
  rwa [startState_canonicalCallArgs]

/-- Exact canonical output at the old heap, with the entire guest region
reserved as scratch. The guest width is supplied through its word bound. -/
def scratchWrapperContract (w guestWidth : ℕ) (Q : Program) (f : ℕ)
    (T S : ℕ → ℕ → ℕ) (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T S))
    (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, J.solverWords.length, 2 ^ guestWidth, h] ∧
      ListAt mem a J.solverWords ∧ a + J.solverWords.length ≤ h)
    (fun args _ mem' => J.readSolverFlow mem' (heapArg args) =
      scratchCanonicalSolverAt guestWidth Q f T S hproc J)
    (fun _ _ => (Q.regBound + 6) * T J.n J.m +
      40 * J.solverWords.length + Q.regBound + 200)
    (fun _ _ => 1 + 2 ^ guestWidth)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 + 2 ^ guestWidth }

/-- The executable wrapper computes the fixed canonical model function,
with exact heap framing and an explicit cost for every call and copy. -/
theorem scratchWrapper_meetsContract
    {guestWidth w b prepare copy entry : ℕ} {Q P : Program} {f : ℕ}
    {T S : ℕ → ℕ → ℕ}
    (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T S))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : ScratchCanonicalInput guestWidth T S J)
    (hentry : P.procs[entry]? =
      some (canonicalWrapperBody Q prepare (b + 1 + f) copy))
    (hprepare : P.HasAt prepare (canonicalPrepareModule prepare))
    (hcopy : P.HasAt copy [copyWords])
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ w) :
    MeetsContract w P entry (scratchWrapperContract w guestWidth Q f T S hproc J) := by
  have hkP := canonicalPrepare_meetsContract (w := w) hprepare guestWidth J
  have hkC := copyWords_meetsContract (w := w) hcopy
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (1 + 2 ^ guestWidth) < 2 ^ w at hspace
  have hsize := J.solverWords_length
  have houtput := hin.output_fits
  have hlen := hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hl : J.solverWords.length < 2 ^ w := by omega
  have hW : 2 ^ guestWidth < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have hbase : heap + 1 < 2 ^ w := by omega
  have hsource : heap + 1 + J.solverWords.length < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hfour : 4 ≤ 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have hmcell : mem (a + 1) = J.m := by
    have hh := hat 1 (by rw [hsize]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ,
      List.getElem_cons_zero] using hh
  have hkS := scratchCall_meetsContract hproc hdet J hin hmodule hw
    (by omega : heap + 1 + 2 ^ guestWidth ≤ 2 ^ w) hfour
  apply runs_start_le
  unfold canonicalWrapperBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [a, J.solverWords.length, 2 ^ guestWidth, heap])
    (by eval_expr) ?_ ?_ ?_
  · exact hwords
  · exact ⟨⟨a, heap, rfl, hat, hend, hlen⟩, hzero, hspace⟩
  · intro finalHeap memP posP hpostP
    obtain ⟨⟨_, _, hframeP, hzeroP, hcanonical⟩, hptr⟩ := hpostP
    change finalHeap = heap + 1 + 2 ^ guestWidth at hptr
    change (∀ x < heap, memP x = mem x) at hframeP
    change ZeroFrom memP finalHeap at hzeroP
    change (∀ i < 2 ^ guestWidth,
      memP (heap + 1 + i) = initMem J.solverWords i) at hcanonical
    have hfinal : finalHeap < 2 ^ w := by omega
    refine runs_seq_assign_le (v := heap + 1) (by eval_expr) ?_
    refine runs_seq_call_le hkS (vs := canonicalCallArgs Q J guestWidth heap) ?_ ?_ ?_ ?_
    · apply canonicalCallExprs_eval
      · simp [startState]
      · simp
      · simp [startState]
      · exact hl
    · exact scratchCallArgs_words hin hw (by omega)
    · exact ⟨rfl, hcanonical⟩
    · intro _ memS posS hpostS
      obtain ⟨hflow, hframeS⟩ := hpostS
      change J.readSolverFlow memS (heap + 1 + J.solverWords.length) =
        scratchCanonicalSolverAt guestWidth Q f T S hproc J at hflow
      change (∀ x, x < heap + 1 ∨ heap + 1 + 2 ^ guestWidth ≤ x →
        memS x = memP x) at hframeS
      refine runs_seq_call_le hkC (vs := [heap + 1 + J.solverWords.length, heap, J.m])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨heap + 1 + J.solverWords.length, heap, J.m, rfl, hone,
          by omega, by omega, Or.inl (by omega)⟩
      · intro _ memC posC hpostC
        obtain ⟨src, dst, len, hargs, _, hcopied, hframeC⟩ := hpostC
        have hs : src = heap + 1 + J.solverWords.length := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 0 0) hargs
          simpa only [List.getD_cons_zero] using hh.symm
        have hd : dst = heap := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 1 0) hargs
          simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
        have hl' : len = J.m := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 2 0) hargs
          simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
        subst src; subst dst; subst len
        change (∀ i < J.m, memC (heap + i) =
          memS (heap + 1 + J.solverWords.length + i)) at hcopied
        change (∀ x, x < heap ∨ heap + J.m ≤ x → memC x = memS x) at hframeC
        refine runs_ret_le (v := finalHeap) (by eval_expr) ?_ ?_
        · change (heap ≤ finalHeap ∧ finalHeap ≤ heap + (1 + 2 ^ guestWidth) ∧
            (∀ x < heap, memC x = mem x) ∧ ZeroFrom memC finalHeap ∧
            J.readSolverFlow memC heap = scratchCanonicalSolverAt guestWidth Q f T S hproc J) ∧
            finalHeap = heap + 1 + 2 ^ guestWidth
          refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, hptr⟩
          · intro x hx
            exact (hframeC x (Or.inl hx)).trans
              ((hframeS x (Or.inl (by omega))).trans (hframeP x hx))
          · intro x hx
            exact (hframeC x (Or.inr (by omega))).trans
              ((hframeS x (Or.inr (by omega))).trans (hzeroP x hx))
          · rw [← hflow]
            funext e
            exact congrArg (fun v : ℕ => (v : ℤ)) (hcopied e.val e.isLt)
        · simp only [scratchWrapperContract, heapContract, canonicalPrepareContract,
            scratchCallContract, copyWordsContract, canonicalCallExprs_size,
            argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
          omega


/-- A relocated canonical solver body returns the model's fixed output
function. Its body cost is at most `(Q.regBound+6)*T(n,m)`, and it preserves
memory outside the guest region. Input copying and the call wrapper are
accounted for by the enclosing procedure. -/
theorem compressed_relocated_run
    {guestWidth hostWidth h b pos : ℕ} {Q P : Program} {f : ℕ}
    {T S : ℕ → ℕ → ℕ} {ω : ℕ → Bool}
    (hproc : MeetsContract guestWidth Q f (compressedSolverContract guestWidth T S))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : CompressedCanonicalInput guestWidth T S J)
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ hostWidth) (hspace : h + 1 + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hfour : 4 ≤ 2 ^ hostWidth) (mem : ℕ → ℕ)
    (hmem : ∀ a < 2 ^ guestWidth, mem (h + 1 + a) = initMem J.solverWords a) :
    ∃ body o st cost, Q.procs[f]? = some body ∧
      Runs hostWidth P ω (relocStmt Q.regBound b body)
        (canonicalHostState Q J guestWidth h pos mem) o st cost ∧
      cost ≤ (Q.regBound + 6) * T J.n J.m ∧
      J.readSolverFlow st.mem (h + 1 + J.solverWords.length) =
        compressedCanonicalSolverAt guestWidth Q f T S hproc J ∧
      (∀ a, a < h + 1 ∨ h + 1 + 2 ^ guestWidth ≤ a → st.mem a = mem a) := by
  obtain ⟨body, o, stQ, costQ, hb, hr, hc, hout⟩ :=
    compressedCanonicalSolverAt_has_run guestWidth Q f T S hproc J hin
  have hnrand := hdet body (List.mem_of_getElem? hb)
  have hrtape := runs_of_deterministic hdet
    (ω' := subBits hostWidth guestWidth pos ω) hnrand hr
  obtain ⟨fuel, hfuel⟩ := hrtape
  have hregs : ∀ r < Q.regBound,
      (canonicalHostState Q J guestWidth h pos mem).regs r =
        (startState [0, J.solverWords.length] (initMem J.solverWords) 0).regs r := by
    intro r hr
    simp only [canonicalHostState, startState, ite_eq_right (by omega : r ≠ Q.regBound),
      ite_eq_right (by omega : r ≠ Q.regBound + 1)]
  have hgregs : ∀ r, (startState [0, J.solverWords.length] (initMem J.solverWords) 0).regs r <
      2 ^ guestWidth := by
    intro r
    rcases r with _ | r
    · exact hin.1 0 (List.mem_cons_self)
    · rcases r with _ | r
      · exact hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
      · simp only [startState, List.getD_cons_succ, List.getD_nil]
        exact Nat.two_pow_pos _
  have hgmem : ∀ a, initMem J.solverWords a < 2 ^ guestWidth := by
    intro a
    simp only [initMem, List.getD_eq_getElem?_getD]
    cases hx : J.solverWords[a]? with
    | none => exact Nat.two_pow_pos _
    | some x => exact hin.toScratch.words_fit x (List.mem_of_getElem? hx)
  have hbase : (canonicalHostState Q J guestWidth h pos mem).regs Q.regBound = h + 1 := by
    simp only [canonicalHostState, ↓reduceIte]
  have hW : (canonicalHostState Q J guestWidth h pos mem).regs (Q.regBound + 1) = 2 ^ guestWidth := by
    simp only [canonicalHostState, ite_eq_right (by omega : Q.regBound + 1 ≠ Q.regBound), ↓reduceIte]
  have hreloc := Link.runs_relocStmt hmodule hw hspace hfour fuel body
    (startState [0, J.solverWords.length] (initMem J.solverWords) 0)
    (canonicalHostState Q J guestWidth h pos mem) 0 o stQ costQ
    (Link.regBound_le_of_mem (List.mem_of_getElem? hb)) hbase hW hregs hgregs hgmem hmem
    (by simp only [startState, Nat.zero_mul])
    (by simp only [canonicalHostState, Nat.zero_mul, Nat.add_zero]) hfuel
  obtain ⟨stH, costH, _, hrun, hcost, _, _, _, _, _, _, hmemory, hframe, _, _⟩ := hreloc
  refine ⟨body, o, stH, costH, hb, hrun,
    hcost.trans (Nat.mul_le_mul_left _ hc), ?_, hframe⟩
  have hbound := hin.toScratch.output_fits
  rw [hout]
  funext e
  have he := hmemory (J.solverWords.length + e.val) (by have hh := e.isLt; omega)
  change (stH.mem (h + 1 + J.solverWords.length + e.val) : ℤ) =
    (stQ.mem (J.solverWords.length + e.val) : ℤ)
  rw [Nat.add_assoc, he]

/-- All call arguments fit when the canonical guest input fits and the
fresh guest region ends strictly inside host memory. -/
theorem compressedCallArgs_words {Q : Program} {J : Circulation}
    {guestWidth hostWidth h : ℕ} {T S : ℕ → ℕ → ℕ}
    (hin : CompressedCanonicalInput guestWidth T S J) (hw : guestWidth ≤ hostWidth)
    (hspace : h + 1 + 2 ^ guestWidth < 2 ^ hostWidth) :
    ∀ a ∈ canonicalCallArgs Q J guestWidth h, a < 2 ^ hostWidth := by
  intro a ha
  have hpositive : 0 < 2 ^ guestWidth := Nat.two_pow_pos _
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    have hlen : J.solverWords.length < 2 ^ hostWidth :=
      lt_of_lt_of_le (hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
        (Nat.pow_le_pow_right (by decide) hw)
    rcases r with _ | r
    · simp only [List.getD_cons_zero]; omega
    · rcases r with _ | r
      · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hlen
      · simp only [List.getD_cons_succ, List.getD_nil]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega

/-- A prepared relocated call, before the wrapper copies its output.
The guest region already contains the canonical input followed by zeros. -/
def compressedCallContract (guestWidth : ℕ) (Q : Program) (f : ℕ)
    (T S : ℕ → ℕ → ℕ) (hproc : MeetsContract guestWidth Q f (compressedSolverContract guestWidth T S))
    (J : Circulation) (h : ℕ) : Contract where
  pre args mem := args = canonicalCallArgs Q J guestWidth h ∧
    ∀ a < 2 ^ guestWidth, mem (h + 1 + a) = initMem J.solverWords a
  post _ mem _ mem' :=
    J.readSolverFlow mem' (h + 1 + J.solverWords.length) =
      compressedCanonicalSolverAt guestWidth Q f T S hproc J ∧
    ∀ a, a < h + 1 ∨ h + 1 + 2 ^ guestWidth ≤ a → mem' a = mem a
  cost _ _ := (Q.regBound + 6) * T J.n J.m

/-- A body placed at the relocated solver index meets the ordinary call
contract, with exactly the canonical model output and the relocation cost. -/
theorem compressedCall_meetsContract
    {guestWidth hostWidth h b : ℕ} {Q P : Program} {f : ℕ}
    {T S : ℕ → ℕ → ℕ}
    (hproc : MeetsContract guestWidth Q f (compressedSolverContract guestWidth T S))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : CompressedCanonicalInput guestWidth T S J)
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ hostWidth) (hspace : h + 1 + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hfour : 4 ≤ 2 ^ hostWidth) :
    MeetsContract hostWidth P (b + 1 + f)
      (compressedCallContract guestWidth Q f T S hproc J h) := by
  intro args mem pos ω _ hpre
  obtain ⟨rfl, hmem⟩ := hpre
  obtain ⟨body, o, st, cost, hb, hr, hc, hout, hframe⟩ :=
    compressed_relocated_run hproc hdet J hin hmodule hw hspace hfour mem hmem
  refine ⟨relocStmt Q.regBound b body, hmodule f body hb, o, st, cost, ?_,
    ⟨hout, hframe⟩, hc⟩
  rwa [startState_canonicalCallArgs]

/-- Exact canonical output at the old heap, with the entire guest region
reserved as scratch. The guest width is supplied through its word bound. -/
def compressedWrapperContract (w guestWidth : ℕ) (Q : Program) (f : ℕ)
    (T S : ℕ → ℕ → ℕ) (hproc : MeetsContract guestWidth Q f (compressedSolverContract guestWidth T S))
    (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, J.solverWords.length, 2 ^ guestWidth, h] ∧
      ListAt mem a J.solverWords ∧ a + J.solverWords.length ≤ h)
    (fun args _ mem' => J.readSolverFlow mem' (heapArg args) =
      compressedCanonicalSolverAt guestWidth Q f T S hproc J)
    (fun _ _ => (Q.regBound + 6) * T J.n J.m +
      40 * J.solverWords.length + Q.regBound + 200)
    (fun _ _ => 1 + 2 ^ guestWidth)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 + 2 ^ guestWidth }

/-- The executable wrapper computes the fixed canonical model function,
with exact heap framing and an explicit cost for every call and copy. -/
theorem compressedWrapper_meetsContract
    {guestWidth w b prepare copy entry : ℕ} {Q P : Program} {f : ℕ}
    {T S : ℕ → ℕ → ℕ}
    (hproc : MeetsContract guestWidth Q f (compressedSolverContract guestWidth T S))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : CompressedCanonicalInput guestWidth T S J)
    (hentry : P.procs[entry]? =
      some (canonicalWrapperBody Q prepare (b + 1 + f) copy))
    (hprepare : P.HasAt prepare (canonicalPrepareModule prepare))
    (hcopy : P.HasAt copy [copyWords])
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ w) :
    MeetsContract w P entry (compressedWrapperContract w guestWidth Q f T S hproc J) := by
  have hkP := canonicalPrepare_meetsContract (w := w) hprepare guestWidth J
  have hkC := copyWords_meetsContract (w := w) hcopy
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (1 + 2 ^ guestWidth) < 2 ^ w at hspace
  have hsize := J.solverWords_length
  have houtput := hin.toScratch.output_fits
  have hlen := hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hl : J.solverWords.length < 2 ^ w := by omega
  have hW : 2 ^ guestWidth < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have hbase : heap + 1 < 2 ^ w := by omega
  have hsource : heap + 1 + J.solverWords.length < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hfour : 4 ≤ 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have hmcell : mem (a + 1) = J.m := by
    have hh := hat 1 (by rw [hsize]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ,
      List.getElem_cons_zero] using hh
  have hkS := compressedCall_meetsContract hproc hdet J hin hmodule hw
    (by omega : heap + 1 + 2 ^ guestWidth ≤ 2 ^ w) hfour
  apply runs_start_le
  unfold canonicalWrapperBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [a, J.solverWords.length, 2 ^ guestWidth, heap])
    (by eval_expr) ?_ ?_ ?_
  · exact hwords
  · exact ⟨⟨a, heap, rfl, hat, hend, hlen⟩, hzero, hspace⟩
  · intro finalHeap memP posP hpostP
    obtain ⟨⟨_, _, hframeP, hzeroP, hcanonical⟩, hptr⟩ := hpostP
    change finalHeap = heap + 1 + 2 ^ guestWidth at hptr
    change (∀ x < heap, memP x = mem x) at hframeP
    change ZeroFrom memP finalHeap at hzeroP
    change (∀ i < 2 ^ guestWidth,
      memP (heap + 1 + i) = initMem J.solverWords i) at hcanonical
    have hfinal : finalHeap < 2 ^ w := by omega
    refine runs_seq_assign_le (v := heap + 1) (by eval_expr) ?_
    refine runs_seq_call_le hkS (vs := canonicalCallArgs Q J guestWidth heap) ?_ ?_ ?_ ?_
    · apply canonicalCallExprs_eval
      · simp [startState]
      · simp
      · simp [startState]
      · exact hl
    · exact compressedCallArgs_words hin hw (by omega)
    · exact ⟨rfl, hcanonical⟩
    · intro _ memS posS hpostS
      obtain ⟨hflow, hframeS⟩ := hpostS
      change J.readSolverFlow memS (heap + 1 + J.solverWords.length) =
        compressedCanonicalSolverAt guestWidth Q f T S hproc J at hflow
      change (∀ x, x < heap + 1 ∨ heap + 1 + 2 ^ guestWidth ≤ x →
        memS x = memP x) at hframeS
      refine runs_seq_call_le hkC (vs := [heap + 1 + J.solverWords.length, heap, J.m])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨heap + 1 + J.solverWords.length, heap, J.m, rfl, hone,
          by omega, by omega, Or.inl (by omega)⟩
      · intro _ memC posC hpostC
        obtain ⟨src, dst, len, hargs, _, hcopied, hframeC⟩ := hpostC
        have hs : src = heap + 1 + J.solverWords.length := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 0 0) hargs
          simpa only [List.getD_cons_zero] using hh.symm
        have hd : dst = heap := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 1 0) hargs
          simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
        have hl' : len = J.m := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 2 0) hargs
          simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
        subst src; subst dst; subst len
        change (∀ i < J.m, memC (heap + i) =
          memS (heap + 1 + J.solverWords.length + i)) at hcopied
        change (∀ x, x < heap ∨ heap + J.m ≤ x → memC x = memS x) at hframeC
        refine runs_ret_le (v := finalHeap) (by eval_expr) ?_ ?_
        · change (heap ≤ finalHeap ∧ finalHeap ≤ heap + (1 + 2 ^ guestWidth) ∧
            (∀ x < heap, memC x = mem x) ∧ ZeroFrom memC finalHeap ∧
            J.readSolverFlow memC heap = compressedCanonicalSolverAt guestWidth Q f T S hproc J) ∧
            finalHeap = heap + 1 + 2 ^ guestWidth
          refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, hptr⟩
          · intro x hx
            exact (hframeC x (Or.inl hx)).trans
              ((hframeS x (Or.inl (by omega))).trans (hframeP x hx))
          · intro x hx
            exact (hframeC x (Or.inr (by omega))).trans
              ((hframeS x (Or.inr (by omega))).trans (hzeroP x hx))
          · rw [← hflow]
            funext e
            exact congrArg (fun v : ℕ => (v : ℤ)) (hcopied e.val e.isLt)
        · simp only [compressedWrapperContract, heapContract, canonicalPrepareContract,
            compressedCallContract, copyWordsContract, canonicalCallExprs_size,
            argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
          omega

end MinCostFlow.Final
