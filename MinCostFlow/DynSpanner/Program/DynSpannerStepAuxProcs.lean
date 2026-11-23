module

public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.DynSpanner.Program.EmbLayouts
public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
import WordRAM.Tactic

/-!
# Small Step Utility Procedures (`DynSpannerStepAuxProcs`)

Provides six short deterministic Word-RAM utility procedures (`stepAuxProcs`, length `6`) shared
by the `j > 0` step, the `j = 0` restart step, and the batch update loop:

* `dsUpdateLenStmt` (`stepAuxIdxUpdateLen = 0`): returns the word length of an encoded update
  record at `updPtr` in `O(1)` time.
* `dsClearSBitStmt` (`stepAuxIdxClearSBit = 1`): clears `sBit[v] := 0` for each vertex `v` in a
  list of length `len` in `O(len + 1)` time.
* `dsSumWalkLensStmt` (`stepAuxIdxSumWalkLens = 2`): sums `mem[mem[wpPtr + k]]` over `k < len`
  in `O(len + 1)` time.
* `dsSumRangeStmt` (`stepAuxIdxSumRange = 3`): sums `mem[base + i]` for `lo ≤ i < hi` in
  `O(hi - lo + 1)` time.
* `dsCopyWordsStmt` (`stepAuxIdxCopyWords = 4`): copies `n` words from `[src, src + n)` to
  `[dst, dst + n)` in `O(n + 1)` time.
* `dsCopyDelInsStmt` (`stepAuxIdxCopyDelIns = 5`): copies `count` delete/insert records (tag `0`
  has `4` words, tag `1` has `2` words) from `src` to `dst`, returning the total word count in
  `O(words + 1)` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices -/

def stepAuxIdxUpdateLen : ℕ := 0
def stepAuxIdxClearSBit : ℕ := 1
def stepAuxIdxSumWalkLens : ℕ := 2
def stepAuxIdxSumRange : ℕ := 3
def stepAuxIdxCopyWords : ℕ := 4
def stepAuxIdxCopyDelIns : ℕ := 5

/-! ## Word-RAM statement bodies -/

/-- `args = [updPtr]`: returns the word length of an `UpdateAt` record (`0 => 4`, `1 => 2`,
`2/3 => 5 + kt + kh`). -/
def dsUpdateLenStmt : Stmt :=
  .assign 1 (.load (.reg 0)) ;;
  .cond (.bin .eq (.reg 1) (.const 0))
    (.ret (.const 4))
    (.cond (.bin .eq (.reg 1) (.const 1))
      (.ret (.const 2))
      (.ret (.bin .add (.const 5)
        (.bin .add (.load (.bin .add (.reg 0) (.const 3)))
          (.load (.bin .add (.reg 0) (.const 4)))))))

/-- `args = [sBitPtr, listPtr, len]`: sets `mem[sBitPtr + mem[listPtr + k]] := 0` for `k < len`. -/
def dsClearSBitStmt : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
     .store (.bin .add (.reg 0) (.reg 4)) (.const 0)) ;;
  .ret (.const 0)

/-- `args = [wpPtr, len]`: returns `∑_{k < len} mem[mem[wpPtr + k]]`. -/
def dsSumWalkLensStmt : Stmt :=
  .assign 2 (.const 0) ;;
  forRange 3 (.const 0) (.reg 1)
    (.assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
     .assign 2 (.bin .add (.reg 2) (.load (.reg 4)))) ;;
  .ret (.reg 2)

/-- `args = [base, lo, hi]`: returns `∑_{i ∈ [lo, hi)} mem[base + i]`. -/
def dsSumRangeStmt : Stmt :=
  .assign 3 (.const 0) ;;
  forRange 4 (.reg 1) (.reg 2)
    (.assign 3 (.bin .add (.reg 3) (.load (.bin .add (.reg 0) (.reg 4))))) ;;
  .ret (.reg 3)

/-- `args = [src, dst, n]`: copies `n` words from `src` to `dst`, returning `n`. -/
def dsCopyWordsStmt : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))) ;;
  .ret (.reg 2)

/-- `args = [src, dst, count]`: copies `count` delete/insert update records from `src` to `dst`,
returning the total number of words copied. -/
def dsCopyDelInsStmt : Stmt :=
  .assign 3 (.const 0) ;;
  forRange 4 (.const 0) (.reg 2)
    (.assign 5 (.load (.bin .add (.reg 0) (.reg 3))) ;;
     .cond (.bin .eq (.reg 5) (.const 1))
       (.store (.bin .add (.reg 1) (.reg 3)) (.const 1) ;;
        .store (.bin .add (.reg 1) (.bin .add (.reg 3) (.const 1)))
          (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.const 1)))) ;;
        .assign 3 (.bin .add (.reg 3) (.const 2)))
       (.store (.bin .add (.reg 1) (.reg 3)) (.const 0) ;;
        .store (.bin .add (.reg 1) (.bin .add (.reg 3) (.const 1)))
          (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.const 1)))) ;;
        .store (.bin .add (.reg 1) (.bin .add (.reg 3) (.const 2)))
          (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.const 2)))) ;;
        .store (.bin .add (.reg 1) (.bin .add (.reg 3) (.const 3)))
          (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.const 3)))) ;;
        .assign 3 (.bin .add (.reg 3) (.const 4)))) ;;
  .ret (.reg 3)

/-- Utility module (`6` deterministic procedures). -/
def stepAuxProcs : List Stmt :=
  [dsUpdateLenStmt, dsClearSBitStmt, dsSumWalkLensStmt, dsSumRangeStmt, dsCopyWordsStmt,
    dsCopyDelInsStmt]

lemma stepAuxProcs_length : stepAuxProcs.length = 6 := rfl

lemma stepAuxProcs_noRand : ∀ s ∈ stepAuxProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Pure helpers and contracts -/

/-- Whether an update is a deletion or an insertion. -/
def isDelOrIns : Update → Prop
  | .delete _ => True
  | .insert _ _ _ => True
  | .split _ _ _ _ => False

/-- Word length of a delete/insert update record (`2` for delete, `4` for insert). -/
def delInsWordLen : Update → ℕ
  | .delete _ => 2
  | .insert _ _ _ => 4
  | .split _ _ _ _ => 0

/-- Total word length of a list of delete/insert update records. -/
def delInsWords (us : List Update) : ℕ :=
  (us.map delInsWordLen).sum

lemma BatchBodyAt.delIns_words {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {us : List Update} {tot : ℕ}
    (hB : BatchBodyAt mem a G us tot) (hdi : ∀ u ∈ us, isDelOrIns u) :
    tot = delInsWords us := by
  induction us generalizing a G tot with
  | nil => exact hB
  | cons u us ih =>
    rcases hB with ⟨len, hle, hu, hrest⟩
    have hu_di := hdi u (List.mem_cons_self)
    have hrest_eq := ih hrest (fun x hx => hdi x (List.mem_cons_of_mem u hx))
    cases u with
    | delete e =>
      rcases hu with ⟨rfl, _⟩
      simp only [delInsWords, List.map_cons, List.sum_cons, delInsWordLen] at hrest_eq ⊢
      omega
    | insert e x y =>
      rcases hu with ⟨rfl, _⟩
      simp only [delInsWords, List.map_cons, List.sum_cons, delInsWordLen] at hrest_eq ⊢
      omega
    | split _ _ _ _ => exact hu_di.elim

lemma BatchBodyAt.append {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {u₁ u₂ : List Update} {w₁ w₂ : ℕ}
    (h1 : BatchBodyAt mem a G u₁ w₁)
    (h2 : BatchBodyAt mem (a + w₁) (G.applyBatch u₁) u₂ w₂) :
    BatchBodyAt mem a G (u₁ ++ u₂) (w₁ + w₂) := by
  induction u₁ generalizing a G w₁ with
  | nil =>
    have hw : w₁ = 0 := h1
    subst hw
    simpa [MGraph.applyBatch] using h2
  | cons u us ih =>
    rcases h1 with ⟨len, hle, hu, hrest⟩
    refine ⟨len, by omega, hu, ?_⟩
    rw [show w₁ + w₂ - len = (w₁ - len) + w₂ by omega]
    refine ih hrest ?_
    simpa [MGraph.applyBatch, show a + len + (w₁ - len) = a + w₁ by omega] using h2

lemma UpdateAt.copy {mem mem' : ℕ → ℕ} {a b : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (h : UpdateAt mem a G u len) (hag : ∀ i < len, mem' (b + i) = mem (a + i)) :
    UpdateAt mem' b G u len := by
  cases u with
  | insert e x y =>
    rcases h with ⟨rfl, hL⟩
    refine ⟨rfl, fun i hi => (hag i hi).trans (hL i hi)⟩
  | delete e =>
    rcases h with ⟨rfl, hL⟩
    refine ⟨rfl, fun i hi => (hag i hi).trans (hL i hi)⟩
  | split v v' St Sh =>
    rcases h with ⟨Lt, Lh, h1, h2, h3, h4, hlen, hL⟩ | ⟨Lt, Lh, h1, h2, h3, h4, hlen, hL⟩
    · left
      refine ⟨Lt, Lh, h1, h2, h3, h4, hlen, fun i hi => ?_⟩
      have hi' : i < len := by simp [hlen] at hi ⊢; omega
      exact (hag i hi').trans (hL i hi)
    · right
      refine ⟨Lt, Lh, h1, h2, h3, h4, hlen, fun i hi => ?_⟩
      have hi' : i < len := by simp [hlen] at hi ⊢; omega
      exact (hag i hi').trans (hL i hi)

lemma BatchBodyAt.copy {mem mem' : ℕ → ℕ} {a b : ℕ} {G : MGraph} {us : List Update} {tot : ℕ}
    (h : BatchBodyAt mem a G us tot) (hag : ∀ i < tot, mem' (b + i) = mem (a + i)) :
    BatchBodyAt mem' b G us tot := by
  induction us generalizing a b G tot with
  | nil => exact h
  | cons u us ih =>
    rcases h with ⟨len, hle, hu, hrest⟩
    refine ⟨len, hle, hu.copy (fun i hi => hag i (by omega)), ih hrest fun i hi => ?_⟩
    simpa [Nat.add_assoc] using hag (len + i) (by omega)

/-- Contract for `dsUpdateLenStmt` (`[updPtr]`). -/
def dsUpdateLenContract (w : ℕ) (G : MGraph) (u : Update) (len : ℕ) : Contract where
  pre args mem := ∃ updPtr,
    args = [updPtr] ∧ 16 ≤ 2 ^ w ∧ updPtr + len < 2 ^ w ∧ UpdateAt mem updPtr G u len
  post _ mem ret mem' := ret = len ∧ mem' = mem
  cost _ _ := 35

/-- Contract for `dsClearSBitStmt` (`[sBitPtr, listPtr, len]`). -/
def dsClearSBitContract (w vCap : ℕ) (vs : List ℕ) : Contract where
  pre args mem := ∃ sBitPtr listPtr,
    args = [sBitPtr, listPtr, vs.length] ∧ 16 ≤ 2 ^ w ∧
    sBitPtr + vCap < 2 ^ w ∧ listPtr + vs.length < 2 ^ w ∧
    IvlDisj sBitPtr vCap listPtr vs.length ∧
    ListAt mem listPtr vs ∧ (∀ v ∈ vs, v < vCap)
  post args mem ret mem' := ∃ sBitPtr listPtr,
    args = [sBitPtr, listPtr, vs.length] ∧ ret = 0 ∧
    (∀ v ∈ vs, mem' (sBitPtr + v) = 0) ∧
    ∀ addr, (∀ v ∈ vs, addr ≠ sBitPtr + v) → mem' addr = mem addr
  cost _ _ := 35 * vs.length + 25

/-- Contract for `dsSumWalkLensStmt` (`[wpPtr, len]`). -/
def dsSumWalkLensContract (w : ℕ) (es : List ℕ) (emb : MinCostFlow.Embedding) : Contract where
  pre args mem := ∃ wpPtr,
    args = [wpPtr, es.length] ∧ 16 ≤ 2 ^ w ∧ wpPtr + es.length < 2 ^ w ∧
    (es.map fun e => (emb e).length).sum < 2 ^ w ∧
    ∀ k (hk : k < es.length), MWalkAt mem (mem (wpPtr + k)) (emb (es[k]'hk)) ∧
      mem (wpPtr + k) < 2 ^ w
  post _ mem ret mem' := ret = (es.map fun e => (emb e).length).sum ∧ mem' = mem
  cost _ _ := 35 * es.length + 25

/-- Contract for `dsSumRangeStmt` (`[base, lo, hi]`). -/
def dsSumRangeContract (w base lo hi : ℕ) : Contract where
  pre args mem :=
    args = [base, lo, hi] ∧ 16 ≤ 2 ^ w ∧ lo ≤ hi ∧ base + hi < 2 ^ w ∧
    ((List.range (hi - lo)).map fun k => mem (base + (lo + k))).sum < 2 ^ w
  post _ mem ret mem' :=
    ret = ((List.range (hi - lo)).map fun k => mem (base + (lo + k))).sum ∧ mem' = mem
  cost _ _ := 30 * (hi - lo) + 25

/-- Contract for `dsCopyWordsStmt` (`[src, dst, n]`). -/
def dsCopyWordsContract (w n : ℕ) : Contract where
  pre args _mem := ∃ src dst,
    args = [src, dst, n] ∧ 16 ≤ 2 ^ w ∧ src + n < 2 ^ w ∧ dst + n < 2 ^ w ∧
    IvlDisj src n dst n
  post args mem ret mem' := ∃ src dst,
    args = [src, dst, n] ∧ ret = n ∧
    (∀ i < n, mem' (dst + i) = mem (src + i)) ∧
    ∀ addr, (addr < dst ∨ dst + n ≤ addr) → mem' addr = mem addr
  cost _ _ := 30 * n + 25

/-- Contract for `dsCopyDelInsStmt` (`[src, dst, count]`). -/
def dsCopyDelInsContract (w : ℕ) (G : MGraph) (us : List Update) (tot : ℕ) : Contract where
  pre args mem := ∃ src dst,
    args = [src, dst, us.length] ∧ 16 ≤ 2 ^ w ∧ src + tot < 2 ^ w ∧ dst + tot < 2 ^ w ∧
    IvlDisj src tot dst tot ∧ BatchBodyAt mem src G us tot ∧ (∀ u ∈ us, isDelOrIns u)
  post args mem ret mem' := ∃ src dst,
    args = [src, dst, us.length] ∧ ret = tot ∧
    (∀ i < tot, mem' (dst + i) = mem (src + i)) ∧
    ∀ addr, (addr < dst ∨ dst + tot ≤ addr) → mem' addr = mem addr
  cost _ _ := 95 * us.length + 25

end

/-! ## Contract proofs -/

public section

/-- `dsUpdateLenStmt` meets `dsUpdateLenContract`. -/
theorem dsUpdateLen_meetsContract {w : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    {p : Program} {bA : ℕ} (hpA : p.HasAt bA stepAuxProcs) :
    MeetsContract w p (bA + stepAuxIdxUpdateLen) (dsUpdateLenContract w G u len) := by
  refine meetsContract_of_runs
    (hpA.get (i := stepAuxIdxUpdateLen) (by simp [stepAuxProcs, stepAuxIdxUpdateLen])) ?_
  rintro args mem pos ω _ ⟨updPtr, rfl, hw16, hub, hu⟩
  simp only [stepAuxProcs, stepAuxIdxUpdateLen, List.getElem_cons_zero]
  dsimp only [dsUpdateLenStmt]
  refine runs_start_le ?_
  cases u with
  | insert e x y =>
    rcases hu with ⟨rfl, hL⟩
    have h0 : mem updPtr = 0 := by simpa using hL 0 (by simp)
    refine runs_seq_assign_le (v := 0) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) h0) ?_
    refine runs_cond_le (v := if (0 : ℕ) = 0 then 1 else 0)
      (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := 0) (by simp)) (Expr.eval_const (by omega)) (by omega))
      (fun _ => ?_) (fun h => by simp at h)
    refine runs_ret_le (v := 4) (Expr.eval_const (by omega)) ⟨rfl, rfl⟩ ?_
    simp [Expr.size, dsUpdateLenContract]
  | delete e =>
    rcases hu with ⟨rfl, hL⟩
    have h0 : mem updPtr = 1 := by simpa using hL 0 (by simp)
    refine runs_seq_assign_le (v := 1) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) h0) ?_
    refine runs_cond_le (v := if (1 : ℕ) = 0 then 1 else 0)
      (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := 1) (by simp)) (Expr.eval_const (by omega)) (by omega))
      (fun h => by simp at h) (fun _ => ?_)
    refine runs_cond_le (v := if (1 : ℕ) = 1 then 1 else 0)
      (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := 1) (by simp)) (Expr.eval_const (by omega)) (by omega))
      (fun _ => ?_) (fun h => by simp at h)
    refine runs_ret_le (v := 2) (Expr.eval_const (by omega)) ⟨rfl, rfl⟩ ?_
    simp [Expr.size, dsUpdateLenContract]
  | split v v' St Sh =>
    have hsplit : ∃ tag Lt Lh, (tag = 2 ∨ tag = 3) ∧ len = 5 + Lt.length + Lh.length ∧
        ListAt mem updPtr ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) := by
      rcases hu with ⟨Lt, Lh, _, _, _, _, hlen, hL⟩ | ⟨Lt, Lh, _, _, _, _, hlen, hL⟩
      · exact ⟨2, Lt, Lh, Or.inl rfl, hlen, hL⟩
      · exact ⟨3, Lt, Lh, Or.inr rfl, hlen, hL⟩
    rcases hsplit with ⟨tag, Lt, Lh, htag, hlen, hL⟩
    have h0 : mem updPtr = tag := by simpa using hL 0 (by simp)
    have h3 : mem (updPtr + 3) = Lt.length := by simpa using hL 3 (by simp)
    have h4 : mem (updPtr + 4) = Lh.length := by simpa using hL 4 (by simp)
    have hne0 : tag ≠ 0 := by rcases htag with rfl | rfl <;> omega
    have hne1 : tag ≠ 1 := by rcases htag with rfl | rfl <;> omega
    refine runs_seq_assign_le (v := tag) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) h0) ?_
    refine runs_cond_le (v := if tag = 0 then 1 else 0)
      (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := tag) (by simp)) (Expr.eval_const (by omega)) (by omega))
      (fun h => by simp [hne0] at h) (fun _ => ?_)
    refine runs_cond_le (v := if tag = 1 then 1 else 0)
      (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := tag) (by simp)) (Expr.eval_const (by omega)) (by omega))
      (fun h => by simp [hne1] at h) (fun _ => ?_)
    refine runs_ret_le (v := 5 + (Lt.length + Lh.length)) ?_ ⟨by simp [Outcome.value]; omega, rfl⟩ ?_
    · exact Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_add
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
            (Expr.eval_const (by omega)) (by omega)) h3)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
            (Expr.eval_const (by omega)) (by omega)) h4)
          (by omega))
        (by omega)
    · simp [Expr.size, dsUpdateLenContract]

/-- `dsClearSBitStmt` meets `dsClearSBitContract`. -/
theorem dsClearSBit_meetsContract {w vCap : ℕ} {vs : List ℕ}
    {p : Program} {bA : ℕ} (hpA : p.HasAt bA stepAuxProcs) :
    MeetsContract w p (bA + stepAuxIdxClearSBit) (dsClearSBitContract w vCap vs) := by
  refine meetsContract_of_runs
    (hpA.get (i := stepAuxIdxClearSBit) (by simp [stepAuxProcs, stepAuxIdxClearSBit])) ?_
  rintro args mem pos ω _ ⟨sBitPtr, listPtr, rfl, hw16, hsB, hlB, hdisj, hL, hvs⟩
  simp only [stepAuxProcs, stepAuxIdxClearSBit, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsClearSBitStmt]
  set Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = sBitPtr ∧ st.regs 1 = listPtr ∧ st.regs 2 = vs.length ∧ st.regs 3 = k ∧
    (∀ j < k, ∀ (hj : j < vs.length), st.mem (sBitPtr + vs[j]'hj) = 0) ∧
    ∀ addr, (∀ v ∈ vs, addr ≠ sBitPtr + v) → st.mem addr = mem addr
  have hloop : Triple w p (fun st => Inv 0 { st with regs := Function.update st.regs 3 0 })
      (forRange 3 (.const 0) (.reg 2)
        (.assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
         .store (.bin .add (.reg 0) (.reg 4)) (.const 0)))
      (normalPost (Inv vs.length))
      (fun _ => 35 * vs.length + 12) := by
    refine Triple.forRange_const 20 0 vs.length (Nat.zero_le _) (by omega) (fun _ => by omega)
      (Inv := Inv) (fun _ h => ⟨Expr.eval_const (by omega), h⟩)
      (fun _ _ _ _ h => h.2.2.2.1) (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
      (fun k _ hk => ?_) |>.conseq (fun _ h => h) (fun o st h => h) (fun _ _ => by simp [Expr.size]; omega)
    intro st ω' ⟨r0, r1, r2, r3, hcl, hfr⟩
    have hv : vs[k]'hk < vCap := hvs _ (List.getElem_mem hk)
    have hmem_k : st.mem (listPtr + k) = vs[k]'hk := by
      rw [hfr _ fun v hv' => by
        have hvc := hvs v hv'
        have := hdisj.addr_sub (Nat.le_refl _) (Nat.le_refl _) (listPtr + k) (by omega) (by omega)
        omega]
      exact hL k hk
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := vs[k]'hk)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r1) (Expr.eval_reg_of_eq r3)
        (by omega)) hmem_k) ?_
    refine runs_store_le (x := sBitPtr + vs[k]'hk) (v := 0)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0])) (Expr.eval_reg_of_eq (v := vs[k]'hk) (by simp))
        (by omega)) (Expr.eval_const (by omega)) ?_ ?_
    · refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp, fun j hj hjv => ?_,
        fun addr ha => ?_⟩, by simp [r3]⟩
      · dsimp only
        by_cases hjk : j = k
        · subst hjk; simp [Function.update]
        · by_cases heq : sBitPtr + vs[j]'hjv = sBitPtr + vs[k]'hk
          · rw [heq]; simp [Function.update]
          · rw [Function.update_of_ne heq]; exact hcl j (by omega) hjv
      · dsimp only
        rw [Function.update_of_ne (ha _ (List.getElem_mem hk))]
        exact hfr addr ha
    · simp [Expr.size]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState], by simp [startState],
    by simp, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩ ?_
  intro st₁ ⟨_, _, _, _, hcl, hfr⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
    ⟨sBitPtr, listPtr, rfl, rfl, fun v hv => ?_, hfr⟩ ?_
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
    exact hcl j hj hj
  · simp [Expr.size, dsClearSBitContract]

/-- `dsSumWalkLensStmt` meets `dsSumWalkLensContract`. -/
theorem dsSumWalkLens_meetsContract {w : ℕ} {es : List ℕ} {emb : MinCostFlow.Embedding}
    {p : Program} {bA : ℕ} (hpA : p.HasAt bA stepAuxProcs) :
    MeetsContract w p (bA + stepAuxIdxSumWalkLens) (dsSumWalkLensContract w es emb) := by
  refine meetsContract_of_runs
    (hpA.get (i := stepAuxIdxSumWalkLens) (by simp [stepAuxProcs, stepAuxIdxSumWalkLens])) ?_
  rintro args mem pos ω _ ⟨wpPtr, rfl, hw16, hwpB, hsumB, hwk⟩
  simp only [stepAuxProcs, stepAuxIdxSumWalkLens, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsSumWalkLensStmt]
  set Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = wpPtr ∧ st.regs 1 = es.length ∧
    st.regs 2 = ((es.take k).map fun e => (emb e).length).sum ∧
    st.regs 3 = k ∧ st.mem = mem
  have hloop : Triple w p (fun st => Inv 0 { st with regs := Function.update st.regs 3 0 })
      (forRange 3 (.const 0) (.reg 1)
        (.assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
         .assign 2 (.bin .add (.reg 2) (.load (.reg 4)))))
      (normalPost (Inv es.length))
      (fun _ => 35 * es.length + 12) := by
    refine Triple.forRange_const 20 0 es.length (Nat.zero_le _) (by omega) (fun _ => by omega)
      (Inv := Inv) (fun _ h => ⟨Expr.eval_const (by omega), h⟩)
      (fun _ _ _ _ h => h.2.2.2.1) (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.1)
      (fun k _ hk => ?_) |>.conseq (fun _ h => h) (fun o st h => h) (fun _ _ => by simp [Expr.size]; omega)
    intro st ω' ⟨r0, r1, r2, r3, hmem⟩
    obtain ⟨hW, hp_lt⟩ := hwk k hk
    have htake : ((es.take (k + 1)).map fun e => (emb e).length).sum =
        ((es.take k).map fun e => (emb e).length).sum + (emb (es[k]'hk)).length := by
      rw [List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
    have htake_le : ((es.take (k + 1)).map fun e => (emb e).length).sum ≤
        (es.map fun e => (emb e).length).sum := by
      conv_rhs => rw [← List.take_append_drop (k + 1) es, List.map_append, List.sum_append]
      exact Nat.le_add_right _ _
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := mem (wpPtr + k))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r3)
        (by omega)) (by rw [hmem])) ?_
    refine runs_assign_le (v := ((es.take (k + 1)).map fun e => (emb e).length).sum) ?_ ?_ ?_
    · rw [htake]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
        (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := mem (wpPtr + k)) (by simp))
          (by rw [hmem]; exact MWalkAt_head hW))
        (by omega)
    · exact ⟨⟨by simp [r0], by simp [r1], by simp, by simp, hmem⟩, by simp [r3]⟩
    · simp [Expr.size]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState], by simp,
    by simp, rfl⟩ ?_
  intro st₁ ⟨_, _, r2, _, hmem⟩
  refine runs_ret_le (v := (es.map fun e => (emb e).length).sum)
    (Expr.eval_reg_of_eq (by simpa using r2)) ⟨rfl, hmem⟩ ?_
  simp [Expr.size, dsSumWalkLensContract]; omega

/-- `dsSumRangeStmt` meets `dsSumRangeContract`. -/
theorem dsSumRange_meetsContract {w base lo hi : ℕ}
    {p : Program} {bA : ℕ} (hpA : p.HasAt bA stepAuxProcs) :
    MeetsContract w p (bA + stepAuxIdxSumRange) (dsSumRangeContract w base lo hi) := by
  refine meetsContract_of_runs
    (hpA.get (i := stepAuxIdxSumRange) (by simp [stepAuxProcs, stepAuxIdxSumRange])) ?_
  rintro args mem pos ω _ ⟨rfl, hw16, hlohi, hbB, hsumB⟩
  simp only [stepAuxProcs, stepAuxIdxSumRange, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsSumRangeStmt]
  set Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = base ∧ st.regs 1 = lo ∧ st.regs 2 = hi ∧
    st.regs 3 = ((List.range (i - lo)).map fun k => mem (base + (lo + k))).sum ∧
    st.regs 4 = i ∧ st.mem = mem
  have hloop : Triple w p (fun st => Inv lo { st with regs := Function.update st.regs 4 lo })
      (forRange 4 (.reg 1) (.reg 2)
        (.assign 3 (.bin .add (.reg 3) (.load (.bin .add (.reg 0) (.reg 4))))))
      (normalPost (Inv hi))
      (fun _ => 30 * (hi - lo) + 12) := by
    refine Triple.forRange_const 15 lo hi hlohi (by omega) (fun _ => by omega)
      (Inv := Inv) (fun _ h => ⟨Expr.eval_reg_of_eq (by simpa [Inv] using h.2.1), h⟩)
      (fun _ _ _ _ h => h.2.2.2.2.1) (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
      (fun i hlo hhi => ?_) |>.conseq (fun _ h => h) (fun o st h => h) (fun _ _ => by simp [Expr.size]; omega)
    intro st ω' ⟨r0, r1, r2, r3, r4, hmem⟩
    have hstep : ((List.range (i + 1 - lo)).map fun k => mem (base + (lo + k))).sum =
        ((List.range (i - lo)).map fun k => mem (base + (lo + k))).sum + mem (base + i) := by
      rw [show i + 1 - lo = (i - lo) + 1 by omega, List.range_succ, List.map_append,
        List.sum_append, List.map_singleton, List.sum_singleton, show lo + (i - lo) = i by omega]
    have hle_sum : ((List.range (i + 1 - lo)).map fun k => mem (base + (lo + k))).sum ≤
        ((List.range (hi - lo)).map fun k => mem (base + (lo + k))).sum := by
      have hpr : List.range (i + 1 - lo) = (List.range (hi - lo)).take (i + 1 - lo) := by
        rw [List.take_range]; simp [Nat.min_eq_left (show i + 1 - lo ≤ hi - lo by omega)]
      rw [hpr]
      conv_rhs => rw [← List.take_append_drop (i + 1 - lo) (List.range (hi - lo)), List.map_append,
        List.sum_append]
      exact Nat.le_add_right _ _
    refine runs_start_le ?_
    refine runs_assign_le (v := ((List.range (i + 1 - lo)).map fun k => mem (base + (lo + k))).sum)
      ?_ ?_ (by simp [Expr.size])
    · rw [hstep]
      exact Expr.eval_add (Expr.eval_reg_of_eq r3)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r4)
          (by omega)) (by rw [hmem])) (by omega)
    · exact ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp, by simp, hmem⟩, by simp [r4]⟩
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState], by simp [startState],
    by simp, by simp, rfl⟩ ?_
  intro st₁ ⟨_, _, _, r3, _, hmem⟩
  refine runs_ret_le (v := ((List.range (hi - lo)).map fun k => mem (base + (lo + k))).sum)
    (Expr.eval_reg_of_eq r3) ⟨rfl, hmem⟩ ?_
  simp [Expr.size, dsSumRangeContract]; omega

/-- `dsCopyWordsStmt` meets `dsCopyWordsContract`. -/
theorem dsCopyWords_meetsContract {w n : ℕ} {p : Program} {bA : ℕ} (hpA : p.HasAt bA stepAuxProcs) :
    MeetsContract w p (bA + stepAuxIdxCopyWords) (dsCopyWordsContract w n) := by
  refine meetsContract_of_runs
    (hpA.get (i := stepAuxIdxCopyWords) (by simp [stepAuxProcs, stepAuxIdxCopyWords])) ?_
  rintro args mem pos ω _ ⟨src, dst, rfl, hw16, hsB, hdB, hdisj⟩
  simp only [stepAuxProcs, stepAuxIdxCopyWords, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsCopyWordsStmt]
  set Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = n ∧ st.regs 3 = k ∧
    (∀ i < k, st.mem (dst + i) = mem (src + i)) ∧
    ∀ addr, (addr < dst ∨ dst + n ≤ addr) → st.mem addr = mem addr
  have hloop : Triple w p (fun st => Inv 0 { st with regs := Function.update st.regs 3 0 })
      (forRange 3 (.const 0) (.reg 2)
        (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))))
      (normalPost (Inv n))
      (fun _ => 30 * n + 12) := by
    refine Triple.forRange_const 15 0 n (Nat.zero_le _) (by omega) (fun _ => by omega)
      (Inv := Inv) (fun _ h => ⟨Expr.eval_const (by omega), h⟩)
      (fun _ _ _ _ h => h.2.2.2.1) (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
      (fun k _ hk => ?_) |>.conseq (fun _ h => h) (fun o st h => h) (fun _ _ => by simp [Expr.size]; omega)
    intro st ω' ⟨r0, r1, r2, r3, hcp, hfr⟩
    have hsrc : st.mem (src + k) = mem (src + k) :=
      hfr _ (hdisj.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) (src + k) (by omega) (by omega))
    refine runs_start_le ?_
    refine runs_store_le (x := dst + k) (v := mem (src + k))
      (Expr.eval_add (Expr.eval_reg_of_eq r1) (Expr.eval_reg_of_eq r3) (by omega))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r3)
        (by omega)) hsrc) ?_ (by simp [Expr.size])
    refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp, fun i hi => ?_, fun addr ha => ?_⟩, r3⟩
    · dsimp only
      by_cases hik : i = k
      · subst hik; simp [Function.update]
      · rw [Function.update_of_ne (by omega)]; exact hcp i (by omega)
    · dsimp only
      rw [Function.update_of_ne (by omega)]; exact hfr addr ha
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState], by simp [startState],
    by simp, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩ ?_
  intro st₁ ⟨_, _, r2, _, hcp, hfr⟩
  refine runs_ret_le (v := n) (Expr.eval_reg_of_eq r2) ⟨src, dst, rfl, rfl, hcp, hfr⟩ ?_
  simp [Expr.size, dsCopyWordsContract]

private lemma batchBody_split_take {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {us : List Update}
    {tot : ℕ} (hB : BatchBodyAt mem a G us tot) (hdi : ∀ u ∈ us, isDelOrIns u) :
    ∀ k (hk : k < us.length),
      let off := delInsWords (us.take k)
      off + delInsWordLen (us[k]'hk) ≤ tot ∧
      UpdateAt mem (a + off) (G.applyBatch (us.take k)) (us[k]'hk) (delInsWordLen (us[k]'hk)) := by
  induction us generalizing a G tot with
  | nil => intro _ hk; simp at hk
  | cons u us ih =>
    rcases hB with ⟨len, hle, hu, hrest⟩
    have hu_di := hdi u List.mem_cons_self
    have hlen_eq : len = delInsWordLen u := by
      cases u with
      | delete _ => exact hu.1
      | insert _ _ _ => exact hu.1
      | split _ _ _ _ => exact hu_di.elim
    intro k hk
    cases k with
    | zero =>
      simp only [List.take_zero, delInsWords, List.map_nil, List.sum_nil, Nat.add_zero,
        List.getElem_cons_zero, MGraph.applyBatch]
      rw [← hlen_eq]
      exact ⟨by omega, hu⟩
    | succ k' =>
      have hk' : k' < us.length := Nat.lt_of_succ_lt_succ hk
      have hsub := ih hrest (fun x hx => hdi x (List.mem_cons_of_mem u hx)) k' hk'
      simp only [List.take_succ_cons, delInsWords, List.map_cons, List.sum_cons,
        List.getElem_cons_succ, MGraph.applyBatch] at hsub ⊢
      rw [← hlen_eq]
      refine ⟨by omega, ?_⟩
      simpa [Nat.add_assoc] using hsub.2

/-- `dsCopyDelInsStmt` meets `dsCopyDelInsContract`. -/
theorem dsCopyDelIns_meetsContract {w : ℕ} {G : MGraph} {us : List Update} {tot : ℕ}
    {p : Program} {bA : ℕ} (hpA : p.HasAt bA stepAuxProcs) :
    MeetsContract w p (bA + stepAuxIdxCopyDelIns) (dsCopyDelInsContract w G us tot) := by
  refine meetsContract_of_runs
    (hpA.get (i := stepAuxIdxCopyDelIns) (by simp [stepAuxProcs, stepAuxIdxCopyDelIns])) ?_
  rintro args mem pos ω _ ⟨src, dst, rfl, hw16, hsB, hdB, hdisj, hB, hdi⟩
  simp only [stepAuxProcs, stepAuxIdxCopyDelIns, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsCopyDelInsStmt]
  have htot_eq : tot = delInsWords us := hB.delIns_words hdi
  have hlen_le : us.length ≤ tot := by
    rw [htot_eq]
    suffices ∀ l : List Update, (∀ u ∈ l, isDelOrIns u) → l.length ≤ delInsWords l from this us hdi
    intro l
    induction l with
    | nil => intro _; simp [delInsWords]
    | cons u l ih =>
      intro hl
      have h1 := hl u List.mem_cons_self
      have h2 := ih (fun x hx => hl x (List.mem_cons_of_mem u hx))
      cases u with
      | delete _ => simp only [delInsWords, List.map_cons, List.sum_cons, delInsWordLen, List.length_cons] at h2 ⊢; omega
      | insert _ _ _ => simp only [delInsWords, List.map_cons, List.sum_cons, delInsWordLen, List.length_cons] at h2 ⊢; omega
      | split _ _ _ _ => exact h1.elim
  set Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = us.length ∧
    st.regs 3 = delInsWords (us.take k) ∧ st.regs 4 = k ∧
    (∀ i < delInsWords (us.take k), st.mem (dst + i) = mem (src + i)) ∧
    ∀ addr, (addr < dst ∨ dst + tot ≤ addr) → st.mem addr = mem addr
  have hloop : Triple w p (fun st => Inv 0 { st with regs := Function.update st.regs 4 0 })
      (forRange 4 (.const 0) (.reg 2)
        (.assign 5 (.load (.bin .add (.reg 0) (.reg 3))) ;;
         .cond (.bin .eq (.reg 5) (.const 1))
           (.store (.bin .add (.reg 1) (.reg 3)) (.const 1) ;;
            .store (.bin .add (.reg 1) (.bin .add (.reg 3) (.const 1)))
              (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.const 1)))) ;;
            .assign 3 (.bin .add (.reg 3) (.const 2)))
           (.store (.bin .add (.reg 1) (.reg 3)) (.const 0) ;;
            .store (.bin .add (.reg 1) (.bin .add (.reg 3) (.const 1)))
              (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.const 1)))) ;;
            .store (.bin .add (.reg 1) (.bin .add (.reg 3) (.const 2)))
              (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.const 2)))) ;;
            .store (.bin .add (.reg 1) (.bin .add (.reg 3) (.const 3)))
              (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.const 3)))) ;;
            .assign 3 (.bin .add (.reg 3) (.const 4)))))
      (normalPost (Inv us.length))
      (fun _ => 95 * us.length + 12) := by
    refine Triple.forRange_const 80 0 us.length (Nat.zero_le _) (by omega) (fun _ => by omega)
      (Inv := Inv) (fun _ h => ⟨Expr.eval_const (by omega), h⟩)
      (fun _ _ _ _ h => h.2.2.2.2.1) (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
      (fun k _ hk => ?_) |>.conseq (fun _ h => h) (fun o st h => h) (fun _ _ => by simp [Expr.size]; omega)
    intro st ω' ⟨r0, r1, r2, r3, r4, hcp, hfr⟩
    obtain ⟨hoff_le, hu_at⟩ := batchBody_split_take hB hdi k hk
    set off := delInsWords (us.take k)
    have htake_succ : delInsWords (us.take (k + 1)) = off + delInsWordLen (us[k]'hk) := by
      simp only [off, delInsWords, List.take_succ_eq_append_getElem hk, List.map_append,
        List.sum_append, List.map_singleton, List.sum_singleton]
    have hrd : ∀ d < delInsWordLen (us[k]'hk), st.mem (src + (off + d)) = mem (src + (off + d)) := by
      intro d hd
      exact hfr _ (hdisj.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
    have huk_di := hdi _ (List.getElem_mem hk)
    cases h_uk : us[k]'hk with
    | split _ _ _ _ => rw [h_uk] at huk_di; exact huk_di.elim
    | delete e =>
      rw [h_uk] at hu_at hoff_le htake_succ hrd
      simp only [delInsWordLen] at hu_at hoff_le htake_succ hrd
      have hm0 : mem (src + off) = 1 := by simpa using hu_at.2 0 (by simp)
      have hm1 : mem (src + (off + 1)) = e := by simpa [Nat.add_assoc] using hu_at.2 1 (by simp)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := 1)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r3)
          (by omega)) ((hrd 0 (by omega)).trans hm0)) ?_
      refine runs_cond_le (v := if (1 : ℕ) = 1 then 1 else 0)
        (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := 1) (by simp))
          (Expr.eval_const (by omega)) (by omega))
        (fun _ => ?_) (fun h => by simp at h)
      refine runs_seq_store_le (x := dst + off) (v := 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1])) (Expr.eval_reg_of_eq (by simp [r3]))
          (by omega)) (Expr.eval_const (by omega)) ?_
      have hsrc1 : Function.update st.mem (dst + off) 1 (src + (off + 1)) = mem (src + (off + 1)) := by
        have hne : src + (off + 1) ≠ dst + off := by
          have := hdisj.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) (src + (off + 1))
            (by omega) (by omega)
          omega
        rw [Function.update_of_ne hne]; exact hrd 1 (by omega)
      refine runs_seq_store_le (x := dst + (off + 1)) (v := mem (src + (off + 1)))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1]))
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3])) (Expr.eval_const (by omega))
            (by omega)) (by omega))
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3])) (Expr.eval_const (by omega))
              (by omega)) (by omega)) hsrc1) ?_
      refine runs_assign_le (v := off + 2)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3])) (Expr.eval_const (by omega))
          (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [htake_succ], by simp,
        fun i hi => ?_, fun addr ha => ?_⟩, by simp [r4]⟩
      · dsimp only; rw [htake_succ] at hi
        by_cases h1 : i = off + 1
        · subst h1; simp [Function.update]
        · rw [Function.update_of_ne (by omega)]
          by_cases h0 : i = off
          · subst h0; simp [Function.update, hm0]
          · rw [Function.update_of_ne (by omega)]; exact hcp i (by omega)
      · dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr addr ha
    | insert e x y =>
      rw [h_uk] at hu_at hoff_le htake_succ hrd
      simp only [delInsWordLen] at hu_at hoff_le htake_succ hrd
      have hm0 : mem (src + off) = 0 := by simpa using hu_at.2 0 (by simp)
      have hne_s : ∀ d < 4, ∀ d' < 4, src + (off + d) ≠ dst + (off + d') := fun d hd d' hd' => by
        have := hdisj.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) (src + (off + d))
          (by omega) (by omega)
        omega
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := 0)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r3)
          (by omega)) ((hrd 0 (by omega)).trans hm0)) ?_
      refine runs_cond_le (v := if (0 : ℕ) = 1 then 1 else 0)
        (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := 0) (by simp))
          (Expr.eval_const (by omega)) (by omega))
        (fun h => by simp at h) (fun _ => ?_)
      refine runs_seq_store_le (x := dst + off) (v := 0)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1])) (Expr.eval_reg_of_eq (by simp [r3]))
          (by omega)) (Expr.eval_const (by omega)) ?_
      refine runs_seq_store_le (x := dst + (off + 1)) (v := mem (src + (off + 1)))
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) (by simp [r1]))
          (Expr.eval_add (Expr.eval_reg_of_eq (v := off) (by simp [r3])) (Expr.eval_const (by omega))
            (by omega)) (by omega))
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := src) (by simp [r0]))
            (Expr.eval_add (Expr.eval_reg_of_eq (v := off) (by simp [r3])) (Expr.eval_const (by omega))
              (by omega)) (by omega))
          (by dsimp only; rw [Function.update_of_ne (by simpa using hne_s 1 (by omega) 0 (by omega))]; exact hrd 1 (by omega))) ?_
      refine runs_seq_store_le (x := dst + (off + 2)) (v := mem (src + (off + 2)))
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) (by simp [r1]))
          (Expr.eval_add (Expr.eval_reg_of_eq (v := off) (by simp [r3])) (Expr.eval_const (by omega))
            (by omega)) (by omega))
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := src) (by simp [r0]))
            (Expr.eval_add (Expr.eval_reg_of_eq (v := off) (by simp [r3])) (Expr.eval_const (by omega))
              (by omega)) (by omega))
          (by
            dsimp only
            rw [Function.update_of_ne (hne_s 2 (by omega) 1 (by omega)),
              Function.update_of_ne (by simpa using hne_s 2 (by omega) 0 (by omega))]
            exact hrd 2 (by omega))) ?_
      refine runs_seq_store_le (x := dst + (off + 3)) (v := mem (src + (off + 3)))
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) (by simp [r1]))
          (Expr.eval_add (Expr.eval_reg_of_eq (v := off) (by simp [r3])) (Expr.eval_const (by omega))
            (by omega)) (by omega))
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := src) (by simp [r0]))
            (Expr.eval_add (Expr.eval_reg_of_eq (v := off) (by simp [r3])) (Expr.eval_const (by omega))
              (by omega)) (by omega))
          (by
            dsimp only
            rw [Function.update_of_ne (hne_s 3 (by omega) 2 (by omega)),
              Function.update_of_ne (hne_s 3 (by omega) 1 (by omega)),
              Function.update_of_ne (by simpa using hne_s 3 (by omega) 0 (by omega))]
            exact hrd 3 (by omega))) ?_
      refine runs_assign_le (v := off + 4)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := off) (by simp [r3])) (Expr.eval_const (by omega))
          (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [htake_succ], by simp,
        fun i hi => ?_, fun addr ha => ?_⟩, by simp [r4]⟩
      · dsimp only; rw [htake_succ] at hi
        by_cases h3 : i = off + 3
        · subst h3; simp [Function.update]
        · rw [Function.update_of_ne (by omega)]
          by_cases h2 : i = off + 2
          · subst h2; simp [Function.update]
          · rw [Function.update_of_ne (by omega)]
            by_cases h1 : i = off + 1
            · subst h1; simp [Function.update]
            · rw [Function.update_of_ne (by omega)]
              by_cases h0 : i = off
              · subst h0; simp [Function.update, hm0]
              · rw [Function.update_of_ne (by omega)]; exact hcp i (by omega)
      · dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr addr ha
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState], by simp [startState],
    by simp [delInsWords], by simp, fun _ h => by simp [delInsWords] at h, fun _ _ => rfl⟩ ?_
  intro st₁ ⟨_, _, _, r3, _, hcp, hfr⟩
  rw [List.take_length, ← htot_eq] at r3 hcp
  refine runs_ret_le (v := tot) (Expr.eval_reg_of_eq r3) ⟨src, dst, rfl, rfl, hcp, hfr⟩ ?_
  simp [Expr.size, dsCopyDelInsContract]; omega

end

end MinCostFlow.DynSpanner.Program
