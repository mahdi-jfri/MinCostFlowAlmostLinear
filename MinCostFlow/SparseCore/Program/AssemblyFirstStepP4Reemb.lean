module

public import MinCostFlow.SparseCore.Program.AssemblyFirstRotProg

import WordRAM.Tactic

/-!
# The re-embedded list of Phase 4 (`AssemblyFirstStepP4Reemb`)

The step of a branch reports the sorted list of the edges whose embedding changes
(`stepBundleTree_reembList`). This set is the union of three parts: the edges of the bundles of
the newly active components, the sets `updateReembSet` of the spanners, and the edges that leave
the output graph (`stepBundleTree_reembSet_eq_sup`). After the front of Phase 4, the workspace
holds the first two parts in one list `Lr`, and the delete list of the output step holds the
third part, two words per edge.

The procedure `asmFirstP4ReembStmt fCopy fBuild`, with arguments `[lrPtr, lrLen, delPtr, h]`,
copies `Lr` and the edges of the delete list into a raw list at `h + 1`, stores at `h` the end of
the raw list, and sorts the raw list there and drops repeats with `asmFirstBuildRotStmt`. So the
sorted list is at `mem h + 1`, and its length at `mem h`.

The copies use one small procedure, `asmFirstStrideCopyStmt` (`[src, stride, n, dst]`), which
copies the words `src + stride * i` for `i < n` to `dst + i`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## The procedures -/

@[expose] public section

/-- **Strided copy**, `[src, stride, n, dst]`: for `i < n`, copies the word at `src + stride * i`
to `dst + i`. Returns `dst + n`. -/
def asmFirstStrideCopyStmt : Stmt :=
  forRange 4 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 3) (.reg 4))
      (.load (.bin .add (.reg 0) (.bin .mul (.reg 1) (.reg 4))))) ;;
  .ret (.bin .add (.reg 3) (.reg 2))

/-- **The re-embedded list of Phase 4**, `[lrPtr, lrLen, delPtr, h]`. Register `4` holds the
place `h + 1` of the raw list, register `5` the number of edges of the delete list, and
register `6` the end of the raw list. -/
def asmFirstP4ReembStmt (fCopy fBuild : ℕ) : Stmt :=
  .assign 4 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 5 (.load (.reg 2)) ;;
  .assign 6 (.bin .add (.bin .add (.reg 4) (.reg 1)) (.reg 5)) ;;
  .call 7 fCopy [.reg 0, .const 1, .reg 1, .reg 4] ;;
  .call 8 fCopy [.bin .add (.reg 2) (.const 1), .const 2, .reg 5, .bin .add (.reg 4) (.reg 1)] ;;
  .store (.reg 3) (.reg 6) ;;
  .call 9 fBuild [.reg 4, .bin .add (.reg 1) (.reg 5), .reg 6] ;;
  .ret (.reg 9)

/-- The cost of `asmFirstP4ReembStmt` on a raw list of `m` entries: the two copies and the
sort. -/
def p4ReembCost (m : ℕ) : ℕ :=
  20 * m + 280 * m * (Nat.log 2 (m + 1) + 1) + 300

/-- What `asmFirstP4ReembStmt` leaves for the raw list `rawL`: at `h` the place of the sorted list
of the distinct entries of `rawL`, with its length first, below the returned pointer. Every cell
below `h` is kept. -/
def P4ReembPost (h : ℕ) (rawL : List ℕ) (space costB : ℕ) (mem₀ : ℕ → ℕ) (o : Outcome)
    (st' : State) (cost : ℕ) : Prop :=
  st'.mem (st'.mem h) = (rawL.toFinset.sort (· ≤ ·)).length ∧
    ListAt st'.mem (st'.mem h + 1) (rawL.toFinset.sort (· ≤ ·)) ∧
    st'.mem h + 1 + (rawL.toFinset.sort (· ≤ ·)).length ≤ o.value ∧
    h + 1 ≤ st'.mem h ∧ h + 1 ≤ o.value ∧ o.value ≤ h + space ∧ ZeroFrom st'.mem o.value ∧
    (∀ x < h, st'.mem x = mem₀ x) ∧ cost ≤ costB

end

public section

theorem asmFirstStrideCopyStmt_noRand : asmFirstStrideCopyStmt.NoRand := by
  simp [asmFirstStrideCopyStmt, forRange, forUp, Stmt.NoRand]

theorem asmFirstP4ReembStmt_noRand (fCopy fBuild : ℕ) :
    (asmFirstP4ReembStmt fCopy fBuild).NoRand := by
  simp [asmFirstP4ReembStmt, Stmt.NoRand]

end

/-! ## The strided copy -/

/-- **The run of the strided copy.** The words `src + stride * i` for `i < L.length` hold `L`
and lie below `dst`. Then the procedure writes `L` at `dst` and changes no other cell. -/
public theorem asmFirstStrideCopy_runs {w src stride dst pos : ℕ} {p : Program} {L : List ℕ}
    {mem₀ : ℕ → ℕ} {ω : ℕ → Bool} (hw16 : 16 ≤ 2 ^ w)
    (hL : ∀ i < L.length, mem₀ (src + stride * i) = L.getD i 0)
    (hsrc : ∀ i < L.length, src + stride * i < dst) (hdst : dst + L.length < 2 ^ w) :
    ∃ st' cost, Runs w p ω asmFirstStrideCopyStmt
        (startState [src, stride, L.length, dst] mem₀ pos) (.returned (dst + L.length)) st' cost ∧
      ListAt st'.mem dst L ∧ (∀ a, a < dst ∨ dst + L.length ≤ a → st'.mem a = mem₀ a) ∧
      cost ≤ 20 * L.length + 20 := by
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  let inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = src ∧ st.regs 1 = stride ∧ st.regs 2 = L.length ∧ st.regs 3 = dst ∧
    st.regs 4 = i ∧ (∀ j < i, st.mem (dst + j) = L.getD j 0) ∧
    (∀ a, a < dst ∨ dst + i ≤ a → st.mem a = mem₀ a)
  have hLoop := Triple.forRange_le (w := w) (p := p) (r := 4) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 3) (.reg 4))
      (.load (.bin .add (.reg 0) (.bin .mul (.reg 1) (.reg 4)))))
    (P := fun st => inv 0 { st with regs := Function.update st.regs 4 0 })
    (Inv := inv) (fun _ => 10) 0 L.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.1)
    (fun i _ hi st ω' ⟨r0, r1, r2, r3, r4, hcp, hfr⟩ => by
      have hs := hsrc i hi
      have hv : st.mem (src + stride * i) = L.getD i 0 :=
        (hfr _ (Or.inl hs)).trans (hL i hi)
      have hrun : Runs w p ω' (.store (.bin .add (.reg 3) (.reg 4))
          (.load (.bin .add (.reg 0) (.bin .mul (.reg 1) (.reg 4))))) st .normal
          { st with mem := Function.update st.mem (dst + i) (L.getD i 0) } 10 :=
        runs_store_iff.mpr ⟨dst + i, L.getD i 0,
          Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r4) (by omega),
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0)
            (Expr.eval_mul (Expr.eval_reg_of_eq r1) (Expr.eval_reg_of_eq r4) (by omega))
            (by omega)) hv, rfl, rfl, rfl⟩
      refine ⟨.normal, _, 10, hrun, ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3],
        by simp, fun j hj => ?_, fun a ha => ?_⟩, r4⟩, le_rfl⟩
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hji | rfl
        · show Function.update st.mem (dst + i) (L.getD i 0) (dst + j) = _
          rw [Function.update_of_ne (by omega)]
          exact hcp j hji
        · show Function.update st.mem (dst + j) (L.getD j 0) (dst + j) = _
          exact Function.update_self ..
      · show Function.update st.mem (dst + i) (L.getD i 0) a = _
        rw [Function.update_of_ne (by omega)]
        exact hfr a (by omega))
  obtain ⟨o₁, st₁, c₁, hr₁, hpost, hc₁⟩ := hLoop (startState [src, stride, L.length, dst] mem₀ pos)
    ω ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  cases o₁ with
  | returned _ => cases hpost
  | normal =>
  obtain ⟨_, _, r2, r3, _, hcp, hfr⟩ := hpost
  have hret : Runs w p ω (.ret (.bin .add (.reg 3) (.reg 2))) st₁ (.returned (dst + L.length))
      st₁ 4 :=
    runs_ret_iff.mpr ⟨dst + L.length,
      Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r2) hdst, rfl, rfl, rfl⟩
  simp only [rangeCost_const, Nat.sub_zero, Expr.size] at hc₁
  refine ⟨st₁, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr₁, hret, rfl⟩), fun i hi => ?_, hfr,
    by omega⟩
  rw [hcp i hi, List.getD_eq_getElem _ _ hi]

/-! ## The run of the re-embedded list -/

/-- A call followed by a statement, with the cost bound carried along. -/
private theorem reemb_runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ}
    (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

/-- The run of the statement from the runs of its three calls. -/
private theorem asmFirstP4Reemb_run_of {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {fCopy fBuild : ℕ} {bCopy bBuild : Stmt}
    (hfCopy : p.procs[fCopy]? = some bCopy) (hfBuild : p.procs[fBuild]? = some bBuild)
    {lrPtr lrLen delPtr h pos nDel : ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hmD : mem₀ delPtr = nDel) (hdp : delPtr + 1 < 2 ^ w)
    (hsz : h + 1 + lrLen + nDel < 2 ^ w)
    {o₁ o₂ o₃ : Outcome} {st₁ st₂ st₃ : State} {c₁ c₂ c₃ : ℕ}
    (hr₁ : Runs w p ω bCopy (startState [lrPtr, 1, lrLen, h + 1] mem₀ pos) o₁ st₁ c₁)
    (hr₂ : Runs w p ω bCopy (startState [delPtr + 1, 2, nDel, h + 1 + lrLen] st₁.mem st₁.pos)
      o₂ st₂ c₂)
    (hr₃ : Runs w p ω bBuild (startState [h + 1, lrLen + nDel, h + 1 + lrLen + nDel]
      (Function.update st₂.mem h (h + 1 + lrLen + nDel)) st₂.pos) o₃ st₃ c₃) :
    ∃ st' c, Runs w p ω (asmFirstP4ReembStmt fCopy fBuild)
        (startState [lrPtr, lrLen, delPtr, h] mem₀ pos) (.returned o₃.value) st' c ∧
      st'.mem = st₃.mem ∧ c ≤ c₁ + c₂ + c₃ + 80 := by
  have key : ∃ o st' c, Runs w p ω (asmFirstP4ReembStmt fCopy fBuild)
      (startState [lrPtr, lrLen, delPtr, h] mem₀ pos) o st' c ∧
      (o = .returned o₃.value ∧ st'.mem = st₃.mem) ∧ 0 + c ≤ c₁ + c₂ + c₃ + 80 := by
    unfold asmFirstP4ReembStmt
    refine runs_seq_assign_le (v := h + 1) (by eval_expr) ?_
    refine runs_seq_assign_le (v := nDel) (by eval_expr) ?_
    refine runs_seq_assign_le (v := h + 1 + lrLen + nDel) (by eval_expr) ?_
    refine reemb_runs_seq_callRuns_le (by eval_expr) hfCopy hr₁ ?_
    refine reemb_runs_seq_callRuns_le (by eval_expr) hfCopy hr₂ ?_
    refine runs_seq_store_le (x := h) (v := h + 1 + lrLen + nDel) (by eval_expr) (by eval_expr) ?_
    refine reemb_runs_seq_callRuns_le (by eval_expr) hfBuild hr₃ ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o, st', c, hr, ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c, hr, hm, by omega⟩

/-- **The run of `asmFirstP4ReembStmt`.** The list `Lr` and the delete list lie below `h`, and
every entry of `Lr` and of the delete list is below `eCap`. Then the procedure leaves the sorted
list of the distinct entries of `Lr ++ delL`, as `P4ReembPost` says. -/
public theorem asmFirstP4Reemb_runs {w fCopy fBuild bSort eCap lrPtr delPtr h pos : ℕ}
    {p : Program}
    (hfCopy : p.procs[fCopy]? = some asmFirstStrideCopyStmt)
    (hfBuild : p.procs[fBuild]? = some (asmFirstBuildRotStmt bSort))
    (hpS : p.HasAt bSort (sortProcs bSort))
    {Lr delL : List ℕ} {E' : Finset ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (heCap_w : eCap < 2 ^ w)
    (hLr : ListAt mem₀ lrPtr Lr) (hLr_le : lrPtr + Lr.length ≤ h)
    (hDel : OutDelAt mem₀ delPtr delL E') (hDel_le : delPtr + 1 + 2 * delL.length ≤ h)
    (hcap : ∀ e ∈ Lr ++ delL, e < eCap) (hz : ZeroFrom mem₀ h)
    (hsp : h + 2 + 4 * (Lr.length + delL.length) < 2 ^ w) :
    ∃ o st' cost, Runs w p ω (asmFirstP4ReembStmt fCopy fBuild)
        (startState [lrPtr, Lr.length, delPtr, h] mem₀ pos) o st' cost ∧
      P4ReembPost h (Lr ++ delL) (2 + 4 * (Lr.length + delL.length))
        (p4ReembCost (Lr.length + delL.length)) mem₀ o st' cost := by
  -- Step 1: copy `Lr` to `h + 1`.
  obtain ⟨st₁, c₁, hr₁, hL₁, hk₁, hc₁⟩ := asmFirstStrideCopy_runs (p := p) (ω := ω) (pos := pos)
    (src := lrPtr) (stride := 1) (dst := h + 1) (L := Lr) (mem₀ := mem₀) hw16
    (fun i hi => by rw [Nat.one_mul, hLr i hi, List.getD_eq_getElem _ _ hi])
    (fun i hi => by omega) (by omega)
  -- Step 2: copy the edges of the delete list after it.
  obtain ⟨st₂, c₂, hr₂, hL₂, hk₂, hc₂⟩ := asmFirstStrideCopy_runs (p := p) (ω := ω)
    (pos := st₁.pos) (src := delPtr + 1) (stride := 2) (dst := h + 1 + Lr.length) (L := delL)
    (mem₀ := st₁.mem) hw16
    (fun i hi => by rw [hk₁ _ (Or.inl (by omega))]; exact (hDel.2 i hi).1)
    (fun i hi => by omega) (by omega)
  have hk₂₁ : ∀ x, x < h + 1 ∨ h + 1 + Lr.length + delL.length ≤ x → st₂.mem x = mem₀ x := by
    intro x hx
    rw [hk₂ x (by omega), hk₁ x (by omega)]
  have hraw₂ : ListAt st₂.mem (h + 1) (Lr ++ delL) :=
    listAt_append.mpr ⟨hL₁.congr fun k hk1 hk2 => hk₂ k (Or.inl hk2), hL₂⟩
  -- Step 3: store the end of the raw list at `h`, then sort the raw list.
  have hlen : (Lr ++ delL).length = Lr.length + delL.length := List.length_append
  have hz₂ : ZeroFrom (Function.update st₂.mem h (h + 1 + Lr.length + delL.length))
      (h + 1 + Lr.length + delL.length) := by
    intro x hx
    rw [Function.update_of_ne (by omega), hk₂₁ x (Or.inr hx)]
    exact hz x (by omega)
  obtain ⟨o₃, st₃, c₃, hr₃, ho₃, hcnt₃, hL₃, -, -, hlenT, hz₃, hk₃, hc₃⟩ :=
    asmFirstBuildRot_runs (pos := st₂.pos) (ω := ω) (h := h + 1 + Lr.length + delL.length)
      (rawPtr := h + 1) (rawL := Lr ++ delL) (vCap := eCap) hpS hw16
      (hraw₂.update_lt (by omega)) (by omega) hcap heCap_w hz₂ (by omega)
  rw [hlen] at hr₃ hc₃ ho₃ hlenT
  obtain ⟨st', c, hrun, hm', hc⟩ := asmFirstP4Reemb_run_of hfCopy hfBuild hw16 hDel.1 (by omega)
    (by omega) hr₁ hr₂ hr₃
  have hmh : st'.mem h = h + 1 + Lr.length + delL.length := by
    rw [hm', hk₃ h (by omega)]
    exact Function.update_self ..
  have hov : (Outcome.returned o₃.value).value = o₃.value := rfl
  refine ⟨_, st', c, hrun, ?_, ?_, ?_, by omega, by omega, by rw [hov, ho₃]; omega,
    by rw [hm', hov]; exact hz₃, fun x hx => ?_, ?_⟩
  · rw [hmh, hm']
    exact hcnt₃
  · rw [hmh, hm']
    exact hL₃
  · rw [hmh, hov, ho₃]
    omega
  · rw [hm', hk₃ x (by omega), Function.update_of_ne (by omega)]
    exact hk₂₁ x (Or.inl (by omega))
  · unfold p4ReembCost
    omega

end MinCostFlow.SparseCore.Program
