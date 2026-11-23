module

public import MinCostFlow.SparseCore.Program.ReadLoops
public import MinCostFlow.DynSpanner.Program.DynGraphInsert
public import MinCostFlow.DynSpanner.Program.DynGraphOps

import WordRAM.Tactic

/-!
# Helper procedures for the restart of a branch: deletion pass and loop rule (`ReadRestartOps`)

This file provides the deterministic loop infrastructure and deletion pass for the restart
procedure of piece P10 (`ReadRestart.lean`):

1. `forRange_phi_runs`: a potential-carrying `forRange` loop rule on `Runs`, telescoping an
   arbitrary potential `Φ : α → (ℕ → ℕ) → ℕ` across iterations without subtraction.
2. `copyListStmt` (`[dst, src, n]`): copies `n` words from `src` to `dst` in `30 · n + 20` steps
   (`copyList_meetsContract`). The restart copies the slot list to fresh heap before calling P4's
   root query `Q`, so `Q`'s writes to its own footprint cannot disturb the slot list.
3. `bucketSpanner_slot_graphs`, `slotsHE_subset_slotsGE`: extracts the `G` and `H` graph blocks of
   an active slot from `bucketSpannerRep SP cap`.
4. `restartDelSlotsStmt` (`[sPtr, spanTbl, slotsPtr, n]`): deletes the edges of every listed
   slot's bundle graph `(d.state SP).G` from `S` via `delEdgesStmt`, removing `slotsGE SP S6 slots`
   (which also contains `slotsHE SP S6 slots`) in `O(Σ |G_s.E| + n + 1)` steps
   (`restartDelSlots_runs`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Potential-carrying `forRange` rule -/

/-- Sum of a per-index cost over `0 .. L.length - 1` equals `(L.map f).sum`. -/
theorem rangeCost_eq_sum_map {α : Type*} (L : List α) (d : α) (f : α → ℕ) :
    rangeCost (fun i => f (L.getD i d)) 0 L.length = (L.map f).sum := by
  suffices ∀ k ≤ L.length,
      rangeCost (fun i => f (L.getD i d)) k L.length = ((L.drop k).map f).sum by
    simpa using this 0 (Nat.zero_le _)
  intro k hk
  induction hrem : L.length - k generalizing k with
  | zero =>
    have hge : L.length ≤ k := by omega
    rw [rangeCost_of_le hge, List.drop_of_length_le hge]; simp
  | succ m ih =>
    have hlt : k < L.length := by omega
    rw [rangeCost_step hlt, ih (k + 1) (by omega) (by omega), List.drop_eq_getElem_cons hlt,
      List.getD_eq_getElem _ _ hlt, List.map_cons, List.sum_cons]

/-- Potential-carrying `forUp` loop rule: if each iteration `i < n` runs `body` normally from
`(st, x)` to `(st₁, x₁)` with `c₁ + Φ x₁ st₁.mem ≤ stepCost i + Φ x st.mem`, then the whole loop
runs from `i₀` to `n` telescoping `Φ`. -/
theorem forUp_phi_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {α : Type*}
    {r : ℕ} {hi : Expr} {body : Stmt}
    {Inv : ℕ → State → α → Prop} {Φ : α → (ℕ → ℕ) → ℕ}
    (stepCost : ℕ → ℕ) {i₀ n : ℕ} (hle : i₀ ≤ n) (hw : 1 < 2 ^ w) (hnw : i₀ < n → n < 2 ^ w)
    (hreg : ∀ i st x, i₀ ≤ i → i ≤ n → Inv i st x → st.regs r = i)
    (hhi : ∀ i st x, i₀ ≤ i → i ≤ n → Inv i st x → hi.eval w st = some n)
    (hbody : ∀ i, i₀ ≤ i → i < n → ∀ st x, Inv i st x →
      ∃ st₁ c₁ x₁, Runs w p ω body st .normal st₁ c₁ ∧ st₁.regs r = i ∧
        Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } x₁ ∧
        c₁ + Φ x₁ st₁.mem ≤ stepCost i + Φ x st.mem)
    {st₀ : State} {x₀ : α} (h0 : Inv i₀ st₀ x₀) :
    ∃ st' c x', Runs w p ω (WordRAM.forUp r hi body) st₀ .normal st' c ∧
      Inv n st' x' ∧
      c + Φ x' st'.mem ≤
        rangeCost stepCost i₀ n + (n - i₀) * (hi.size + 8) + (hi.size + 3) + Φ x₀ st₀.mem := by
  suffices ∀ k i st x, n - i = k → i₀ ≤ i → i ≤ n → Inv i st x →
      ∃ st' c x', Runs w p ω (WordRAM.forUp r hi body) st .normal st' c ∧
        Inv n st' x' ∧
        c + Φ x' st'.mem ≤
          rangeCost stepCost i n + (n - i) * (hi.size + 8) + (hi.size + 3) + Φ x st.mem from
    this (n - i₀) i₀ st₀ x₀ rfl le_rfl hle h0
  intro k
  induction k with
  | zero =>
    intro i st x hk hi₀ hin hInv
    have heq : i = n := by omega
    subst heq
    have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 0 :=
      Expr.eval_lt_false (by simp [Expr.eval, hreg i st x hi₀ le_rfl hInv])
        (hhi i st x hi₀ le_rfl hInv) le_rfl hw
    have hrun : Runs w p ω (WordRAM.forUp r hi body) st .normal st (hi.size + 3) :=
      runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, by simp [Expr.size]; omega⟩)
    exact ⟨st, hi.size + 3, x, hrun, hInv, by rw [rangeCost_of_le le_rfl]; omega⟩
  | succ m ih =>
    intro i st x hk hi₀ hin hInv
    have hlt : i < n := by omega
    have hi1w : i + 1 < 2 ^ w := Nat.lt_of_le_of_lt hlt (hnw (Nat.lt_of_le_of_lt hi₀ hlt))
    have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 1 :=
      Expr.eval_lt_true (by simp [Expr.eval, hreg i st x hi₀ hin hInv])
        (hhi i st x hi₀ hin hInv) hlt hw
    obtain ⟨st₁, c₁, x₁, hr₁, hreg₁, hInv₁, hc₁⟩ := hbody i hi₀ hlt st x hInv
    have hincEval : (Expr.bin .add (.reg r) (.const 1)).eval w st₁ = some (i + 1) :=
      Expr.eval_add (by simp [Expr.eval, hreg₁]) (Expr.eval_const hw) hi1w
    have hinc : Runs w p ω (.assign r (.bin .add (.reg r) (.const 1))) st₁ .normal
        { st₁ with regs := Function.update st₁.regs r (i + 1) } 4 :=
      runs_assign_iff.mpr ⟨i + 1, hincEval, rfl, rfl, by simp [Expr.size]⟩
    have hseq : Runs w p ω (body ;; .assign r (.bin .add (.reg r) (.const 1))) st .normal
        { st₁ with regs := Function.update st₁.regs r (i + 1) } (c₁ + 5) :=
      runs_seq_iff.mpr (Or.inr ⟨_, c₁, 4, hr₁, hinc, by omega⟩)
    obtain ⟨st₂, c₂, x₂, hr₂, hInv₂, hc₂⟩ :=
      ih (i + 1) _ x₁ (by omega) (by omega) (by omega) hInv₁
    have hrun : Runs w p ω (WordRAM.forUp r hi body) st .normal st₂ (hi.size + c₁ + c₂ + 8) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, c₁ + 5, c₂, hcond, by decide, hseq, hr₂,
        by simp [Expr.size]; omega⟩))
    refine ⟨st₂, hi.size + c₁ + c₂ + 8, x₂, hrun, hInv₂, ?_⟩
    rw [rangeCost_step hlt, show n - i = (n - (i + 1)) + 1 by omega, Nat.add_one_mul]
    dsimp only at hc₂
    omega

/-- Potential-carrying `forRange r lo hi body` rule starting at `lo = 0` up to `n`. -/
theorem forRange_phi_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {α : Type*}
    {r : ℕ} {lo hi : Expr} {body : Stmt}
    {Inv : ℕ → State → α → Prop} {Φ : α → (ℕ → ℕ) → ℕ}
    (stepCost : ℕ → ℕ) {n : ℕ} (hw : 1 < 2 ^ w) (hnw : 0 < n → n < 2 ^ w)
    {st₀ : State} {x₀ : α}
    (hlo : lo.eval w st₀ = some 0)
    (h0 : Inv 0 { st₀ with regs := Function.update st₀.regs r 0 } x₀)
    (hreg : ∀ i st x, i ≤ n → Inv i st x → st.regs r = i)
    (hhi : ∀ i st x, i ≤ n → Inv i st x → hi.eval w st = some n)
    (hbody : ∀ i, i < n → ∀ st x, Inv i st x →
      ∃ st₁ c₁ x₁, Runs w p ω body st .normal st₁ c₁ ∧ st₁.regs r = i ∧
        Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } x₁ ∧
        c₁ + Φ x₁ st₁.mem ≤ stepCost i + Φ x st.mem) :
    ∃ st' c x', Runs w p ω (forRange r lo hi body) st₀ .normal st' c ∧
      Inv n st' x' ∧
      c + Φ x' st'.mem ≤
        rangeCost stepCost 0 n + n * (hi.size + 8) + (lo.size + hi.size + 5) + Φ x₀ st₀.mem := by
  have hass : Runs w p ω (.assign r lo) st₀ .normal
      { st₀ with regs := Function.update st₀.regs r 0 } (lo.size + 1) :=
    runs_assign_iff.mpr ⟨0, hlo, rfl, rfl, rfl⟩
  obtain ⟨st', c', x', hup, hInv', hc'⟩ :=
    forUp_phi_runs stepCost (Nat.zero_le n) hw hnw
      (fun i st x _ hin hI => hreg i st x hin hI)
      (fun i st x _ hin hI => hhi i st x hin hI)
      (fun i _ hlt st x hI => hbody i hlt st x hI) h0
  refine ⟨st', (lo.size + 1) + c' + 1, x',
    runs_seq_iff.mpr (Or.inr ⟨_, lo.size + 1, c', hass, hup, rfl⟩), hInv', ?_⟩
  simp only [Nat.sub_zero] at hc'
  omega

/-! ## Procedure 1: copying a list of words -/

/-- `[dst, src, n]`: copy `n` words from `src` to `dst`. -/
def copyListStmt : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
     .store (.bin .add (.reg 0) (.reg 3)) (.reg 4)) ;;
  .ret (.const 0)

theorem copyListStmt_noRand : copyListStmt.NoRand := by
  simp [copyListStmt, forRange, forUp, Stmt.NoRand]

/-- Contract of `copyListStmt` for list `L`: source and destination do not overlap. -/
def copyListContract (w : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ dst src, args = [dst, src, L.length] ∧
    16 ≤ 2 ^ w ∧ dst + L.length < 2 ^ w ∧ src + L.length < 2 ^ w ∧
    ListAt mem src L ∧
    (∀ i < L.length, src + i < dst ∨ dst + L.length ≤ src + i)
  post args mem ret mem' := ∃ dst src, args = [dst, src, L.length] ∧ ret = 0 ∧
    ListAt mem' dst L ∧
    ∀ addr, addr < dst ∨ dst + L.length ≤ addr → mem' addr = mem addr
  cost _ _ := 30 * L.length + 20

/-- `copyListStmt` meets `copyListContract`. -/
theorem copyList_meetsContract {w : ℕ} {p : Program} {f : ℕ} {L : List ℕ}
    (hp : p.procs[f]? = some copyListStmt) :
    MeetsContract w p f (copyListContract w L) := by
  refine meetsContract_of_runs hp ?_
  rintro args mem pos ω hargs ⟨dst, src, rfl, hw16, hdstB, hsrcB, hlist, hdisj⟩
  have hn : L.length < 2 ^ w := hargs _ (by simp)
  let frame : (ℕ → ℕ) → Prop := fun m =>
    ∀ addr, addr < dst ∨ dst + L.length ≤ addr → m addr = mem addr
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = L.length ∧ st.regs 3 = k ∧
    ListAt st.mem dst (L.take k) ∧ frame st.mem
  let body : Stmt :=
    .assign 4 (.load (.bin .add (.reg 1) (.reg 3))) ;;
    .store (.bin .add (.reg 0) (.reg 3)) (.reg 4)
  have hLoop : Triple w p (fun st => st = startState [dst, src, L.length] mem pos)
      (forRange 3 (.const 0) (.reg 2) body) (normalPost (Inv L.length))
      (fun _ => (L.length - 0) * (20 + Expr.size (.reg 2) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 2) + 5)) := by
    refine Triple.forRange_const 20 0 L.length (Nat.zero_le _) (by omega) (fun _ => hn)
      (fun st hst => by
        subst hst
        refine ⟨Expr.eval_const (by omega), ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
        · simp [startState]
        · simp [startState]
        · simp [startState]
        · simp
        · intro i hi; simp at hi)
      (fun _ _ _ _ hk => hk.2.2.2.1)
      (fun _ _ _ _ hk => by simp [Expr.eval, hk.2.2.1])
      (fun k _ hk st ω' hInv => by
        obtain ⟨hr0, hr1, hr2, hr3, hLk, hfr⟩ := hInv
        have hval : st.mem (src + k) = L[k] := by
          rw [hfr _ (hdisj k hk)]; exact hlist k hk
        apply runs_start_le
        refine runs_seq_assign_le (v := L[k]) (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_reg_of_eq hr3) (by omega)) hval) ?_
        refine runs_store_le (x := dst + k) (v := L[k])
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
            (Expr.eval_reg_of_eq (by simp [hr3])) (by omega))
          (Expr.eval_reg_of_eq (by simp)) ?_ ?_
        · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simp [Function.update_of_ne, hr0]
          · simp [Function.update_of_ne, hr1]
          · simp [Function.update_of_ne, hr2]
          · simp
          · intro i hi
            rw [List.length_take] at hi
            have hik : i < k + 1 := by omega
            have hiL : i < L.length := by omega
            simp only [List.getElem_take]
            by_cases hiek : i = k
            · subst hiek; simp
            · have hi' : i < (L.take k).length := by rw [List.length_take]; omega
              show Function.update st.mem (dst + k) L[k] (dst + i) = L[i]
              rw [Function.update_of_ne (by omega)]
              simpa [List.getElem_take] using hLk i hi'
          · intro addr ha
            have hne : addr ≠ dst + k := by rcases ha with ha | ha <;> omega
            show Function.update st.mem (dst + k) L[k] addr = mem addr
            rw [Function.update_of_ne hne]
            exact hfr addr ha
          · simp [Function.update_of_ne, hr3]
        · simp only [Expr.size]; omega)
  apply runs_start_le
  refine runs_seq_triple_le hLoop rfl ?_
  rintro st ⟨_, _, _, _, hLn, hfr⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
    ⟨dst, src, rfl, rfl, ?_, hfr⟩ ?_
  · rwa [List.take_of_length_le le_rfl] at hLn
  · simp only [copyListContract, Expr.size]; omega

/-! ## Extracting slot graphs from `bucketSpannerRep` -/

/-- From `bucketSpannerRep SP cap` at `spanTbl` and an active slot `s`, extract its handle `b_s`,
both graphs `G_s` and `H_s` (`DynGraphAt`), their containment `H_s.E ⊆ G_s.E`, their capacity
header words, and their fixed-block bounds inside `bucketFoot`. -/
theorem bucketSpanner_slot_graphs {SP : DSParams} {cap spanTbl s : ℕ}
    {S6 : BucketSpannerState cap} {x6 : (bucketSpannerRep SP cap).τ} {mem : ℕ → ℕ}
    (hrep : (bucketSpannerRep SP cap).rep spanTbl S6 x6 mem)
    (hs : s < cap) (hact : (S6 ⟨s, hs⟩).isSome) :
    ∃ (b_s : ℕ) (d : DSHist), S6 ⟨s, hs⟩ = some d ∧ mem (spanTbl + s) = b_s ∧
      slotGE SP S6 s = (d.state SP).G.E ∧ slotHE SP S6 s = (d.state SP).H.E ∧
      (d.state SP).H.E ⊆ (d.state SP).G.E ∧
      mem (b_s + dsVCapOff) = SP.vCap ∧ mem (b_s + dsECapOff) = SP.eCap ∧
      DynGraphAt mem (dsGPtr b_s) SP.vCap SP.eCap (d.state SP).G ∧
      DynGraphAt mem (dsHPtr b_s SP.vCap SP.eCap) SP.vCap SP.eCap (d.state SP).H ∧
      (∀ a, b_s ≤ a → a < b_s + dsFixedSize SP.L SP.vCap SP.eCap →
        (bucketSpannerRep SP cap).foot spanTbl x6 a) ∧
      dsHPtr b_s SP.vCap SP.eCap + dynGraphSize SP.vCap SP.eCap ≤
        b_s + dsFixedSize SP.L SP.vCap SP.eCap := by
  obtain ⟨hslots, _⟩ := hrep
  specialize hslots ⟨s, hs⟩
  cases hS : S6 ⟨s, hs⟩ with
  | none => simp [hS] at hact
  | some d =>
    rw [hS] at hslots
    cases hx : x6.slots ⟨s, hs⟩ with
    | none => simp [hx] at hslots
    | some bm =>
      rcases bm with ⟨b_s, m⟩
      rw [hx] at hslots
      obtain ⟨hmem_b, hds, _⟩ := hslots
      obtain ⟨hm1, hDSAt, _⟩ := hds
      have hSt := hDSAt.2.2.2.2.2.2.2.1
      have hxv : m.2.vCap = SP.vCap := hSt.1
      have hxe : m.2.eCap = SP.eCap := hSt.2.1
      have hHEsub : (d.state SP).H.E ⊆ (d.state SP).G.E := hSt.2.2.2.2.2.2.2.1
      have hmv : mem (b_s + dsVCapOff) = SP.vCap := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hme : mem (b_s + dsECapOff) = SP.eCap := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hG : DynGraphAt mem (dsGPtr b_s) SP.vCap SP.eCap (d.state SP).G :=
        hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hH : DynGraphAt mem (dsHPtr b_s SP.vCap SP.eCap) SP.vCap SP.eCap (d.state SP).H :=
        hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hle_aux := dsFixedSize_ge_aux b_s SP.L SP.vCap SP.eCap
      have hH_le : dsHPtr b_s SP.vCap SP.eCap + dynGraphSize SP.vCap SP.eCap ≤
          b_s + dsFixedSize SP.L SP.vCap SP.eCap := by
        dsimp only [dsAuxPtr] at hle_aux; omega
      refine ⟨b_s, d, rfl, hmem_b, ?_, ?_, hHEsub, hmv, hme, hG, hH, ?_, hH_le⟩
      · simp [slotGE, hs, hS]
      · simp [slotHE, hs, hS]
      · intro a ha1 ha2
        exact Or.inr ⟨⟨s, hs⟩, b_s, m, hx, Or.inl ⟨ha1, by rwa [hxv, hxe]⟩⟩

/-- In a `bucketSpannerRep`, `slotsHE SP S6 slots ⊆ slotsGE SP S6 slots` when all listed slots
are active. -/
theorem slotsHE_subset_slotsGE {SP : DSParams} {cap spanTbl : ℕ}
    {S6 : BucketSpannerState cap} {x6 : (bucketSpannerRep SP cap).τ} {mem : ℕ → ℕ}
    {slots : List ℕ} (hrep : (bucketSpannerRep SP cap).rep spanTbl S6 x6 mem)
    (hact : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome) :
    slotsHE SP S6 slots ⊆ slotsGE SP S6 slots := by
  intro e he
  rcases Finset.mem_biUnion.mp he with ⟨s, hs, hes⟩
  obtain ⟨hsc, ha⟩ := hact s (List.mem_toFinset.mp hs)
  obtain ⟨_, d, _, _, hGE, hHE, hsub, _⟩ := bucketSpanner_slot_graphs hrep hsc ha
  rw [hHE] at hes
  exact Finset.mem_biUnion.mpr ⟨s, hs, hGE ▸ hsub hes⟩

/-! ## Procedure 2: deleting all edges of `slotsGE` from `S` -/

/-- `[sPtr, spanTbl, slotsPtr, n]`: for each slot `s` listed at `slotsPtr`, delete the edges of
`(d.state SP).G` from the graph at `sPtr` via `delEdgesStmt`. -/
def restartDelSlotsStmt (bLoop : ℕ) : Stmt :=
  forRange 4 (.const 0) (.reg 3)
    (.assign 5 (.load (.bin .add (.reg 2) (.reg 4))) ;;
     .assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
     .assign 7 (.bin .add (.reg 6) (.const dsHdrSize)) ;;
     .assign 8 (.load (.reg 7)) ;;
     .assign 9 (.load (.bin .add (.reg 7) (.const 1))) ;;
     .assign 10 (.load (.bin .add (.reg 7) (.const 3))) ;;
     .assign 11 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 4))
       (.bin .mul (.const 7) (.reg 8))) (.reg 9)) ;;
     .call 12 (bLoop + readIdxDelEdges) [.reg 0, .reg 11, .reg 10]) ;;
  .ret (.const 0)

theorem restartDelSlotsStmt_noRand (bLoop : ℕ) : (restartDelSlotsStmt bLoop).NoRand := by
  simp [restartDelSlotsStmt, forRange, forUp, Stmt.NoRand]

/-- Running `restartDelSlotsStmt` removes `slotsGE SP S6 slots` from `S`, modifies only
`[sPtr, sPtr + dynGraphSize vCap eCap)`, and costs at most
`490 * (slots.map (fun s => (slotGE SP S6 s).card)).sum + 80 * slots.length + 30`. -/
theorem restartDelSlots_runs {w vCap eCap cap : ℕ} {SP : DSParams} {p : Program}
    {bLoop bEdge bOps : ℕ} (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps)) (hpOps : p.HasAt bOps dgOpsProcs)
    {sPtr spanTbl slotsPtr h : ℕ} {slots : List ℕ} {S : MGraph}
    {S6 : BucketSpannerState cap} {x6 : (bucketSpannerRep SP cap).τ}
    {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hsPtrB : sPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hlist : ListAt mem slotsPtr slots) (hlistW : slotsPtr + slots.length < 2 ^ w)
    (hnW : slots.length < 2 ^ w)
    (hS : DynGraphAt mem sPtr vCap eCap S)
    (hrep6 : (bucketSpannerRep SP cap).rep spanTbl S6 x6 mem)
    (hact : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (hfoot6 : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → a < h) (hhW : h < 2 ^ w)
    (hdisj6 : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
      ¬ (bucketSpannerRep SP cap).foot spanTbl x6 a)
    (hdisjL : ∀ i < slots.length,
      slotsPtr + i < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ slotsPtr + i) :
    ∃ o st' c, Runs w p ω (restartDelSlotsStmt bLoop)
        (startState [sPtr, spanTbl, slotsPtr, slots.length] mem pos) o st' c ∧
      (o = .returned 0 ∧
        DynGraphAt st'.mem sPtr vCap eCap { S with E := S.E \ slotsGE SP S6 slots } ∧
        ∀ addr, addr < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ addr → st'.mem addr = mem addr) ∧
      c ≤ 490 * (slots.map fun s => (slotGE SP S6 s).card).sum + 85 * slots.length + 30 := by
  let frame : (ℕ → ℕ) → Prop := fun m =>
    ∀ addr, addr < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ addr → m addr = mem addr
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = sPtr ∧ st.regs 1 = spanTbl ∧ st.regs 2 = slotsPtr ∧ st.regs 3 = slots.length ∧
    st.regs 4 = i ∧
    DynGraphAt st.mem sPtr vCap eCap { S with E := S.E \ slotsGE SP S6 (slots.take i) } ∧
    frame st.mem
  let stepCost : ℕ → ℕ := fun i => 490 * (slotGE SP S6 (slots.getD i 0)).card + 72
  let body : Stmt :=
    .assign 5 (.load (.bin .add (.reg 2) (.reg 4))) ;;
    .assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
    .assign 7 (.bin .add (.reg 6) (.const dsHdrSize)) ;;
    .assign 8 (.load (.reg 7)) ;;
    .assign 9 (.load (.bin .add (.reg 7) (.const 1))) ;;
    .assign 10 (.load (.bin .add (.reg 7) (.const 3))) ;;
    .assign 11 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 4))
      (.bin .mul (.const 7) (.reg 8))) (.reg 9)) ;;
    .call 12 (bLoop + readIdxDelEdges) [.reg 0, .reg 11, .reg 10]
  have hLoop : Triple w p (fun st => st = startState [sPtr, spanTbl, slotsPtr, slots.length] mem pos)
      (forRange 4 (.const 0) (.reg 3) body) (normalPost (Inv slots.length))
      (fun _ => rangeCost stepCost 0 slots.length + slots.length * (Expr.size (.reg 3) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 3) + 5)) := by
    refine Triple.forRange_le stepCost 0 slots.length (Nat.zero_le _) (by omega) (fun _ => hnW)
      (fun st hst => by
        subst hst
        refine ⟨Expr.eval_const (by omega), ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
        · simp [startState]
        · simp [startState]
        · simp [startState]
        · simp [startState]
        · simp
        · simpa [startState, slotsGE] using hS)
      (fun _ _ _ _ hk => hk.2.2.2.2.1)
      (fun _ _ _ _ hk => by simp [Expr.eval, hk.2.2.2.1])
      (fun i _ hi st ω' hInv => by
        obtain ⟨hr0, hr1, hr2, hr3, hr4, hSi, hfr⟩ := hInv
        set s := slots[i] with hs_def
        have hs_mem : s ∈ slots := List.getElem_mem hi
        obtain ⟨hsc, ha⟩ := hact s hs_mem
        obtain ⟨b_s, d, _, hmem_b, hGE_eq, _, _, _, _, hG_s, _, hfoot_bs, hHle⟩ :=
          bucketSpanner_slot_graphs hrep6 hsc ha
        have hbfix : b_s + dsFixedSize SP.L SP.vCap SP.eCap ≤ h := by
          have hpos := dsFixedSize_pos SP.L SP.vCap SP.eCap
          have := hfoot6 (b_s + dsFixedSize SP.L SP.vCap SP.eCap - 1)
            (hfoot_bs _ (by omega) (by omega))
          omega
        have hG_end : dsGPtr b_s + dynGraphSize SP.vCap SP.eCap ≤ b_s + dsFixedSize SP.L SP.vCap SP.eCap := by
          dsimp only [dsHPtr] at hHle; omega
        have hmem_foot : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → st.mem a = mem a := fun a ha' =>
          hfr a (by by_contra hnot; exact hdisj6 a (by omega) (by omega) ha')
        have hval_s : st.mem (slotsPtr + i) = s := by
          rw [hfr _ (hdisjL i hi)]; exact hlist i hi
        have hval_bs : st.mem (spanTbl + s) = b_s := by
          rw [hmem_foot _ (Or.inl ⟨by omega, by omega⟩)]; exact hmem_b
        have hspan_s_lt : spanTbl + s < 2 ^ w :=
          lt_trans (hfoot6 _ (Or.inl ⟨by omega, by omega⟩)) hhW
        have hgs_lt : dsGPtr b_s + dynGraphSize SP.vCap SP.eCap < 2 ^ w := by omega
        have hgs_eq : ∀ a, dsGPtr b_s ≤ a → a < dsGPtr b_s + dynGraphSize SP.vCap SP.eCap →
            st.mem a = mem a := fun a ha1 ha2 =>
          hmem_foot a (hfoot_bs a (by dsimp only [dsGPtr] at ha1; omega) (by omega))
        have hvc_s : st.mem (dsGPtr b_s) = SP.vCap := by
          rw [hgs_eq _ le_rfl (by dsimp only [dynGraphSize]; omega)]
          simpa [dgVCapOff] using hG_s.2.2.2.1
        have hec_s : st.mem (dsGPtr b_s + 1) = SP.eCap := by
          rw [hgs_eq _ (by omega) (by dsimp only [dynGraphSize]; omega)]
          simpa [dgECapOff] using hG_s.2.2.2.2.1
        have hm_s : st.mem (dsGPtr b_s + 3) = (d.state SP).G.m := by
          rw [hgs_eq _ (by omega) (by dsimp only [dynGraphSize]; omega)]
          simpa [dgMOff] using hG_s.2.2.2.2.2.2.1
        obtain ⟨eL, heL_len, _, heL_mem, heL_at, _⟩ := hG_s.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hm_le_eCap : (d.state SP).G.m ≤ SP.eCap := by
          have hsub : (d.state SP).G.E ⊆ Finset.range SP.eCap :=
            fun e he => Finset.mem_range.mpr (hG_s.2.2.1 e he)
          exact (Finset.card_le_card hsub).trans (by simp)
        have heL_at' : ListAt st.mem (dgEListBase (dsGPtr b_s) SP.vCap SP.eCap) eL := fun k hk => by
          rw [hgs_eq _ (by dsimp only [dgEListBase]; omega)
            (by dsimp only [dgEListBase, dynGraphSize]; omega)]
          exact heL_at k hk
        have heL_disj : ∀ k < eL.length,
            dgEListBase (dsGPtr b_s) SP.vCap SP.eCap + k < sPtr ∨
            sPtr + dynGraphSize vCap eCap ≤ dgEListBase (dsGPtr b_s) SP.vCap SP.eCap + k := by
          intro k hk
          by_contra hnot
          have ha_in : (bucketSpannerRep SP cap).foot spanTbl x6
              (dgEListBase (dsGPtr b_s) SP.vCap SP.eCap + k) :=
            hfoot_bs _ (by dsimp only [dgEListBase, dsGPtr]; omega)
              (by dsimp only [dgEListBase, dynGraphSize] at *; omega)
          exact hdisj6 _ (by omega) (by omega) ha_in
        have heL_w : ∀ e ∈ eL, e < 2 ^ w := fun e he => by
          have := hG_s.2.2.1 e ((heL_mem e).mp he)
          dsimp only [dynGraphSize] at hgs_lt; omega
        have heL_bound : dgEListBase (dsGPtr b_s) SP.vCap SP.eCap + eL.length < 2 ^ w := by
          dsimp only [dgEListBase, dynGraphSize] at *; omega
        have hcard_eq : eL.length = (slotGE SP S6 (slots.getD i 0)).card := by
          rw [List.getD_eq_getElem _ _ hi, hGE_eq]; exact heL_len
        apply runs_start_le
        dsimp only [body]
        refine runs_seq_assign_le (v := s) (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr4) (by omega)) hval_s) ?_
        refine runs_seq_assign_le (v := b_s) (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr1])) (Expr.eval_reg_of_eq (by simp))
            hspan_s_lt) hval_bs) ?_
        refine runs_seq_assign_le (v := dsGPtr b_s) (Expr.eval_add
          (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by dsimp [dsHdrSize]; omega))
          (by dsimp [dsGPtr, dynGraphSize] at hgs_lt ⊢; omega)) ?_
        refine runs_seq_assign_le (v := SP.vCap) (Expr.eval_load_of_eq
          (Expr.eval_reg_of_eq (by simp)) hvc_s) ?_
        refine runs_seq_assign_le (v := SP.eCap) (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega))
            (by dsimp [dynGraphSize] at hgs_lt; omega)) hec_s) ?_
        refine runs_seq_assign_le (v := eL.length) (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega))
            (by dsimp [dynGraphSize] at hgs_lt; omega)) (hm_s.trans heL_len.symm)) ?_
        have hgs_4 : dsGPtr b_s + 4 < 2 ^ w := by dsimp [dynGraphSize] at hgs_lt; omega
        have hgs_7v : 7 * SP.vCap < 2 ^ w := by dsimp [dynGraphSize] at hgs_lt; omega
        have hgs_add1 : dsGPtr b_s + 4 + 7 * SP.vCap < 2 ^ w := by dsimp [dynGraphSize] at hgs_lt; omega
        have hgs_el : dsGPtr b_s + 4 + 7 * SP.vCap + SP.eCap < 2 ^ w := by dsimp [dynGraphSize] at hgs_lt; omega
        refine runs_seq_assign_le (v := dgEListBase (dsGPtr b_s) SP.vCap SP.eCap)
          (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_const (by omega)) hgs_4)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) hgs_7v) hgs_add1)
            (Expr.eval_reg_of_eq (by simp)) hgs_el) ?_
        refine runs_call_le (delEdges_meetsContract (G := { S with E := S.E \ slotsGE SP S6 (slots.take i) })
          (l := eL) (vCap := vCap) (eCap := eCap) hpLoop hpEdge hpOps)
          (vs := [sPtr, dgEListBase (dsGPtr b_s) SP.vCap SP.eCap, eL.length])
          (by simp [evalArgs, Expr.eval, hr0])
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl | rfl | rfl)
              · dsimp only [dynGraphSize] at hsPtrB; omega
              · omega
              · omega)
          ⟨sPtr, dgEListBase (dsGPtr b_s) SP.vCap SP.eCap, rfl, hw16, hsPtrB, heL_bound,
            heL_at', heL_w, heL_disj, hSi⟩ ?_
        rintro _ mem' _ ⟨_, _, hEq, _, hS', hfr'⟩
        simp only [List.cons.injEq, and_true] at hEq
        obtain ⟨rfl, _⟩ := hEq
        refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · simp [Function.update_of_ne, hr0]
        · simp [Function.update_of_ne, hr1]
        · simp [Function.update_of_ne, hr2]
        · simp [Function.update_of_ne, hr3]
        · simp
        · have hE_eq : (S.E \ slotsGE SP S6 (slots.take i)) \ eL.toFinset =
              S.E \ slotsGE SP S6 (slots.take (i + 1)) := by
            rw [List.take_succ_eq_append_getElem hi]
            ext e
            simp only [Finset.mem_sdiff, List.mem_toFinset, slotsGE, Finset.mem_biUnion,
              List.mem_append, List.mem_singleton, heL_mem, ← hGE_eq, hs_def]
            constructor
            · rintro ⟨⟨heS, hnot⟩, hne⟩
              refine ⟨heS, ?_⟩
              rintro ⟨s', hs' | rfl, hes'⟩
              · exact hnot ⟨s', hs', hes'⟩
              · exact hne hes'
            · rintro ⟨heS, hnot⟩
              exact ⟨⟨heS, fun ⟨s', hs', hes'⟩ => hnot ⟨s', Or.inl hs', hes'⟩⟩,
                fun he => hnot ⟨slots[i], Or.inr rfl, he⟩⟩
          simpa only [hE_eq] using hS'
        · exact fun addr ha => (hfr' addr ha).trans (hfr addr ha)
        · simp [Function.update_of_ne, hr4]
        · dsimp only [delEdgesContract, argsSize, Expr.size, stepCost] at *
          rw [← hcard_eq]
          omega)
  apply runs_start_le
  refine runs_seq_triple_le hLoop rfl ?_
  rintro st ⟨_, _, _, _, _, hSn, hfr⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ⟨rfl, ?_, hfr⟩ ?_
  · rwa [List.take_of_length_le le_rfl] at hSn
  · have hsum : rangeCost stepCost 0 slots.length =
        490 * (slots.map fun s => (slotGE SP S6 s).card).sum + 72 * slots.length := by
      have h1 := rangeCost_eq_sum_map slots 0 (fun s => 490 * (slotGE SP S6 s).card + 72)
      dsimp only [stepCost]
      rw [h1]
      have hlin : ∀ (L : List ℕ) (f : ℕ → ℕ),
          (L.map fun s => 490 * f s + 72).sum = 490 * (L.map f).sum + 72 * L.length := by
        intro L f
        induction L with
        | nil => simp
        | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
      exact hlin slots (fun s => (slotGE SP S6 s).card)
    rw [hsum]
    simp only [Expr.size]
    omega

end MinCostFlow.SparseCore.Program.Read
