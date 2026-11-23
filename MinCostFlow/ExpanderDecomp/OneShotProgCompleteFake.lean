module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OneShotProgLayout
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase
import Mathlib.Tactic.Linarith

/-!
# Fake-Edge Completion Word-RAM Primitive for `OneShot`

Implements and verifies `completeFakeProc`, a deterministic (`NoRand`), strictly local Word-RAM
procedure using the reusable zero-initialized marker buffer `locAddr` of size `n` (never scanning
`range n`, restoring `locAddr` to all zeros on exit): computes `completeMatchingFake A B M` from
sorted `A`, sorted `B` (`|A| ≤ |B|`), and a partial matching `M ⊆ A × B`, writing the resulting
fake edges directly into `outAddr` (`EdgesAt`) with zero extra scratch space and returning their
count in `O(|A| + |B| + |M| + 1)` time.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. `completeFakeProc` -/

/-- Compute `completeMatchingFake A B M` in 6 linear passes using reusable zeroed `locAddr`:
`args = [lenA, aAddr, lenB, bAddr, lenM, mAddr, locAddr, outAddr]`.
Writes `completeMatchingFake A B M` directly at `outAddr` (`EdgesAt`) and returns its length. -/
def completeFakeProc : Stmt :=
  seqStmts
    [ -- Pass 1: mark `e.1` for `e ∈ M`
      forRange 8 (.const 0) (.reg 4)
        (seqStmts
          [ .assign 11 (.load (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 8))))
          , .store (.bin .add (.reg 6) (.reg 11)) (.const 1) ])
    , -- Pass 2: write `unmatchedFst A M` into even slots `outAddr + 2 * cnt`
      .assign 9 (.const 0)
    , forRange 8 (.const 0) (.reg 0)
        (seqStmts
          [ .assign 11 (.load (.bin .add (.reg 1) (.reg 8)))
          , .assign 12 (.load (.bin .add (.reg 6) (.reg 11)))
          , .cond (.bin .eq (.reg 12) (.const 0))
              (seqStmts
                [ .store (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 9))) (.reg 11)
                , .assign 9 (.bin .add (.reg 9) (.const 1)) ])
              .nop ])
    , -- Pass 3: clear `e.1` marks
      forRange 8 (.const 0) (.reg 4)
        (seqStmts
          [ .assign 11 (.load (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 8))))
          , .store (.bin .add (.reg 6) (.reg 11)) (.const 0) ])
    , -- Pass 4: mark `e.2` for `e ∈ M`
      forRange 8 (.const 0) (.reg 4)
        (seqStmts
          [ .assign 11 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 8))) (.const 1)))
          , .store (.bin .add (.reg 6) (.reg 11)) (.const 1) ])
    , -- Pass 5: write first `cnt` elements of `unmatchedSnd B M` into odd slots `outAddr + 2 * j + 1`
      .assign 10 (.const 0)
    , forRange 8 (.const 0) (.reg 2)
        (.cond (.bin .lt (.reg 10) (.reg 9))
          (seqStmts
            [ .assign 11 (.load (.bin .add (.reg 3) (.reg 8)))
            , .assign 12 (.load (.bin .add (.reg 6) (.reg 11)))
            , .cond (.bin .eq (.reg 12) (.const 0))
                (seqStmts
                  [ .store (.bin .add (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 10))) (.const 1)) (.reg 11)
                  , .assign 10 (.bin .add (.reg 10) (.const 1)) ])
                .nop ])
          .nop)
    , -- Pass 6: clear `e.2` marks
      forRange 8 (.const 0) (.reg 4)
        (seqStmts
          [ .assign 11 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 8))) (.const 1)))
          , .store (.bin .add (.reg 6) (.reg 11)) (.const 0) ])
    , .ret (.reg 9) ]

def completeFakeCost (lenA lenB lenM : ℕ) : ℕ :=
  70 * lenA + 80 * lenB + 160 * lenM + 160

def CompleteFakeWordBound (w n lenA lenB lenM aAddr bAddr mAddr locAddr outAddr : ℕ) : Prop :=
  aAddr + lenA < 2 ^ w ∧
  bAddr + lenB < 2 ^ w ∧
  mAddr + 2 * lenM < 2 ^ w ∧
  locAddr + n < 2 ^ w ∧
  outAddr + 2 * lenA < 2 ^ w ∧
  2 * lenA + 2 < 2 ^ w ∧
  lenB + 1 < 2 ^ w ∧
  2 * lenM + 2 < 2 ^ w ∧
  16 < 2 ^ w

def CompleteFakeDisjoint (n lenA lenB lenM aAddr bAddr mAddr locAddr outAddr : ℕ) : Prop :=
  DisjointRange locAddr n aAddr lenA ∧
  DisjointRange locAddr n bAddr lenB ∧
  DisjointRange locAddr n mAddr (2 * lenM) ∧
  DisjointRange locAddr n outAddr (2 * lenA) ∧
  DisjointRange outAddr (2 * lenA) aAddr lenA ∧
  DisjointRange outAddr (2 * lenA) bAddr lenB ∧
  DisjointRange outAddr (2 * lenA) mAddr (2 * lenM)

/-- Contract for `completeFakeProc`:
`args = [lenA, aAddr, lenB, bAddr, lenM, mAddr, locAddr, outAddr]`.
Writes `F = completeMatchingFake A B M` at `outAddr`, returns `F.length`, restores `locAddr` to
all zeros, and preserves memory outside `[outAddr, outAddr + 2 * lenA)`. -/
def completeFakeContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n lenA aAddr lenB bAddr lenM mAddr locAddr outAddr : ℕ)
      (A B : Finset ℕ) (M : List (ℕ × ℕ)),
      args = [lenA, aAddr, lenB, bAddr, lenM, mAddr, locAddr, outAddr] ∧
      VertsAt mem aAddr lenA A ∧ VertsAt mem bAddr lenB B ∧
      A.card ≤ B.card ∧ A ⊆ Finset.range n ∧ B ⊆ Finset.range n ∧
      M.length = lenM ∧ EdgesAt mem mAddr M ∧
      (∀ e ∈ M, e.1 ∈ A ∧ e.2 ∈ B) ∧
      (M.map Prod.fst).Nodup ∧ (M.map Prod.snd).Nodup ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      CompleteFakeWordBound w n lenA lenB lenM aAddr bAddr mAddr locAddr outAddr ∧
      CompleteFakeDisjoint n lenA lenB lenM aAddr bAddr mAddr locAddr outAddr
  post args mem v mem' :=
    let lenA := args.getD 0 0
    let aAddr := args.getD 1 0
    let lenB := args.getD 2 0
    let bAddr := args.getD 3 0
    let lenM := args.getD 4 0
    let mAddr := args.getD 5 0
    let outAddr := args.getD 7 0
    let A := (readList mem aAddr lenA).toFinset
    let B := (readList mem bAddr lenB).toFinset
    let M := readEdges mem mAddr lenM
    let F := completeMatchingFake A B M
    v = F.length ∧ v ≤ lenA ∧
    EdgesAt mem' outAddr F ∧
    MemFrame mem mem' outAddr (outAddr + 2 * lenA)
  cost args _ := completeFakeCost (args.getD 0 0) (args.getD 2 0) (args.getD 4 0)


end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

theorem completeFakeProc_noRand : completeFakeProc.NoRand := by
  simp [completeFakeProc, seqStmts, forRange, forUp, Stmt.NoRand]


/-! ## 5. Verification of `completeFakeProc` -/

private structure FakeRegs (lenA aAddr lenB bAddr lenM mAddr locAddr outAddr : ℕ)
    (st : State) : Prop where
  r0 : st.regs 0 = lenA
  r1 : st.regs 1 = aAddr
  r2 : st.regs 2 = lenB
  r3 : st.regs 3 = bAddr
  r4 : st.regs 4 = lenM
  r5 : st.regs 5 = mAddr
  r6 : st.regs 6 = locAddr
  r7 : st.regs 7 = outAddr

private lemma fakeRegs_update_ge {lenA aAddr lenB bAddr lenM mAddr locAddr outAddr : ℕ}
    {st : State} {r v : ℕ} (hr : 8 ≤ r)
    (h : FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr st) :
    FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr
      { st with regs := Function.update st.regs r v } :=
  ⟨by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r0,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r1,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r2,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r3,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r4,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r5,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r6,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r7⟩

private lemma fakeRegs_update_mem {lenA aAddr lenB bAddr lenM mAddr locAddr outAddr : ℕ}
    {st : State} {mem' : ℕ → ℕ}
    (h : FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr st) :
    FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr { st with mem := mem' } :=
  ⟨h.r0, h.r1, h.r2, h.r3, h.r4, h.r5, h.r6, h.r7⟩

/-- Passes 1, 3, 4, 6 helper: marks or clears `locAddr[M[t].1]` (`useSnd = false`) or
`locAddr[M[t].2]` (`useSnd = true`) with `val`. -/
private lemma edgeMarkLoop_triple
    {w n lenA aAddr lenB bAddr lenM mAddr locAddr outAddr val : ℕ} (useSnd : Bool)
    (p : Program) (mem₀ : ℕ → ℕ) (M : List (ℕ × ℕ)) (st₀ : State)
    (hMlen : M.length = lenM) (hM_lt : ∀ e ∈ M, e.1 < n ∧ e.2 < n)
    (hM_at : EdgesAt st₀.mem mAddr M)
    (hdisj_lm : DisjointRange locAddr n mAddr (2 * lenM))
    (hpr0 : PreservedOutside2 mem₀ st₀.mem locAddr (locAddr + n) outAddr (outAddr + 2 * lenA))
    (hval_w : val < 2 ^ w)
    (hw : CompleteFakeWordBound w n lenA lenB lenM aAddr bAddr mAddr locAddr outAddr)
    (hregs : FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr st₀) :
    let addrExpr : Expr :=
      if useSnd then .bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 8))) (.const 1)
      else .bin .add (.reg 5) (.bin .mul (.const 2) (.reg 8))
    let proj : ℕ × ℕ → ℕ := if useSnd then Prod.snd else Prod.fst
    Triple w p (fun st => st = st₀)
      (forRange 8 (.const 0) (.reg 4)
        (seqStmts
          [ .assign 11 (.load addrExpr)
          , .store (.bin .add (.reg 6) (.reg 11)) (.const val) ]))
      (normalPost fun st' =>
        FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr st' ∧
        st'.regs 9 = st₀.regs 9 ∧ st'.regs 10 = st₀.regs 10 ∧
        PreservedOutside2 mem₀ st'.mem locAddr (locAddr + n) outAddr (outAddr + 2 * lenA) ∧
        (∀ a, (a < locAddr ∨ locAddr + n ≤ a) → st'.mem a = st₀.mem a) ∧
        (∀ u < n, st'.mem (locAddr + u) = if u ∈ M.map proj then val else st₀.mem (locAddr + u)))
      (fun _ => 38 * lenM + 25) := by
  intro addrExpr proj
  rcases hw with ⟨_, _, hm_w, hloc_w, _, _, _, hm2_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun t st =>
    FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr st ∧
    st.regs 8 = t ∧ st.regs 9 = st₀.regs 9 ∧ st.regs 10 = st₀.regs 10 ∧
    PreservedOutside2 mem₀ st.mem locAddr (locAddr + n) outAddr (outAddr + 2 * lenA) ∧
    (∀ a, (a < locAddr ∨ locAddr + n ≤ a) → st.mem a = st₀.mem a) ∧
    (∀ u < n, st.mem (locAddr + u) =
      if u ∈ (M.take t).map proj then val else st₀.mem (locAddr + u))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 4)
    (body := seqStmts
      [ .assign 11 (.load addrExpr)
      , .store (.bin .add (.reg 6) (.reg 11)) (.const val) ])
    (P := fun st => st = st₀) (Inv := Inv) 26 0 lenM (Nat.zero_le lenM) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        fakeRegs_update_ge (r := 8) (by decide) hregs, by simp, by simp, by simp,
        hpr0, fun _ _ => rfl, fun u _ => by simp⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r4)
    (fun t _ htlt => by
      intro st ω' ⟨hr, ht, hr9, hr10, hpr, hloc_fr, hmap⟩
      have ht_lt : t < M.length := hMlen ▸ htlt
      set vtx := proj (M[t]'ht_lt)
      have hv_lt : vtx < n := by
        cases useSnd
        · exact (hM_lt _ (List.getElem_mem ht_lt)).1
        · exact (hM_lt _ (List.getElem_mem ht_lt)).2
      have hload : (Expr.load addrExpr).eval w st = some vtx := by
        cases useSnd
        · have hmem : st.mem (mAddr + 2 * t) = (M[t]'ht_lt).1 := by
            rw [hloc_fr (mAddr + 2 * t) (disjointRange_outside hdisj_lm (by omega) (by omega))]
            exact (hM_at t ht_lt).1
          exact Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq hr.r5)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq ht) (by omega))
              (by omega)) hmem
        · have hmem : st.mem (mAddr + 2 * t + 1) = (M[t]'ht_lt).2 := by
            rw [hloc_fr (mAddr + 2 * t + 1) (disjointRange_outside hdisj_lm (by omega) (by omega))]
            exact (hM_at t ht_lt).2
          exact Expr.eval_load_of_eq
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq hr.r5)
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq ht) (by omega))
                (by omega))
              (Expr.eval_const hw2) (by omega)) hmem
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := vtx) hload ?_
      refine runs_store_le (x := locAddr + vtx) (v := val)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r6]))
          (Expr.eval_reg_of_eq (v := vtx) (by simp)) (by omega))
        (Expr.eval_const hval_w) ?_ (by cases useSnd <;> simp [addrExpr, Expr.size])
      refine ⟨⟨fakeRegs_update_ge (r := 8) (by decide)
          (fakeRegs_update_mem (fakeRegs_update_ge (r := 11) (by decide) hr)),
        by simp, by simp [hr9], by simp [hr10], ?_, ?_, ?_⟩, by simp [ht]⟩
      · intro a hal hao
        dsimp only
        rw [Function.update_of_ne (by rcases hal with h | h <;> omega)]
        exact hpr a hal hao
      · intro a hal
        dsimp only
        rw [Function.update_of_ne (by rcases hal with h | h <;> omega)]
        exact hloc_fr a hal
      · intro u hu
        dsimp only
        rw [List.take_succ_eq_append_getElem ht_lt, List.map_append, List.map_singleton]
        by_cases huv : u = vtx
        · subst huv
          simp only [vtx, Function.update_self, List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
        · rw [Function.update_of_ne (by omega)]
          have huv' : u ≠ proj (M[t]'ht_lt) := huv
          simp only [List.mem_append, List.mem_singleton, huv', or_false]
          exact hmap u hu)
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size]; omega)
  rintro o st' hpost
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hr, _, hr9, hr10, hpr, hloc_fr, hmap⟩
    refine ⟨hr, hr9, hr10, hpr, hloc_fr, fun u hu => ?_⟩
    have ht := hmap u hu
    rw [← hMlen, List.take_length] at ht
    exact ht

theorem completeFakeProc_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hb : p.procs[b]? = some completeFakeProc) :
    MeetsContract w p b (completeFakeContract w) := by
  refine meetsContract_of_runs hb fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, lenA, aAddr, lenB, bAddr, lenM, mAddr, locAddr, outAddr, A, B, M, rfl,
    hAat, hBat, hAB, hAn, hBn, hMlen, hMat, hMmem, hMfst, hMsnd, hloc0, hw, hdisj⟩
  have hAlen : (A.sort (· ≤ ·)).length = lenA := by rw [Finset.length_sort, ← hAat.1]
  have hBlen : (B.sort (· ≤ ·)).length = lenB := by rw [Finset.length_sort, ← hBat.1]
  have hAfin : (readList mem aAddr lenA).toFinset = A := hAat.toNodupVertsAt.2
  have hBfin : (readList mem bAddr lenB).toFinset = B := hBat.toNodupVertsAt.2
  have hMread : readEdges mem mAddr lenM = M := by
    apply List.ext_getElem
    · simp [readEdges, hMlen]
    · intro j hj1 hj2
      simp only [readEdges, List.getElem_map, List.getElem_range]
      exact Prod.ext (hMat j hj2).1 (hMat j hj2).2
  have hA_lt : ∀ u ∈ A.sort (· ≤ ·), u < n := fun u hu =>
    Finset.mem_range.mp (hAn ((Finset.mem_sort _).mp hu))
  have hB_lt : ∀ u ∈ B.sort (· ≤ ·), u < n := fun u hu =>
    Finset.mem_range.mp (hBn ((Finset.mem_sort _).mp hu))
  have hM_lt : ∀ e ∈ M, e.1 < n ∧ e.2 < n := fun e he =>
    ⟨Finset.mem_range.mp (hAn (hMmem e he).1), Finset.mem_range.mp (hBn (hMmem e he).2)⟩
  rcases hdisj with ⟨hd_la, hd_lb, hd_lm, hd_lo, hd_oa, hd_ob, hd_om⟩
  rcases hw with ⟨ha_w, hb_w, hm_w, hloc_w, hout_w, ha2_w, hb1_w, hm2_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  have hw_pack : CompleteFakeWordBound w n lenA lenB lenM aAddr bAddr mAddr locAddr outAddr :=
    ⟨ha_w, hb_w, hm_w, hloc_w, hout_w, ha2_w, hb1_w, hm2_w, hw16⟩
  have hregs0 : FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr
      (startState [lenA, aAddr, lenB, bAddr, lenM, mAddr, locAddr, outAddr] mem pos) :=
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], by simp [startState]⟩
  -- Pass 1: mark `M.map Prod.fst` in `locAddr`.
  have hP1 := edgeMarkLoop_triple (val := 1) false p mem M
    (startState [lenA, aAddr, lenB, bAddr, lenM, mAddr, locAddr, outAddr] mem pos)
    hMlen hM_lt hMat hd_lm (fun _ _ _ => rfl) hw2 hw_pack hregs0
  obtain ⟨o₁, st₁, c₁, hrun₁, hInv₁, hc₁⟩ := hP1.runs ω rfl
  cases o₁ with
  | returned _ => exact False.elim hInv₁
  | normal =>
  rcases hInv₁ with ⟨hr₁, _, _, hpr₁, _, hmap₁⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hmap₁
  -- Assign `r9 := 0`.
  set st₂ : State := { st₁ with regs := Function.update st₁.regs 9 0 }
  have hrun₂ : Runs w p ω (.assign 9 (.const 0)) st₁ .normal st₂ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  -- Pass 2: write `unmatchedFst A M` into even slots `outAddr + 2 * j`.
  let predA : ℕ → Bool := fun u => decide (u ∉ M.map Prod.fst)
  let Inv2 : ℕ → State → Prop := fun i st =>
    let pref := ((A.sort (· ≤ ·)).take i).filter predA
    FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr st ∧
    st.regs 8 = i ∧ st.regs 9 = pref.length ∧
    PreservedOutside2 mem st.mem locAddr (locAddr + n) outAddr (outAddr + 2 * lenA) ∧
    (∀ a, (a < outAddr ∨ outAddr + 2 * lenA ≤ a) → st.mem a = st₁.mem a) ∧
    (∀ j (hj : j < pref.length), st.mem (outAddr + 2 * j) = pref[j]'hj)
  have hP2 := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 0)
    (body := seqStmts
      [ .assign 11 (.load (.bin .add (.reg 1) (.reg 8)))
      , .assign 12 (.load (.bin .add (.reg 6) (.reg 11)))
      , .cond (.bin .eq (.reg 12) (.const 0))
          (seqStmts
            [ .store (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 9))) (.reg 11)
            , .assign 9 (.bin .add (.reg 9) (.const 1)) ])
          .nop ])
    (P := fun st => st = st₂) (Inv := Inv2) 55 0 lenA (Nat.zero_le lenA) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        fakeRegs_update_ge (r := 8) (by decide) (fakeRegs_update_ge (r := 9) (by decide) hr₁),
        by simp, by simp [st₂], hpr₁, fun _ _ => rfl, fun j hj => by simp at hj⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r0)
    (fun i _ hilt => by
      intro st ω' ⟨hr, hi, hcnt, hpr, hout_fr, heven⟩
      have hi_lt : i < (A.sort (· ≤ ·)).length := hAlen ▸ hilt
      set u := (A.sort (· ≤ ·))[i]'hi_lt
      have hu_lt : u < n := hA_lt u (List.getElem_mem hi_lt)
      have hmem_a : st.mem (aAddr + i) = u := by
        rw [hpr (aAddr + i)
          (disjointRange_outside hd_la (by omega) (by omega))
          (disjointRange_outside hd_oa (by omega) (by omega))]
        exact hAat.2 i hi_lt
      have hmem_loc : st.mem (locAddr + u) = if u ∈ M.map Prod.fst then 1 else 0 := by
        rw [hout_fr (locAddr + u) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
          hmap₁ u hu_lt]
        dsimp only [startState]
        rw [hloc0 u hu_lt]
      have hcnt_le : ((A.sort (· ≤ ·)).take i |>.filter predA).length ≤ i := by
        calc _ ≤ ((A.sort (· ≤ ·)).take i).length := List.length_filter_le _ _
          _ ≤ i := by rw [List.length_take]; exact Nat.min_le_left _ _
      set mVal : ℕ := if u ∈ M.map Prod.fst then 1 else 0
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r1) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_a) ?_
      refine runs_seq_assign_le (v := mVal)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r6]))
            (Expr.eval_reg_of_eq (v := u) (by simp)) (by omega))
          hmem_loc) ?_
      refine runs_cond_le
        (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := mVal) (by simp)) (Expr.eval_const (by omega)) hw2) ?_ ?_
      · intro hne
        have huM : u ∉ M.map Prod.fst := by by_cases h : u ∈ M.map Prod.fst <;> simp_all [mVal]
        have hpu : predA u = true := by simp [predA, huM]
        dsimp only [seqStmts]
        refine runs_seq_store_le
          (x := outAddr + 2 * ((A.sort (· ≤ ·)).take i |>.filter predA).length) (v := u)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := outAddr) (by simp [hr.r7]))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := ((A.sort (· ≤ ·)).take i |>.filter predA).length)
                (by simp [hcnt])) (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := u) (by simp)) ?_
        refine runs_assign_le (v := ((A.sort (· ≤ ·)).take i |>.filter predA).length + 1)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := ((A.sort (· ≤ ·)).take i |>.filter predA).length)
              (by simp [hcnt])) (Expr.eval_const hw2) (by omega)) ?_ (by simp [Expr.size])
        have htake : ((A.sort (· ≤ ·)).take (i + 1)).filter predA =
            ((A.sort (· ≤ ·)).take i).filter predA ++ [u] := by
          rw [List.take_succ_eq_append_getElem hi_lt, List.filter_append, List.filter_cons,
            List.filter_nil, hpu]; simp [u]
        refine ⟨⟨fakeRegs_update_ge (r := 8) (by decide)
            (fakeRegs_update_ge (r := 9) (by decide)
              (fakeRegs_update_mem (fakeRegs_update_ge (r := 12) (by decide)
                (fakeRegs_update_ge (r := 11) (by decide) hr)))),
          by simp, by rw [htake, List.length_append, List.length_singleton]; simp,
          ?_, ?_, ?_⟩, by simp [hi]⟩
        · intro a hal hao
          dsimp only
          rw [Function.update_of_ne (by rcases hao with h | h <;> omega)]
          exact hpr a hal hao
        · intro a hao
          dsimp only
          rw [Function.update_of_ne (by rcases hao with h | h <;> omega)]
          exact hout_fr a hao
        · intro j hj
          dsimp only
          revert hj
          rw [htake]
          intro hj
          rw [List.length_append, List.length_singleton] at hj
          by_cases hjeq : j = ((A.sort (· ≤ ·)).take i |>.filter predA).length
          · subst hjeq; simp
          · have hjlt' : j < ((A.sort (· ≤ ·)).take i |>.filter predA).length := by omega
            rw [Function.update_of_ne (by omega), List.getElem_append_left hjlt']
            exact heven j hjlt'
      · intro heq
        have huM : u ∈ M.map Prod.fst := by by_cases h : u ∈ M.map Prod.fst <;> simp_all [mVal]
        have hpu : predA u = false := by simp [predA, huM]
        refine runs_nop_le ?_ (by simp [Expr.size])
        have htake : ((A.sort (· ≤ ·)).take (i + 1)).filter predA =
            ((A.sort (· ≤ ·)).take i).filter predA := by
          rw [List.take_succ_eq_append_getElem hi_lt, List.filter_append, List.filter_cons,
            List.filter_nil, hpu]; simp
        refine ⟨⟨fakeRegs_update_ge (r := 8) (by decide)
            (fakeRegs_update_ge (r := 12) (by decide) (fakeRegs_update_ge (r := 11) (by decide) hr)),
          by simp, by rw [htake]; simp [hcnt], hpr, hout_fr, by rw [htake]; exact heven⟩,
          by simp [hi]⟩)
  obtain ⟨o₃, st₃, c₃, hrun₃, hInv₃, hc₃⟩ := hP2.runs ω rfl
  cases o₃ with
  | returned _ => exact False.elim hInv₃
  | normal =>
  rcases hInv₃ with ⟨hr₃, _, hcnt₃, hpr₃, hout_fr₃, heven₃⟩
  set lsA := unmatchedFst A M
  have hlsA_eq : ((A.sort (· ≤ ·)).take lenA).filter predA = lsA := by
    rw [← hAlen, List.take_length]
    have h1 := filter_sort_eq_sort_sdiff A (M.map Prod.fst).toFinset
    have h2 : (A.sort (· ≤ ·)).filter predA =
        (A.sort (· ≤ ·)).filter (fun v => decide (v ∉ (M.map Prod.fst).toFinset)) := by
      congr 1; funext v; simp [predA]
    rw [h2, h1]; rfl
  rw [hlsA_eq] at hcnt₃ heven₃
  have hlsA_le : lsA.length ≤ lenA := by
    have h1 : lsA.length = ((A.sort (· ≤ ·)).filter predA).length := by
      rw [← hlsA_eq, ← hAlen, List.take_length]
    rw [h1, ← hAlen]; exact List.length_filter_le _ _
  -- Pass 3: clear `M.map Prod.fst` marks.
  have hMat₃ : EdgesAt st₃.mem mAddr M := fun j hj => by
    have h1 := hpr₃ (mAddr + 2 * j) (disjointRange_outside hd_lm (by omega) (by omega))
      (disjointRange_outside hd_om (by omega) (by omega))
    have h2 := hpr₃ (mAddr + 2 * j + 1) (disjointRange_outside hd_lm (by omega) (by omega))
      (disjointRange_outside hd_om (by omega) (by omega))
    rw [h1, h2]; exact hMat j hj
  have hP3 := edgeMarkLoop_triple (val := 0) false p mem M st₃
    hMlen hM_lt hMat₃ hd_lm hpr₃ (by omega) hw_pack hr₃
  obtain ⟨o₄, st₄, c₄, hrun₄, hInv₄, hc₄⟩ := hP3.runs ω rfl
  cases o₄ with
  | returned _ => exact False.elim hInv₄
  | normal =>
  rcases hInv₄ with ⟨hr₄, hr9₄, _, hpr₄, hloc_fr₄, hmap₄⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hmap₄
  have hloc_zero₄ : ∀ u < n, st₄.mem (locAddr + u) = 0 := by
    intro u hu
    rw [hmap₄ u hu]
    by_cases hm : u ∈ M.map Prod.fst
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      rw [hout_fr₃ (locAddr + u) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
        hmap₁ u hu]
      dsimp only [startState]
      simp [hm, hloc0 u hu]
  have heven₄ : ∀ j (hj : j < lsA.length), st₄.mem (outAddr + 2 * j) = lsA[j]'hj := by
    intro j hj
    rw [hloc_fr₄ (outAddr + 2 * j) (disjointRange_outside hd_lo (by omega) (by omega))]
    exact heven₃ j hj
  -- Pass 4: mark `M.map Prod.snd` in `locAddr`.
  have hMat₄ : EdgesAt st₄.mem mAddr M := fun j hj => by
    have h1 := hpr₄ (mAddr + 2 * j) (disjointRange_outside hd_lm (by omega) (by omega))
      (disjointRange_outside hd_om (by omega) (by omega))
    have h2 := hpr₄ (mAddr + 2 * j + 1) (disjointRange_outside hd_lm (by omega) (by omega))
      (disjointRange_outside hd_om (by omega) (by omega))
    rw [h1, h2]; exact hMat j hj
  have hP4 := edgeMarkLoop_triple (val := 1) true p mem M st₄
    hMlen hM_lt hMat₄ hd_lm hpr₄ hw2 hw_pack hr₄
  obtain ⟨o₅, st₅, c₅, hrun₅, hInv₅, hc₅⟩ := hP4.runs ω rfl
  cases o₅ with
  | returned _ => exact False.elim hInv₅
  | normal =>
  rcases hInv₅ with ⟨hr₅, hr9₅, _, hpr₅, hloc_fr₅, hmap₅⟩
  simp only [↓reduceIte] at hmap₅
  have heven₅ : ∀ j (hj : j < lsA.length), st₅.mem (outAddr + 2 * j) = lsA[j]'hj := by
    intro j hj
    rw [hloc_fr₅ (outAddr + 2 * j) (disjointRange_outside hd_lo (by omega) (by omega))]
    exact heven₄ j hj
  -- Assign `r10 := 0`.
  set st₆ : State := { st₅ with regs := Function.update st₅.regs 10 0 }
  have hrun₆ : Runs w p ω (.assign 10 (.const 0)) st₅ .normal st₆ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  -- Pass 5: write first `lsA.length` elements of `unmatchedSnd B M` into odd slots.
  let predB : ℕ → Bool := fun v => decide (v ∉ M.map Prod.snd)
  let Inv5 : ℕ → State → Prop := fun i st =>
    let pref := (((B.sort (· ≤ ·)).take i).filter predB).take lsA.length
    FakeRegs lenA aAddr lenB bAddr lenM mAddr locAddr outAddr st ∧
    st.regs 8 = i ∧ st.regs 9 = lsA.length ∧ st.regs 10 = pref.length ∧
    PreservedOutside2 mem st.mem locAddr (locAddr + n) outAddr (outAddr + 2 * lenA) ∧
    (∀ a, (a < outAddr ∨ outAddr + 2 * lenA ≤ a) → st.mem a = st₅.mem a) ∧
    (∀ j (hj : j < lsA.length), st.mem (outAddr + 2 * j) = lsA[j]'hj) ∧
    (∀ j (hj : j < pref.length), st.mem (outAddr + 2 * j + 1) = pref[j]'hj)
  have hP5 := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 2)
    (body := .cond (.bin .lt (.reg 10) (.reg 9))
      (seqStmts
        [ .assign 11 (.load (.bin .add (.reg 3) (.reg 8)))
        , .assign 12 (.load (.bin .add (.reg 6) (.reg 11)))
        , .cond (.bin .eq (.reg 12) (.const 0))
            (seqStmts
              [ .store (.bin .add (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 10))) (.const 1)) (.reg 11)
              , .assign 10 (.bin .add (.reg 10) (.const 1)) ])
            .nop ])
      .nop)
    (P := fun st => st = st₆) (Inv := Inv5) 68 0 lenB (Nat.zero_le lenB) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        fakeRegs_update_ge (r := 8) (by decide) (fakeRegs_update_ge (r := 10) (by decide) hr₅),
        by simp, by simp [st₆, hr9₅, hr9₄, hcnt₃], by simp [st₆], hpr₅, fun _ _ => rfl,
        heven₅, fun j hj => by simp at hj⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r2)
    (fun i _ hilt => by
      intro st ω' ⟨hr, hi, hr9, hr10, hpr, hout_fr, heven, hodd⟩
      have hi_lt : i < (B.sort (· ≤ ·)).length := hBlen ▸ hilt
      set v := (B.sort (· ≤ ·))[i]'hi_lt
      have hv_lt : v < n := hB_lt v (List.getElem_mem hi_lt)
      set pref := (((B.sort (· ≤ ·)).take i).filter predB).take lsA.length
      have hpref_le : pref.length ≤ lsA.length := by
        dsimp only [pref]; rw [List.length_take]; exact Nat.min_le_left _ _
      refine runs_start_le ?_
      refine runs_cond_le
        (Expr.eval_lt_op (Expr.eval_reg_of_eq hr10) (Expr.eval_reg_of_eq hr9) hw2) ?_ ?_
      · intro hlt_ne
        have hlt_len : pref.length < lsA.length := by
          by_contra h; simp only [h, ↓reduceIte] at hlt_ne; exact hlt_ne rfl
        have hraw_lt : (((B.sort (· ≤ ·)).take i).filter predB).length < lsA.length := by
          dsimp only [pref] at hlt_len; rw [List.length_take] at hlt_len; omega
        have hpref_raw : pref = ((B.sort (· ≤ ·)).take i).filter predB := by
          dsimp only [pref]; exact List.take_of_length_le (by omega)
        have hmem_b : st.mem (bAddr + i) = v := by
          rw [hpr (bAddr + i)
            (disjointRange_outside hd_lb (by omega) (by omega))
            (disjointRange_outside hd_ob (by omega) (by omega))]
          exact hBat.2 i hi_lt
        have hmem_loc : st.mem (locAddr + v) = if v ∈ M.map Prod.snd then 1 else 0 := by
          rw [hout_fr (locAddr + v) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
            hmap₅ v hv_lt, hloc_zero₄ v hv_lt]
        set mVal : ℕ := if v ∈ M.map Prod.snd then 1 else 0
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := v)
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq hr.r3) (Expr.eval_reg_of_eq hi) (by omega))
            hmem_b) ?_
        refine runs_seq_assign_le (v := mVal)
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r6]))
              (Expr.eval_reg_of_eq (v := v) (by simp)) (by omega))
            hmem_loc) ?_
        refine runs_cond_le
          (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := mVal) (by simp)) (Expr.eval_const (by omega)) hw2) ?_ ?_
        · intro hne
          have hvM : v ∉ M.map Prod.snd := by
            intro h; simp only [mVal, h, ↓reduceIte, Nat.one_ne_zero] at hne; exact hne rfl
          have hpv : predB v = true := by simp [predB, hvM]
          dsimp only [seqStmts]
          refine runs_seq_store_le (x := outAddr + 2 * pref.length + 1) (v := v)
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq (v := outAddr) (by simp [hr.r7]))
                (Expr.eval_mul (Expr.eval_const (by omega))
                  (Expr.eval_reg_of_eq (v := pref.length) (by simp [hr10])) (by omega)) (by omega))
              (Expr.eval_const hw2) (by omega))
            (Expr.eval_reg_of_eq (v := v) (by simp)) ?_
          refine runs_assign_le (v := pref.length + 1)
            (Expr.eval_add (Expr.eval_reg_of_eq (v := pref.length) (by simp [hr10]))
              (Expr.eval_const hw2) (by omega)) ?_ (by simp [Expr.size])
          have htake : (((B.sort (· ≤ ·)).take (i + 1)).filter predB).take lsA.length =
              pref ++ [v] := by
            rw [List.take_succ_eq_append_getElem hi_lt, List.filter_append, List.filter_cons,
              List.filter_nil, hpv]
            simp only [↓reduceIte]
            rw [List.take_of_length_le]
            · rw [hpref_raw]
            · rw [List.length_append, List.length_singleton]; omega
          refine ⟨⟨fakeRegs_update_ge (r := 8) (by decide)
              (fakeRegs_update_ge (r := 10) (by decide)
                (fakeRegs_update_mem (fakeRegs_update_ge (r := 12) (by decide)
                  (fakeRegs_update_ge (r := 11) (by decide) hr)))),
            by simp, by simp [hr9], by rw [htake, List.length_append, List.length_singleton]; simp,
            ?_, ?_, ?_, ?_⟩, by simp [hi]⟩
          · intro a hal hao
            dsimp only
            rw [Function.update_of_ne (by rcases hao with h | h <;> omega)]
            exact hpr a hal hao
          · intro a hao
            dsimp only
            rw [Function.update_of_ne (by rcases hao with h | h <;> omega)]
            exact hout_fr a hao
          · intro j hj
            dsimp only
            rw [Function.update_of_ne (by omega)]
            exact heven j hj
          · intro j hj
            dsimp only
            revert hj
            rw [htake]
            intro hj
            rw [List.length_append, List.length_singleton] at hj
            by_cases hjeq : j = pref.length
            · subst hjeq; simp
            · have hjlt' : j < pref.length := by omega
              rw [Function.update_of_ne (by omega), List.getElem_append_left hjlt']
              exact hodd j hjlt'
        · intro heq
          have hvM : v ∈ M.map Prod.snd := by
            by_contra h; simp only [mVal, h, ↓reduceIte] at heq; omega
          have hpv : predB v = false := by simp [predB, hvM]
          refine runs_nop_le ?_ (by simp [Expr.size])
          have htake : (((B.sort (· ≤ ·)).take (i + 1)).filter predB).take lsA.length = pref := by
            rw [List.take_succ_eq_append_getElem hi_lt, List.filter_append, List.filter_cons,
              List.filter_nil, hpv]
            simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
            rfl
          refine ⟨⟨fakeRegs_update_ge (r := 8) (by decide)
              (fakeRegs_update_ge (r := 12) (by decide) (fakeRegs_update_ge (r := 11) (by decide) hr)),
            by simp, by simp [hr9], by rw [htake]; simp [hr10], hpr, hout_fr, heven,
            by rw [htake]; exact hodd⟩, by simp [hi]⟩
      · intro hlt_eq
        have hge_len : lsA.length ≤ pref.length := by
          by_contra h
          have hlt' : pref.length < lsA.length := by omega
          simp only [hlt', ↓reduceIte] at hlt_eq; omega
        have hraw_ge : lsA.length ≤ (((B.sort (· ≤ ·)).take i).filter predB).length := by
          dsimp only [pref] at hge_len; rw [List.length_take] at hge_len; omega
        refine runs_nop_le ?_ (by simp [Expr.size])
        have htake : (((B.sort (· ≤ ·)).take (i + 1)).filter predB).take lsA.length = pref := by
          rw [List.take_succ_eq_append_getElem hi_lt, List.filter_append,
            List.take_append_of_le_length hraw_ge]
        refine ⟨⟨fakeRegs_update_ge (r := 8) (by decide) hr,
          by simp, by simp [hr9], by rw [htake]; simp [hr10], hpr, hout_fr, heven,
          by rw [htake]; exact hodd⟩, by simp [hi]⟩)
  obtain ⟨o₇, st₇, c₇, hrun₇, hInv₇, hc₇⟩ := hP5.runs ω rfl
  cases o₇ with
  | returned _ => exact False.elim hInv₇
  | normal =>
  rcases hInv₇ with ⟨hr₇, _, hr9₇, _, hpr₇, hout_fr₇, heven₇, hodd₇⟩
  -- Pass 6: clear `M.map Prod.snd` marks.
  have hMat₇ : EdgesAt st₇.mem mAddr M := fun j hj => by
    have h1 := hpr₇ (mAddr + 2 * j) (disjointRange_outside hd_lm (by omega) (by omega))
      (disjointRange_outside hd_om (by omega) (by omega))
    have h2 := hpr₇ (mAddr + 2 * j + 1) (disjointRange_outside hd_lm (by omega) (by omega))
      (disjointRange_outside hd_om (by omega) (by omega))
    rw [h1, h2]; exact hMat j hj
  have hP6 := edgeMarkLoop_triple (val := 0) true p mem M st₇
    hMlen hM_lt hMat₇ hd_lm hpr₇ (by omega) hw_pack hr₇
  obtain ⟨o₈, st₈, c₈, hrun₈, hInv₈, hc₈⟩ := hP6.runs ω rfl
  cases o₈ with
  | returned _ => exact False.elim hInv₈
  | normal =>
  rcases hInv₈ with ⟨_, hr9₈, _, hpr₈, hloc_fr₈, hmap₈⟩
  simp only [↓reduceIte] at hmap₈
  -- Return `r9`.
  have hret_eval : (Expr.reg 9).eval w st₈ = some lsA.length :=
    Expr.eval_reg_of_eq (hr9₈.trans hr9₇)
  have hret : Runs w p ω (.ret (.reg 9)) st₈ (.returned lsA.length) st₈ 2 :=
    runs_ret_iff.mpr ⟨lsA.length, hret_eval, rfl, rfl, rfl⟩
  -- Chain all 9 statements.
  have hrun_full : Runs w p ω completeFakeProc
      (startState [lenA, aAddr, lenB, bAddr, lenM, mAddr, locAddr, outAddr] mem pos)
      (.returned lsA.length) st₈
      (c₁ + (2 + (c₃ + (c₄ + (c₅ + (2 + (c₇ + (c₈ + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    unfold completeFakeProc seqStmts
    exact runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, _, hrun₁,
      runs_seq_iff.mpr (Or.inr ⟨st₂, 2, _, hrun₂,
        runs_seq_iff.mpr (Or.inr ⟨st₃, c₃, _, hrun₃,
          runs_seq_iff.mpr (Or.inr ⟨st₄, c₄, _, hrun₄,
            runs_seq_iff.mpr (Or.inr ⟨st₅, c₅, _, hrun₅,
              runs_seq_iff.mpr (Or.inr ⟨st₆, 2, _, hrun₆,
                runs_seq_iff.mpr (Or.inr ⟨st₇, c₇, _, hrun₇,
                  runs_seq_iff.mpr (Or.inr ⟨st₈, c₈, 2, hrun₈, hret, rfl⟩),
                  rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Identify `lsB = unmatchedSnd B M` and `completeMatchingFake A B M = lsA.zip lsB`.
  set lsB := unmatchedSnd B M
  have hlsB_eq : ((B.sort (· ≤ ·)).take lenB).filter predB = lsB := by
    rw [← hBlen, List.take_length]
    have h1 := filter_sort_eq_sort_sdiff B (M.map Prod.snd).toFinset
    have h2 : (B.sort (· ≤ ·)).filter predB =
        (B.sort (· ≤ ·)).filter (fun v => decide (v ∉ (M.map Prod.snd).toFinset)) := by
      congr 1; funext v; simp [predB]
    rw [h2, h1]; rfl
  rw [hlsB_eq] at hodd₇
  have hcmf_spec := completeMatchingFake_spec hAB hMmem hMfst hMsnd
  have hlsA_len : lsA.length = A.card - M.length := by
    have hsubA : (M.map Prod.fst).toFinset ⊆ A := by
      intro u hu; rw [List.mem_toFinset, List.mem_map] at hu
      obtain ⟨e, he, rfl⟩ := hu; exact (hMmem e he).1
    have hcard := Finset.card_sdiff_add_card_eq_card hsubA
    have hmcard : (M.map Prod.fst).toFinset.card = M.length := by
      rw [List.toFinset_card_of_nodup hMfst, List.length_map]
    unfold lsA unmatchedFst
    rw [Finset.length_sort]; omega
  have hlsB_len : lsB.length = B.card - M.length := by
    have hsubB : (M.map Prod.snd).toFinset ⊆ B := by
      intro v hv; rw [List.mem_toFinset, List.mem_map] at hv
      obtain ⟨e, he, rfl⟩ := hv; exact (hMmem e he).2
    have hcard := Finset.card_sdiff_add_card_eq_card hsubB
    have hmcard : (M.map Prod.snd).toFinset.card = M.length := by
      rw [List.toFinset_card_of_nodup hMsnd, List.length_map]
    unfold lsB unmatchedSnd
    rw [Finset.length_sort]; omega
  have hlsAB : lsA.length ≤ lsB.length := by omega
  have hF_len : (completeMatchingFake A B M).length = lsA.length := by
    rw [hcmf_spec.1, hlsA_len]
  refine ⟨.returned lsA.length, st₈, _, hrun_full, ?_, ?_⟩
  · dsimp only [completeFakeContract]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Outcome.value]
    rw [hAfin, hBfin, hMread]
    refine ⟨hF_len.symm, hlsA_le, ?_, ?_⟩
    · intro j hj
      have hjA : j < lsA.length := hF_len ▸ hj
      have hjB : j < (lsB.take lsA.length).length := by
        rw [List.length_take, Nat.min_eq_left hlsAB]; exact hjA
      have h1 := hloc_fr₈ (outAddr + 2 * j) (disjointRange_outside hd_lo (by omega) (by omega))
      have h2 := hloc_fr₈ (outAddr + 2 * j + 1) (disjointRange_outside hd_lo (by omega) (by omega))
      rw [h1, h2, heven₇ j hjA, hodd₇ j hjB, List.getElem_take]
      simp only [completeMatchingFake, List.getElem_zip]
      exact ⟨rfl, rfl⟩
    · intro a ha
      by_cases hloc : locAddr ≤ a ∧ a < locAddr + n
      · obtain ⟨hlo, hhi⟩ := hloc
        have heq : a = locAddr + (a - locAddr) := by omega
        rw [heq, hmap₈ (a - locAddr) (by omega)]
        by_cases hm : a - locAddr ∈ M.map Prod.snd
        · simp only [hm, ↓reduceIte, hloc0 (a - locAddr) (by omega)]
        · simp only [hm, ↓reduceIte]
          rw [hout_fr₇ (locAddr + (a - locAddr)) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
            hmap₅ (a - locAddr) (by omega)]
          simp only [hm, ↓reduceIte]
          rw [hloc_zero₄ (a - locAddr) (by omega), hloc0 (a - locAddr) (by omega)]
      · exact hpr₈ a (by omega) ha
  · dsimp only [completeFakeContract, completeFakeCost, Expr.size] at hc₁ hc₃ hc₄ hc₅ hc₇ hc₈ ⊢
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    omega

end MinCostFlow.ExpanderDecomp
