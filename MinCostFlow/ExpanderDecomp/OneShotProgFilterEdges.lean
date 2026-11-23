module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OneShotProgLayout
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase
import Mathlib.Tactic.Linarith

/-!
# Induced-Edge Extraction Word-RAM Primitive for `OneShot`

Implements and verifies `filterEdgesInProc`, a deterministic (`NoRand`), strictly local Word-RAM
procedure using the reusable zero-initialized marker buffer `locAddr` of size `n` (never scanning
`range n`, restoring `locAddr` to all zeros on exit): extracts `H = (Graph.mk n edges).inside X`
into `outEdgesAddr` and returns `H.length` in `O(|X| + |E| + 1)` time.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. `filterEdgesInProc` -/

/-- Extract edges of `edges` (`mE = r0` at `edgesAddr = r1`) with both endpoints in `X`
(`k = r2` at `xAddr = r3`) into `outAddr = r5` using zeroed `locAddr = r4`. Returns `|H|`. -/
def filterEdgesInProc : Stmt :=
  seqStmts
    [ forRange 6 (.const 0) (.reg 2)
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 3) (.reg 6)))
          , .store (.bin .add (.reg 4) (.reg 8)) (.const 1) ])
    , .assign 7 (.const 0)
    , forRange 6 (.const 0) (.reg 0)
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 6))))
          , .assign 9 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 6))) (.const 1)))
          , .assign 10 (.load (.bin .add (.reg 4) (.reg 8)))
          , .assign 11 (.load (.bin .add (.reg 4) (.reg 9)))
          , .cond (.bin .lt (.const 0) (.reg 10))
              (.cond (.bin .lt (.const 0) (.reg 11))
                (seqStmts
                  [ .store (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 7))) (.reg 8)
                  , .store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 7))) (.const 1)) (.reg 9)
                  , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
                .nop)
              .nop ])
    , forRange 6 (.const 0) (.reg 2)
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 3) (.reg 6)))
          , .store (.bin .add (.reg 4) (.reg 8)) (.const 0) ])
    , .ret (.reg 7) ]

def filterEdgesInCost (k mE : ℕ) : ℕ := 70 * k + 100 * mE + 100

def FilterEdgesWordBound (w n mE k edgesAddr xAddr locAddr outAddr : ℕ) : Prop :=
  edgesAddr + 2 * mE < 2 ^ w ∧
  xAddr + k < 2 ^ w ∧
  locAddr + n < 2 ^ w ∧
  outAddr + 2 * mE < 2 ^ w ∧
  2 * mE + 2 < 2 ^ w ∧
  k + 1 < 2 ^ w ∧
  16 < 2 ^ w

def FilterEdgesDisjoint (n mE k edgesAddr xAddr locAddr outAddr : ℕ) : Prop :=
  DisjointRange locAddr n edgesAddr (2 * mE) ∧
  DisjointRange locAddr n xAddr k ∧
  DisjointRange locAddr n outAddr (2 * mE) ∧
  DisjointRange outAddr (2 * mE) edgesAddr (2 * mE) ∧
  DisjointRange outAddr (2 * mE) xAddr k

/-- Contract for `filterEdgesInProc`: `args = [mE, edgesAddr, k, xAddr, locAddr, outAddr]`.
Writes `H = (Graph.mk n edges).inside X` at `outAddr`, returns `H.length`, restores `locAddr` to
all zeros, and preserves memory outside `[outAddr, outAddr + 2 * mE)`. -/
def filterEdgesInContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n mE edgesAddr k xAddr locAddr outAddr : ℕ) (edges : List (ℕ × ℕ)) (X : Finset ℕ),
      args = [mE, edgesAddr, k, xAddr, locAddr, outAddr] ∧
      edges.length = mE ∧ (∀ e ∈ edges, e.1 < n ∧ e.2 < n) ∧
      EdgesAt mem edgesAddr edges ∧
      VertsAt mem xAddr k X ∧ X ⊆ Finset.range n ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      FilterEdgesWordBound w n mE k edgesAddr xAddr locAddr outAddr ∧
      FilterEdgesDisjoint n mE k edgesAddr xAddr locAddr outAddr
  post args mem v mem' :=
    let mE := args.getD 0 0
    let edgesAddr := args.getD 1 0
    let k := args.getD 2 0
    let xAddr := args.getD 3 0
    let outAddr := args.getD 5 0
    let edges := readEdges mem edgesAddr mE
    let X := (readList mem xAddr k).toFinset
    let H := (Graph.mk 0 edges).inside X
    v = H.length ∧ v ≤ mE ∧
    EdgesAt mem' outAddr H ∧
    MemFrame mem mem' outAddr (outAddr + 2 * mE)
  cost args _ := filterEdgesInCost (args.getD 2 0) (args.getD 0 0)


end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

theorem filterEdgesInProc_noRand : filterEdgesInProc.NoRand := by
  simp [filterEdgesInProc, seqStmts, forRange, forUp, Stmt.NoRand]


/-! ## 4. Verification of `filterEdgesInProc` -/

private structure EdgeFilterRegs (mE edgesAddr k xAddr locAddr outAddr : ℕ) (st : State) : Prop where
  r0 : st.regs 0 = mE
  r1 : st.regs 1 = edgesAddr
  r2 : st.regs 2 = k
  r3 : st.regs 3 = xAddr
  r4 : st.regs 4 = locAddr
  r5 : st.regs 5 = outAddr

private lemma efRegs_update_ge {mE edgesAddr k xAddr locAddr outAddr : ℕ}
    {st : State} {r v : ℕ} (hr : 6 ≤ r)
    (h : EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr st) :
    EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr { st with regs := Function.update st.regs r v } :=
  ⟨by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r0,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r1,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r2,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r3,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r4,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r5⟩

private lemma efRegs_update_mem {mE edgesAddr k xAddr locAddr outAddr : ℕ}
    {st : State} {mem' : ℕ → ℕ}
    (h : EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr st) :
    EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr { st with mem := mem' } :=
  ⟨h.r0, h.r1, h.r2, h.r3, h.r4, h.r5⟩

private lemma efMarkLoop_triple {w n mE edgesAddr k xAddr locAddr outAddr val : ℕ}
    (p : Program) (mem₀ : ℕ → ℕ) (xList : List ℕ) (st₀ : State)
    (hxlen : xList.length = k) (hx_lt : ∀ u ∈ xList, u < n)
    (hx_at : ListAt st₀.mem xAddr xList)
    (hdisj_lx : DisjointRange locAddr n xAddr k)
    (hpr0 : PreservedOutside2 mem₀ st₀.mem locAddr (locAddr + n) outAddr (outAddr + 2 * mE))
    (hval_w : val < 2 ^ w)
    (hw : FilterEdgesWordBound w n mE k edgesAddr xAddr locAddr outAddr)
    (hregs : EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr st₀) :
    Triple w p (fun st => st = st₀)
      (forRange 6 (.const 0) (.reg 2)
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 3) (.reg 6)))
          , .store (.bin .add (.reg 4) (.reg 8)) (.const val) ]))
      (normalPost fun st' =>
        EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr st' ∧
        st'.regs 7 = st₀.regs 7 ∧
        PreservedOutside2 mem₀ st'.mem locAddr (locAddr + n) outAddr (outAddr + 2 * mE) ∧
        (∀ a, (a < locAddr ∨ locAddr + n ≤ a) → st'.mem a = st₀.mem a) ∧
        (∀ u < n, st'.mem (locAddr + u) = if u ∈ xList then val else st₀.mem (locAddr + u)))
      (fun _ => 30 * k + 25) := by
  rcases hw with ⟨_, hx_w, hloc_w, _, _, hk1_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr st ∧
    st.regs 6 = i ∧ st.regs 7 = st₀.regs 7 ∧
    PreservedOutside2 mem₀ st.mem locAddr (locAddr + n) outAddr (outAddr + 2 * mE) ∧
    (∀ a, (a < locAddr ∨ locAddr + n ≤ a) → st.mem a = st₀.mem a) ∧
    (∀ u < n, st.mem (locAddr + u) = if u ∈ xList.take i then val else st₀.mem (locAddr + u))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 2)
    (body := seqStmts
      [ .assign 8 (.load (.bin .add (.reg 3) (.reg 6)))
      , .store (.bin .add (.reg 4) (.reg 8)) (.const val) ])
    (P := fun st => st = st₀) (Inv := Inv) 16 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        efRegs_update_ge (r := 6) (by decide) hregs, by simp, by simp,
        hpr0, fun _ _ => rfl, fun u _ => by simp⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r2)
    (fun i _ hilt => by
      intro st ω' ⟨hr, hi, hr7, hpr, hloc_fr, hmap⟩
      have hi_lt : i < xList.length := hxlen ▸ hilt
      have hu_lt : xList[i]'hi_lt < n := hx_lt _ (List.getElem_mem hi_lt)
      have hmem_x : st.mem (xAddr + i) = xList[i]'hi_lt := by
        rw [hloc_fr (xAddr + i) (disjointRange_outside hdisj_lx (by omega) (by omega))]
        exact hx_at i hi_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := xList[i]'hi_lt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r3) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_x) ?_
      refine runs_store_le (x := locAddr + xList[i]'hi_lt) (v := val)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r4]))
          (Expr.eval_reg_of_eq (v := xList[i]'hi_lt) (by simp)) (by omega))
        (Expr.eval_const hval_w) ?_ (by simp [Expr.size])
      refine ⟨⟨efRegs_update_ge (r := 6) (by decide)
          (efRegs_update_mem (efRegs_update_ge (r := 8) (by decide) hr)),
        by simp, by simp [hr7], ?_, ?_, ?_⟩, by simp [hi]⟩
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
        rw [List.take_succ_eq_append_getElem hi_lt]
        by_cases huv : u = xList[i]'hi_lt
        · subst huv
          simp only [Function.update_self, List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
        · rw [Function.update_of_ne (by omega)]
          simp only [List.mem_append, List.mem_singleton, huv, or_false]
          exact hmap u hu)
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size]; omega)
  rintro o st' hpost
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hr, _, hr7, hpr, hloc_fr, hmap⟩
    refine ⟨hr, hr7, hpr, hloc_fr, fun u hu => ?_⟩
    have ht := hmap u hu
    rw [← hxlen, List.take_length] at ht
    exact ht

theorem filterEdgesInProc_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hb : p.procs[b]? = some filterEdgesInProc) :
    MeetsContract w p b (filterEdgesInContract w) := by
  refine meetsContract_of_runs hb fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, mE, edgesAddr, k, xAddr, locAddr, outAddr, edges, X, rfl,
    helen, he_lt, heAt, hXat, hXn, hloc0, hw, hdisj⟩
  have hXlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort, ← hXat.1]
  have hXread : readList mem xAddr k = X.sort (· ≤ ·) := by
    rw [← hXlen]; exact readList_eq_of_listAt hXat.2
  have hXfin : (readList mem xAddr k).toFinset = X := by rw [hXread]; ext v; simp
  have heread : readEdges mem edgesAddr mE = edges := by
    apply List.ext_getElem
    · simp [readEdges, helen]
    · intro j hj1 hj2
      simp only [readEdges, List.getElem_map, List.getElem_range]
      exact Prod.ext (heAt j hj2).1 (heAt j hj2).2
  have hx_lt : ∀ u ∈ X.sort (· ≤ ·), u < n := fun u hu =>
    Finset.mem_range.mp (hXn ((Finset.mem_sort _).mp hu))
  rcases hdisj with ⟨hd_le, hd_lx, hd_lo, hd_oe, hd_ox⟩
  rcases hw with ⟨he_w, hx_w, hloc_w, hout_w, hm2_w, hk1_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  have hregs0 : EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr
      (startState [mE, edgesAddr, k, xAddr, locAddr, outAddr] mem pos) :=
    ⟨by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState]⟩
  -- Loop 1: mark `X` in `locAddr`.
  have hL1 := efMarkLoop_triple (val := 1) p mem (X.sort (· ≤ ·))
    (startState [mE, edgesAddr, k, xAddr, locAddr, outAddr] mem pos)
    hXlen hx_lt hXat.2 hd_lx (fun _ _ _ => rfl) hw2
    ⟨he_w, hx_w, hloc_w, hout_w, hm2_w, hk1_w, hw16⟩ hregs0
  obtain ⟨o₁, st₁, c₁, hrun₁, hInv₁, hc₁⟩ := hL1.runs ω rfl
  cases o₁ with
  | returned _ => exact False.elim hInv₁
  | normal =>
  rcases hInv₁ with ⟨hr₁, _, hpr₁, hloc_fr₁, hmap₁⟩
  -- Assign `r7 := 0`.
  set st₂ : State := { st₁ with regs := Function.update st₁.regs 7 0 }
  have hrun₂ : Runs w p ω (.assign 7 (.const 0)) st₁ .normal st₂ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  -- Loop 2: filter edges with both endpoints marked.
  let epred : ℕ × ℕ → Bool := fun e => decide (e.1 ∈ X) && decide (e.2 ∈ X)
  let Inv2 : ℕ → State → Prop := fun j st =>
    let pref := (edges.take j).filter epred
    EdgeFilterRegs mE edgesAddr k xAddr locAddr outAddr st ∧
    st.regs 6 = j ∧ st.regs 7 = pref.length ∧
    PreservedOutside2 mem st.mem locAddr (locAddr + n) outAddr (outAddr + 2 * mE) ∧
    (∀ a, (a < outAddr ∨ outAddr + 2 * mE ≤ a) → st.mem a = st₁.mem a) ∧
    EdgesAt st.mem outAddr pref
  have hL2 := Triple.forRange_const (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 0)
    (body := seqStmts
      [ .assign 8 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 6))))
      , .assign 9 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 6))) (.const 1)))
      , .assign 10 (.load (.bin .add (.reg 4) (.reg 8)))
      , .assign 11 (.load (.bin .add (.reg 4) (.reg 9)))
      , .cond (.bin .lt (.const 0) (.reg 10))
          (.cond (.bin .lt (.const 0) (.reg 11))
            (seqStmts
              [ .store (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 7))) (.reg 8)
              , .store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 7))) (.const 1)) (.reg 9)
              , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
            .nop)
          .nop ])
    (P := fun st => st = st₂) (Inv := Inv2) 85 0 mE (Nat.zero_le mE) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        efRegs_update_ge (r := 6) (by decide) (efRegs_update_ge (r := 7) (by decide) hr₁),
        by simp, by simp [st₂], hpr₁, fun _ _ => rfl, fun i hi => by simp at hi⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r0)
    (fun j _ hjlt => by
      intro st ω' ⟨hr, hj, hcnt, hpr, hout_fr, hed⟩
      have hj_lt : j < edges.length := helen ▸ hjlt
      set e := edges[j]'hj_lt
      have he1_lt : e.1 < n := (he_lt e (List.getElem_mem hj_lt)).1
      have he2_lt : e.2 < n := (he_lt e (List.getElem_mem hj_lt)).2
      have hmem_e1 : st.mem (edgesAddr + 2 * j) = e.1 := by
        rw [hpr (edgesAddr + 2 * j)
          (disjointRange_outside hd_le (by omega) (by omega))
          (disjointRange_outside hd_oe (by omega) (by omega))]
        exact (heAt j hj_lt).1
      have hmem_e2 : st.mem (edgesAddr + 2 * j + 1) = e.2 := by
        rw [hpr (edgesAddr + 2 * j + 1)
          (disjointRange_outside hd_le (by omega) (by omega))
          (disjointRange_outside hd_oe (by omega) (by omega))]
        exact (heAt j hj_lt).2
      have hloc_e1 : st.mem (locAddr + e.1) = if e.1 ∈ X then 1 else 0 := by
        rw [hout_fr (locAddr + e.1) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
          hmap₁ e.1 he1_lt]
        dsimp only [startState]
        rw [hloc0 e.1 he1_lt]; simp only [Finset.mem_sort]
      have hloc_e2 : st.mem (locAddr + e.2) = if e.2 ∈ X then 1 else 0 := by
        rw [hout_fr (locAddr + e.2) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
          hmap₁ e.2 he2_lt]
        dsimp only [startState]
        rw [hloc0 e.2 he2_lt]; simp only [Finset.mem_sort]
      have hcnt_le : ((edges.take j).filter epred).length ≤ j := by
        calc _ ≤ (edges.take j).length := List.length_filter_le _ _
          _ ≤ j := by rw [List.length_take]; exact Nat.min_le_left _ _
      set m1 : ℕ := if e.1 ∈ X then 1 else 0
      set m2 : ℕ := if e.2 ∈ X then 1 else 0
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := e.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r1)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hj) (by omega))
            (by omega))
          hmem_e1) ?_
      refine runs_seq_assign_le (v := e.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (v := edgesAddr) (by simp [hr.r1]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := j) (by simp [hj])) (by omega))
              (by omega))
            (Expr.eval_const hw2) (by omega))
          hmem_e2) ?_
      refine runs_seq_assign_le (v := m1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r4]))
            (Expr.eval_reg_of_eq (v := e.1) (by simp)) (by omega))
          hloc_e1) ?_
      refine runs_seq_assign_le (v := m2)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r4]))
            (Expr.eval_reg_of_eq (v := e.2) (by simp)) (by omega))
          hloc_e2) ?_
      refine runs_cond_le
        (Expr.eval_lt_op (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := m1) (by simp)) hw2) ?_ ?_
      · intro hm1_ne
        have he1X : e.1 ∈ X := by by_cases h : e.1 ∈ X <;> simp_all [m1]
        refine runs_cond_le
          (Expr.eval_lt_op (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := m2) (by simp)) hw2) ?_ ?_
        · intro hm2_ne
          have he2X : e.2 ∈ X := by by_cases h : e.2 ∈ X <;> simp_all [m2]
          have hpe : epred e = true := by simp [epred, he1X, he2X]
          dsimp only [seqStmts]
          refine runs_seq_store_le (x := outAddr + 2 * ((edges.take j).filter epred).length) (v := e.1)
            (Expr.eval_add (Expr.eval_reg_of_eq (v := outAddr) (by simp [hr.r5]))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := ((edges.take j).filter epred).length) (by simp [hcnt]))
                (by omega)) (by omega))
            (Expr.eval_reg_of_eq (v := e.1) (by simp)) ?_
          refine runs_seq_store_le (x := outAddr + 2 * ((edges.take j).filter epred).length + 1) (v := e.2)
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq (v := outAddr) (by simp [hr.r5]))
                (Expr.eval_mul (Expr.eval_const (by omega))
                  (Expr.eval_reg_of_eq (v := ((edges.take j).filter epred).length) (by simp [hcnt]))
                  (by omega)) (by omega))
              (Expr.eval_const hw2) (by omega))
            (Expr.eval_reg_of_eq (v := e.2) (by simp)) ?_
          refine runs_assign_le (v := ((edges.take j).filter epred).length + 1)
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := ((edges.take j).filter epred).length) (by simp [hcnt]))
              (Expr.eval_const hw2) (by omega)) ?_ (by simp [Expr.size])
          have htake : (edges.take (j + 1)).filter epred = (edges.take j).filter epred ++ [e] := by
            rw [List.take_succ_eq_append_getElem hj_lt, List.filter_append, List.filter_cons,
              List.filter_nil, hpe]; simp [e]
          refine ⟨⟨efRegs_update_ge (r := 6) (by decide)
              (efRegs_update_ge (r := 7) (by decide)
                (efRegs_update_mem (efRegs_update_mem
                  (efRegs_update_ge (r := 11) (by decide)
                    (efRegs_update_ge (r := 10) (by decide)
                      (efRegs_update_ge (r := 9) (by decide)
                        (efRegs_update_ge (r := 8) (by decide) hr))))))),
            by simp, by rw [htake, List.length_append, List.length_singleton]; simp,
            ?_, ?_, ?_⟩, by simp [hj]⟩
          · intro a hal hao
            dsimp only
            rw [Function.update_of_ne (by rcases hao with h | h <;> omega),
              Function.update_of_ne (by rcases hao with h | h <;> omega)]
            exact hpr a hal hao
          · intro a hao
            dsimp only
            rw [Function.update_of_ne (by rcases hao with h | h <;> omega),
              Function.update_of_ne (by rcases hao with h | h <;> omega)]
            exact hout_fr a hao
          · intro idx hidx
            dsimp only
            revert hidx
            rw [htake]
            intro hidx
            rw [List.length_append, List.length_singleton] at hidx
            by_cases heq : idx = ((edges.take j).filter epred).length
            · subst heq
              constructor
              · rw [Function.update_of_ne (by omega), Function.update_self]; simp
              · rw [Function.update_self]; simp
            · have hlt' : idx < ((edges.take j).filter epred).length := by omega
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                List.getElem_append_left hlt']
              exact hed idx hlt'
        · intro hm2_eq
          have he2X : e.2 ∉ X := by by_cases h : e.2 ∈ X <;> simp_all [m2]
          have hpe : epred e = false := by simp [epred, he2X]
          refine runs_nop_le ?_ (by simp [Expr.size])
          have htake : (edges.take (j + 1)).filter epred = (edges.take j).filter epred := by
            rw [List.take_succ_eq_append_getElem hj_lt, List.filter_append, List.filter_cons,
              List.filter_nil, hpe]; simp
          refine ⟨⟨efRegs_update_ge (r := 6) (by decide)
              (efRegs_update_ge (r := 11) (by decide)
                (efRegs_update_ge (r := 10) (by decide)
                  (efRegs_update_ge (r := 9) (by decide)
                    (efRegs_update_ge (r := 8) (by decide) hr)))),
            by simp, by rw [htake]; simp [hcnt], hpr, hout_fr, by rw [htake]; exact hed⟩,
            by simp [hj]⟩
      · intro hm1_eq
        have he1X : e.1 ∉ X := by by_cases h : e.1 ∈ X <;> simp_all [m1]
        have hpe : epred e = false := by simp [epred, he1X]
        refine runs_nop_le ?_ (by simp [Expr.size])
        have htake : (edges.take (j + 1)).filter epred = (edges.take j).filter epred := by
          rw [List.take_succ_eq_append_getElem hj_lt, List.filter_append, List.filter_cons,
            List.filter_nil, hpe]; simp
        refine ⟨⟨efRegs_update_ge (r := 6) (by decide)
            (efRegs_update_ge (r := 11) (by decide)
              (efRegs_update_ge (r := 10) (by decide)
                (efRegs_update_ge (r := 9) (by decide)
                  (efRegs_update_ge (r := 8) (by decide) hr)))),
          by simp, by rw [htake]; simp [hcnt], hpr, hout_fr, by rw [htake]; exact hed⟩,
          by simp [hj]⟩)
  obtain ⟨o₃, st₃, c₃, hrun₃, hInv₃, hc₃⟩ := hL2.runs ω rfl
  cases o₃ with
  | returned _ => exact False.elim hInv₃
  | normal =>
  rcases hInv₃ with ⟨hr₃, _, hcnt₃, hpr₃, hout_fr₃, hed₃⟩
  -- Loop 3: clear `X` in `locAddr`.
  have hxAt₃ : ListAt st₃.mem xAddr (X.sort (· ≤ ·)) := fun i hi => by
    rw [hpr₃ (xAddr + i)
      (disjointRange_outside hd_lx (by omega) (by omega))
      (disjointRange_outside hd_ox (by omega) (by omega))]
    exact hXat.2 i hi
  have hL3 := efMarkLoop_triple (val := 0) p mem (X.sort (· ≤ ·)) st₃
    hXlen hx_lt hxAt₃ hd_lx hpr₃ (by omega)
    ⟨he_w, hx_w, hloc_w, hout_w, hm2_w, hk1_w, hw16⟩ hr₃
  obtain ⟨o₄, st₄, c₄, hrun₄, hInv₄, hc₄⟩ := hL3.runs ω rfl
  cases o₄ with
  | returned _ => exact False.elim hInv₄
  | normal =>
  rcases hInv₄ with ⟨_, hr7₄, hpr₄, hloc_fr₄, hmap₄⟩
  -- Return `r7`.
  set H := edges.filter epred
  have hH_eq : (edges.take mE).filter epred = H := by rw [← helen, List.take_length]
  rw [hH_eq] at hcnt₃ hed₃
  have hret_eval : (Expr.reg 7).eval w st₄ = some H.length :=
    Expr.eval_reg_of_eq (hr7₄.trans hcnt₃)
  have hret : Runs w p ω (.ret (.reg 7)) st₄ (.returned H.length) st₄ 2 :=
    runs_ret_iff.mpr ⟨H.length, hret_eval, rfl, rfl, rfl⟩
  have hrun_full : Runs w p ω filterEdgesInProc
      (startState [mE, edgesAddr, k, xAddr, locAddr, outAddr] mem pos)
      (.returned H.length) st₄ (c₁ + (2 + (c₃ + (c₄ + 2 + 1) + 1) + 1) + 1) := by
    unfold filterEdgesInProc seqStmts
    exact runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, _, hrun₁,
      runs_seq_iff.mpr (Or.inr ⟨st₂, 2, _, hrun₂,
        runs_seq_iff.mpr (Or.inr ⟨st₃, c₃, _, hrun₃,
          runs_seq_iff.mpr (Or.inr ⟨st₄, c₄, 2, hrun₄, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨.returned H.length, st₄, _, hrun_full, ?_, ?_⟩
  · dsimp only [filterEdgesInContract]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Outcome.value]
    rw [heread, hXfin]
    have hH_inside : (Graph.mk 0 edges).inside X = H := rfl
    rw [hH_inside]
    have hH_le : H.length ≤ mE := by rw [← helen]; exact List.length_filter_le _ _
    refine ⟨rfl, hH_le, ?_, ?_⟩
    · intro j hj
      have h1 := hloc_fr₄ (outAddr + 2 * j) (disjointRange_outside hd_lo (by omega) (by omega))
      have h2 := hloc_fr₄ (outAddr + 2 * j + 1) (disjointRange_outside hd_lo (by omega) (by omega))
      rw [h1, h2]
      exact hed₃ j hj
    · intro a ha
      by_cases hloc : locAddr ≤ a ∧ a < locAddr + n
      · obtain ⟨hlo, hhi⟩ := hloc
        have heq : a = locAddr + (a - locAddr) := by omega
        rw [heq, hmap₄ (a - locAddr) (by omega)]
        by_cases hm : a - locAddr ∈ X.sort (· ≤ ·)
        · simp only [hm, ↓reduceIte, hloc0 (a - locAddr) (by omega)]
        · simp only [hm, ↓reduceIte]
          rw [hout_fr₃ (locAddr + (a - locAddr)) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
            hmap₁ (a - locAddr) (by omega)]
          simp only [hm, ↓reduceIte]
          rfl
      · exact hpr₄ a (by omega) ha
  · dsimp only [filterEdgesInContract, filterEdgesInCost, Expr.size] at hc₁ hc₃ hc₄ ⊢
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    omega


end MinCostFlow.ExpanderDecomp
