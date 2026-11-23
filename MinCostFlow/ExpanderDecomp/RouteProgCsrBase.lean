module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.Expander.HeapSortProg
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.ExpanderDecomp.RouteProgLayout

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local Induced-Subgraph CSR Builder: Definitions and First Four Stages

Defines the workspace layout (`localCsrSpace`, `csrOrigAddr`, `csrOffAddr`, `csrWCurAddr`,
`csrNbAddr`, `csrEdgeAddr`, `csrLocIdAddr`), the deterministic Word-RAM statements for
`buildLocalCsrProc`, its contract `buildLocalCsrContract`, the edge-prefix helper `adjOfTake`,
and verifies the first four stages (`csrCopyXStmt`, `csrFillLocStmt`, `csrCountDegStmt`,
`csrPrefixSumStmt`). Stage 5 (`csrFillAdjStmt`) and the assembled contract proof live in
`RouteProgCsr.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Workspace Offset Map and Prefix-Edge Helper -/

/-- Total heap words reserved by `buildLocalCsrProc`: `origVert` (`nX`), `off` (`nX + 1`),
`writeCur` (`nX`), `nb` (`2*m`), `edge` (`2*m`), and `locId` (`n`). -/
def localCsrSpace (n m nX : ℕ) : ℕ :=
  3 * nX + 1 + 4 * m + n

def csrOrigAddr (workAddr : ℕ) : ℕ := workAddr
def csrOffAddr (workAddr nX : ℕ) : ℕ := workAddr + nX
def csrWCurAddr (workAddr nX : ℕ) : ℕ := workAddr + 2 * nX + 1
def csrNbAddr (workAddr nX : ℕ) : ℕ := workAddr + 3 * nX + 1
def csrEdgeAddr (workAddr nX m : ℕ) : ℕ := workAddr + 3 * nX + 1 + 2 * m
def csrLocIdAddr (workAddr nX m : ℕ) : ℕ := workAddr + 3 * nX + 1 + 4 * m

/-- Local adjacency list of `v` using only the first `k` edges of `G`. -/
def adjOfTake (G : Graph) (X : Finset ℕ) (k : ℕ) (v : ℕ) : List (ℕ × ℕ) :=
  adjOf ⟨G.n, G.edges.take k⟩ X v

/-- Explicit step bound for `buildLocalCsrProc`. -/
def buildLocalCsrCost (m nX : ℕ) : ℕ :=
  280 * (nX * (2 * Nat.log 2 (nX + 2) + 1) + 1) + 160 * nX + 240 * m + 200

/-! ## 2. Procedure Statements -/

/-- Copy `X` from `xAddr + 1 .. xAddr + nX` into `origVertAddr = reg 2`. -/
def csrCopyXStmt : Stmt :=
  seqStmts
    [ .assign 11 (.const 0)
    , .loop (.bin .lt (.reg 11) (.reg 5))
        (seqStmts
          [ .assign 12 (.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 11)))
          , .store (.bin .add (.reg 2) (.reg 11)) (.reg 12)
          , .assign 11 (.bin .add (.reg 11) (.const 1)) ]) ]

/-- Fill `locId[origVert[i]] := i + 1` for `i < nX`. -/
def csrFillLocStmt : Stmt :=
  seqStmts
    [ .assign 11 (.const 0)
    , .loop (.bin .lt (.reg 11) (.reg 5))
        (seqStmts
          [ .assign 12 (.load (.bin .add (.reg 2) (.reg 11)))
          , .store (.bin .add (.reg 10) (.reg 12)) (.bin .add (.reg 11) (.const 1))
          , .assign 11 (.bin .add (.reg 11) (.const 1)) ]) ]

/-- Pass 1 over `G.edges`: accumulate degrees of vertices in `X` at `offAddr + 1 + i`. -/
def csrCountDegStmt : Stmt :=
  seqStmts
    [ .assign 11 (.const 0)
    , .loop (.bin .lt (.reg 11) (.reg 4))
        (seqStmts
          [ .assign 12 (.load (.bin .add (.bin .add (.reg 0) (.const 2))
              (.bin .mul (.const 2) (.reg 11))))
          , .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const 3))
              (.bin .mul (.const 2) (.reg 11))))
          , .assign 14 (.load (.bin .add (.reg 10) (.reg 12)))
          , .assign 15 (.load (.bin .add (.reg 10) (.reg 13)))
          , .cond (.reg 14)
              (.cond (.reg 15)
                (seqStmts
                  [ .assign 14 (.bin .sub (.reg 14) (.const 1))
                  , .assign 15 (.bin .sub (.reg 15) (.const 1))
                  , .assign 12 (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 14))
                  , .store (.reg 12) (.bin .add (.load (.reg 12)) (.const 1))
                  , .assign 13 (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 15))
                  , .store (.reg 13) (.bin .add (.load (.reg 13)) (.const 1)) ])
                .nop)
              .nop
          , .assign 11 (.bin .add (.reg 11) (.const 1)) ]) ]

/-- Compute CSR prefix sums in `offAddr[0..nX]` and copy starting offsets to `writeCurAddr`. -/
def csrPrefixSumStmt : Stmt :=
  seqStmts
    [ .assign 11 (.const 0)
    , .loop (.bin .lt (.reg 11) (.reg 5))
        (seqStmts
          [ .assign 12 (.load (.bin .add (.reg 6) (.reg 11)))
          , .store (.bin .add (.reg 7) (.reg 11)) (.reg 12)
          , .assign 13 (.bin .add (.bin .add (.reg 6) (.reg 11)) (.const 1))
          , .store (.reg 13) (.bin .add (.reg 12) (.load (.reg 13)))
          , .assign 11 (.bin .add (.reg 11) (.const 1)) ]) ]

/-- Pass 2 over `G.edges`: scatter `(locOf X w, j)` into `nbAddr` and `edgeAddr`. -/
def csrFillAdjStmt : Stmt :=
  seqStmts
    [ .assign 11 (.const 0)
    , .loop (.bin .lt (.reg 11) (.reg 4))
        (seqStmts
          [ .assign 12 (.load (.bin .add (.bin .add (.reg 0) (.const 2))
              (.bin .mul (.const 2) (.reg 11))))
          , .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const 3))
              (.bin .mul (.const 2) (.reg 11))))
          , .assign 14 (.load (.bin .add (.reg 10) (.reg 12)))
          , .assign 15 (.load (.bin .add (.reg 10) (.reg 13)))
          , .cond (.reg 14)
              (.cond (.reg 15)
                (seqStmts
                  [ .assign 14 (.bin .sub (.reg 14) (.const 1))
                  , .assign 15 (.bin .sub (.reg 15) (.const 1))
                  , .assign 12 (.load (.bin .add (.reg 7) (.reg 14)))
                  , .store (.bin .add (.reg 8) (.reg 12)) (.reg 15)
                  , .store (.bin .add (.reg 9) (.reg 12)) (.reg 11)
                  , .store (.bin .add (.reg 7) (.reg 14)) (.bin .add (.reg 12) (.const 1))
                  , .assign 13 (.load (.bin .add (.reg 7) (.reg 15)))
                  , .store (.bin .add (.reg 8) (.reg 13)) (.reg 14)
                  , .store (.bin .add (.reg 9) (.reg 13)) (.reg 11)
                  , .store (.bin .add (.reg 7) (.reg 15)) (.bin .add (.reg 13) (.const 1)) ])
                .nop)
              .nop
          , .assign 11 (.bin .add (.reg 11) (.const 1)) ]) ]

/-- `buildLocalCsrProc bSort`: args `[gAddr, xAddr, workAddr]`, calling `heapSortProc` at
`bSort`. Returns `2 * (G.inside X).length` (`off[nX]`). -/
def buildLocalCsrProc (bSort : ℕ) : Stmt :=
  seqStmts
    [ .assign 3 (.load (.reg 0))
    , .assign 4 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 5 (.load (.reg 1))
    , .assign 6 (.bin .add (.reg 2) (.reg 5))
    , .assign 7 (.bin .add (.bin .add (.reg 6) (.reg 5)) (.const 1))
    , .assign 8 (.bin .add (.reg 7) (.reg 5))
    , .assign 9 (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 4)))
    , .assign 10 (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 4)))
    , csrCopyXStmt
    , .call 12 bSort [.reg 2, .reg 5]
    , csrFillLocStmt
    , csrCountDegStmt
    , csrPrefixSumStmt
    , csrFillAdjStmt
    , .ret (.load (.bin .add (.reg 6) (.reg 5))) ]

/-- Word-RAM contract for `buildLocalCsrProc bSort`. -/
def buildLocalCsrContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr xAddr workAddr : ℕ) (G : Graph) (X : Finset ℕ),
      args = [gAddr, xAddr, workAddr] ∧
      GraphAt mem gAddr G ∧ G.IsValid ∧
      VertSetAt mem xAddr X ∧ X ⊆ Finset.range G.n ∧
      gAddr + G.encode.length ≤ workAddr ∧
      xAddr + 1 + X.card ≤ workAddr ∧
      ZeroFrom mem workAddr ∧
      workAddr + localCsrSpace G.n G.m X.card + 4 < 2 ^ w ∧
      4 ≤ 2 ^ w
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let xAddr := args.getD 1 0
    let workAddr := args.getD 2 0
    ∀ (G : Graph) (X : Finset ℕ),
      GraphAt mem gAddr G → G.IsValid →
      VertSetAt mem xAddr X → X ⊆ Finset.range G.n →
      v = 2 * (G.inside X).length ∧
      ListAt mem' (csrOrigAddr workAddr) (sortedX X) ∧
      (∀ u < G.n, mem' (csrLocIdAddr workAddr X.card G.m + u) =
        if u ∈ X then locOf X u + 1 else 0) ∧
      AdjCsrAt mem' (csrOffAddr workAddr X.card) (csrNbAddr workAddr X.card)
        (csrEdgeAddr workAddr X.card G.m) X (adjOf G X) ∧
      (∀ a < workAddr, mem' a = mem a) ∧
      ZeroFrom mem' (workAddr + localCsrSpace G.n G.m X.card)
  cost args mem :=
    buildLocalCsrCost (mem (args.getD 0 0 + 1)) (mem (args.getD 1 0))

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 3. `NoRand` and Prefix-Edge Recurrence Lemmas -/

lemma buildLocalCsrProc_noRand (bSort : ℕ) : (buildLocalCsrProc bSort).NoRand := by
  simp [buildLocalCsrProc, csrCopyXStmt, csrFillLocStmt, csrCountDegStmt, csrPrefixSumStmt,
    csrFillAdjStmt, seqStmts, Stmt.NoRand]

lemma adjOfTake_zero (G : Graph) (X : Finset ℕ) (v : ℕ) :
    adjOfTake G X 0 v = [] := by
  simp [adjOfTake, adjOf, insideEdgesIdx]

lemma adjOfTake_m (G : Graph) (X : Finset ℕ) (v : ℕ) :
    adjOfTake G X G.m v = adjOf G X v := by
  simp [adjOfTake, Graph.m]

private lemma zipIdx_append_singleton {α : Type*} (l : List α) (x : α) (r : ℕ) :
    (l ++ [x]).zipIdx r = l.zipIdx r ++ [(x, r + l.length)] := by
  induction l generalizing r with
  | nil => simp
  | cons a rest ih =>
    simp only [List.cons_append, List.zipIdx_cons, ih (r + 1), List.length_cons]
    rw [show r + 1 + rest.length = r + (rest.length + 1) by omega]

lemma adjOfTake_succ (G : Graph) (X : Finset ℕ) {j : ℕ} (hj : j < G.m) (v : ℕ) :
    let e := G.edges[j]'hj
    adjOfTake G X (j + 1) v =
      adjOfTake G X j v ++
        (if e.1 ∈ X ∧ e.2 ∈ X then
          (if e.1 = v then [(e.2, j)] else []) ++ (if e.2 = v then [(e.1, j)] else [])
        else []) := by
  intro e
  have htake : G.edges.take (j + 1) = G.edges.take j ++ [e] :=
    List.take_succ_eq_append_getElem hj
  have hlen : (G.edges.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  unfold adjOfTake adjOf insideEdgesIdx
  dsimp only
  rw [htake, zipIdx_append_singleton, hlen, Nat.zero_add, List.map_append, List.map_singleton,
    Prod.swap_prod_mk, List.filter_append, List.filter_cons, List.filter_nil, List.flatMap_append]
  congr 1
  by_cases hIn : e.1 ∈ X ∧ e.2 ∈ X
  · have hB : insideB X e = true := by
      unfold insideB; simp [hIn.1, hIn.2]
    simp [hIn, hB]
  · have hB : insideB X e = false := by
      unfold insideB
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      tauto
    simp [hIn, hB]

lemma adjOfTake_prefix (G : Graph) (X : Finset ℕ) {j : ℕ} (hj : j ≤ G.m) (v : ℕ) :
    adjOfTake G X j v <+: adjOf G X v := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
  have hgen : ∀ t, j + t ≤ G.m → adjOfTake G X j v <+: adjOfTake G X (j + t) v := by
    intro t
    induction t with
    | zero => intro _; exact List.prefix_refl _
    | succ t ih =>
      intro ht
      have hlt : j + t < G.m := by omega
      have hstep := adjOfTake_succ G X hlt v
      rw [show j + (t + 1) = (j + t) + 1 by omega, hstep]
      exact (ih (by omega)).trans (List.prefix_append _ _)
  have h := hgen d (by omega)
  rwa [← hd, adjOfTake_m] at h

lemma adjOfTake_length_le (G : Graph) (X : Finset ℕ) {j : ℕ} (hj : j ≤ G.m) (v : ℕ) :
    (adjOfTake G X j v).length ≤ (adjOf G X v).length :=
  (adjOfTake_prefix G X hj v).length_le

lemma adjOfTake_getElem_eq (G : Graph) (X : Finset ℕ) {j : ℕ} (hj : j ≤ G.m)
    {v r : ℕ} (hr : r < (adjOfTake G X j v).length) :
    (adjOfTake G X j v)[r]'hr =
      (adjOf G X v)[r]'(lt_of_lt_of_le hr (adjOfTake_length_le G X hj v)) := by
  obtain ⟨t, ht⟩ := adjOfTake_prefix G X hj v
  have h1 : (adjOfTake G X j v)[r]? = (adjOf G X v)[r]? := by
    rw [← ht, List.getElem?_append_left hr]
  rw [List.getElem?_eq_getElem hr,
      List.getElem?_eq_getElem (lt_of_lt_of_le hr (adjOfTake_length_le G X hj v))] at h1
  exact Option.some.inj h1

/-! ## 4. Stages 1–4 Verification Lemmas -/

lemma csrCopyX_triple {w : ℕ} {p : Program}
    {gAddr xAddr workAddr : ℕ} {G : Graph} {X : Finset ℕ} {xs : List ℕ}
    {mem0 : ℕ → ℕ} {st0 : State}
    (hxs_len : xs.length = X.card) (hxs_seq : SeqAt mem0 xAddr xs)
    (hx_disj : xAddr + 1 + X.card ≤ workAddr)
    (hw : workAddr + localCsrSpace G.n G.m X.card + 4 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w) (hmem_lt : ∀ i < X.card, mem0 (xAddr + 1 + i) < 2 ^ w)
    (hregs : ∀ r, r ≤ 10 → st0.regs r =
      match r with
      | 0 => gAddr | 1 => xAddr | 2 => workAddr | 3 => G.n | 4 => G.m | 5 => X.card
      | 6 => csrOffAddr workAddr X.card
      | 7 => csrWCurAddr workAddr X.card
      | 8 => csrNbAddr workAddr X.card
      | 9 => csrEdgeAddr workAddr X.card G.m
      | _ => csrLocIdAddr workAddr X.card G.m)
    (hmem0 : st0.mem = mem0) :
    Triple w p
      (fun st => st = st0)
      csrCopyXStmt
      (normalPost fun st' =>
        (∀ r ≤ 10, st'.regs r = st0.regs r) ∧
        ListAt st'.mem workAddr xs ∧
        (∀ a, (a < workAddr ∨ workAddr + X.card ≤ a) → st'.mem a = mem0 a))
      (fun _ => 25 * X.card + 15) := by
  have hsp_ge : X.card ≤ localCsrSpace G.n G.m X.card := by dsimp only [localCsrSpace]; omega
  wram_enter
  · subst st
    dsimp only [csrCopyXStmt, seqStmts]
    wram_step
    have hloop :
        Triple w p
          (fun st =>
            (∀ r ≤ 10, st.regs r = st0.regs r) ∧
            st.regs 11 ≤ X.card ∧
            (∀ i < st.regs 11, st.mem (workAddr + i) = xs.getD i 0) ∧
            (∀ a, (a < workAddr ∨ workAddr + X.card ≤ a) → st.mem a = mem0 a))
          (.loop (.bin .lt (.reg 11) (.reg 5))
            (seqStmts
              [ .assign 12 (.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 11)))
              , .store (.bin .add (.reg 2) (.reg 11)) (.reg 12)
              , .assign 11 (.bin .add (.reg 11) (.const 1)) ]))
          (normalPost fun st' =>
            (∀ r ≤ 10, st'.regs r = st0.regs r) ∧
            st'.regs 11 = X.card ∧
            (∀ i < X.card, st'.mem (workAddr + i) = xs.getD i 0) ∧
            (∀ a, (a < workAddr ∨ workAddr + X.card ≤ a) → st'.mem a = mem0 a))
          (fun st => ((Expr.bin .lt (.reg 11) (.reg 5)).size + 20 + 1) * (X.card - st.regs 11) +
            (Expr.bin .lt (.reg 11) (.reg 5)).size + 1) := by
      refine Triple.loop_const_normal
        (m := fun st => X.card - st.regs 11)
        (condVal := fun st => if st.regs 11 < X.card then 1 else 0)
        (bodyBound := 20) ?_ ?_ ?_
      · intro stL ⟨hr, _, _, _⟩
        have hr5 : stL.regs 5 = X.card := by rw [hr 5 (by decide)]; exact hregs 5 (by decide)
        eval_expr
      · intro stL ⟨hr, hle, hcopy, hframe⟩ hv
        have heq : stL.regs 11 = X.card := by split_ifs at hv; omega
        exact ⟨hr, heq, by rwa [heq] at hcopy, hframe⟩
      · intro stL ⟨hr, hle, hcopy, hframe⟩ hv
        have hr1 : stL.regs 1 = xAddr := by rw [hr 1 (by decide)]; exact hregs 1 (by decide)
        have hr2 : stL.regs 2 = workAddr := by rw [hr 2 (by decide)]; exact hregs 2 (by decide)
        have hr5 : stL.regs 5 = X.card := by rw [hr 5 (by decide)]; exact hregs 5 (by decide)
        have hlt : stL.regs 11 < X.card := by split_ifs at hv <;> omega
        have hval_eq : stL.mem (xAddr + 1 + stL.regs 11) = xs.getD (stL.regs 11) 0 := by
          rw [hframe _ (Or.inl (by omega)), List.getD_eq_getElem _ 0 (by omega)]
          exact hxs_seq.2 (stL.regs 11) (by omega)
        have hval_lt : stL.mem (xAddr + 1 + stL.regs 11) < 2 ^ w := by
          rw [hframe _ (Or.inl (by omega))]; exact hmem_lt _ hlt
        wram_enter
        · subst st
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := xs.getD (stL.regs 11) 0)
            (by rw [← hval_eq]; eval_expr) ?_
          refine runs_seq_store_le (x := workAddr + stL.regs 11)
            (v := xs.getD (stL.regs 11) 0) (by eval_expr) (by eval_expr) ?_
          wram_step
          · dsimp only [normalPost]
            refine ⟨⟨fun r hr' => by
                simp only [Function.update_of_ne (by omega : r ≠ 11),
                  Function.update_of_ne (by omega : r ≠ 12)]
                exact hr r hr',
              by simp; omega, ?_, ?_⟩, by simp; omega⟩
            · intro i hi
              simp only [Function.update_self] at hi
              by_cases hieq : i = stL.regs 11
              · subst hieq; rw [Function.update_self]
              · rw [Function.update_of_ne (by omega)]; exact hcopy i (by omega)
            · intro a ha
              rw [Function.update_of_ne (by omega)]; exact hframe a ha
          · wram_cost
    have hinit :
        (∀ r ≤ 10, ({ st0 with regs := Function.update st0.regs 11 0 }).regs r = st0.regs r) ∧
        ({ st0 with regs := Function.update st0.regs 11 0 }).regs 11 ≤ X.card ∧
        (∀ i < ({ st0 with regs := Function.update st0.regs 11 0 }).regs 11,
          ({ st0 with regs := Function.update st0.regs 11 0 }).mem (workAddr + i) = xs.getD i 0) ∧
        (∀ a, (a < workAddr ∨ workAddr + X.card ≤ a) →
          ({ st0 with regs := Function.update st0.regs 11 0 }).mem a = mem0 a) := by
      refine ⟨fun r hr => Function.update_of_ne (by omega) _ _, by simp,
        fun _ hi => by simp at hi, fun _ _ => hmem0 ▸ rfl⟩
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := hloop _ ω hinit
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      rcases hpost with ⟨hr', _, hcopy', hframe'⟩
      refine ⟨.normal, st', c, hrun, ⟨hr', ?_, hframe'⟩, by
        simp only [Function.update_self, Nat.sub_zero, Expr.size_bin, Expr.size_reg,
          Expr.size_const] at hcost ⊢
        omega⟩
      intro i hi
      rw [hcopy' i (by omega), List.getD_eq_getElem _ 0 hi]

lemma csrFillLoc_triple {w : ℕ} {p : Program}
    {gAddr xAddr workAddr : ℕ} {G : Graph} {X : Finset ℕ}
    {mem1 : ℕ → ℕ} {st1 : State}
    (hX_sub : X ⊆ Finset.range G.n)
    (horig : ListAt mem1 workAddr (sortedX X))
    (hloc0 : ∀ u < G.n, mem1 (csrLocIdAddr workAddr X.card G.m + u) = 0)
    (hw : workAddr + localCsrSpace G.n G.m X.card + 4 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hregs : ∀ r ≤ 10, st1.regs r =
      match r with
      | 0 => gAddr | 1 => xAddr | 2 => workAddr | 3 => G.n | 4 => G.m | 5 => X.card
      | 6 => csrOffAddr workAddr X.card
      | 7 => csrWCurAddr workAddr X.card
      | 8 => csrNbAddr workAddr X.card
      | 9 => csrEdgeAddr workAddr X.card G.m
      | _ => csrLocIdAddr workAddr X.card G.m)
    (hmem1 : st1.mem = mem1) :
    Triple w p
      (fun st => st = st1)
      csrFillLocStmt
      (normalPost fun st' =>
        (∀ r ≤ 10, st'.regs r = st1.regs r) ∧
        (∀ u < G.n, st'.mem (csrLocIdAddr workAddr X.card G.m + u) =
          if u ∈ X then locOf X u + 1 else 0) ∧
        (∀ a, (a < csrLocIdAddr workAddr X.card G.m ∨
               csrLocIdAddr workAddr X.card G.m + G.n ≤ a) → st'.mem a = mem1 a))
      (fun _ => 25 * X.card + 15) := by
  wram_enter
  · subst st
    dsimp only [csrFillLocStmt, seqStmts]
    wram_step
    let locBase := csrLocIdAddr workAddr X.card G.m
    have hlocal_space : workAddr + X.card ≤ locBase ∧
        locBase + G.n ≤ workAddr + localCsrSpace G.n G.m X.card := by
      dsimp only [locBase, csrLocIdAddr, localCsrSpace]; omega
    have hloop :
        Triple w p
          (fun st =>
            (∀ r ≤ 10, st.regs r = st1.regs r) ∧
            st.regs 11 ≤ X.card ∧
            (∀ u < G.n, st.mem (locBase + u) =
              if u ∈ X ∧ locOf X u < st.regs 11 then locOf X u + 1 else 0) ∧
            (∀ a, (a < locBase ∨ locBase + G.n ≤ a) → st.mem a = mem1 a))
          (.loop (.bin .lt (.reg 11) (.reg 5))
            (seqStmts
              [ .assign 12 (.load (.bin .add (.reg 2) (.reg 11)))
              , .store (.bin .add (.reg 10) (.reg 12)) (.bin .add (.reg 11) (.const 1))
              , .assign 11 (.bin .add (.reg 11) (.const 1)) ]))
          (normalPost fun st' =>
            (∀ r ≤ 10, st'.regs r = st1.regs r) ∧
            st'.regs 11 = X.card ∧
            (∀ u < G.n, st'.mem (locBase + u) =
              if u ∈ X then locOf X u + 1 else 0) ∧
            (∀ a, (a < locBase ∨ locBase + G.n ≤ a) → st'.mem a = mem1 a))
          (fun st => ((Expr.bin .lt (.reg 11) (.reg 5)).size + 20 + 1) * (X.card - st.regs 11) +
            (Expr.bin .lt (.reg 11) (.reg 5)).size + 1) := by
      refine Triple.loop_const_normal
        (m := fun st => X.card - st.regs 11)
        (condVal := fun st => if st.regs 11 < X.card then 1 else 0)
        (bodyBound := 20) ?_ ?_ ?_
      · intro stL ⟨hr, _, _, _⟩
        have hr5 : stL.regs 5 = X.card := by rw [hr 5 (by decide)]; exact hregs 5 (by decide)
        eval_expr
      · intro stL ⟨hr, hle, hloc, hframe⟩ hv
        have heq : stL.regs 11 = X.card := by split_ifs at hv; omega
        refine ⟨hr, heq, ?_, hframe⟩
        intro u hu
        rw [hloc u hu, heq]
        by_cases huX : u ∈ X
        · simp [huX, locOf_lt huX]
        · simp [huX]
      · intro stL ⟨hr, hle, hloc, hframe⟩ hv
        have hr2 : stL.regs 2 = workAddr := by rw [hr 2 (by decide)]; exact hregs 2 (by decide)
        have hr5 : stL.regs 5 = X.card := by rw [hr 5 (by decide)]; exact hregs 5 (by decide)
        have hr10 : stL.regs 10 = locBase := by rw [hr 10 (by decide)]; exact hregs 10 (by decide)
        have hlt : stL.regs 11 < X.card := by split_ifs at hv <;> omega
        have horig_eq : stL.mem (workAddr + stL.regs 11) = origOf X (stL.regs 11) := by
          rw [hframe _ (Or.inl (by dsimp only [locBase, csrLocIdAddr]; omega))]
          have hget := horig (stL.regs 11) (by rw [sortedX_length]; exact hlt)
          rw [hget, ← origOf_eq_getElem hlt]
        have horig_lt : origOf X (stL.regs 11) < G.n :=
          Finset.mem_range.mp (hX_sub (origOf_mem hlt))
        wram_enter
        · subst st
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := origOf X (stL.regs 11))
            (by rw [← horig_eq]; eval_expr) ?_
          refine runs_seq_store_le (x := locBase + origOf X (stL.regs 11))
            (v := stL.regs 11 + 1) (by eval_expr) (by eval_expr) ?_
          wram_step
          · dsimp only [normalPost]
            refine ⟨⟨fun r hr' => by
                simp only [Function.update_of_ne (by omega : r ≠ 11),
                  Function.update_of_ne (by omega : r ≠ 12)]
                exact hr r hr',
              by simp; omega, ?_, ?_⟩, by simp; omega⟩
            · intro u hu
              simp only [Function.update_self]
              by_cases hueq : u = origOf X (stL.regs 11)
              · subst hueq
                rw [Function.update_self]
                have hmX : origOf X (stL.regs 11) ∈ X := origOf_mem hlt
                have hloc_eq : locOf X (origOf X (stL.regs 11)) = stL.regs 11 := locOf_origOf hlt
                simp [hmX, hloc_eq]
              · rw [Function.update_of_ne (by omega), hloc u hu]
                by_cases huX : u ∈ X
                · have hne_loc : locOf X u ≠ stL.regs 11 := fun h => by
                    apply hueq; rw [← h, origOf_locOf huX]
                  have hiff : locOf X u < stL.regs 11 ↔ locOf X u < stL.regs 11 + 1 := by omega
                  simp [huX, hiff]
                · simp [huX]
            · intro a ha
              rw [Function.update_of_ne (by omega)]
              exact hframe a ha
          · wram_cost
    have hinit :
        (∀ r ≤ 10, ({ st1 with regs := Function.update st1.regs 11 0 }).regs r = st1.regs r) ∧
        ({ st1 with regs := Function.update st1.regs 11 0 }).regs 11 ≤ X.card ∧
        (∀ u < G.n, ({ st1 with regs := Function.update st1.regs 11 0 }).mem (locBase + u) =
          if u ∈ X ∧ locOf X u < ({ st1 with regs := Function.update st1.regs 11 0 }).regs 11
          then locOf X u + 1 else 0) ∧
        (∀ a, (a < locBase ∨ locBase + G.n ≤ a) →
          ({ st1 with regs := Function.update st1.regs 11 0 }).mem a = mem1 a) := by
      refine ⟨fun r hr => Function.update_of_ne (by omega) _ _, by simp,
        fun u hu => by
          dsimp only
          simp only [Function.update_self, Nat.not_lt_zero, and_false, ↓reduceIte, hmem1]
          exact hloc0 u hu,
        fun _ _ => hmem1 ▸ rfl⟩
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := hloop _ ω hinit
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      rcases hpost with ⟨hr', _, hloc', hframe'⟩
      exact ⟨.normal, st', c, hrun, ⟨hr', hloc', hframe'⟩, by
        simp only [Function.update_self, Nat.sub_zero, Expr.size_bin, Expr.size_reg,
          Expr.size_const] at hcost ⊢
        omega⟩

lemma csrCountDeg_triple {w : ℕ} {p : Program}
    {gAddr xAddr workAddr : ℕ} {G : Graph} {X : Finset ℕ}
    {mem2 : ℕ → ℕ} {st2 : State}
    (hG : GraphAt mem2 gAddr G) (hG_val : G.IsValid)
    (hg_disj : gAddr + G.encode.length ≤ workAddr)
    (hloc : ∀ u < G.n, mem2 (csrLocIdAddr workAddr X.card G.m + u) =
      if u ∈ X then locOf X u + 1 else 0)
    (hoff0 : ∀ i < X.card, mem2 (csrOffAddr workAddr X.card + 1 + i) = 0)
    (hw : workAddr + localCsrSpace G.n G.m X.card + 4 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hregs : ∀ r ≤ 10, st2.regs r =
      match r with
      | 0 => gAddr | 1 => xAddr | 2 => workAddr | 3 => G.n | 4 => G.m | 5 => X.card
      | 6 => csrOffAddr workAddr X.card
      | 7 => csrWCurAddr workAddr X.card
      | 8 => csrNbAddr workAddr X.card
      | 9 => csrEdgeAddr workAddr X.card G.m
      | _ => csrLocIdAddr workAddr X.card G.m)
    (hmem2 : st2.mem = mem2) :
    Triple w p
      (fun st => st = st2)
      csrCountDegStmt
      (normalPost fun st' =>
        (∀ r ≤ 10, st'.regs r = st2.regs r) ∧
        (∀ i < X.card, st'.mem (csrOffAddr workAddr X.card + 1 + i) =
          (adjOf G X (origOf X i)).length) ∧
        (∀ a, (a < csrOffAddr workAddr X.card + 1 ∨
               csrOffAddr workAddr X.card + 1 + X.card ≤ a) → st'.mem a = mem2 a))
      (fun _ => 100 * G.m + 20) := by
  wram_enter
  · subst st
    dsimp only [csrCountDegStmt, seqStmts]
    wram_step
    let offBase := csrOffAddr workAddr X.card
    let locBase := csrLocIdAddr workAddr X.card G.m
    have hloop :
        Triple w p
          (fun st =>
            (∀ r ≤ 10, st.regs r = st2.regs r) ∧
            st.regs 11 ≤ G.m ∧
            (∀ i < X.card, st.mem (offBase + 1 + i) =
              (adjOfTake G X (st.regs 11) (origOf X i)).length) ∧
            (∀ a, (a < offBase + 1 ∨ offBase + 1 + X.card ≤ a) → st.mem a = mem2 a))
          (.loop (.bin .lt (.reg 11) (.reg 4))
            (seqStmts
              [ .assign 12 (.load (.bin .add (.bin .add (.reg 0) (.const 2))
                  (.bin .mul (.const 2) (.reg 11))))
              , .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const 3))
                  (.bin .mul (.const 2) (.reg 11))))
              , .assign 14 (.load (.bin .add (.reg 10) (.reg 12)))
              , .assign 15 (.load (.bin .add (.reg 10) (.reg 13)))
              , .cond (.reg 14)
                  (.cond (.reg 15)
                    (seqStmts
                      [ .assign 14 (.bin .sub (.reg 14) (.const 1))
                      , .assign 15 (.bin .sub (.reg 15) (.const 1))
                      , .assign 12 (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 14))
                      , .store (.reg 12) (.bin .add (.load (.reg 12)) (.const 1))
                      , .assign 13 (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 15))
                      , .store (.reg 13) (.bin .add (.load (.reg 13)) (.const 1)) ])
                    .nop)
                  .nop
              , .assign 11 (.bin .add (.reg 11) (.const 1)) ]))
          (normalPost fun st' =>
            (∀ r ≤ 10, st'.regs r = st2.regs r) ∧
            st'.regs 11 = G.m ∧
            (∀ i < X.card, st'.mem (offBase + 1 + i) = (adjOf G X (origOf X i)).length) ∧
            (∀ a, (a < offBase + 1 ∨ offBase + 1 + X.card ≤ a) → st'.mem a = mem2 a))
          (fun st => ((Expr.bin .lt (.reg 11) (.reg 4)).size + 90 + 1) * (G.m - st.regs 11) +
            (Expr.bin .lt (.reg 11) (.reg 4)).size + 1) := by
      refine Triple.loop_const_normal
        (m := fun st => G.m - st.regs 11)
        (condVal := fun st => if st.regs 11 < G.m then 1 else 0)
        (bodyBound := 90) ?_ ?_ ?_
      · intro stL ⟨hr, _, _, _⟩
        have hr4 : stL.regs 4 = G.m := by rw [hr 4 (by decide)]; exact hregs 4 (by decide)
        eval_expr
      · intro stL ⟨hr, _, hdeg, hframe⟩ hv
        have heq : stL.regs 11 = G.m := by split_ifs at hv; omega
        refine ⟨hr, heq, ?_, hframe⟩
        intro i hi
        rw [hdeg i hi, heq, adjOfTake_m]
      · intro stL ⟨hr, hle, hdeg, hframe⟩ hv
        have hr0 : stL.regs 0 = gAddr := by rw [hr 0 (by decide)]; exact hregs 0 (by decide)
        have hr4 : stL.regs 4 = G.m := by rw [hr 4 (by decide)]; exact hregs 4 (by decide)
        have hr6 : stL.regs 6 = offBase := by rw [hr 6 (by decide)]; exact hregs 6 (by decide)
        have hr10 : stL.regs 10 = locBase := by rw [hr 10 (by decide)]; exact hregs 10 (by decide)
        have hlt : stL.regs 11 < G.m := by split_ifs at hv <;> omega
        set j := stL.regs 11 with hj_def
        set e := G.edges[j]'hlt with he_def
        have he_val : e.1 < G.n ∧ e.2 < G.n := hG_val e (List.getElem_mem hlt)
        have hgl : G.encode.length = 2 + 2 * G.m := graph_encode_length G
        have hsp : offBase + 1 + X.card ≤ locBase ∧
            locBase + G.n ≤ workAddr + localCsrSpace G.n G.m X.card := by
          dsimp only [offBase, locBase, csrOffAddr, csrLocIdAddr, localCsrSpace]; omega
        have ha_mem : stL.mem (gAddr + 2 + 2 * j) = e.1 := by
          rw [hframe _ (Or.inl (by dsimp only [offBase, csrOffAddr]; omega))]
          exact graphAt_edge_fst hG hlt
        have hb_mem : stL.mem (gAddr + 3 + 2 * j) = e.2 := by
          rw [hframe _ (Or.inl (by dsimp only [offBase, csrOffAddr]; omega))]
          exact graphAt_edge_snd hG hlt
        have hla_mem : stL.mem (locBase + e.1) = if e.1 ∈ X then locOf X e.1 + 1 else 0 := by
          rw [hframe _ (Or.inr (by omega))]; exact hloc e.1 he_val.1
        have hlb_mem : stL.mem (locBase + e.2) = if e.2 ∈ X then locOf X e.2 + 1 else 0 := by
          rw [hframe _ (Or.inr (by omega))]; exact hloc e.2 he_val.2
        have hlen_bnd : ∀ i < X.card, (adjOfTake G X j (origOf X i)).length ≤ 2 * G.m := by
          intro i hi
          have h1 := adjOfTake_length_le G X (Nat.le_of_lt hlt) (origOf X i)
          have h2 : (adjOf G X (origOf X i)).length ≤ ∑ v ∈ X, (adjOf G X v).length :=
            Finset.single_le_sum (f := fun v => (adjOf G X v).length)
              (fun _ _ => Nat.zero_le _) (origOf_mem hi)
          rw [sum_adjOf_length] at h2
          have h3 : (G.inside X).length ≤ G.m := List.length_filter_le _ _
          omega
        wram_enter
        · subst st
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := e.1) (by rw [← ha_mem]; eval_expr) ?_
          refine runs_seq_assign_le (v := e.2) (by rw [← hb_mem]; eval_expr) ?_
          refine runs_seq_assign_le (v := if e.1 ∈ X then locOf X e.1 + 1 else 0)
            (by rw [← hla_mem]; eval_expr) ?_
          refine runs_seq_assign_le (v := if e.2 ∈ X then locOf X e.2 + 1 else 0)
            (by rw [← hlb_mem]; eval_expr) ?_
          by_cases he1 : e.1 ∈ X
          · have hia_lt : locOf X e.1 < X.card := locOf_lt he1
            refine runs_seq_cond_le (v := locOf X e.1 + 1) (by simp only [he1, ↓reduceIte]; eval_expr)
              (fun _ => ?_) (fun h0 => absurd h0 (Nat.succ_ne_zero _))
            by_cases he2 : e.2 ∈ X
            · have hib_lt : locOf X e.2 < X.card := locOf_lt he2
              refine runs_seq_cond_le (v := locOf X e.2 + 1) (by simp only [he2, ↓reduceIte]; eval_expr)
                (fun _ => ?_) (fun h0 => absurd h0 (Nat.succ_ne_zero _))
              set ia := locOf X e.1
              set ib := locOf X e.2
              have hda_eq : stL.mem (offBase + 1 + ia) = (adjOfTake G X j (origOf X ia)).length :=
                hdeg ia hia_lt
              have hda_le : (adjOfTake G X j (origOf X ia)).length ≤ 2 * G.m := hlen_bnd ia hia_lt
              have hdb_le : (adjOfTake G X j (origOf X ib)).length ≤ 2 * G.m := hlen_bnd ib hib_lt
              have hda_lt : stL.mem (offBase + 1 + ia) + 1 < 2 ^ w := by
                have : 2 * G.m ≤ localCsrSpace G.n G.m X.card := by dsimp only [localCsrSpace]; omega
                omega
              have hupd_le : Function.update stL.mem (offBase + 1 + ia)
                  (stL.mem (offBase + 1 + ia) + 1) (offBase + 1 + ib) + 1 < 2 ^ w := by
                have h2m : 2 * G.m ≤ localCsrSpace G.n G.m X.card := by dsimp only [localCsrSpace]; omega
                by_cases hab : ia = ib
                · rw [hab, Function.update_self, hdeg ib hib_lt]; omega
                · rw [Function.update_of_ne (by omega), hdeg ib hib_lt]; omega
              refine runs_seq_assoc_le ?_
              refine runs_seq_assign_le (v := ia)
                (by (conv_rhs => rw [← Nat.add_sub_cancel ia 1]); simp only [he1, ↓reduceIte]; eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_assign_le (v := ib)
                (by (conv_rhs => rw [← Nat.add_sub_cancel ib 1]); simp only [he2, ↓reduceIte]; eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_assign_le (v := offBase + 1 + ia) (by eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_store_le (x := offBase + 1 + ia)
                (v := stL.mem (offBase + 1 + ia) + 1) (by eval_expr) (by eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_assign_le (v := offBase + 1 + ib) (by eval_expr) ?_
              refine runs_seq_store_le (x := offBase + 1 + ib)
                (v := Function.update stL.mem (offBase + 1 + ia) (stL.mem (offBase + 1 + ia) + 1)
                  (offBase + 1 + ib) + 1)
                (by eval_expr) (by eval_expr) ?_
              wram_step
              · dsimp only [normalPost]
                refine ⟨⟨fun r hr' => by
                    simp only [Function.update_of_ne (by omega : r ≠ 11),
                      Function.update_of_ne (by omega : r ≠ 12),
                      Function.update_of_ne (by omega : r ≠ 13),
                      Function.update_of_ne (by omega : r ≠ 14),
                      Function.update_of_ne (by omega : r ≠ 15)]
                    exact hr r hr',
                  by simp [← hj_def]; omega, ?_, ?_⟩, by simp [← hj_def]; omega⟩
                · intro i hi
                  simp only [Function.update_self, ← hj_def]
                  rw [adjOfTake_succ G X hlt (origOf X i)]
                  rw [← he_def]
                  simp only [he1, he2, and_self, ↓reduceIte, List.length_append]
                  have hia_iff : e.1 = origOf X i ↔ i = ia :=
                    ⟨fun h => by dsimp only [ia]; rw [h, locOf_origOf hi],
                     fun h => by rw [h, origOf_locOf he1]⟩
                  have hib_iff : e.2 = origOf X i ↔ i = ib :=
                    ⟨fun h => by dsimp only [ib]; rw [h, locOf_origOf hi],
                     fun h => by rw [h, origOf_locOf he2]⟩
                  have h1_eq : (if e.1 = origOf X i then [(e.2, j)] else []).length =
                      if i = ia then 1 else 0 := by
                    simp only [hia_iff]; split_ifs <;> simp
                  have h2_eq : (if e.2 = origOf X i then [(e.1, j)] else []).length =
                      if i = ib then 1 else 0 := by
                    simp only [hib_iff]; split_ifs <;> simp
                  rw [h1_eq, h2_eq, ← hdeg i hi]
                  by_cases hi1 : i = ia <;> by_cases hi2 : i = ib
                  · subst hi1; rw [hi2]
                    simp only [Function.update_self, ↓reduceIte]
                  · subst hi1
                    rw [Function.update_of_ne (by omega), Function.update_self]; simp [hi2]
                  · subst hi2
                    rw [Function.update_self, Function.update_of_ne (by omega)]; simp [hi1]
                  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                    simp [hi1, hi2]
                · intro a ha
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                  exact hframe a ha
              · wram_cost
            · refine runs_seq_cond_le (v := 0) (by simp only [he2, ↓reduceIte]; eval_expr)
                (fun h0 => absurd rfl h0) (fun _ => ?_)
              wram_run
              · dsimp only [normalPost]
                refine ⟨⟨fun r hr' => by
                    simp only [Function.update_of_ne (by omega : r ≠ 11),
                      Function.update_of_ne (by omega : r ≠ 12),
                      Function.update_of_ne (by omega : r ≠ 13),
                      Function.update_of_ne (by omega : r ≠ 14),
                      Function.update_of_ne (by omega : r ≠ 15)]
                    exact hr r hr',
                  by simp [← hj_def]; omega, ?_, hframe⟩, by simp [← hj_def]; omega⟩
                intro i hi
                simp only [Function.update_self, ← hj_def]
                rw [adjOfTake_succ G X hlt (origOf X i)]
                rw [← he_def]
                simp [he2, hdeg i hi]
              · wram_cost
          · refine runs_seq_cond_le (v := 0) (by simp only [he1, ↓reduceIte]; eval_expr)
              (fun h0 => absurd rfl h0) (fun _ => ?_)
            wram_run
            · dsimp only [normalPost]
              refine ⟨⟨fun r hr' => by
                  simp only [Function.update_of_ne (by omega : r ≠ 11),
                    Function.update_of_ne (by omega : r ≠ 12),
                    Function.update_of_ne (by omega : r ≠ 13),
                    Function.update_of_ne (by omega : r ≠ 14),
                    Function.update_of_ne (by omega : r ≠ 15)]
                  exact hr r hr',
                by simp [← hj_def]; omega, ?_, hframe⟩, by simp [← hj_def]; omega⟩
              intro i hi
              simp only [Function.update_self, ← hj_def]
              rw [adjOfTake_succ G X hlt (origOf X i)]
              rw [← he_def]
              simp [he1, hdeg i hi]
            · wram_cost
    have hinit :
        (∀ r ≤ 10, ({ st2 with regs := Function.update st2.regs 11 0 }).regs r = st2.regs r) ∧
        ({ st2 with regs := Function.update st2.regs 11 0 }).regs 11 ≤ G.m ∧
        (∀ i < X.card, ({ st2 with regs := Function.update st2.regs 11 0 }).mem (offBase + 1 + i) =
          (adjOfTake G X (({ st2 with regs := Function.update st2.regs 11 0 }).regs 11)
            (origOf X i)).length) ∧
        (∀ a, (a < offBase + 1 ∨ offBase + 1 + X.card ≤ a) →
          ({ st2 with regs := Function.update st2.regs 11 0 }).mem a = mem2 a) := by
      refine ⟨fun r hr => Function.update_of_ne (by omega) _ _, by simp,
        fun i hi => by
          dsimp only
          simp only [Function.update_self, hmem2, adjOfTake_zero, List.length_nil]
          exact hoff0 i hi,
        fun _ _ => hmem2 ▸ rfl⟩
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := hloop _ ω hinit
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      rcases hpost with ⟨hr', _, hdeg', hframe'⟩
      exact ⟨.normal, st', c, hrun, ⟨hr', hdeg', hframe'⟩, by
        simp only [Function.update_self, Nat.sub_zero, Expr.size_bin, Expr.size_reg,
          Expr.size_const] at hcost ⊢
        omega⟩

lemma csrPrefixSum_triple {w : ℕ} {p : Program}
    {gAddr xAddr workAddr : ℕ} {G : Graph} {X : Finset ℕ}
    {mem3 : ℕ → ℕ} {st3 : State}
    (hoff0 : mem3 (csrOffAddr workAddr X.card) = 0)
    (hdeg : ∀ i < X.card, mem3 (csrOffAddr workAddr X.card + 1 + i) =
      (adjOf G X (origOf X i)).length)
    (hw : workAddr + localCsrSpace G.n G.m X.card + 4 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hregs : ∀ r ≤ 10, st3.regs r =
      match r with
      | 0 => gAddr | 1 => xAddr | 2 => workAddr | 3 => G.n | 4 => G.m | 5 => X.card
      | 6 => csrOffAddr workAddr X.card
      | 7 => csrWCurAddr workAddr X.card
      | 8 => csrNbAddr workAddr X.card
      | 9 => csrEdgeAddr workAddr X.card G.m
      | _ => csrLocIdAddr workAddr X.card G.m)
    (hmem3 : st3.mem = mem3) :
    Triple w p
      (fun st => st = st3)
      csrPrefixSumStmt
      (normalPost fun st' =>
        (∀ r ≤ 10, st'.regs r = st3.regs r) ∧
        (∀ i ≤ X.card, st'.mem (csrOffAddr workAddr X.card + i) = adjCsrOff X (adjOf G X) i) ∧
        (∀ i < X.card, st'.mem (csrWCurAddr workAddr X.card + i) = adjCsrOff X (adjOf G X) i) ∧
        (∀ a, (a < csrOffAddr workAddr X.card ∨
               csrWCurAddr workAddr X.card + X.card ≤ a) → st'.mem a = mem3 a))
      (fun _ => 50 * X.card + 20) := by
  wram_enter
  · subst st
    dsimp only [csrPrefixSumStmt, seqStmts]
    wram_step
    let offBase := csrOffAddr workAddr X.card
    let wcurBase := csrWCurAddr workAddr X.card
    have htotal_le : adjCsrOff X (adjOf G X) X.card ≤ 2 * G.m := by
      rw [adjCsrOff_adjOf_card]
      have : (G.inside X).length ≤ G.m := List.length_filter_le _ _
      omega
    have hloop :
        Triple w p
          (fun st =>
            (∀ r ≤ 10, st.regs r = st3.regs r) ∧
            st.regs 11 ≤ X.card ∧
            (∀ i ≤ st.regs 11, st.mem (offBase + i) = adjCsrOff X (adjOf G X) i) ∧
            (∀ i, st.regs 11 < i → i ≤ X.card →
              st.mem (offBase + i) = (adjOf G X (origOf X (i - 1))).length) ∧
            (∀ i < st.regs 11, st.mem (wcurBase + i) = adjCsrOff X (adjOf G X) i) ∧
            (∀ a, (a < offBase ∨ wcurBase + X.card ≤ a) → st.mem a = mem3 a))
          (.loop (.bin .lt (.reg 11) (.reg 5))
            (seqStmts
              [ .assign 12 (.load (.bin .add (.reg 6) (.reg 11)))
              , .store (.bin .add (.reg 7) (.reg 11)) (.reg 12)
              , .assign 13 (.bin .add (.bin .add (.reg 6) (.reg 11)) (.const 1))
              , .store (.reg 13) (.bin .add (.reg 12) (.load (.reg 13)))
              , .assign 11 (.bin .add (.reg 11) (.const 1)) ]))
          (normalPost fun st' =>
            (∀ r ≤ 10, st'.regs r = st3.regs r) ∧
            st'.regs 11 = X.card ∧
            (∀ i ≤ X.card, st'.mem (offBase + i) = adjCsrOff X (adjOf G X) i) ∧
            (∀ i < X.card, st'.mem (wcurBase + i) = adjCsrOff X (adjOf G X) i) ∧
            (∀ a, (a < offBase ∨ wcurBase + X.card ≤ a) → st'.mem a = mem3 a))
          (fun st => ((Expr.bin .lt (.reg 11) (.reg 5)).size + 42 + 1) * (X.card - st.regs 11) +
            (Expr.bin .lt (.reg 11) (.reg 5)).size + 1) := by
      refine Triple.loop_const_normal
        (m := fun st => X.card - st.regs 11)
        (condVal := fun st => if st.regs 11 < X.card then 1 else 0)
        (bodyBound := 42) ?_ ?_ ?_
      · intro stL ⟨hr, _, _, _, _, _⟩
        have hr5 : stL.regs 5 = X.card := by rw [hr 5 (by decide)]; exact hregs 5 (by decide)
        eval_expr
      · intro stL ⟨hr, _, hoff_pre, _, hwcur, hframe⟩ hv
        have heq : stL.regs 11 = X.card := by split_ifs at hv; omega
        exact ⟨hr, heq, by rwa [heq] at hoff_pre, by rwa [heq] at hwcur, hframe⟩
      · intro stL ⟨hr, hle, hoff_pre, hoff_suf, hwcur, hframe⟩ hv
        have hr5 : stL.regs 5 = X.card := by rw [hr 5 (by decide)]; exact hregs 5 (by decide)
        have hr6 : stL.regs 6 = offBase := by rw [hr 6 (by decide)]; exact hregs 6 (by decide)
        have hr7 : stL.regs 7 = wcurBase := by rw [hr 7 (by decide)]; exact hregs 7 (by decide)
        have hlt : stL.regs 11 < X.card := by split_ifs at hv <;> omega
        set i := stL.regs 11 with hi_def
        have hcur_eq : stL.mem (offBase + i) = adjCsrOff X (adjOf G X) i := hoff_pre i le_rfl
        have hnxt_eq : stL.mem (offBase + i + 1) = (adjOf G X (origOf X i)).length := by
          rw [show offBase + i + 1 = offBase + (i + 1) by omega]
          simpa using hoff_suf (i + 1) (by omega) (by omega)
        have hsum_eq : adjCsrOff X (adjOf G X) i + (adjOf G X (origOf X i)).length =
            adjCsrOff X (adjOf G X) (i + 1) := (adjCsrOff_succ X (adjOf G X) i).symm
        have hsum_le : adjCsrOff X (adjOf G X) (i + 1) ≤ 2 * G.m :=
          le_trans (adjCsrOff_mono X (adjOf G X) (Nat.succ_le_of_lt hlt)) htotal_le
        have hsp : wcurBase = offBase + X.card + 1 ∧
            wcurBase + X.card ≤ workAddr + localCsrSpace G.n G.m X.card ∧
            2 * G.m ≤ localCsrSpace G.n G.m X.card := by
          dsimp only [offBase, wcurBase, csrOffAddr, csrWCurAddr, localCsrSpace]; omega
        have hnxt_eq' : Function.update stL.mem (wcurBase + i) (adjCsrOff X (adjOf G X) i)
            (offBase + i + 1) = (adjOf G X (origOf X i)).length := by
          rw [Function.update_of_ne (by omega), hnxt_eq]
        wram_enter
        · subst st
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := adjCsrOff X (adjOf G X) i)
            (by rw [← hcur_eq]; eval_expr) ?_
          refine runs_seq_store_le (x := wcurBase + i) (v := adjCsrOff X (adjOf G X) i)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := offBase + i + 1) (by eval_expr) ?_
          refine runs_seq_store_le (x := offBase + i + 1)
            (v := adjCsrOff X (adjOf G X) (i + 1)) (by eval_expr)
            (by rw [← hsum_eq, ← hnxt_eq']; eval_expr) ?_
          wram_step
          · dsimp only [normalPost]
            refine ⟨⟨fun r hr' => by
                simp only [Function.update_of_ne (by omega : r ≠ 11),
                  Function.update_of_ne (by omega : r ≠ 12),
                  Function.update_of_ne (by omega : r ≠ 13)]
                exact hr r hr',
              by simp [← hi_def]; omega, ?_, ?_, ?_, ?_⟩, by simp [← hi_def]; omega⟩
            · intro k hk
              simp only [Function.update_self, ← hi_def] at hk
              by_cases hkeq : k = i + 1
              · subst hkeq
                rw [show offBase + (i + 1) = offBase + i + 1 by omega, Function.update_self]
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hoff_pre k (by omega)
            · intro k hk1 hk2
              simp only [Function.update_self, ← hi_def] at hk1
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hoff_suf k (by omega) hk2
            · intro k hk
              simp only [Function.update_self, ← hi_def] at hk
              by_cases hkeq : k = i
              · subst hkeq
                rw [Function.update_of_ne (by omega), Function.update_self]
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hwcur k (by omega)
            · intro a ha
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hframe a ha
          · wram_cost
    have hinit :
        (∀ r ≤ 10, ({ st3 with regs := Function.update st3.regs 11 0 }).regs r = st3.regs r) ∧
        ({ st3 with regs := Function.update st3.regs 11 0 }).regs 11 ≤ X.card ∧
        (∀ i ≤ ({ st3 with regs := Function.update st3.regs 11 0 }).regs 11,
          ({ st3 with regs := Function.update st3.regs 11 0 }).mem (offBase + i) =
            adjCsrOff X (adjOf G X) i) ∧
        (∀ i, ({ st3 with regs := Function.update st3.regs 11 0 }).regs 11 < i → i ≤ X.card →
          ({ st3 with regs := Function.update st3.regs 11 0 }).mem (offBase + i) =
            (adjOf G X (origOf X (i - 1))).length) ∧
        (∀ i < ({ st3 with regs := Function.update st3.regs 11 0 }).regs 11,
          ({ st3 with regs := Function.update st3.regs 11 0 }).mem (wcurBase + i) =
            adjCsrOff X (adjOf G X) i) ∧
        (∀ a, (a < offBase ∨ wcurBase + X.card ≤ a) →
          ({ st3 with regs := Function.update st3.regs 11 0 }).mem a = mem3 a) := by
      refine ⟨fun r hr => Function.update_of_ne (by omega) _ _, by simp,
        fun i hi => by
          dsimp only at hi ⊢
          have hi0 : i = 0 := by simp only [Function.update_self] at hi; omega
          subst hi0
          simp only [Nat.add_zero, hmem3, adjCsrOff_zero]
          exact hoff0,
        fun i hi1 hi2 => by
          dsimp only at hi1 ⊢
          simp only [Function.update_self] at hi1
          rw [hmem3, show offBase + i = offBase + 1 + (i - 1) by omega]
          exact hdeg (i - 1) (by omega),
        fun _ hi => by simp at hi, fun _ _ => hmem3 ▸ rfl⟩
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := hloop _ ω hinit
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      rcases hpost with ⟨hr', _, hoff', hwcur', hframe'⟩
      exact ⟨.normal, st', c, hrun, ⟨hr', hoff', hwcur', hframe'⟩, by
        simp only [Function.update_self, Nat.sub_zero, Expr.size_bin, Expr.size_reg,
          Expr.size_const] at hcost ⊢
        omega⟩

end MinCostFlow.ExpanderDecomp
