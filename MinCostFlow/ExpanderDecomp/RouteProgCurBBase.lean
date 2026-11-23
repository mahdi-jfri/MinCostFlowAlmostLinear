module

public import MinCostFlow.ExpanderDecomp.RouteProgResCsrBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sorted Target-Set Builder Base (`RouteProgCurBBase`)

Specification, procedure statements, pure helper lemmas, and zero/count pass verifications
(`curBZero_triple`, `curBCount_triple`) for `buildCurBProc`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Sorted Target-Set Builder (`buildCurBProc`) -/

/-- Compact sorted local-ID slices for target sets `B_i` of `pairs`. -/
def LocalBSlicesAt (mem : ℕ → ℕ) (bOffAddr bLenAddr bDataAddr : ℕ)
    (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (cap : ℕ) : Prop :=
  mem (bOffAddr + pairs.length) ≤ cap ∧
  ∀ i (hi : i < pairs.length),
    let off := mem (bOffAddr + i)
    let len := mem (bLenAddr + i)
    off + len = mem (bOffAddr + i + 1) ∧
    len = (pairs[i]'hi).2.card ∧
    ListAt mem (bDataAddr + off) (((pairs[i]'hi).2.sort (· ≤ ·)).map (locOf X))

/-- Prefix sum of `|B_t|` over `t < i`. -/
def pairBOff (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ) : ℕ :=
  ((pairs.take i).map fun p => p.2.card).sum

/-- Step bound for `buildCurBProc`. -/
def buildCurBCost (nX k : ℕ) : ℕ :=
  115 * (nX + k + 1)

/-- Addresses written by `buildCurBProc`. -/
def CurBWriteSet (nX k bOffAddr bLenAddr bDataAddr bCurAddr : ℕ) (a : ℕ) : Prop :=
  (bOffAddr ≤ a ∧ a < bOffAddr + k + 1) ∨
  (bLenAddr ≤ a ∧ a < bLenAddr + k) ∨
  (bDataAddr ≤ a ∧ a < bDataAddr + nX) ∨
  (bCurAddr ≤ a ∧ a < bCurAddr + k)

/-- Disjointness and word-size invariants for `buildCurBProc`. -/
structure CurBDisj (w nX k pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr : ℕ) : Prop where
  bo_bl : DisjRange bOffAddr (k + 1) bLenAddr k
  bo_bd : DisjRange bOffAddr (k + 1) bDataAddr nX
  bo_bc : DisjRange bOffAddr (k + 1) bCurAddr k
  bo_pb : DisjRange bOffAddr (k + 1) pairBAddr nX
  bl_bd : DisjRange bLenAddr k bDataAddr nX
  bl_bc : DisjRange bLenAddr k bCurAddr k
  bl_pb : DisjRange bLenAddr k pairBAddr nX
  bd_bc : DisjRange bDataAddr nX bCurAddr k
  bd_pb : DisjRange bDataAddr nX pairBAddr nX
  bc_pb : DisjRange bCurAddr k pairBAddr nX
  w_pb : pairBAddr + nX + 5 < 2 ^ w
  w_bo : bOffAddr + k + 5 < 2 ^ w
  w_bl : bLenAddr + k + 5 < 2 ^ w
  w_bd : bDataAddr + nX + 5 < 2 ^ w
  w_bc : bCurAddr + k + 5 < 2 ^ w
  w_nX : nX + 5 < 2 ^ w
  w_k : k + 5 < 2 ^ w
  w_4 : 4 ≤ 2 ^ w

/-- Pass 0: zero `bLen[0 .. k - 1]`. -/
def curBZeroStmt : Stmt :=
  seqStmts
    [ .assign 7 (.const 0)
    , .loop (.bin .lt (.reg 7) (.reg 2))
        (seqStmts
          [ .store (.bin .add (.reg 4) (.reg 7)) (.const 0)
          , .assign 7 (.bin .add (.reg 7) (.const 1)) ]) ]

/-- Pass 1: count `|B_i|` into `bLen[i]` by sweeping `pairB[0 .. nX - 1]`. -/
def curBCountStmt : Stmt :=
  seqStmts
    [ .assign 7 (.const 0)
    , .loop (.bin .lt (.reg 7) (.reg 1))
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 0) (.reg 7)))
          , .cond (.reg 8)
              (seqStmts
                [ .assign 9 (.bin .sub (.reg 8) (.const 1))
                , .assign 10 (.load (.bin .add (.reg 4) (.reg 9)))
                , .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1)) ])
              .nop
          , .assign 7 (.bin .add (.reg 7) (.const 1)) ]) ]

/-- Pass 2: prefix-sum `bLen[0 .. k - 1]` into `bOff[0 .. k]` and `bCur[0 .. k - 1]`, leaving
total `∑ |B_i|` in register `8`. -/
def curBPrefixStmt : Stmt :=
  seqStmts
    [ .assign 7 (.const 0)
    , .assign 8 (.const 0)
    , .loop (.bin .lt (.reg 7) (.reg 2))
        (seqStmts
          [ .store (.bin .add (.reg 3) (.reg 7)) (.reg 8)
          , .store (.bin .add (.reg 6) (.reg 7)) (.reg 8)
          , .assign 9 (.load (.bin .add (.reg 4) (.reg 7)))
          , .assign 8 (.bin .add (.reg 8) (.reg 9))
          , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
    , .store (.bin .add (.reg 3) (.reg 2)) (.reg 8) ]

/-- Pass 3: scatter `v = 0 .. nX - 1` into `bData` in ascending order using `bCur`. -/
def curBScatterStmt : Stmt :=
  seqStmts
    [ .assign 7 (.const 0)
    , .loop (.bin .lt (.reg 7) (.reg 1))
        (seqStmts
          [ .assign 9 (.load (.bin .add (.reg 0) (.reg 7)))
          , .cond (.reg 9)
              (seqStmts
                [ .assign 10 (.bin .sub (.reg 9) (.const 1))
                , .assign 11 (.load (.bin .add (.reg 6) (.reg 10)))
                , .store (.bin .add (.reg 5) (.reg 11)) (.reg 7)
                , .store (.bin .add (.reg 6) (.reg 10)) (.bin .add (.reg 11) (.const 1)) ])
              .nop
          , .assign 7 (.bin .add (.reg 7) (.const 1)) ]) ]

/-- Build compact sorted local-ID slices for all remaining target sets `B_i`.
Arguments: `[pairBAddr, nX, k, bOffAddr, bLenAddr, bDataAddr, bCurAddr]`.
Returns `∑ |B_i|`. -/
def buildCurBProc : Stmt :=
  seqStmts
    [ curBZeroStmt
    , curBCountStmt
    , curBPrefixStmt
    , curBScatterStmt
    , .ret (.reg 8) ]

theorem buildCurBProc_noRand : Stmt.NoRand buildCurBProc := by
  unfold buildCurBProc curBZeroStmt curBCountStmt curBPrefixStmt curBScatterStmt
  repeat (first | apply seqStmts_noRand | constructor | simp)

/-- Contract for `buildCurBProc` on
`[pairBAddr, nX, k, bOffAddr, bLenAddr, bDataAddr, bCurAddr]`. -/
def buildCurBContract (w : ℕ) (X : Finset ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) : Contract where
  pre args mem :=
    args.length = 7 ∧
    let pairBAddr := args.getD 0 0
    let nX := args.getD 1 0
    let k := args.getD 2 0
    let bOffAddr := args.getD 3 0
    let bLenAddr := args.getD 4 0
    let bDataAddr := args.getD 5 0
    let bCurAddr := args.getD 6 0
    nX = X.card ∧
    k = pairs.length ∧
    RouteTerminalPairs X pairs ∧
    LocalBPairsAt mem pairBAddr X pairs ∧
    CurBDisj w X.card pairs.length pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr
  post args mem v mem' :=
    let bOffAddr := args.getD 3 0
    let bLenAddr := args.getD 4 0
    let bDataAddr := args.getD 5 0
    let bCurAddr := args.getD 6 0
    v = pairBOff pairs pairs.length ∧
    v ≤ X.card ∧
    LocalBSlicesAt mem' bOffAddr bLenAddr bDataAddr X pairs X.card ∧
    (∀ a, ¬ CurBWriteSet X.card pairs.length bOffAddr bLenAddr bDataAddr bCurAddr a → mem' a = mem a)
  cost _ _ := buildCurBCost X.card pairs.length

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 5. Pure Helper Lemmas for `buildCurBProc` -/

lemma pairBOff_zero (pairs : List (Finset ℕ × Finset ℕ)) : pairBOff pairs 0 = 0 := by
  simp [pairBOff]

lemma pairBOff_succ (pairs : List (Finset ℕ × Finset ℕ)) {i : ℕ} (hi : i < pairs.length) :
    pairBOff pairs (i + 1) = pairBOff pairs i + (pairs[i]'hi).2.card := by
  unfold pairBOff
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

lemma pairBOff_mono (pairs : List (Finset ℕ × Finset ℕ)) {i j : ℕ} (hij : i ≤ j) :
    pairBOff pairs i ≤ pairBOff pairs j := by
  induction hij with
  | refl => exact le_rfl
  | @step m _ ih =>
    by_cases hm : m < pairs.length
    · rw [pairBOff_succ pairs hm]; omega
    · have h1 : pairs.take (m + 1) = pairs.take m := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp only [pairBOff, h1]; exact ih

lemma pairBOff_le_card {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hp : RouteTerminalPairs X pairs) (i : ℕ) :
    pairBOff pairs i ≤ X.card := by
  have h1 : pairBOff pairs i ≤ pairBOff pairs pairs.length := by
    by_cases hi : i ≤ pairs.length
    · exact pairBOff_mono pairs hi
    · unfold pairBOff; rw [List.take_of_length_le (by omega), List.take_length]
  have h2 : pairBOff pairs pairs.length ≤ (pairs.map fun p => p.1.card + p.2.card).sum := by
    unfold pairBOff; rw [List.take_length]
    clear hp h1
    induction pairs with
    | nil => simp
    | cons pq rest ih => simp only [List.map_cons, List.sum_cons]; omega
  exact le_trans (le_trans h1 h2) (routeTerminalPairs_sum_card_le hp)

lemma localPrefix_zero' (X A : Finset ℕ) : localPrefix X A 0 = [] := by
  simp [localPrefix]

lemma localPrefix_card_eq (X : Finset ℕ) {A : Finset ℕ} (hA : A ⊆ X) :
    localPrefix X A X.card = (A.sort (· ≤ ·)).map (locOf X) := by
  unfold localPrefix
  rw [List.filter_eq_self]
  intro x hx
  rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
  rw [Finset.mem_sort] at hu
  simp [locOf_lt (hA hu)]

lemma localPrefix_succ' {X A : Finset ℕ} (hA : A ⊆ X) {v : ℕ} (hv : v < X.card) :
    localPrefix X A (v + 1) = localPrefix X A v ++ if origOf X v ∈ A then [v] else [] := by
  simp only [localPrefix, filter_lt_succ_of_pairwise_lt (pairwise_lt_map_locOf hA) v,
    mem_map_locOf_iff hA hv]

lemma localPrefix_length_le' {X A : Finset ℕ} (v : ℕ) :
    (localPrefix X A v).length ≤ A.card := by
  unfold localPrefix
  exact le_trans (List.length_filter_le _ _) (by simp)

/-! ## 6. Verification of `buildCurBProc` -/

lemma curBZero_triple {w : ℕ} {p : Program}
    {nX k pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr : ℕ}
    (hdisj : CurBDisj w nX k pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr)
    {st0 : State}
    (hr2 : st0.regs 2 = k) (hr4 : st0.regs 4 = bLenAddr) :
    ∀ ω,
      ∃ st' c,
        Runs w p ω curBZeroStmt st0 .normal st' c ∧
        (∀ r, r ≠ 7 → st'.regs r = st0.regs r) ∧
        (∀ i < k, st'.mem (bLenAddr + i) = 0) ∧
        (∀ a, ¬ (bLenAddr ≤ a ∧ a < bLenAddr + k) → st'.mem a = st0.mem a) ∧
        c ≤ 18 * k + 15 := by
  have hw_bl := hdisj.w_bl; have hw_k := hdisj.w_k; have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hloop : ∀ (rem i : ℕ) (st : State),
      i + rem = k →
      st.regs 2 = k → st.regs 4 = bLenAddr → st.regs 7 = i →
      (∀ j < i, st.mem (bLenAddr + j) = 0) →
      ∀ ω,
        ∃ st' c,
          Runs w p ω
            (.loop (.bin .lt (.reg 7) (.reg 2))
              (seqStmts
                [ .store (.bin .add (.reg 4) (.reg 7)) (.const 0)
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ]))
            st .normal st' c ∧
          (∀ r, r ≠ 7 → st'.regs r = st.regs r) ∧
          (∀ j < k, st'.mem (bLenAddr + j) = 0) ∧
          (∀ a, ¬ (bLenAddr ≤ a ∧ a < bLenAddr + k) → st'.mem a = st.mem a) ∧
          c ≤ 18 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i st hi h2 h4 h7 hinv ω
      have hi_eq : i = k := by omega
      subst hi_eq
      refine ⟨st, _, runs_loop_zero (by simp [Expr.eval, BinOp.eval, h7, h2]),
        fun _ _ => rfl, hinv, fun _ _ => rfl, by simp [Expr.size]⟩
    | succ rem ih =>
      intro i st hi h2 h4 h7 hinv ω
      have hcond : (Expr.bin .lt (.reg 7) (.reg 2)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, h7, h2, show i < k by omega, hw_ne]
      set st1 : State :=
        { mem := Function.update st.mem (bLenAddr + i) 0
          regs := Function.update st.regs 7 (i + 1)
          pos := st.pos }
      have hbody : ∃ cB,
          Runs w p ω
            (seqStmts
              [ .store (.bin .add (.reg 4) (.reg 7)) (.const 0)
              , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
            st .normal st1 cB ∧ cB ≤ 14 := by
        have h0 : ∃ o s c,
            Runs w p ω
              (seqStmts
                [ .store (.bin .add (.reg 4) (.reg 7)) (.const 0)
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 14 := by
          dsimp only [seqStmts]
          refine runs_seq_store_le (x := bLenAddr + i) (v := 0) (by eval_expr) (by eval_expr) ?_
          refine runs_assign_le (v := i + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0 with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
        exact ⟨cB, hrun, by omega⟩
      rcases hbody with ⟨cB, hrunB, hcB⟩
      obtain ⟨stF, cIH, hrunIH, hregsIH, hinvF, hfrF, hcIH⟩ :=
        ih (i + 1) st1 (by omega) (by simp [st1, h2]) (by simp [st1, h4]) (by simp [st1])
          (fun j hj => by
            by_cases hji : j < i
            · rw [show st1.mem _ = Function.update st.mem (bLenAddr + i) 0 _ from rfl,
                  Function.update_of_ne (by omega)]; exact hinv j hji
            · have : j = i := by omega
              subst this; simp [st1]) ω
      refine ⟨stF, _, runs_loop_step hcond (by decide) hrunB hrunIH,
        fun r hr => (hregsIH r hr).trans (by simp [st1, hr]),
        hinvF,
        fun a ha => (hfrF a ha).trans (by simp [st1, Function.update_of_ne (by omega : a ≠ bLenAddr + i)]),
        by simp only [Expr.size]; omega⟩
  intro ω
  set st1 : State := { st0 with regs := Function.update st0.regs 7 0 }
  have hinit : Runs w p ω (.assign 7 (.const 0)) st0 .normal st1 ((Expr.const 0).size + 1) :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨stF, cL, hrunL, hregsL, hinvF, hfrF, hcL⟩ :=
    hloop k 0 st1 (Nat.zero_add _) (by simp [st1, hr2]) (by simp [st1, hr4]) (by simp [st1])
      (fun _ h => by omega) ω
  refine ⟨stF, _, runs_seq_iff.mpr (Or.inr ⟨st1, _, cL, hinit, hrunL, rfl⟩),
    fun r hr => (hregsL r hr).trans (by simp [st1, hr]), hinvF, hfrF,
    by simp only [Expr.size]; omega⟩

lemma curBCount_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr : ℕ}
    (hp : RouteTerminalPairs X pairs)
    (hdisj : CurBDisj w X.card pairs.length pairBAddr bOffAddr bLenAddr bDataAddr bCurAddr)
    {st0 : State}
    (hbp : LocalBPairsAt st0.mem pairBAddr X pairs)
    (hzero : ∀ i < pairs.length, st0.mem (bLenAddr + i) = 0)
    (hr0 : st0.regs 0 = pairBAddr) (hr1 : st0.regs 1 = X.card) (hr4 : st0.regs 4 = bLenAddr) :
    ∀ ω,
      ∃ st' c,
        Runs w p ω curBCountStmt st0 .normal st' c ∧
        (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → st'.regs r = st0.regs r) ∧
        (∀ i (hi : i < pairs.length), st'.mem (bLenAddr + i) = (pairs[i]'hi).2.card) ∧
        (∀ a, ¬ (bLenAddr ≤ a ∧ a < bLenAddr + pairs.length) → st'.mem a = st0.mem a) ∧
        c ≤ 40 * X.card + 15 := by
  have hw_pb := hdisj.w_pb; have hw_bl := hdisj.w_bl; have hw_nX := hdisj.w_nX
  have hw_k := hdisj.w_k; have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hloop : ∀ (rem v : ℕ) (st : State),
      v + rem = X.card →
      LocalBPairsAt st.mem pairBAddr X pairs →
      st.regs 0 = pairBAddr → st.regs 1 = X.card → st.regs 4 = bLenAddr → st.regs 7 = v →
      (∀ i (hi : i < pairs.length), st.mem (bLenAddr + i) = (localPrefix X (pairs[i]'hi).2 v).length) →
      ∀ ω,
        ∃ st' c,
          Runs w p ω
            (.loop (.bin .lt (.reg 7) (.reg 1))
              (seqStmts
                [ .assign 8 (.load (.bin .add (.reg 0) (.reg 7)))
                , .cond (.reg 8)
                    (seqStmts
                      [ .assign 9 (.bin .sub (.reg 8) (.const 1))
                      , .assign 10 (.load (.bin .add (.reg 4) (.reg 9)))
                      , .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1)) ])
                    .nop
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ]))
            st .normal st' c ∧
          (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → st'.regs r = st.regs r) ∧
          (∀ i (hi : i < pairs.length), st'.mem (bLenAddr + i) = (pairs[i]'hi).2.card) ∧
          (∀ a, ¬ (bLenAddr ≤ a ∧ a < bLenAddr + pairs.length) → st'.mem a = st.mem a) ∧
          c ≤ 40 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro v st hv _ h0 h1 h4 h7 hinv ω
      have hv_eq : v = X.card := by omega
      subst hv_eq
      refine ⟨st, _, runs_loop_zero (by simp [Expr.eval, BinOp.eval, h7, h1]),
        fun _ _ _ _ _ => rfl, ?_, fun _ _ => rfl, by simp [Expr.size]⟩
      intro i hi
      have hBiX : (pairs[i]'hi).2 ⊆ X := (hp.1 _ (List.getElem_mem hi)).2.1
      rw [hinv i hi, localPrefix_card_eq X hBiX]; simp
    | succ rem ih =>
      intro v st hv hbp_s h0 h1 h4 h7 hinv ω
      have hv_lt : v < X.card := by omega
      have hcond : (Expr.bin .lt (.reg 7) (.reg 1)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, h7, h1, hv_lt, hw_ne]
      set tag := st.mem (pairBAddr + v)
      have htag_le : tag ≤ pairs.length := (hbp_s v hv_lt).1
      by_cases htag0 : tag = 0
      · set st1 : State :=
          { mem := st.mem
            regs := Function.update (Function.update st.regs 8 0) 7 (v + 1)
            pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .assign 8 (.load (.bin .add (.reg 0) (.reg 7)))
                , .cond (.reg 8)
                    (seqStmts
                      [ .assign 9 (.bin .sub (.reg 8) (.const 1))
                      , .assign 10 (.load (.bin .add (.reg 4) (.reg 9)))
                      , .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1)) ])
                    .nop
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              st .normal st1 cB ∧ cB ≤ 36 := by
          have h0' : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 8 (.load (.bin .add (.reg 0) (.reg 7)))
                  , .cond (.reg 8)
                      (seqStmts
                        [ .assign 9 (.bin .sub (.reg 8) (.const 1))
                        , .assign 10 (.load (.bin .add (.reg 4) (.reg 9)))
                        , .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1)) ])
                      .nop
                  , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
                st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 36 := by
            dsimp only [seqStmts]
            refine runs_seq_assign_le (v := 0)
              (by simp [Expr.eval, BinOp.eval, h0, h7, show pairBAddr + v < 2 ^ w by omega,
                   show st.mem (pairBAddr + v) = 0 from htag0]) ?_
            refine runs_seq_cond_zero_le (by eval_expr) ?_
            refine runs_seq_nop_le ?_
            refine runs_assign_le (v := v + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
          exact ⟨cB, hrun, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        have hinv1 : ∀ i (hi : i < pairs.length),
            st1.mem (bLenAddr + i) = (localPrefix X (pairs[i]'hi).2 (v + 1)).length := by
          intro i hi
          have hBiX : (pairs[i]'hi).2 ⊆ X := (hp.1 _ (List.getElem_mem hi)).2.1
          have hnot : origOf X v ∉ (pairs[i]'hi).2 := by
            intro hm; have := ((hbp_s v hv_lt).2 i hi).mpr hm; omega
          rw [localPrefix_succ' hBiX hv_lt]; simp [st1, hnot, hinv i hi]
        obtain ⟨stF, cIH, hrunIH, hregsIH, hinvF, hfrF, hcIH⟩ :=
          ih (v + 1) st1 (by omega) hbp_s (by simp [st1, h0]) (by simp [st1, h1])
            (by simp [st1, h4]) (by simp [st1]) hinv1 ω
        refine ⟨stF, _, runs_loop_step hcond (by decide) hrunB hrunIH,
          fun r h7' h8' h9' h10' => (hregsIH r h7' h8' h9' h10').trans (by simp [st1, h7', h8']),
          hinvF, hfrF, by simp only [Expr.size]; omega⟩
      · set idx := tag - 1
        have hidx_lt : idx < pairs.length := by omega
        have htag_eq : tag = idx + 1 := by omega
        have hv_in : origOf X v ∈ (pairs[idx]'hidx_lt).2 := ((hbp_s v hv_lt).2 idx hidx_lt).mp htag_eq
        have hBiX : (pairs[idx]'hidx_lt).2 ⊆ X := (hp.1 _ (List.getElem_mem hidx_lt)).2.1
        set curL := (localPrefix X (pairs[idx]'hidx_lt).2 v).length
        have hcurL_mem : st.mem (bLenAddr + idx) = curL := hinv idx hidx_lt
        have hcurL_lt : curL + 1 ≤ X.card := by
          have h1 : (localPrefix X (pairs[idx]'hidx_lt).2 (v + 1)).length ≤ (pairs[idx]'hidx_lt).2.card :=
            localPrefix_length_le' (v + 1)
          have h2 : (pairs[idx]'hidx_lt).2.card ≤ X.card := Finset.card_le_card hBiX
          rw [localPrefix_succ' hBiX hv_lt] at h1; simp [hv_in] at h1; omega
        set mem1 := Function.update st.mem (bLenAddr + idx) (curL + 1)
        set regs1 := Function.update (Function.update (Function.update (Function.update
          st.regs 8 tag) 9 idx) 10 curL) 7 (v + 1)
        set st1 : State := { mem := mem1, regs := regs1, pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .assign 8 (.load (.bin .add (.reg 0) (.reg 7)))
                , .cond (.reg 8)
                    (seqStmts
                      [ .assign 9 (.bin .sub (.reg 8) (.const 1))
                      , .assign 10 (.load (.bin .add (.reg 4) (.reg 9)))
                      , .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1)) ])
                    .nop
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              st .normal st1 cB ∧ cB ≤ 36 := by
          have h0' : ∃ o s c,
              Runs w p ω
                (seqStmts
                  [ .assign 8 (.load (.bin .add (.reg 0) (.reg 7)))
                  , .cond (.reg 8)
                      (seqStmts
                        [ .assign 9 (.bin .sub (.reg 8) (.const 1))
                        , .assign 10 (.load (.bin .add (.reg 4) (.reg 9)))
                        , .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1)) ])
                      .nop
                  , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
                st o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 36 := by
            dsimp only [seqStmts]
            refine runs_seq_assign_le (v := tag) (by eval_expr) ?_
            refine runs_seq_cond_pos_le (v := tag) (by eval_expr) (by omega) ?_
            refine runs_seq_seq_le ?_
            refine runs_seq_assign_le (v := idx) (by eval_expr) ?_
            refine runs_seq_seq_le ?_
            refine runs_seq_assign_le (v := curL) (by rw [← hcurL_mem]; eval_expr) ?_
            refine runs_seq_store_le (x := bLenAddr + idx) (v := curL + 1)
              (by eval_expr) (by eval_expr) ?_
            refine runs_assign_le (v := v + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
          rcases h0' with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
          exact ⟨cB, hrun, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        have hbp1 : LocalBPairsAt st1.mem pairBAddr X pairs := by
          intro u hu
          simp only [st1, mem1,
            Function.update_of_ne (by rcases hdisj.bl_pb with x | x <;> omega : pairBAddr + u ≠ bLenAddr + idx)]
          exact hbp_s u hu
        have hinv1 : ∀ i (hi : i < pairs.length),
            st1.mem (bLenAddr + i) = (localPrefix X (pairs[i]'hi).2 (v + 1)).length := by
          intro i hi
          have hBiX' : (pairs[i]'hi).2 ⊆ X := (hp.1 _ (List.getElem_mem hi)).2.1
          rw [localPrefix_succ' hBiX' hv_lt]
          by_cases heq : i = idx
          · subst heq; simp [st1, mem1, hv_in, curL]
          · have hnot : origOf X v ∉ (pairs[i]'hi).2 := by
              intro hm; have := ((hbp_s v hv_lt).2 i hi).mpr hm; omega
            simp only [st1, mem1, Function.update_of_ne (by omega : bLenAddr + i ≠ bLenAddr + idx),
              hnot, ↓reduceIte, List.append_nil]
            exact hinv i hi
        obtain ⟨stF, cIH, hrunIH, hregsIH, hinvF, hfrF, hcIH⟩ :=
          ih (v + 1) st1 (by omega) hbp1
            (by simp [st1, regs1, h0]) (by simp [st1, regs1, h1])
            (by simp [st1, regs1, h4]) (by simp [st1, regs1]) hinv1 ω
        refine ⟨stF, _, runs_loop_step hcond (by decide) hrunB hrunIH,
          fun r h7' h8' h9' h10' => (hregsIH r h7' h8' h9' h10').trans (by simp [st1, regs1, h7', h8', h9', h10']),
          hinvF,
          fun a ha => (hfrF a ha).trans (by simp [st1, mem1, Function.update_of_ne (by omega : a ≠ bLenAddr + idx)]),
          by simp only [Expr.size]; omega⟩
  intro ω
  set st1 : State := { st0 with regs := Function.update st0.regs 7 0 }
  have hinit : Runs w p ω (.assign 7 (.const 0)) st0 .normal st1 ((Expr.const 0).size + 1) :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨stF, cL, hrunL, hregsL, hinvF, hfrF, hcL⟩ :=
    hloop X.card 0 st1 (Nat.zero_add _) hbp
      (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr4]) (by simp [st1])
      (fun i hi => by simp [st1, localPrefix_zero', hzero i hi]) ω
  refine ⟨stF, _, runs_seq_iff.mpr (Or.inr ⟨st1, _, cL, hinit, hrunL, rfl⟩),
    fun r h7 h8 h9 h10 => (hregsL r h7 h8 h9 h10).trans (by simp [st1, h7]),
    hinvF, hfrF, by simp only [Expr.size]; omega⟩


end MinCostFlow.ExpanderDecomp
