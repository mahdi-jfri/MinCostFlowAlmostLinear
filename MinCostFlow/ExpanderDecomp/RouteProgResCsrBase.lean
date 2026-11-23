module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.RouteProgLayout
public import MinCostFlow.ExpanderDecomp.RouteProgCongr
public import MinCostFlow.ExpanderDecomp.RouteProgPairsBase
public import MinCostFlow.ExpanderDecomp.RouteProgBFSBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Residual Neighbor-Only CSR Builder and Sorted Target-Set Builder (`RouteProgResCsr`)

Provides two `O(|X| + e_X + k + 1)` deterministic Word-RAM helper procedures invoked on the
failed-batch (cut-finding) branch of `runBatch`:

1. `buildResCsrProc`: filters a local neighbor-only CSR `NbCsrAt` of `G[X]` against a vertex
   mask `origOf X v ∈ V` (`V ⊆ X`), producing `NbCsrAt` of the residual graph
   `H_res = ⟨G.n, G.inside V⟩` on `X` in `≤ 45 * (|X| + m2 + 1)` steps.
2. `buildCurBProc`: converts the target-membership table `LocalBPairsAt` of `remPairs` into
   compact sorted local-ID slices `LocalBPairsSlicesAt` (`bOff`, `bLen`, `bData`) in
   `≤ 80 * (|X| + k + 1)` steps.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander


/-! ## 1. Residual CSR Builder (`buildResCsrProc`) -/

/-- Step bound for `buildResCsrProc`. -/
def buildResCsrCost (nX m2 : ℕ) : ℕ :=
  70 * (nX + m2 + 1)

/-- Addresses written by `buildResCsrProc`. -/
def ResCsrWriteSet (nX m2 resOffAddr resNbAddr : ℕ) (a : ℕ) : Prop :=
  (resOffAddr ≤ a ∧ a < resOffAddr + nX + 1) ∨
  (resNbAddr ≤ a ∧ a < resNbAddr + m2)

/-- Disjointness and word-size invariants for `buildResCsrProc`. -/
structure ResCsrDisj (w nX m2 offAddr nbAddr maskArrAddr maskBadVal
    resOffAddr resNbAddr : ℕ) : Prop where
  ro_rn : DisjRange resOffAddr (nX + 1) resNbAddr m2
  ro_off : DisjRange resOffAddr (nX + 1) offAddr (nX + 1)
  ro_nb : DisjRange resOffAddr (nX + 1) nbAddr m2
  ro_mask : DisjRange resOffAddr (nX + 1) maskArrAddr nX
  rn_off : DisjRange resNbAddr m2 offAddr (nX + 1)
  rn_nb : DisjRange resNbAddr m2 nbAddr m2
  rn_mask : DisjRange resNbAddr m2 maskArrAddr nX
  w_off : offAddr + nX + 5 < 2 ^ w
  w_nb : nbAddr + m2 + 5 < 2 ^ w
  w_mask : maskArrAddr + nX + 5 < 2 ^ w
  w_ro : resOffAddr + nX + 5 < 2 ^ w
  w_rn : resNbAddr + m2 + 5 < 2 ^ w
  w_nX : nX + 5 < 2 ^ w
  w_m2 : m2 + 5 < 2 ^ w
  w_mb : maskBadVal < 2 ^ w
  w_4 : 4 ≤ 2 ^ w

/-- Inner loop of `buildResCsrProc`: scan `nb[r10 .. r11 - 1]`, appending unmasked neighbors to
`resNb[r7++]`. -/
def resCsrInnerLoop : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 11))
    (seqStmts
      [ .assign 12 (.load (.bin .add (.reg 1) (.reg 10)))
      , .assign 13 (.load (.bin .add (.reg 2) (.reg 12)))
      , .cond (.bin .eq (.reg 13) (.reg 3))
          .nop
          (seqStmts
            [ .store (.bin .add (.reg 6) (.reg 7)) (.reg 12)
            , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
      , .assign 10 (.bin .add (.reg 10) (.const 1)) ])

/-- Outer loop of `buildResCsrProc`: scan `u = 0 .. nX - 1`, recording `resOff[u]` and filtering
neighbors when `mask[u] ≠ maskBadVal`. -/
def resCsrOuterLoop : Stmt :=
  .loop (.bin .lt (.reg 8) (.reg 4))
    (seqStmts
      [ .store (.bin .add (.reg 5) (.reg 8)) (.reg 7)
      , .assign 9 (.load (.bin .add (.reg 2) (.reg 8)))
      , .cond (.bin .eq (.reg 9) (.reg 3))
          .nop
          (seqStmts
            [ .assign 10 (.load (.bin .add (.reg 0) (.reg 8)))
            , .assign 11 (.load (.bin .add (.reg 0) (.bin .add (.reg 8) (.const 1))))
            , resCsrInnerLoop ])
      , .assign 8 (.bin .add (.reg 8) (.const 1)) ])

/-- Build neighbor-only residual CSR of `H_res = ⟨G.n, G.inside V⟩` from `G[X]`'s `NbCsrAt`.
Arguments: `[offAddr, nbAddr, maskArrAddr, maskBadVal, nX, resOffAddr, resNbAddr]`.
Returns `adjCsrOff X (adjOf ⟨G.n, G.inside V⟩ X) X.card`. -/
def buildResCsrProc : Stmt :=
  seqStmts
    [ .assign 7 (.const 0)
    , .assign 8 (.const 0)
    , resCsrOuterLoop
    , .store (.bin .add (.reg 5) (.reg 4)) (.reg 7)
    , .ret (.reg 7) ]

theorem buildResCsrProc_noRand : Stmt.NoRand buildResCsrProc := by
  unfold buildResCsrProc resCsrOuterLoop resCsrInnerLoop
  repeat (first | apply seqStmts_noRand | constructor | simp)

/-- Contract for `buildResCsrProc` on
`[offAddr, nbAddr, maskArrAddr, maskBadVal, nX, resOffAddr, resNbAddr]`. -/
def buildResCsrContract (w : ℕ) (G : Graph) (X V : Finset ℕ) (m2 : ℕ) : Contract where
  pre args mem :=
    args.length = 7 ∧
    let offAddr := args.getD 0 0
    let nbAddr := args.getD 1 0
    let maskArrAddr := args.getD 2 0
    let maskBadVal := args.getD 3 0
    let nX := args.getD 4 0
    let resOffAddr := args.getD 5 0
    let resNbAddr := args.getD 6 0
    nX = X.card ∧
    V ⊆ X ∧
    NbCsrAt mem offAddr nbAddr X (adjOf G X) ∧
    adjCsrOff X (adjOf G X) X.card ≤ m2 ∧
    (∀ v < X.card, mem (maskArrAddr + v) ≠ maskBadVal ↔ origOf X v ∈ V) ∧
    ResCsrDisj w X.card m2 offAddr nbAddr maskArrAddr maskBadVal resOffAddr resNbAddr
  post args mem v mem' :=
    let resOffAddr := args.getD 5 0
    let resNbAddr := args.getD 6 0
    let adjRes := adjOf ⟨G.n, G.inside V⟩ X
    v = adjCsrOff X adjRes X.card ∧
    v ≤ m2 ∧
    NbCsrAt mem' resOffAddr resNbAddr X adjRes ∧
    (∀ a, ¬ ResCsrWriteSet X.card m2 resOffAddr resNbAddr a → mem' a = mem a)
  cost _ _ := buildResCsrCost X.card m2

/-! ## 3. Pure Helper Lemmas for Residual CSR -/

lemma adjOf_fst_mem_X (G : Graph) (X : Finset ℕ) (u : ℕ) :
    ∀ p ∈ adjOf G X u, p.1 ∈ X := by
  intro p hp
  unfold adjOf insideEdgesIdx at hp
  rw [List.mem_flatMap] at hp
  rcases hp with ⟨ie, hie, hp'⟩
  rw [List.mem_filter] at hie
  have hX : ie.2.1 ∈ X ∧ ie.2.2 ∈ X := by
    have h := hie.2
    unfold insideB at h
    simpa [Bool.and_eq_true, decide_eq_true_eq] using h
  rw [List.mem_append] at hp'
  rcases hp' with h1 | h2
  · split_ifs at h1
    · simp only [List.mem_singleton] at h1; rw [h1]; exact hX.2
    · cases h1
  · split_ifs at h2
    · simp only [List.mem_singleton] at h2; rw [h2]; exact hX.1
    · cases h2

lemma adjOf_inside_length (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X) (v : ℕ) :
    (adjOf ⟨G.n, G.inside V⟩ X v).length =
      if v ∈ V then ((adjOf G X v).filter fun p => decide (p.1 ∈ V)).length else 0 := by
  have h := congrArg List.length (adjOf_inside_map_fst G hVX v)
  simp only [List.length_map] at h
  split_ifs at h ⊢
  · simpa [List.length_map] using h
  · simpa using h

lemma adjCsrOff_inside_le (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X) (k : ℕ) :
    adjCsrOff X (adjOf ⟨G.n, G.inside V⟩ X) k ≤ adjCsrOff X (adjOf G X) k := by
  unfold adjCsrOff
  apply Finset.sum_le_sum
  intro i _
  rw [adjOf_inside_length G hVX]
  split_ifs
  · exact List.length_filter_le _ _
  · exact Nat.zero_le _

lemma adjOf_inside_getElem_fst (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    {v : ℕ} (hv : v ∈ V) {j : ℕ} (hj : j < (adjOf ⟨G.n, G.inside V⟩ X v).length) :
    ((adjOf ⟨G.n, G.inside V⟩ X v)[j]'hj).1 =
      (((adjOf G X v).filter fun p => decide (p.1 ∈ V))[j]'(by
        have := adjOf_inside_length G hVX v; simp [hv] at this; omega)).1 := by
  have h := adjOf_inside_map_fst G hVX v
  simp only [hv, ↓reduceIte] at h
  have hj1 : j < ((adjOf ⟨G.n, G.inside V⟩ X v).map Prod.fst).length := by
    simp only [List.length_map]; exact hj
  have hget := congrArg (fun l => l[j]?) h
  rw [List.getElem?_eq_getElem hj1,
      List.getElem?_eq_getElem (by rw [← h]; exact hj1)] at hget
  simp only [Option.some.injEq, List.getElem_map] at hget
  exact hget

/-! ## 4. Verification of `buildResCsrProc` -/

lemma runs_seq_seq_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ s₃ : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω (.seq s₁ (.seq s₂ s₃)) st o st' c ∧ Q o st' ∧ (k + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.seq s₁ s₂) s₃) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  rcases runs_seq_iff.mp hr with ⟨v, c₁, hr₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂₃, hr₁, hr₂₃, rfl⟩
  · refine ⟨.returned v, st', (c₁ + 1) + 1,
      runs_seq_iff.mpr (Or.inl ⟨v, c₁ + 1, runs_seq_iff.mpr (Or.inl ⟨v, c₁, hr₁, rfl, rfl⟩), rfl, rfl⟩),
      hq, by omega⟩
  · rcases runs_seq_iff.mp hr₂₃ with ⟨v, c₂, hr₂, rfl, rfl⟩ | ⟨st₂, c₂, c₃, hr₂, hr₃, rfl⟩
    · refine ⟨.returned v, st', (c₁ + c₂ + 1) + 1,
        runs_seq_iff.mpr (Or.inl ⟨v, c₁ + c₂ + 1,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), rfl, rfl⟩),
        hq, by omega⟩
    · refine ⟨o, st', (c₁ + c₂ + 1) + c₃ + 1,
        runs_seq_iff.mpr (Or.inr ⟨st₂, c₁ + c₂ + 1, c₃,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hr₃, rfl⟩),
        hq, by omega⟩

lemma runs_loop_zero {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

lemma runs_loop_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {v c₁ c₂ : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h₁ : Runs w p ω body st .normal st₁ c₁)
    (h₂ : Runs w p ω (.loop e body) st₁ o st₂ c₂) :
    Runs w p ω (.loop e body) st o st₂ (e.size + c₁ + c₂ + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, he, hv, h₁, h₂, rfl⟩))

lemma runs_cond_zero {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st st' : State} {o : Outcome} {c : ℕ}
    (he : e.eval w st = some 0) (h : Runs w p ω s₂ st o st' c) :
    Runs w p ω (.cond e s₁ s₂) st o st' (e.size + c + 1) :=
  runs_cond_iff.mpr ⟨0, c, he, by simpa using h, rfl⟩

lemma runs_cond_pos {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st st' : State} {o : Outcome} {v c : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0) (h : Runs w p ω s₁ st o st' c) :
    Runs w p ω (.cond e s₁ s₂) st o st' (e.size + c + 1) :=
  runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using h, rfl⟩

lemma runs_seq_cond_zero_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ s : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some 0)
    (hF : ∃ o st' c, Runs w p ω (.seq s₂ s) st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.cond e s₁ s₂) s) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_cond_le he (fun h => absurd rfl h) (fun _ => hF)

lemma runs_seq_cond_pos_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ s : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (hT : ∃ o st' c, Runs w p ω (.seq s₁ s) st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.cond e s₁ s₂) s) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_cond_le he (fun _ => hT) (fun h => absurd h hv)

lemma resCsrInnerLoop_triple {w : ℕ} {p : Program}
    {G : Graph} {X V : Finset ℕ} {m2 offAddr nbAddr maskArrAddr maskBadVal
      resOffAddr resNbAddr : ℕ}
    (_hVX : V ⊆ X)
    (hm2 : adjCsrOff X (adjOf G X) X.card ≤ m2)
    (hdisj : ResCsrDisj w X.card m2 offAddr nbAddr maskArrAddr maskBadVal resOffAddr resNbAddr)
    {u : ℕ} (hu : u < X.card) (_huV : origOf X u ∈ V)
    {basePos : ℕ}
    (hbase_le : basePos + ((adjOf G X (origOf X u)).filter fun e => decide (e.1 ∈ V)).length ≤ m2)
    (rem : ℕ) :
    ∀ (k : ℕ) (st0 : State),
      k + rem = (adjOf G X (origOf X u)).length →
      NbCsrAt st0.mem offAddr nbAddr X (adjOf G X) →
      (∀ v < X.card, st0.mem (maskArrAddr + v) ≠ maskBadVal ↔ origOf X v ∈ V) →
      st0.regs 1 = nbAddr →
      st0.regs 2 = maskArrAddr →
      st0.regs 3 = maskBadVal →
      st0.regs 6 = resNbAddr →
      st0.regs 7 = basePos + (((adjOf G X (origOf X u)).take k).filter fun e => decide (e.1 ∈ V)).length →
      st0.regs 10 = adjCsrOff X (adjOf G X) u + k →
      st0.regs 11 = adjCsrOff X (adjOf G X) u + (adjOf G X (origOf X u)).length →
      (∀ j (hj : j < (((adjOf G X (origOf X u)).take k).filter fun e => decide (e.1 ∈ V)).length),
        st0.mem (resNbAddr + basePos + j) =
          locOf X ((((adjOf G X (origOf X u)).take k).filter fun e => decide (e.1 ∈ V))[j]'hj).1) →
      ∀ ω,
        ∃ st' c,
          Runs w p ω resCsrInnerLoop st0 .normal st' c ∧
          (∀ r, r ≠ 7 → r ≠ 10 → r ≠ 12 → r ≠ 13 → st'.regs r = st0.regs r) ∧
          st'.regs 7 = basePos + ((adjOf G X (origOf X u)).filter fun e => decide (e.1 ∈ V)).length ∧
          (∀ j (hj : j < ((adjOf G X (origOf X u)).filter fun e => decide (e.1 ∈ V)).length),
            st'.mem (resNbAddr + basePos + j) =
              locOf X (((adjOf G X (origOf X u)).filter fun e => decide (e.1 ∈ V))[j]'hj).1) ∧
          (∀ a, ¬ (resNbAddr + basePos + (((adjOf G X (origOf X u)).take k).filter fun e => decide (e.1 ∈ V)).length ≤ a ∧
                   a < resNbAddr + m2) →
            st'.mem a = st0.mem a) ∧
          c ≤ 40 * rem + 10 := by
  have hw_off := hdisj.w_off; have hw_nb := hdisj.w_nb; have hw_mask := hdisj.w_mask
  have hw_ro := hdisj.w_ro; have hw_rn := hdisj.w_rn; have hw_nX := hdisj.w_nX
  have hw_m2 := hdisj.w_m2; have hw_mb := hdisj.w_mb; have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hhi_le_m2 : adjCsrOff X (adjOf G X) u + (adjOf G X (origOf X u)).length ≤ m2 := by
    have h1 := adjCsrOff_succ X (adjOf G X) u
    have h2 := adjCsrOff_mono X (adjOf G X) (show u + 1 ≤ X.card by omega)
    omega
  induction rem with
  | zero =>
    intro k st0 hk hcsr hmask hr1 hr2 hr3 hr6 hr7 hr10 hr11 hpref ω
    have hk_eq : k = (adjOf G X (origOf X u)).length := by omega
    have htake : (adjOf G X (origOf X u)).take k = adjOf G X (origOf X u) := by
      rw [hk_eq, List.take_length]
    have hcond : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st0 = some 0 := by
      simp [Expr.eval, BinOp.eval, hr10, hr11, hk_eq]
    refine ⟨st0, (Expr.bin .lt (.reg 10) (.reg 11)).size + 1,
      runs_loop_zero hcond, fun _ _ _ _ _ => rfl, ?_, ?_, fun _ _ => rfl, ?_⟩
    · simpa [htake] using hr7
    · simpa [htake] using hpref
    · simp [Expr.size]
  | succ rem ih =>
    intro k st0 hk hcsr hmask hr1 hr2 hr3 hr6 hr7 hr10 hr11 hpref ω
    set l := adjOf G X (origOf X u)
    set pref := (l.take k).filter fun e => decide (e.1 ∈ V)
    have hk_lt : k < l.length := by omega
    set e := l[k]'hk_lt
    have heX : e.1 ∈ X := adjOf_fst_mem_X G X (origOf X u) e (List.getElem_mem hk_lt)
    have hnb_loc : locOf X e.1 < X.card := locOf_lt heX
    have hnb_mem : st0.mem (nbAddr + (adjCsrOff X (adjOf G X) u + k)) = locOf X e.1 := by
      rw [← Nat.add_assoc]; exact hcsr.2 u hu k hk_lt
    have hpref_succ : (l.take (k + 1)).filter (fun p => decide (p.1 ∈ V)) =
        pref ++ if e.1 ∈ V then [e] else [] := by
      rw [List.take_succ_eq_append_getElem hk_lt, List.filter_append, List.filter_cons, List.filter_nil]
      by_cases hV : e.1 ∈ V <;> simp [pref, e, hV]
    have hpref_len_le : pref.length ≤ (l.filter fun p => decide (p.1 ∈ V)).length := by
      have hsp := (List.take_append_drop k l).symm
      have hlen : (l.filter fun p => decide (p.1 ∈ V)).length =
          pref.length + ((l.drop k).filter fun p => decide (p.1 ∈ V)).length := by
        conv_lhs => rw [hsp, List.filter_append, List.length_append]
      omega
    have hcond : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hr10, hr11, show adjCsrOff X (adjOf G X) u + k < adjCsrOff X (adjOf G X) u + l.length by omega, hw_ne]
    set mval := st0.mem (maskArrAddr + locOf X e.1)
    have hmval_iff : mval ≠ maskBadVal ↔ e.1 ∈ V := by
      simpa [mval, origOf_locOf heX] using hmask (locOf X e.1) hnb_loc
    -- Execute one body iteration
    by_cases hV : e.1 ∈ V
    · -- Keep neighbor: write resNb[basePos + pref.length] := locOf X e.1
      have hne_mb : mval ≠ maskBadVal := hmval_iff.mpr hV
      have hpref_lt_tot : pref.length + 1 ≤ (l.filter fun p => decide (p.1 ∈ V)).length := by
        have hsp := (List.take_append_drop (k + 1) l).symm
        have hlen : (l.filter fun p => decide (p.1 ∈ V)).length =
            ((l.take (k + 1)).filter fun p => decide (p.1 ∈ V)).length +
            ((l.drop (k + 1)).filter fun p => decide (p.1 ∈ V)).length := by
          conv_lhs => rw [hsp, List.filter_append, List.length_append]
        rw [hpref_succ] at hlen; simp [hV] at hlen; omega
      set mem1 := Function.update st0.mem (resNbAddr + (basePos + pref.length)) (locOf X e.1)
      set regs1 := Function.update (Function.update (Function.update (Function.update
        st0.regs 12 (locOf X e.1)) 13 mval) 7 (basePos + pref.length + 1)) 10
        (adjCsrOff X (adjOf G X) u + k + 1)
      set st1 : State := { mem := mem1, regs := regs1, pos := st0.pos }
      have hbody : ∃ cB,
          Runs w p ω
            (seqStmts
              [ .assign 12 (.load (.bin .add (.reg 1) (.reg 10)))
              , .assign 13 (.load (.bin .add (.reg 2) (.reg 12)))
              , .cond (.bin .eq (.reg 13) (.reg 3))
                  .nop
                  (seqStmts
                    [ .store (.bin .add (.reg 6) (.reg 7)) (.reg 12)
                    , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              , .assign 10 (.bin .add (.reg 10) (.const 1)) ])
            st0 .normal st1 cB ∧ cB ≤ 32 := by
        have h0 : ∃ o s c,
            Runs w p ω
              (seqStmts
                [ .assign 12 (.load (.bin .add (.reg 1) (.reg 10)))
                , .assign 13 (.load (.bin .add (.reg 2) (.reg 12)))
                , .cond (.bin .eq (.reg 13) (.reg 3))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 6) (.reg 7)) (.reg 12)
                      , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
                , .assign 10 (.bin .add (.reg 10) (.const 1)) ])
              st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 32 := by
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := locOf X e.1)
            (by rw [← hnb_mem]; eval_expr) ?_
          refine runs_seq_assign_le (v := mval)
            (by eval_expr) ?_
          refine runs_seq_cond_zero_le
            (by simp [Expr.eval, BinOp.eval, hr3, hne_mb]) ?_
          refine runs_seq_seq_le ?_
          refine runs_seq_store_le (x := resNbAddr + (basePos + pref.length)) (v := locOf X e.1)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := basePos + pref.length + 1) (by eval_expr) ?_
          refine runs_assign_le (v := adjCsrOff X (adjOf G X) u + k + 1) (by eval_expr)
            ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0 with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
        exact ⟨cB, hrun, by omega⟩
      rcases hbody with ⟨cB, hrunB, hcB⟩
      have hmem1_fr : ∀ a, a ≠ resNbAddr + (basePos + pref.length) → mem1 a = st0.mem a :=
        fun a ha => Function.update_of_ne ha _ _
      have hcsr1 : NbCsrAt st1.mem offAddr nbAddr X (adjOf G X) := by
        refine hcsr.congr (fun i hi => hmem1_fr _ (by rcases hdisj.rn_off with x | x <;> omega))
          (fun j hj => hmem1_fr _ (by rcases hdisj.rn_nb with x | x <;> omega))
      have hmask1 : ∀ v < X.card, st1.mem (maskArrAddr + v) ≠ maskBadVal ↔ origOf X v ∈ V := by
        intro v hv
        rw [show st1.mem _ = mem1 _ from rfl, hmem1_fr _ (by rcases hdisj.rn_mask with x | x <;> omega)]
        exact hmask v hv
      have hpref1 : ∀ j (hj : j < ((l.take (k + 1)).filter fun p => decide (p.1 ∈ V)).length),
          st1.mem (resNbAddr + basePos + j) =
          locOf X (((l.take (k + 1)).filter fun p => decide (p.1 ∈ V))[j]'hj).1 := by
        intro j hj
        have hj' : j < (pref ++ [e]).length := by simpa [hpref_succ, hV] using hj
        have hget : ((l.take (k + 1)).filter fun p => decide (p.1 ∈ V))[j]'hj = (pref ++ [e])[j]'hj' := by
          congr 1; simp [hpref_succ, hV]
        rw [hget]
        by_cases hjp : j < pref.length
        · rw [List.getElem_append_left hjp]
          rw [show st1.mem _ = mem1 _ from rfl, hmem1_fr _ (by omega)]
          exact hpref j hjp
        · have hj_eq : j = pref.length := by simp at hj'; omega
          subst hj_eq
          rw [List.getElem_append_right (le_refl _)]
          simp [st1, mem1, Nat.add_assoc]
      obtain ⟨stF, cIH, hrunIH, hregsIH, hr7IH, hprefIH, hfrIH, hcIH⟩ :=
        ih (k + 1) st1 (by omega) hcsr1 hmask1
          (by simp [st1, regs1, hr1]) (by simp [st1, regs1, hr2])
          (by simp [st1, regs1, hr3]) (by simp [st1, regs1, hr6])
          (by simp [st1, regs1, hpref_succ, hV]; omega)
          (by simp [st1, regs1]; omega) (by simp [st1, regs1, hr11])
          hpref1 ω
      refine ⟨stF, _, runs_loop_step hcond (by decide) hrunB hrunIH,
        fun r h7 h10 h12 h13 => (hregsIH r h7 h10 h12 h13).trans (by simp [st1, regs1, h7, h10, h12, h13]),
        hr7IH, hprefIH, ?_, ?_⟩
      · intro a ha
        rw [hfrIH a (by simp [hpref_succ, hV]; omega), show st1.mem a = mem1 a from rfl,
            hmem1_fr a (by omega)]
      · simp only [Expr.size]; omega
    · -- Skip neighbor
      have heq_mb : mval = maskBadVal := by by_contra hne; exact hV (hmval_iff.mp hne)
      set regs1 := Function.update (Function.update (Function.update
        st0.regs 12 (locOf X e.1)) 13 mval) 10 (adjCsrOff X (adjOf G X) u + k + 1)
      set st1 : State := { mem := st0.mem, regs := regs1, pos := st0.pos }
      have hbody : ∃ cB,
          Runs w p ω
            (seqStmts
              [ .assign 12 (.load (.bin .add (.reg 1) (.reg 10)))
              , .assign 13 (.load (.bin .add (.reg 2) (.reg 12)))
              , .cond (.bin .eq (.reg 13) (.reg 3))
                  .nop
                  (seqStmts
                    [ .store (.bin .add (.reg 6) (.reg 7)) (.reg 12)
                    , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              , .assign 10 (.bin .add (.reg 10) (.const 1)) ])
            st0 .normal st1 cB ∧ cB ≤ 32 := by
        have h0 : ∃ o s c,
            Runs w p ω
              (seqStmts
                [ .assign 12 (.load (.bin .add (.reg 1) (.reg 10)))
                , .assign 13 (.load (.bin .add (.reg 2) (.reg 12)))
                , .cond (.bin .eq (.reg 13) (.reg 3))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 6) (.reg 7)) (.reg 12)
                      , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
                , .assign 10 (.bin .add (.reg 10) (.const 1)) ])
              st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 32 := by
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := locOf X e.1)
            (by rw [← hnb_mem]; eval_expr) ?_
          refine runs_seq_assign_le (v := mval)
            (by eval_expr) ?_
          refine runs_seq_cond_pos_le (v := 1)
            (by simp [Expr.eval, BinOp.eval, hr3, heq_mb, hw_ne]) (by decide) ?_
          refine runs_seq_nop_le ?_
          refine runs_assign_le (v := adjCsrOff X (adjOf G X) u + k + 1) (by eval_expr)
            ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0 with ⟨_, _, cB, hrun, ⟨rfl, rfl⟩, hcB⟩
        exact ⟨cB, hrun, by omega⟩
      rcases hbody with ⟨cB, hrunB, hcB⟩
      obtain ⟨stF, cIH, hrunIH, hregsIH, hr7IH, hprefIH, hfrIH, hcIH⟩ :=
        ih (k + 1) st1 (by omega) hcsr hmask
          (by simp [st1, regs1, hr1]) (by simp [st1, regs1, hr2])
          (by simp [st1, regs1, hr3]) (by simp [st1, regs1, hr6])
          (by simp [st1, regs1, hr7, hpref_succ, hV])
          (by simp [st1, regs1]; omega) (by simp [st1, regs1, hr11])
          (by intro j hj; have h1 : (l.take (k + 1)).filter (fun p => decide (p.1 ∈ V)) = pref := by
                simp [hpref_succ, hV]
              simpa [h1] using hpref j (by simpa [h1] using hj)) ω
      refine ⟨stF, _, runs_loop_step hcond (by decide) hrunB hrunIH,
        fun r h7 h10 h12 h13 => (hregsIH r h7 h10 h12 h13).trans (by simp [st1, regs1, h10, h12, h13]),
        hr7IH, hprefIH, ?_, ?_⟩
      · intro a ha
        exact hfrIH a (by simpa [l, pref, hpref_succ, hV] using ha)
      · simp only [Expr.size]; omega


end MinCostFlow.ExpanderDecomp
