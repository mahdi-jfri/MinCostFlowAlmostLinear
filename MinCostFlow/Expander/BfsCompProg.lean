module

public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.Expander.Components
import MinCostFlow.Spanner.Layouts
import Mathlib.Tactic.Linarith

/-!
# Deterministic `O(n + m + 1)` Connected Components in Word-RAM (`BfsCompProg`)

Implements two `NoRand` Word-RAM procedures over CSR representations (`HasCsrAt`):
1. `bfsLabelsProc`: `args = [n, m, csrAddr, queueBase, rootBase]`, `O(n + m + 1)`, single flat BFS loop
   writing `root[0..n-1]` at `rootBase` with `root[x] = root[y] ↔ (compLabels G).getD x 0 = (compLabels G).getD y 0`,
   hence `Cited.partsOf G root = Cited.partsOf G (compLabels G)`.
2. `bfsCompsProc`: `args = [n, m, csrAddr, workAddr, outAddr]`, `O(n + m + 1)`, reusing `bfsLabelsCore`
   plus `O(n)` frequency counting, bucket prefix sums, and linear scatter to emit
   `[rawComps.length] ++ rawComps.flatMap (fun c => c.length :: c)` where each `c` is a nontrivial
   (`2 ≤ c.length`) strictly increasing (`Pairwise (· < ·)`) connected component of `G`.
-/

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

public section

/-! ## 1. Procedures (`NoRand`) -/

/-- Core CSR connected-components labeling (`O(n + m + 1)`), touching only registers `5..14`
and `[rootBase, rootBase + n)`, `[queueBase, queueBase + n)` (`r0 = n, r1 = m, r2 = csrAddr,
r3 = queueBase, r4 = rootBase`). -/
def bfsLabelsCore : Stmt :=
  seqStmts [
    .assign 5 (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 0))) (.const 1)),
    .assign 6 (.const 0),
    .loop (.bin .lt (.reg 6) (.reg 0))
      (.seq (.store (.bin .add (.reg 4) (.reg 6)) (.reg 0))
        (.assign 6 (.bin .add (.reg 6) (.const 1)))),
    .assign 7 (.const 0),
    .assign 8 (.const 0),
    .assign 9 (.const 0),
    .assign 10 (.const 0),
    .assign 11 (.const 0),
    .loop (.bin .lt (.reg 7) (.reg 0))
      (.cond (.bin .lt (.reg 10) (.reg 11))
        (seqStmts [
          .assign 13 (.load (.bin .add (.reg 5) (.reg 10))),
          .assign 14 (.load (.bin .add (.reg 4) (.reg 13))),
          .cond (.bin .eq (.reg 14) (.reg 0))
            (seqStmts [
              .store (.bin .add (.reg 4) (.reg 13)) (.reg 7),
              .store (.bin .add (.reg 3) (.reg 9)) (.reg 13),
              .assign 9 (.bin .add (.reg 9) (.const 1))])
            .nop,
          .assign 10 (.bin .add (.reg 10) (.const 1))])
        (.cond (.bin .lt (.reg 8) (.reg 9))
          (seqStmts [
            .assign 12 (.load (.bin .add (.reg 3) (.reg 8))),
            .assign 8 (.bin .add (.reg 8) (.const 1)),
            .assign 10 (.load (.bin .add (.reg 2) (.reg 12))),
            .assign 11 (.load (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1)))])
          (.seq
            (.assign 14 (.load (.bin .add (.reg 4) (.reg 7))))
            (.cond (.bin .eq (.reg 14) (.reg 0))
              (seqStmts [
                .store (.bin .add (.reg 4) (.reg 7)) (.reg 7),
                .store (.bin .add (.reg 3) (.reg 9)) (.reg 7),
                .assign 9 (.bin .add (.reg 9) (.const 1))])
              (.assign 7 (.bin .add (.reg 7) (.const 1)))))))
  ]

lemma bfsLabelsCore_noRand : bfsLabelsCore.NoRand := by
  simp [bfsLabelsCore, seqStmts, Stmt.NoRand]

/-- `bfsLabelsProc`: `args = [n, m, csrAddr, queueBase, rootBase]`. -/
def bfsLabelsProc : Stmt :=
  .seq bfsLabelsCore (.ret (.const 0))

lemma bfsLabelsProc_noRand : bfsLabelsProc.NoRand :=
  ⟨bfsLabelsCore_noRand, trivial⟩

/-- Scatter core (`O(n)`): given `rootBase` (`r17`) of length `n` (`r0`) with entries `< n`,
uses `sizeBase` (`r3 = workAddr + n`) and `writePtrBase` (`r5 = workAddr + 2 * n`) to emit
nontrivial (`2 ≤ len`) sorted connected components at `outAddr` (`r16`), returning end cursor `r8`. -/
def bfsScatterCore : Stmt :=
  seqStmts [
    .assign 3 (.bin .add (.reg 17) (.reg 0)),
    .assign 5 (.bin .add (.reg 3) (.reg 0)),
    -- Pass 3: zero size[0..n-1]
    .assign 6 (.const 0),
    .loop (.bin .lt (.reg 6) (.reg 0))
      (.seq (.store (.bin .add (.reg 3) (.reg 6)) (.const 0))
        (.assign 6 (.bin .add (.reg 6) (.const 1)))),
    -- Pass 4: count sizes
    .assign 6 (.const 0),
    .loop (.bin .lt (.reg 6) (.reg 0))
      (seqStmts [
        .assign 7 (.load (.bin .add (.reg 17) (.reg 6))),
        .assign 8 (.load (.bin .add (.reg 3) (.reg 7))),
        .store (.bin .add (.reg 3) (.reg 7)) (.bin .add (.reg 8) (.const 1)),
        .assign 6 (.bin .add (.reg 6) (.const 1))]),
    -- Pass 5: prefix sum + emit lengths for nontrivial components
    .assign 7 (.const 0),
    .assign 8 (.bin .add (.reg 16) (.const 1)),
    .assign 6 (.const 0),
    .loop (.bin .lt (.reg 6) (.reg 0))
      (seqStmts [
        .assign 9 (.load (.bin .add (.reg 3) (.reg 6))),
        .cond (.bin .lt (.const 1) (.reg 9))
          (seqStmts [
            .store (.reg 8) (.reg 9),
            .store (.bin .add (.reg 5) (.reg 6)) (.bin .add (.reg 8) (.const 1)),
            .assign 8 (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 9)),
            .assign 7 (.bin .add (.reg 7) (.const 1))])
          .nop,
        .assign 6 (.bin .add (.reg 6) (.const 1))]),
    .store (.reg 16) (.reg 7),
    -- Pass 6: scatter vertices in increasing order
    .assign 6 (.const 0),
    .loop (.bin .lt (.reg 6) (.reg 0))
      (seqStmts [
        .assign 7 (.load (.bin .add (.reg 17) (.reg 6))),
        .assign 9 (.load (.bin .add (.reg 3) (.reg 7))),
        .cond (.bin .lt (.const 1) (.reg 9))
          (seqStmts [
            .assign 10 (.load (.bin .add (.reg 5) (.reg 7))),
            .store (.reg 10) (.reg 6),
            .store (.bin .add (.reg 5) (.reg 7)) (.bin .add (.reg 10) (.const 1))])
          .nop,
        .assign 6 (.bin .add (.reg 6) (.const 1))]),
    .ret (.reg 8)
  ]

lemma bfsScatterCore_noRand : bfsScatterCore.NoRand := by
  simp [bfsScatterCore, seqStmts, Stmt.NoRand]

/-- `bfsCompsProc`: `args = [n, m, csrAddr, workAddr, outAddr]`. Computes sorted nontrivial
connected components in `O(n + m + 1)` time using `[workAddr, workAddr + 3*n)` workspace. -/
def bfsCompsProc : Stmt :=
  seqStmts [
    .assign 17 (.reg 3),
    .assign 16 (.reg 4),
    .assign 4 (.reg 17),
    .assign 3 (.bin .add (.reg 17) (.reg 0)),
    bfsLabelsCore,
    bfsScatterCore
  ]

lemma bfsCompsProc_noRand : bfsCompsProc.NoRand := by
  simp [bfsCompsProc, seqStmts, Stmt.NoRand, bfsLabelsCore_noRand, bfsScatterCore_noRand]

/-! ## 2. Graph reachability and measure helpers -/

private lemma isPathAlong_of_edges_mem {G : Cited.Graph} {mem : ℕ → ℕ} {rootBase : ℕ}
    (hstep : ∀ e ∈ G.edges, mem (rootBase + e.1) = mem (rootBase + e.2))
    {u v : ℕ} {P : List ℕ} (hP : IsPathAlong G.edges u v P) :
    mem (rootBase + u) = mem (rootBase + v) := by
  induction P generalizing u with
  | nil => simp [IsPathAlong] at hP
  | cons x rest ih =>
    rcases hP with ⟨hhead, hlast, hchain⟩
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      rw [hlast]
    | cons y ys =>
      rw [List.isChain_cons_cons] at hchain
      have heq : mem (rootBase + x) = mem (rootBase + y) := by
        rcases hchain.1 with h | h
        · exact hstep (x, y) h
        · exact (hstep (y, x) h).symm
      have ih' := ih (u := y) ⟨rfl, hlast, hchain.2⟩
      exact heq.trans ih'

private lemma csrIncAux_edgeMatches {G : Cited.Graph} (hval : G.IsValid) {u t : ℕ}
    (ht : t < (csrIncAux u 0 G.edges).length) :
    let q := (csrIncAux u 0 G.edges)[t]'ht
    q.1 < G.m ∧ q.2.2 < G.n ∧ q.2.2 ≠ u ∧
      Walk.EdgeMatches (G.edges.getD q.1 (0, 0)) u q.2.2 := by
  have hlt := csrIncAux_getElem_lt hval ht
  have hgen : ∀ (L : List (ℕ × ℕ)) (r : ℕ) q, q ∈ csrIncAux u r L →
      r ≤ q.1 ∧ q.1 - r < L.length ∧ q.2.2 ≠ u ∧
        Walk.EdgeMatches (L.getD (q.1 - r) (0, 0)) u q.2.2 := by
    intro L
    induction L with
    | nil => simp [csrIncAux]
    | cons e rest ih =>
      rcases e with ⟨a, b⟩
      intro r q hq
      simp only [csrIncAux] at hq
      split_ifs at hq with h1 h2 h3
      · rcases ih (r + 1) q hq with ⟨h_ge, h_lt, h_ne, h_em⟩
        have hsub : q.1 - r = (q.1 - (r + 1)) + 1 := by omega
        exact ⟨by omega, by simp; omega, h_ne, by simpa [hsub] using h_em⟩
      · rcases List.mem_cons.mp hq with rfl | hq'
        · refine ⟨le_rfl, by simp, fun h => h1 (h2.trans h.symm), ?_⟩
          simp [Walk.EdgeMatches, h2]
        · rcases ih (r + 1) q hq' with ⟨h_ge, h_lt, h_ne, h_em⟩
          have hsub : q.1 - r = (q.1 - (r + 1)) + 1 := by omega
          exact ⟨by omega, by simp; omega, h_ne, by simpa [hsub] using h_em⟩
      · rcases List.mem_cons.mp hq with rfl | hq'
        · refine ⟨le_rfl, by simp, fun h => h1 (h.trans h3.symm), ?_⟩
          simp [Walk.EdgeMatches, h3]
        · rcases ih (r + 1) q hq' with ⟨h_ge, h_lt, h_ne, h_em⟩
          have hsub : q.1 - r = (q.1 - (r + 1)) + 1 := by omega
          exact ⟨by omega, by simp; omega, h_ne, by simpa [hsub] using h_em⟩
      · rcases ih (r + 1) q hq with ⟨h_ge, h_lt, h_ne, h_em⟩
        have hsub : q.1 - r = (q.1 - (r + 1)) + 1 := by omega
        exact ⟨by omega, by simp; omega, h_ne, by simpa [hsub] using h_em⟩
  have hmem := hgen G.edges 0 _ (List.getElem_mem ht)
  exact ⟨hlt.1, hlt.2.1, hmem.2.2.1, by simpa using hmem.2.2.2⟩

/-! ## 3. Measure helpers for CSR traversal -/

private def compDegSum (G : Cited.Graph) (mem : ℕ → ℕ) (queueBase : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => compDegSum G mem queueBase i +
      (csrOff G (mem (queueBase + i) + 1) - csrOff G (mem (queueBase + i)))

private lemma compDegSum_congr (G : Cited.Graph) (m1 m2 : ℕ → ℕ) (queueBase k : ℕ)
    (h : ∀ i < k, m1 (queueBase + i) = m2 (queueBase + i)) :
    compDegSum G m1 queueBase k = compDegSum G m2 queueBase k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [compDegSum]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

private lemma sum_csrDeg_range (G : Cited.Graph) :
    ∀ k ≤ G.n,
      (∑ u ∈ Finset.range k, (csrOff G (u + 1) - csrOff G u)) = csrOff G k := by
  intro k hk
  induction k with
  | zero => simp [csrOff_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hm := csrOff_mono G (show k ≤ k + 1 by omega)
    omega

private lemma compDegSum_eq_finset_sum (G : Cited.Graph) (mem : ℕ → ℕ) (queueBase : ℕ) :
    ∀ k, compDegSum G mem queueBase k =
      ∑ i ∈ Finset.range k, (csrOff G (mem (queueBase + i) + 1) - csrOff G (mem (queueBase + i)))
  | 0 => by simp [compDegSum]
  | k + 1 => by simp [compDegSum, Finset.sum_range_succ, compDegSum_eq_finset_sum]

private lemma compDegSum_le_two_mul_m (G : Cited.Graph) (mem : ℕ → ℕ) (queueBase k : ℕ)
    (h_lt : ∀ i < k, mem (queueBase + i) < G.n)
    (h_inj : ∀ i < k, ∀ j < k, mem (queueBase + i) = mem (queueBase + j) → i = j) :
    compDegSum G mem queueBase k ≤ 2 * G.m := by
  rw [compDegSum_eq_finset_sum]
  let f : ℕ → ℕ := fun i => mem (queueBase + i)
  let g : ℕ → ℕ := fun u => csrOff G (u + 1) - csrOff G u
  calc ∑ i ∈ Finset.range k, g (f i)
      = ∑ u ∈ (Finset.range k).image f, g u := by
        symm
        refine Finset.sum_image (fun x hx y hy hxy => h_inj x (Finset.mem_range.mp hx)
          y (Finset.mem_range.mp hy) hxy)
    _ ≤ ∑ u ∈ Finset.range G.n, g u := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
        exact Finset.mem_range.mpr (h_lt i (Finset.mem_range.mp hi))
    _ = csrOff G G.n := sum_csrDeg_range G G.n le_rfl
    _ ≤ 2 * G.m := csrOff_le_two_mul_m G G.n

private def compDoneEdges (G : Cited.Graph) (mem : ℕ → ℕ) (queueBase qHead k : ℕ) : ℕ :=
  if qHead = 0 then 0
  else compDegSum G mem queueBase (qHead - 1) + (k - csrOff G (mem (queueBase + (qHead - 1))))

private lemma compDoneEdges_le_two_mul_m (G : Cited.Graph) (mem : ℕ → ℕ) (queueBase qHead k : ℕ)
    (h_lt : ∀ i < qHead, mem (queueBase + i) < G.n)
    (h_inj : ∀ i < qHead, ∀ j < qHead, mem (queueBase + i) = mem (queueBase + j) → i = j)
    (hk_end : 0 < qHead → k ≤ csrOff G (mem (queueBase + (qHead - 1)) + 1)) :
    compDoneEdges G mem queueBase qHead k ≤ 2 * G.m := by
  by_cases h0 : qHead = 0
  · simp [compDoneEdges, h0]
  · have hpos : 0 < qHead := Nat.pos_of_ne_zero h0
    have hq_succ : qHead - 1 + 1 = qHead := Nat.sub_add_cancel hpos
    have hle1 : k - csrOff G (mem (queueBase + (qHead - 1))) ≤
        csrOff G (mem (queueBase + (qHead - 1)) + 1) - csrOff G (mem (queueBase + (qHead - 1))) :=
      Nat.sub_le_sub_right (hk_end hpos) _
    have hsum : compDegSum G mem queueBase (qHead - 1) +
        (csrOff G (mem (queueBase + (qHead - 1)) + 1) - csrOff G (mem (queueBase + (qHead - 1)))) =
        compDegSum G mem queueBase qHead := by
      conv_rhs => rw [← hq_succ]
      rfl
    have h2m := compDegSum_le_two_mul_m G mem queueBase qHead h_lt h_inj
    dsimp only [compDoneEdges]
    simp only [h0, ↓reduceIte]
    omega

private lemma compDoneEdges_congr (G : Cited.Graph) (m1 m2 : ℕ → ℕ) (queueBase qHead k : ℕ)
    (h : ∀ i < qHead, m1 (queueBase + i) = m2 (queueBase + i)) :
    compDoneEdges G m1 queueBase qHead k = compDoneEdges G m2 queueBase qHead k := by
  by_cases h0 : qHead = 0
  · simp [compDoneEdges, h0]
  · dsimp only [compDoneEdges]
    simp only [h0, ↓reduceIte]
    rw [compDegSum_congr G m1 m2 queueBase (qHead - 1) (fun i hi => h i (by omega)),
      h (qHead - 1) (by omega)]

/-! ## 4. Factored step triples for `bfsLabelsCore` -/

private lemma bfsComp_zero_loop {w : ℕ} {p : Program} (n rootBase : ℕ) (memBase : ℕ → ℕ)
    (regs0 : ℕ → ℕ) :
    ∀ (st0 : State), st0.regs 0 = n → st0.regs 4 = rootBase → st0.regs 6 = 0 →
      (∀ r ≤ 4, st0.regs r = regs0 r) → st0.regs 5 = regs0 5 →
      (∀ r ≥ 15, st0.regs r = regs0 r) →
      MemFrame memBase st0.mem rootBase (rootBase + n) →
      rootBase + n < 2 ^ w → n < 2 ^ w → 1 < 2 ^ w → 4 ≤ 2 ^ w →
      Triple w p (fun st => st = st0)
        (.loop (.bin .lt (.reg 6) (.reg 0))
          (.seq (.store (.bin .add (.reg 4) (.reg 6)) (.reg 0))
            (.assign 6 (.bin .add (.reg 6) (.const 1)))))
        (normalPost fun st' =>
          (∀ r ≤ 4, st'.regs r = regs0 r) ∧ st'.regs 5 = regs0 5 ∧
          (∀ r ≥ 15, st'.regs r = regs0 r) ∧
          MemFrame memBase st'.mem rootBase (rootBase + n) ∧
          ∀ x < n, st'.mem (rootBase + x) = n)
        (fun _ => 14 * n + 4) := by
  intro st0 hr0 hr4 hr6 hle4 hr5 hge15 hfr hroot_w hn_w h1_w hw4
  have hL : Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 4 = rootBase ∧ st.regs 6 ≤ n ∧
        (∀ r ≤ 4, st.regs r = regs0 r) ∧ st.regs 5 = regs0 5 ∧
        (∀ r ≥ 15, st.regs r = regs0 r) ∧
        MemFrame memBase st.mem rootBase (rootBase + n) ∧
        ∀ x < st.regs 6, st.mem (rootBase + x) = n)
      (.loop (.bin .lt (.reg 6) (.reg 0))
        (.seq (.store (.bin .add (.reg 4) (.reg 6)) (.reg 0))
          (.assign 6 (.bin .add (.reg 6) (.const 1)))))
      (normalPost fun st' =>
        st'.regs 0 = n ∧ st'.regs 4 = rootBase ∧ st'.regs 6 = n ∧
        (∀ r ≤ 4, st'.regs r = regs0 r) ∧ st'.regs 5 = regs0 5 ∧
        (∀ r ≥ 15, st'.regs r = regs0 r) ∧
        MemFrame memBase st'.mem rootBase (rootBase + n) ∧
        ∀ x < n, st'.mem (rootBase + x) = n)
      (fun st => (3 + 10 + 1) * (n - st.regs 6) + 3 + 1) := by
    refine Triple.loop_const_normal (fun st => n - st.regs 6)
      (fun st => if st.regs 6 < st.regs 0 then 1 else 0) 10
      (fun st hInv => by rcases hInv with ⟨hr0', _⟩; eval_expr)
      (fun st hInv h0 => by
        rcases hInv with ⟨hr0', hr4', h6le', hle4', hr5', hge15', hfr', hall'⟩
        simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, hr0'] at h0
        have h6eq : st.regs 6 = n := by clear hfr' hall' hle4' hge15'; omega
        exact ⟨hr0', hr4', h6eq, hle4', hr5', hge15', hfr', fun x hx => hall' x (h6eq ▸ hx)⟩)
      (fun st hInv hne => by
        rcases hInv with ⟨hr0', hr4', h6le', hle4', hr5', hge15', hfr', hall'⟩
        simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, hr0'] at hne
        have haddr_w : rootBase + st.regs 6 < 2 ^ w := by clear hfr' hall' hle4' hge15'; omega
        have h61_w : st.regs 6 + 1 < 2 ^ w := by clear hfr' hall' hle4' hge15'; omega
        intro s ω hs; rw [hs]; refine runs_start_le ?_
        have he_mem : (Expr.bin .add (.reg 4) (.reg 6)).eval w st = some (rootBase + st.regs 6) := by
          simp [Expr.eval, BinOp.eval, hr4', haddr_w]
        have he_val : (Expr.reg 0).eval w st = some n := by simp [Expr.eval, hr0']
        refine runs_seq_store_le he_mem he_val ?_
        have he6 : (Expr.bin .add (.reg 6) (.const 1)).eval w
            { st with mem := Function.update st.mem (rootBase + st.regs 6) n } = some (st.regs 6 + 1) := by
          simp [Expr.eval, BinOp.eval, h1_w, h61_w]
        refine runs_assign_le he6 ?_ ?_
        · dsimp only [normalPost]
          refine ⟨⟨by simp [hr0'], by simp [hr4'], by simp; clear hfr' hall' hle4' hge15'; omega,
            fun r hr => by rw [Function.update_of_ne (by omega)]; exact hle4' r hr,
            by rw [Function.update_of_ne (by decide : (5 : ℕ) ≠ 6)]; exact hr5',
            fun r hr => by rw [Function.update_of_ne (by omega)]; exact hge15' r hr, ?_, ?_⟩,
            by simp; clear hfr' hall' hle4' hge15'; omega⟩
          · exact memFrame_trans hfr' (memFrame_update (by omega) (by omega))
          · intro x hx
            simp only [Function.update_self] at hx ⊢
            by_cases hxr : x = st.regs 6
            · subst hxr; rw [Function.update_self]
            · rw [Function.update_of_ne (by clear hfr' hall' hle4' hge15'; omega)]
              exact hall' x (by clear hfr' hall' hle4' hge15'; omega)
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega)
  refine hL.conseq (fun st h => ?_) (fun o st h => ?_) (fun st h => ?_)
  · subst h
    refine ⟨hr0, hr4, by omega, hle4, hr5, hge15, hfr, fun x hx => by omega⟩
  · cases o with
    | returned _ => exact False.elim h
    | normal => exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  · subst h; rw [hr6]; simp

private lemma bfsComp_scan_triple {w : ℕ} {p : Program} (st0 : State)
    (n adjVBase rootBase queueBase r k qTail nbr rNbr : ℕ)
    (h0 : st0.regs 0 = n) (h3 : st0.regs 3 = queueBase) (h4 : st0.regs 4 = rootBase)
    (h5 : st0.regs 5 = adjVBase) (h7 : st0.regs 7 = r) (h9 : st0.regs 9 = qTail)
    (h10 : st0.regs 10 = k)
    (hnbr_eq : st0.mem (adjVBase + k) = nbr)
    (hrnbr_eq : st0.mem (rootBase + nbr) = rNbr)
    (h1_w : 1 < 2 ^ w) (_hw4 : 4 ≤ 2 ^ w)
    (hadj_w : adjVBase + k < 2 ^ w) (hroot_w : rootBase + nbr < 2 ^ w)
    (hk1_w : k + 1 < 2 ^ w)
    (hq_w : rNbr = n → queueBase + qTail < 2 ^ w)
    (hqt1_w : rNbr = n → qTail + 1 < 2 ^ w) :
    Triple w p (fun st => st = st0)
      (seqStmts [
        .assign 13 (.load (.bin .add (.reg 5) (.reg 10))),
        .assign 14 (.load (.bin .add (.reg 4) (.reg 13))),
        .cond (.bin .eq (.reg 14) (.reg 0))
          (seqStmts [
            .store (.bin .add (.reg 4) (.reg 13)) (.reg 7),
            .store (.bin .add (.reg 3) (.reg 9)) (.reg 13),
            .assign 9 (.bin .add (.reg 9) (.const 1))])
          .nop,
        .assign 10 (.bin .add (.reg 10) (.const 1))])
      (normalPost fun st' =>
        (rNbr = n →
          (∀ reg ≤ 8, st'.regs reg = st0.regs reg) ∧
          st'.regs 9 = qTail + 1 ∧ st'.regs 10 = k + 1 ∧
          (∀ reg, 11 ≤ reg → reg ≠ 13 → reg ≠ 14 → st'.regs reg = st0.regs reg) ∧
          st'.mem = Function.update (Function.update st0.mem (rootBase + nbr) r) (queueBase + qTail) nbr) ∧
        (rNbr ≠ n →
          (∀ reg ≤ 9, st'.regs reg = st0.regs reg) ∧
          st'.regs 10 = k + 1 ∧
          (∀ reg, 11 ≤ reg → reg ≠ 13 → reg ≠ 14 → st'.regs reg = st0.regs reg) ∧
          st'.mem = st0.mem))
      (fun _ => 37) := by
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  have he13 : (Expr.load (.bin .add (.reg 5) (.reg 10))).eval w st = some nbr := by
    simp [Expr.eval, BinOp.eval, h5, h10, hadj_w, hnbr_eq]
  refine runs_seq_assign_le he13 ?_
  let st1 : State := { st with regs := Function.update st.regs 13 nbr }
  have he14 : (Expr.load (.bin .add (.reg 4) (.reg 13))).eval w st1 = some rNbr := by
    simp [Expr.eval, BinOp.eval, st1, h4, hroot_w, hrnbr_eq]
  refine runs_seq_assign_le he14 ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 14 rNbr }
  have h1_eq : (if rNbr = n then 1 else 0) < 2 ^ w := by split_ifs <;> linarith only [h1_w]
  have hec : (Expr.bin .eq (.reg 14) (.reg 0)).eval w st2 = some (if rNbr = n then 1 else 0) := by
    simp [Expr.eval, BinOp.eval, st2, st1, h0, h1_eq]
  have hr_le8 : ∀ reg ≤ 8, st2.regs reg = st.regs reg := fun reg hreg => by
    simp [st2, st1, Function.update_of_ne (by omega : reg ≠ 14),
      Function.update_of_ne (by omega : reg ≠ 13)]
  have hcond_triple : Triple w p (fun s => s = st2)
      (.cond (.bin .eq (.reg 14) (.reg 0))
        (seqStmts [
          .store (.bin .add (.reg 4) (.reg 13)) (.reg 7),
          .store (.bin .add (.reg 3) (.reg 9)) (.reg 13),
          .assign 9 (.bin .add (.reg 9) (.const 1))])
        .nop)
      (normalPost fun st3 =>
        (rNbr = n →
          (∀ reg ≤ 8, st3.regs reg = st.regs reg) ∧
          st3.regs 9 = qTail + 1 ∧ st3.regs 10 = k ∧
          (∀ reg, 11 ≤ reg → reg ≠ 13 → reg ≠ 14 → st3.regs reg = st.regs reg) ∧
          st3.mem = Function.update (Function.update st.mem (rootBase + nbr) r) (queueBase + qTail) nbr) ∧
        (rNbr ≠ n →
          (∀ reg ≤ 9, st3.regs reg = st.regs reg) ∧
          st3.regs 10 = k ∧
          (∀ reg, 11 ≤ reg → reg ≠ 13 → reg ≠ 14 → st3.regs reg = st.regs reg) ∧
          st3.mem = st.mem))
      (fun _ => 20) := by
    intro s ω' hs; subst hs; refine runs_start_le ?_
    refine runs_cond_le hec ?_ ?_
    · intro hne
      have hreq : rNbr = n := by
        simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
        exact hne
      have hes1_a : (Expr.bin .add (.reg 4) (.reg 13)).eval w st2 = some (rootBase + nbr) := by
        simp [Expr.eval, BinOp.eval, st2, st1, h4, hroot_w]
      have hes1_v : (Expr.reg 7).eval w st2 = some r := by
        rw [Expr.eval, hr_le8 7 (by omega), h7]
      refine runs_seq_store_le hes1_a hes1_v ?_
      have hes2_a : (Expr.bin .add (.reg 3) (.reg 9)).eval w
          { st2 with mem := Function.update st2.mem (rootBase + nbr) r } = some (queueBase + qTail) := by
        simp [Expr.eval, BinOp.eval, st2, st1, h3, h9, hq_w hreq]
      have hes2_v : (Expr.reg 13).eval w
          { st2 with mem := Function.update st2.mem (rootBase + nbr) r } = some nbr := by
        simp [Expr.eval, st2, st1]
      refine runs_seq_store_le hes2_a hes2_v ?_
      let mem2 : ℕ → ℕ := Function.update (Function.update st2.mem (rootBase + nbr) r) (queueBase + qTail) nbr
      have hea9 : (Expr.bin .add (.reg 9) (.const 1)).eval w { st2 with mem := mem2 } = some (qTail + 1) := by
        simp [Expr.eval, BinOp.eval, st2, st1, h9, h1_w, hqt1_w hreq]
      refine runs_assign_le hea9 ?_ ?_
      · dsimp only [normalPost]
        refine ⟨fun _ => ⟨fun reg hreg => by
            rw [Function.update_of_ne (by omega : reg ≠ 9)]; exact hr_le8 reg hreg,
          by simp,
          by rw [Function.update_of_ne (by decide : (10 : ℕ) ≠ 9)]; simp [st2, st1, h10],
          fun reg h1 h2 h3' => by
            rw [Function.update_of_ne (by omega : reg ≠ 9)]
            simp [st2, st1, Function.update_of_ne h3', Function.update_of_ne h2],
          rfl⟩, fun hneg => False.elim (hneg hreq)⟩
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega
    · intro h0c
      have hrne : rNbr ≠ n := by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0c
        exact h0c
      refine runs_nop_le ?_ ?_
      · dsimp only [normalPost]
        refine ⟨fun h => False.elim (hrne h), fun _ => ⟨fun reg hreg => ?_, ?_, ?_, rfl⟩⟩
        · simp [st2, st1, Function.update_of_ne (by omega : reg ≠ 14),
            Function.update_of_ne (by omega : reg ≠ 13)]
        · simp [st2, st1, h10]
        · intro reg h1 h2 h3'
          simp [st2, st1, Function.update_of_ne h3', Function.update_of_ne h2]
      · simp only [Expr.size_reg, Expr.size_bin]; omega
  refine runs_seq_triple_le hcond_triple rfl (fun st3 h3p => ?_)
  rcases h3p with ⟨hpush, hskip⟩
  have hk_3 : st3.regs 10 = k := by
    by_cases h : rNbr = n
    · exact (hpush h).2.2.1
    · exact (hskip h).2.1
  have hea10 : (Expr.bin .add (.reg 10) (.const 1)).eval w st3 = some (k + 1) := by
    simp [Expr.eval, BinOp.eval, hk_3, h1_w, hk1_w]
  refine runs_assign_le hea10 ?_ ?_
  · dsimp only [normalPost]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨hle8, h9', _, hhi, hmem'⟩ := hpush h
      refine ⟨fun reg hr => by rw [Function.update_of_ne (by omega : reg ≠ 10), hle8 reg hr],
        by rw [Function.update_of_ne (by decide : (9 : ℕ) ≠ 10), h9'],
        by simp,
        fun reg h1 h2 h3' => by rw [Function.update_of_ne (by omega : reg ≠ 10), hhi reg h1 h2 h3'],
        hmem'⟩
    · obtain ⟨hle9, _, hhi, hmem'⟩ := hskip h
      refine ⟨fun reg hr => by rw [Function.update_of_ne (by omega : reg ≠ 10), hle9 reg hr],
        by simp,
        fun reg h1 h2 h3' => by rw [Function.update_of_ne (by omega : reg ≠ 10), hhi reg h1 h2 h3'],
        hmem'⟩
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma bfsComp_pop_triple {w : ℕ} {p : Program} (st0 : State)
    (csrAddr queueBase qHead nxt off0 off1 : ℕ)
    (h2 : st0.regs 2 = csrAddr) (h3 : st0.regs 3 = queueBase) (h8 : st0.regs 8 = qHead)
    (hq_eq : st0.mem (queueBase + qHead) = nxt)
    (hoff0_eq : st0.mem (csrAddr + nxt) = off0)
    (hoff1_eq : st0.mem (csrAddr + nxt + 1) = off1)
    (hq_w : queueBase + qHead < 2 ^ w) (hq1_w : qHead + 1 < 2 ^ w)
    (hc0_w : csrAddr + nxt < 2 ^ w) (hc1_w : csrAddr + nxt + 1 < 2 ^ w) (h1_w : 1 < 2 ^ w) :
    Triple w p (fun st => st = st0)
      (seqStmts [
        .assign 12 (.load (.bin .add (.reg 3) (.reg 8))),
        .assign 8 (.bin .add (.reg 8) (.const 1)),
        .assign 10 (.load (.bin .add (.reg 2) (.reg 12))),
        .assign 11 (.load (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1)))])
      (normalPost fun st' =>
        (∀ reg ≤ 7, st'.regs reg = st0.regs reg) ∧
        st'.regs 8 = qHead + 1 ∧ st'.regs 9 = st0.regs 9 ∧
        st'.regs 10 = off0 ∧ st'.regs 11 = off1 ∧ st'.regs 12 = nxt ∧
        (∀ reg ≥ 13, st'.regs reg = st0.regs reg) ∧ st'.mem = st0.mem)
      (fun _ => 25) := by
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  have he12 : (Expr.load (.bin .add (.reg 3) (.reg 8))).eval w st = some nxt := by
    simp [Expr.eval, BinOp.eval, h3, h8, hq_w, hq_eq]
  refine runs_seq_assign_le he12 ?_
  let st1 : State := { st with regs := Function.update st.regs 12 nxt }
  have he8 : (Expr.bin .add (.reg 8) (.const 1)).eval w st1 = some (qHead + 1) := by
    simp [Expr.eval, BinOp.eval, st1, h8, h1_w, hq1_w]
  refine runs_seq_assign_le he8 ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 8 (qHead + 1) }
  have he10 : (Expr.load (.bin .add (.reg 2) (.reg 12))).eval w st2 = some off0 := by
    simp [Expr.eval, BinOp.eval, st2, st1, h2, hc0_w, hoff0_eq]
  refine runs_seq_assign_le he10 ?_
  let st3 : State := { st2 with regs := Function.update st2.regs 10 off0 }
  have he11 : (Expr.load (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1))).eval w st3 = some off1 := by
    simp [Expr.eval, BinOp.eval, st3, st2, st1, h2, h1_w, hc0_w, hc1_w, hoff1_eq]
  refine runs_assign_le he11 ?_ ?_
  · dsimp only [normalPost]
    refine ⟨fun reg hreg => by
        simp [Function.update_of_ne (by omega : reg ≠ 11),
          Function.update_of_ne (by omega : reg ≠ 10), Function.update_of_ne (by omega : reg ≠ 8),
          Function.update_of_ne (by omega : reg ≠ 12)],
      by simp, by simp, by simp, by simp, by simp,
      fun reg hreg => by
        simp [Function.update_of_ne (by omega : reg ≠ 11),
          Function.update_of_ne (by omega : reg ≠ 10), Function.update_of_ne (by omega : reg ≠ 8),
          Function.update_of_ne (by omega : reg ≠ 12)],
      rfl⟩
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma bfsComp_root_triple {w : ℕ} {p : Program} (st0 : State)
    (n queueBase rootBase r qTail rr : ℕ)
    (h0 : st0.regs 0 = n) (h3 : st0.regs 3 = queueBase) (h4 : st0.regs 4 = rootBase)
    (h7 : st0.regs 7 = r) (h9 : st0.regs 9 = qTail)
    (hrr_eq : st0.mem (rootBase + r) = rr)
    (h1_w : 1 < 2 ^ w) (_hw4 : 4 ≤ 2 ^ w)
    (hroot_w : rootBase + r < 2 ^ w)
    (hq_w : rr = n → queueBase + qTail < 2 ^ w)
    (hqt1_w : rr = n → qTail + 1 < 2 ^ w)
    (hr1_w : rr ≠ n → r + 1 < 2 ^ w) :
    Triple w p (fun st => st = st0)
      (.seq
        (.assign 14 (.load (.bin .add (.reg 4) (.reg 7))))
        (.cond (.bin .eq (.reg 14) (.reg 0))
          (seqStmts [
            .store (.bin .add (.reg 4) (.reg 7)) (.reg 7),
            .store (.bin .add (.reg 3) (.reg 9)) (.reg 7),
            .assign 9 (.bin .add (.reg 9) (.const 1))])
          (.assign 7 (.bin .add (.reg 7) (.const 1)))))
      (normalPost fun st' =>
        (rr = n →
          (∀ reg ≤ 8, st'.regs reg = st0.regs reg) ∧
          st'.regs 9 = qTail + 1 ∧
          (∀ reg, 10 ≤ reg → reg ≠ 14 → st'.regs reg = st0.regs reg) ∧
          st'.mem = Function.update (Function.update st0.mem (rootBase + r) r) (queueBase + qTail) r) ∧
        (rr ≠ n →
          (∀ reg ≤ 6, st'.regs reg = st0.regs reg) ∧
          st'.regs 7 = r + 1 ∧
          (∀ reg, 8 ≤ reg → reg ≠ 14 → st'.regs reg = st0.regs reg) ∧
          st'.mem = st0.mem))
      (fun _ => 30) := by
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  have he14 : (Expr.load (.bin .add (.reg 4) (.reg 7))).eval w st = some rr := by
    simp [Expr.eval, BinOp.eval, h4, h7, hroot_w, hrr_eq]
  refine runs_seq_assign_le he14 ?_
  let st1 : State := { st with regs := Function.update st.regs 14 rr }
  have h0_w : (if rr = n then 1 else 0) < 2 ^ w := by split_ifs <;> linarith only [h1_w]
  have hec : (Expr.bin .eq (.reg 14) (.reg 0)).eval w st1 = some (if rr = n then 1 else 0) := by
    simp [Expr.eval, BinOp.eval, st1, h0, h0_w]
  refine runs_cond_le hec ?_ ?_
  · intro hne
    have hreq : rr = n := by
      simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
      exact hne
    have hes1_a : (Expr.bin .add (.reg 4) (.reg 7)).eval w st1 = some (rootBase + r) := by
      simp [Expr.eval, BinOp.eval, st1, h4, h7, hroot_w]
    have hes1_v : (Expr.reg 7).eval w st1 = some r := by simp [Expr.eval, st1, h7]
    refine runs_seq_store_le hes1_a hes1_v ?_
    have hes2_a : (Expr.bin .add (.reg 3) (.reg 9)).eval w
        { st1 with mem := Function.update st1.mem (rootBase + r) r } = some (queueBase + qTail) := by
      simp [Expr.eval, BinOp.eval, st1, h3, h9, hq_w hreq]
    have hes2_v : (Expr.reg 7).eval w
        { st1 with mem := Function.update st1.mem (rootBase + r) r } = some r := by
      simp [Expr.eval, st1, h7]
    refine runs_seq_store_le hes2_a hes2_v ?_
    have hea9 : (Expr.bin .add (.reg 9) (.const 1)).eval w
        { st1 with mem := Function.update (Function.update st1.mem (rootBase + r) r) (queueBase + qTail) r } =
        some (qTail + 1) := by
      simp [Expr.eval, BinOp.eval, st1, h9, h1_w, hqt1_w hreq]
    refine runs_assign_le hea9 ?_ ?_
    · dsimp only [normalPost]
      refine ⟨fun _ => ⟨fun reg hreg => by
          rw [Function.update_of_ne (by omega : reg ≠ 9)]
          simp [Function.update_of_ne (by omega : reg ≠ 14)],
        by simp,
        fun reg h1 h2 => by
          rw [Function.update_of_ne (by omega : reg ≠ 9)]
          simp [Function.update_of_ne h2],
        rfl⟩, fun hneg => False.elim (hneg hreq)⟩
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  · intro h0c
    have hrne : rr ≠ n := by
      simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0c
      exact h0c
    have hea7 : (Expr.bin .add (.reg 7) (.const 1)).eval w st1 = some (r + 1) := by
      simp [Expr.eval, BinOp.eval, st1, h7, h1_w, hr1_w hrne]
    refine runs_assign_le hea7 ?_ ?_
    · dsimp only [normalPost]
      refine ⟨fun h => False.elim (hrne h), fun _ => ⟨fun reg hreg => by
          rw [Function.update_of_ne (by omega : reg ≠ 7)]
          simp [Function.update_of_ne (by omega : reg ≠ 14)],
        by simp,
        fun reg h1 h2 => by
          rw [Function.update_of_ne (by omega : reg ≠ 7)]
          simp [Function.update_of_ne h2],
        rfl⟩⟩
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

/-! ## 5. BFS Labels Loop Invariant & Core Theorem -/

private structure BfsCompInv (n m csrAddr queueBase rootBase adjVBase : ℕ)
    (G : Cited.Graph) (memBase : ℕ → ℕ) (regs0 : ℕ → ℕ) (st : State) : Prop where
  r0 : st.regs 0 = n
  r1 : st.regs 1 = m
  r2 : st.regs 2 = csrAddr
  r3 : st.regs 3 = queueBase
  r4 : st.regs 4 = rootBase
  r5 : st.regs 5 = adjVBase
  rhi : ∀ r ≥ 15, st.regs r = regs0 r
  r_le : st.regs 7 ≤ n
  qh_le : st.regs 8 ≤ st.regs 9
  qt_le : st.regs 9 ≤ n
  k_le : st.regs 10 ≤ st.regs 11
  kend_le : st.regs 11 ≤ 2 * m
  fr2 : ∀ addr, (addr < queueBase ∨ queueBase + n ≤ addr) → (addr < rootBase ∨ rootBase + n ≤ addr) →
    st.mem addr = memBase addr
  q_lt : ∀ i < st.regs 9, st.mem (queueBase + i) < n ∧ st.mem (rootBase + st.mem (queueBase + i)) < n
  q_inj : ∀ i < st.regs 9, ∀ j < st.regs 9,
    st.mem (queueBase + i) = st.mem (queueBase + j) → i = j
  q_cov : ∀ x < n, st.mem (rootBase + x) ≠ n → ∃ i < st.regs 9, st.mem (queueBase + i) = x
  r_pref : ∀ x < st.regs 7, st.mem (rootBase + x) < n
  root_le_r : ∀ x < n, st.mem (rootBase + x) = n ∨ st.mem (rootBase + x) ≤ st.regs 7
  root_reach : ∀ x < n, st.mem (rootBase + x) ≠ n →
    ∃ P, IsPathAlong G.edges x (st.mem (rootBase + x)) P
  csr_k : (st.regs 8 = 0 ∧ st.regs 10 = 0 ∧ st.regs 11 = 0) ∨
    (0 < st.regs 8 ∧ st.regs 12 = st.mem (queueBase + (st.regs 8 - 1)) ∧
      st.regs 12 < n ∧ csrOff G (st.regs 12) ≤ st.regs 10 ∧
      st.regs 11 = csrOff G (st.regs 12 + 1))
  active_lt : (st.regs 10 < st.regs 11 ∨ st.regs 8 < st.regs 9) → st.regs 7 < n
  cur_r : ∀ i, (if st.regs 10 < st.regs 11 then st.regs 8 - 1 else st.regs 8) ≤ i →
    i < st.regs 9 → st.mem (rootBase + st.mem (queueBase + i)) = st.regs 7
  old_fin : ∀ x < n, st.mem (rootBase + x) < st.regs 7 →
    ∃ i < (if st.regs 10 < st.regs 11 then st.regs 8 - 1 else st.regs 8), st.mem (queueBase + i) = x
  scan_prev : ∀ i, i < (if st.regs 10 < st.regs 11 then st.regs 8 - 1 else st.regs 8) →
    ∀ (t : ℕ) (ht : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length),
      st.mem (rootBase + ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht).2.2) =
        st.mem (rootBase + st.mem (queueBase + i))
  scan_cur : st.regs 10 < st.regs 11 →
    ∀ (t : ℕ) (ht : t < (csrIncAux (st.regs 12) 0 G.edges).length),
      csrOff G (st.regs 12) + t < st.regs 10 →
        st.mem (rootBase + ((csrIncAux (st.regs 12) 0 G.edges)[t]'ht).2.2) =
          st.mem (rootBase + st.regs 12)

private def compMeas (n m _csrAddr queueBase : ℕ) (G : Cited.Graph) (st : State) : ℕ :=
  (n - st.regs 7) + (n - st.regs 8) + (n - st.regs 9) +
    (2 * m - compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10))

private lemma bfsComp_main_loop {w : ℕ} {p : Program}
    (n m csrAddr queueBase rootBase adjVBase : ℕ)
    (G : Cited.Graph) (memBase : ℕ → ℕ) (regs0 : ℕ → ℕ)
    (hn : G.n = n) (hm : G.m = m) (hval : G.IsValid)
    (hcsr : HasCsrAt memBase csrAddr G)
    (hdj_cq : csrAddr + 2 * n + 1 + 4 * m ≤ queueBase ∨ queueBase + n ≤ csrAddr)
    (hdj_cr : csrAddr + 2 * n + 1 + 4 * m ≤ rootBase ∨ rootBase + n ≤ csrAddr)
    (hdj_qr : queueBase + n ≤ rootBase ∨ rootBase + n ≤ queueBase)
    (hcsr_w : csrAddr + 2 * n + 1 + 4 * m < 2 ^ w)
    (hq_w : queueBase + n < 2 ^ w) (hroot_w : rootBase + n < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hadj : adjVBase = csrAddr + 2 * n + 1) :
    Triple w p (BfsCompInv n m csrAddr queueBase rootBase adjVBase G memBase regs0)
      (.loop (.bin .lt (.reg 7) (.reg 0))
        (.cond (.bin .lt (.reg 10) (.reg 11))
          (seqStmts [
            .assign 13 (.load (.bin .add (.reg 5) (.reg 10))),
            .assign 14 (.load (.bin .add (.reg 4) (.reg 13))),
            .cond (.bin .eq (.reg 14) (.reg 0))
              (seqStmts [
                .store (.bin .add (.reg 4) (.reg 13)) (.reg 7),
                .store (.bin .add (.reg 3) (.reg 9)) (.reg 13),
                .assign 9 (.bin .add (.reg 9) (.const 1))])
              .nop,
            .assign 10 (.bin .add (.reg 10) (.const 1))])
          (.cond (.bin .lt (.reg 8) (.reg 9))
            (seqStmts [
              .assign 12 (.load (.bin .add (.reg 3) (.reg 8))),
              .assign 8 (.bin .add (.reg 8) (.const 1)),
              .assign 10 (.load (.bin .add (.reg 2) (.reg 12))),
              .assign 11 (.load (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1)))])
            (.seq
              (.assign 14 (.load (.bin .add (.reg 4) (.reg 7))))
              (.cond (.bin .eq (.reg 14) (.reg 0))
                (seqStmts [
                  .store (.bin .add (.reg 4) (.reg 7)) (.reg 7),
                  .store (.bin .add (.reg 3) (.reg 9)) (.reg 7),
                  .assign 9 (.bin .add (.reg 9) (.const 1))])
                (.assign 7 (.bin .add (.reg 7) (.const 1))))))))
      (normalPost fun st' =>
        BfsCompInv n m csrAddr queueBase rootBase adjVBase G memBase regs0 st' ∧
          st'.regs 7 = n)
      (fun st => (3 + 42 + 1) * compMeas n m csrAddr queueBase G st + 3 + 1) := by
  have h1_w : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 4) hw4
  have hn_w : n < 2 ^ w := by linarith only [hroot_w]
  refine Triple.loop_const_normal (compMeas n m csrAddr queueBase G)
    (fun st => if st.regs 7 < st.regs 0 then 1 else 0) 42
    (fun st hInv => by
      have hr0 := hInv.r0
      eval_expr)
    (fun st hInv h0 => by
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, hInv.r0] at h0
      have hr_le := hInv.r_le
      exact ⟨hInv, by clear hInv; omega⟩)
    (fun st hInv hne => by
      have hr_le := hInv.r_le
      have hqh_le := hInv.qh_le
      have hqt_le := hInv.qt_le
      have hk_le := hInv.k_le
      have hkend_le := hInv.kend_le
      simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, hInv.r0] at hne
      have hcsr_st : HasCsrAt st.mem csrAddr G := by
        constructor
        · intro u hu
          rw [hInv.fr2 (csrAddr + u)
            (by rcases hdj_cq with h | h <;> [left; right] <;> (clear hInv; omega))
            (by rcases hdj_cr with h | h <;> [left; right] <;> (clear hInv; omega))]
          exact hcsr.1 u hu
        · intro u hu t ht
          have ht' : t < csrOff G (u + 1) - csrOff G u := by
            have := csrOff_succ G u; clear hInv; omega
          have h1e := hcsr.2 u hu t ht
          have hc_le : csrOff G u + t < 2 * m := by
            have := csrOff_le_two_mul_m G (u + 1); clear hInv; omega
          refine ⟨?_, ?_⟩
          · rw [hInv.fr2 _
              (by rcases hdj_cq with h | h <;> [left; right] <;> (clear hInv; omega))
              (by rcases hdj_cr with h | h <;> [left; right] <;> (clear hInv; omega))]
            exact h1e.1
          · rw [hInv.fr2 _
              (by rcases hdj_cq with h | h <;> [left; right] <;> (clear hInv; omega))
              (by rcases hdj_cr with h | h <;> [left; right] <;> (clear hInv; omega))]
            exact h1e.2
      have hk_w : st.regs 10 < 2 ^ w := by linarith only [hk_le, hkend_le, hcsr_w]
      have hqt_w : st.regs 9 < 2 ^ w := by linarith only [hqt_le, hn_w]
      have hec_k_w : (if st.regs 10 < st.regs 11 then 1 else 0) < 2 ^ w := by split_ifs <;> linarith only [h1_w]
      have hec_k : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st =
          some (if st.regs 10 < st.regs 11 then 1 else 0) := by
        simp [Expr.eval, BinOp.eval, hec_k_w]
      intro s ω hs; rw [hs]
      by_cases hklt : st.regs 10 < st.regs 11
      · -- Branch 1: scan neighbor k < kEnd
        rcases hInv.csr_k with ⟨_, h10_0, h11_0⟩ | ⟨hqh_pos, h12_q, hcur_n, hoff_le, hkend_eq⟩
        · linarith only [hklt, h10_0, h11_0]
        have hqh_n : st.regs 8 ≤ n := le_trans hInv.qh_le hInv.qt_le
        have hcur_eq : st.regs 12 = st.mem (queueBase + (st.regs 8 - 1)) := h12_q
        have ht_def : st.regs 10 - csrOff G (st.regs 12) < (csrIncAux (st.regs 12) 0 G.edges).length := by
          have hs := csrOff_succ G (st.regs 12)
          clear hInv; omega
        obtain ⟨t, ht_eq⟩ : ∃ v, v = st.regs 10 - csrOff G (st.regs 12) := ⟨_, rfl⟩
        have ht_len : t < (csrIncAux (st.regs 12) 0 G.edges).length := ht_eq ▸ ht_def
        have hk_eq : st.regs 10 = csrOff G (st.regs 12) + t := by
          clear hInv; omega
        obtain ⟨q_entry, hq_def⟩ : ∃ q, q = (csrIncAux (st.regs 12) 0 G.edges)[t]'ht_len := ⟨_, rfl⟩
        have hq_em := csrIncAux_edgeMatches hval ht_len
        rw [← hq_def] at hq_em
        have hadj_v_mem : st.mem (adjVBase + st.regs 10) = q_entry.2.2 := by
          have ha_eq : adjVBase + st.regs 10 = csrAddr + 2 * G.n + 1 + csrOff G (st.regs 12) + t := by
            rw [hadj, hn, hk_eq]; clear hInv; omega
          rw [ha_eq, hq_def]
          exact (hcsr_st.2 (st.regs 12) (hn.symm ▸ hcur_n) t ht_len).1
        have hnbr_lt : q_entry.2.2 < n := by rw [← hn]; exact hq_em.2.1
        have hadj_k_w : adjVBase + st.regs 10 < 2 ^ w := by
          have : st.regs 10 < 2 * m := lt_of_lt_of_le hklt hInv.kend_le
          linarith only [hadj, this, hcsr_w]
        have hroot_nbr_w : rootBase + q_entry.2.2 < 2 ^ w := by linarith only [hnbr_lt, hroot_w]
        have hk1_w : st.regs 10 + 1 < 2 ^ w := by
          have : st.regs 10 < 2 * m := lt_of_lt_of_le hklt hInv.kend_le
          linarith only [this, hcsr_w]
        have hdone_cur : compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10) =
            compDegSum G st.mem queueBase (st.regs 8 - 1) + t := by
          dsimp only [compDoneEdges]
          have h8ne : st.regs 8 ≠ 0 := by clear hInv; omega
          simp only [h8ne, ↓reduceIte, ← hcur_eq, ← ht_eq]
        have hdone_lt : compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10) < 2 * m := by
          have hsub : st.regs 10 + 1 ≤ csrOff G (st.regs 12 + 1) := by clear hInv; omega
          have := compDoneEdges_le_two_mul_m G st.mem queueBase (st.regs 8) (st.regs 10 + 1)
            (fun i hi => hn ▸ (hInv.q_lt i (lt_of_lt_of_le hi hqh_le)).1)
            (fun i hi j hj => hInv.q_inj i (lt_of_lt_of_le hi hqh_le) j (lt_of_lt_of_le hj hqh_le))
            (fun _ => by rw [← hcur_eq]; exact hsub)
          have hdone1 : compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10 + 1) =
              compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10) + 1 := by
            dsimp only [compDoneEdges]
            have h8ne : st.regs 8 ≠ 0 := by clear hInv; omega
            simp only [h8ne, ↓reduceIte, ← hcur_eq]
            clear hInv; omega
          rw [← hm]; clear hInv; omega
        have hcur_root_r : st.mem (rootBase + st.regs 12) = st.regs 7 := by
          have hif : (if st.regs 10 < st.regs 11 then st.regs 8 - 1 else st.regs 8) = st.regs 8 - 1 := by
            simp only [hklt, ↓reduceIte]
          have hqm1 : st.regs 8 - 1 < st.regs 9 := by clear hInv; omega
          have := hInv.cur_r (st.regs 8 - 1) (by rw [hif]) hqm1
          rwa [← hcur_eq] at this
        have hqt_lt_n_of_push : st.mem (rootBase + q_entry.2.2) = n → st.regs 9 < n := by
          intro hrn
          by_contra hge
          have hqtn : st.regs 9 = n := by clear hInv; omega
          -- If qTail = n, q_inj gives all n vertices visited, contradiction!
          have hinj : ∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n,
              st.mem (queueBase + a) = st.mem (queueBase + b) → a = b := fun a ha b hb heq =>
            hInv.q_inj a (by rw [hqtn]; exact Finset.mem_range.mp ha)
              b (by rw [hqtn]; exact Finset.mem_range.mp hb) heq
          have himg : (Finset.range n).image (fun i => st.mem (queueBase + i)) ⊆ Finset.range n := by
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
            exact Finset.mem_range.mpr (hInv.q_lt i (by rw [hqtn]; exact Finset.mem_range.mp hi)).1
          have hcard : ((Finset.range n).image (fun i => st.mem (queueBase + i))).card = n := by
            rw [Finset.card_image_of_injOn (fun a ha b hb heq => hinj a ha b hb heq), Finset.card_range]
          have heqset := Finset.eq_of_subset_of_card_le himg (by rw [hcard, Finset.card_range])
          have hmem_nbr : q_entry.2.2 ∈ (Finset.range n).image (fun i => st.mem (queueBase + i)) := by
            rw [heqset]; exact Finset.mem_range.mpr hnbr_lt
          rcases Finset.mem_image.mp hmem_nbr with ⟨i, hi, hi_eq⟩
          have hi_lt : i < st.regs 9 := by rw [hqtn]; exact Finset.mem_range.mp hi
          have := (hInv.q_lt i hi_lt).2
          rw [hi_eq, hrn] at this
          omega
        refine runs_start_le ?_
        refine runs_cond_le hec_k ?_ ?_
        · intro _
          refine runs_triple_le
            (bfsComp_scan_triple st n adjVBase rootBase queueBase (st.regs 7) (st.regs 10) (st.regs 9)
              q_entry.2.2 (st.mem (rootBase + q_entry.2.2))
              hInv.r0 hInv.r3 hInv.r4 hInv.r5 rfl rfl rfl hadj_v_mem rfl h1_w hw4 hadj_k_w
              hroot_nbr_w hk1_w (fun h => by linarith only [hqt_lt_n_of_push h, hq_w])
              (fun h => by linarith only [hqt_lt_n_of_push h, hq_w]))
            rfl ?_ (by simp only [Expr.size_reg, Expr.size_bin]; omega)
          intro o st' hpost
          cases o with
          | returned _ => exact False.elim hpost
          | normal =>
            rcases hpost with ⟨hpush, hskip⟩
            by_cases hnew : st.mem (rootBase + q_entry.2.2) = n
            · have hqn : st.regs 9 < n := hqt_lt_n_of_push hnew
              obtain ⟨hle8, h9', h10', h11', hmem'⟩ := hpush hnew
              have hqt1_n : st'.regs 9 ≤ n := by rw [h9']; exact hqn
              have hfin_eq : (if st'.regs 10 < st'.regs 11 then st'.regs 8 - 1 else st'.regs 8) =
                  if st'.regs 10 < st'.regs 11 then st.regs 8 - 1 else st.regs 8 := by
                rw [hle8 8 le_rfl]
              have hr_unch : st'.regs 7 = st.regs 7 := hle8 7 (by omega)
              have h12_unch : st'.regs 12 = st.regs 12 := h11' 12 (by decide) (by decide) (by decide)
              have h11_unch : st'.regs 11 = st.regs 11 := h11' 11 le_rfl (by decide) (by decide)
              have hnbr_ne_q : ∀ j < st.regs 9, st.mem (queueBase + j) ≠ q_entry.2.2 := fun j hj heq => by
                have := (hInv.q_lt j hj).2
                rw [heq, hnew] at this
                exact absurd this (Nat.lt_irrefl _)
              have hmem_other_q : ∀ j < st.regs 9,
                  st'.mem (queueBase + j) = st.mem (queueBase + j) := fun j hj => by
                rw [hmem', Function.update_of_ne (by clear hInv; omega),
                  Function.update_of_ne (by rcases hdj_qr with h | h <;> (clear hInv; omega))]
              have hmem_other_r : ∀ y, y ≠ q_entry.2.2 → y < n →
                  st'.mem (rootBase + y) = st.mem (rootBase + y) := fun y hne_y hy_n => by
                rw [hmem', Function.update_of_ne (by rcases hdj_qr with h | h <;> (clear hInv; omega)),
                  Function.update_of_ne (by clear hInv; omega)]
              have hmem_nbr' : st'.mem (rootBase + q_entry.2.2) = st.regs 7 := by
                rw [hmem', Function.update_of_ne (by rcases hdj_qr with h | h <;> (clear hInv; omega)),
                  Function.update_self]
              have hmem_qtail' : st'.mem (queueBase + st.regs 9) = q_entry.2.2 := by
                rw [hmem', Function.update_self]
              have hreach_cur := hInv.root_reach (st.regs 12) hcur_n (by rw [hcur_root_r]; omega)
              have hreach_nbr : ∃ P, IsPathAlong G.edges q_entry.2.2 (st.regs 7) P := by
                rcases hreach_cur with ⟨P, hP⟩
                rw [hcur_root_r] at hP
                have hemem : G.edges.getD q_entry.1 (0, 0) ∈ G.edges := by
                  have hlt : q_entry.1 < G.edges.length := by simpa [Cited.Graph.m] using hq_em.1
                  have heget : G.edges.getD q_entry.1 (0, 0) = G.edges[q_entry.1]'hlt := by
                    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
                  rw [heget]; exact List.getElem_mem hlt
                have hedge : (q_entry.2.2, st.regs 12) ∈ G.edges ∨ (st.regs 12, q_entry.2.2) ∈ G.edges := by
                  rcases hq_em.2.2.2 with h | h
                  · right
                    exact (Prod.ext h.1 h.2 : G.edges.getD q_entry.1 (0, 0) = (st.regs 12, q_entry.2.2)) ▸ hemem
                  · left
                    exact (Prod.ext h.2 h.1 : G.edges.getD q_entry.1 (0, 0) = (q_entry.2.2, st.regs 12)) ▸ hemem
                exact ⟨q_entry.2.2 :: P, isPathAlong_cons hedge hP⟩
              have hscan_cur' : ∀ (t0 : ℕ) (ht0 : t0 < (csrIncAux (st.regs 12) 0 G.edges).length),
                  csrOff G (st.regs 12) + t0 < st.regs 10 + 1 →
                    st'.mem (rootBase + ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0).2.2) =
                      st'.mem (rootBase + st.regs 12) := by
                intro t0 ht0 hlt0
                have hcur_eq' : st'.mem (rootBase + st.regs 12) = st.regs 7 := by
                  rw [hmem_other_r _ (Ne.symm hq_em.2.2.1) hcur_n, hcur_root_r]
                rw [hcur_eq']
                by_cases ht_last : t0 = t
                · subst ht_last
                  have hz_eq : ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0).2.2 = q_entry.2.2 := by
                    rw [hq_def]
                  rw [hz_eq, hmem_nbr']
                · have hlt_old : csrOff G (st.regs 12) + t0 < st.regs 10 := by
                    clear hInv; omega
                  have hold := hInv.scan_cur hklt t0 ht0 hlt_old
                  rw [hcur_root_r] at hold
                  have hz_n : ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0).2.2 < n := by
                    rw [← hn]; exact (csrIncAux_getElem_lt hval ht0).2.1
                  by_cases hz_nbr : ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0).2.2 = q_entry.2.2
                  · rw [hz_nbr, hmem_nbr']
                  · rw [hmem_other_r _ hz_nbr hz_n, hold]
              refine ⟨⟨by rw [hle8 0 (by omega), hInv.r0], by rw [hle8 1 (by omega), hInv.r1],
                  by rw [hle8 2 (by omega), hInv.r2], by rw [hle8 3 (by omega), hInv.r3],
                  by rw [hle8 4 (by omega), hInv.r4], by rw [hle8 5 (by omega), hInv.r5],
                  fun reg hreg => by
                    rw [h11' reg (by clear hInv; omega) (by clear hInv; omega) (by clear hInv; omega),
                      hInv.rhi reg hreg],
                  by rw [hr_unch]; exact hInv.r_le,
                  by rw [hle8 8 le_rfl, h9']; exact Nat.le_succ_of_le hInv.qh_le,
                  hqt1_n,
                  by rw [h10', h11_unch]; exact hklt,
                  by rw [h11_unch]; exact hInv.kend_le,
                  ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
              · intro addr ha1 ha2
                rw [hmem', Function.update_of_ne (by clear hInv; omega),
                  Function.update_of_ne (by clear hInv; omega)]
                exact hInv.fr2 addr ha1 ha2
              · intro i hi
                rw [h9'] at hi
                by_cases hi_last : i = st.regs 9
                · subst hi_last
                  rw [hmem_qtail', hmem_nbr']
                  exact ⟨hnbr_lt, hne⟩
                · have hi' : i < st.regs 9 := by clear hInv; omega
                  rw [hmem_other_q i hi']
                  have hqi := hInv.q_lt i hi'
                  have hne_qi : st.mem (queueBase + i) ≠ q_entry.2.2 := hnbr_ne_q i hi'
                  rw [hmem_other_r _ hne_qi hqi.1]
                  exact hqi
              · intro i hi j hj heq
                rw [h9'] at hi hj
                by_cases hi_last : i = st.regs 9 <;> by_cases hj_last : j = st.regs 9
                · subst hi_last; subst hj_last; rfl
                · subst hi_last
                  have hj' : j < st.regs 9 := by clear hInv; omega
                  rw [hmem_qtail', hmem_other_q j hj'] at heq
                  exact False.elim (hnbr_ne_q j hj' heq.symm)
                · subst hj_last
                  have hi' : i < st.regs 9 := by clear hInv; omega
                  rw [hmem_other_q i hi', hmem_qtail'] at heq
                  exact False.elim (hnbr_ne_q i hi' heq)
                · have hi' : i < st.regs 9 := by clear hInv; omega
                  have hj' : j < st.regs 9 := by clear hInv; omega
                  rw [hmem_other_q i hi', hmem_other_q j hj'] at heq
                  exact hInv.q_inj i hi' j hj' heq
              · intro x hx hne
                rw [h9']
                by_cases hxnbr : x = q_entry.2.2
                · subst hxnbr
                  exact ⟨st.regs 9, by omega, hmem_qtail'⟩
                · rw [hmem_other_r x hxnbr hx] at hne
                  rcases hInv.q_cov x hx hne with ⟨i, hi, hi_eq⟩
                  exact ⟨i, by omega, by rw [hmem_other_q i hi, hi_eq]⟩
              · intro x hx
                rw [hr_unch] at hx
                by_cases hxnbr : x = q_entry.2.2
                · rw [hxnbr, hmem_nbr']; exact hne
                · rw [hmem_other_r x hxnbr (by clear hInv; omega)]
                  exact hInv.r_pref x hx
              · intro x hx
                rw [hr_unch]
                by_cases hxnbr : x = q_entry.2.2
                · right; rw [hxnbr, hmem_nbr']
                · rw [hmem_other_r x hxnbr hx]
                  exact hInv.root_le_r x hx
              · intro x hx hne_x
                by_cases hxnbr : x = q_entry.2.2
                · rw [hxnbr, hmem_nbr']; exact hreach_nbr
                · rw [hmem_other_r x hxnbr hx] at hne_x ⊢
                  exact hInv.root_reach x hx hne_x
              · right
                rw [hle8 8 le_rfl, h12_unch, h10', h11_unch, hmem_other_q (st.regs 8 - 1) (by clear hInv; omega)]
                exact ⟨hqh_pos, hcur_eq, hcur_n, by clear hInv; omega, hkend_eq⟩
              · intro _; rw [hr_unch]; exact hne
              · intro i hi1 hi2
                rw [h9'] at hi2
                rw [hr_unch]
                have hi1' : st.regs 8 - 1 ≤ i := by
                  have : (if st'.regs 10 < st'.regs 11 then st'.regs 8 - 1 else st'.regs 8) ≥ st.regs 8 - 1 := by
                    rw [hle8 8 le_rfl]; split_ifs <;> omega
                  omega
                by_cases hi_last : i = st.regs 9
                · subst hi_last
                  rw [hmem_qtail', hmem_nbr']
                · have hi' : i < st.regs 9 := by clear hInv; omega
                  rw [hmem_other_q i hi']
                  have hqi := hInv.q_lt i hi'
                  have hne_qi : st.mem (queueBase + i) ≠ q_entry.2.2 := hnbr_ne_q i hi'
                  rw [hmem_other_r _ hne_qi hqi.1]
                  exact hInv.cur_r i (by simp only [hklt, ↓reduceIte]; exact hi1') hi'
              · intro x hx hlt
                rw [hr_unch] at hlt
                by_cases hxnbr : x = q_entry.2.2
                · subst hxnbr; rw [hmem_nbr'] at hlt; omega
                · rw [hmem_other_r x hxnbr hx] at hlt
                  rcases hInv.old_fin x hx hlt with ⟨i, hi, hi_eq⟩
                  simp only [hklt, ↓reduceIte] at hi
                  have hi_fin' : i < (if st'.regs 10 < st'.regs 11 then st'.regs 8 - 1 else st'.regs 8) := by
                    rw [hle8 8 le_rfl]; split_ifs <;> omega
                  refine ⟨i, hi_fin', ?_⟩
                  rw [hmem_other_q i (by clear hInv; omega), hi_eq]
              · intro i hi t0 ht0
                rw [hle8 8 le_rfl] at hi
                have hi_q : i < st.regs 9 := by split_ifs at hi <;> omega
                have hqi_eq := hmem_other_q i hi_q
                have ht0' : t0 < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by rwa [← hqi_eq]
                have hget_eq : ((csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t0]'ht0).2.2 =
                    ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 := by simp only [hqi_eq]
                rw [hget_eq, hqi_eq]
                have hqi_n : st.mem (queueBase + i) < n := (hInv.q_lt i hi_q).1
                have hz_n : ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 < n := by
                  rw [← hn]; exact (csrIncAux_getElem_lt hval ht0').2.1
                have hqi_ne : st.mem (queueBase + i) ≠ q_entry.2.2 := hnbr_ne_q i hi_q
                by_cases hi_prev : i < st.regs 8 - 1
                · have hold := hInv.scan_prev i (by simp only [hklt, ↓reduceIte]; exact hi_prev) t0 ht0'
                  have hz_ne : ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 ≠ q_entry.2.2 := by
                    intro heq; rw [heq, hnew] at hold
                    have := (hInv.q_lt i hi_q).2; exact absurd hold (Nat.ne_of_gt this)
                  rw [hmem_other_r _ hz_ne hz_n, hmem_other_r _ hqi_ne hqi_n, hold]
                · -- Must be i = st.regs 8 - 1 when k + 1 = kEnd!
                  have hi_eq : i = st.regs 8 - 1 := by
                    by_cases hc : st'.regs 10 < st'.regs 11
                    · simp only [hc, ↓reduceIte] at hi; omega
                    · simp only [hc, ↓reduceIte] at hi; omega
                  have hnotlt : ¬ st'.regs 10 < st'.regs 11 := by
                    by_contra hc; simp only [hc, ↓reduceIte] at hi; omega
                  have hk_last : st.regs 10 + 1 = st.regs 11 := by
                    rw [h10', h11_unch] at hnotlt; clear hInv; omega
                  have hq_i_cur : st.mem (queueBase + i) = st.regs 12 := by rw [hi_eq, ← hcur_eq]
                  have ht0_cur : t0 < (csrIncAux (st.regs 12) 0 G.edges).length := by rwa [← hq_i_cur]
                  have hget_eq2 : ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 =
                      ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0_cur).2.2 := by
                    simp only [hq_i_cur]
                  rw [hget_eq2, hq_i_cur]
                  have hlt0 : csrOff G (st.regs 12) + t0 < st.regs 10 + 1 := by
                    have hs := csrOff_succ G (st.regs 12)
                    have hlen : (csrIncAux (st.regs 12) 0 G.edges).length = csrOff G (st.regs 12 + 1) - csrOff G (st.regs 12) := by omega
                    clear hInv; omega
                  exact hscan_cur' t0 ht0_cur hlt0
              · intro hc t0 ht0 hlt0
                have ht0' : t0 < (csrIncAux (st.regs 12) 0 G.edges).length := by rwa [← h12_unch]
                have hget_eq : ((csrIncAux (st'.regs 12) 0 G.edges)[t0]'ht0).2.2 =
                    ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0').2.2 := by simp only [h12_unch]
                rw [hget_eq, h12_unch]
                rw [h10', h12_unch] at hlt0
                exact hscan_cur' t0 ht0' hlt0
              · -- Measure decreased by 2 (qTail + 1 and k + 1)!
                dsimp only [compMeas]
                rw [hr_unch, hle8 8 le_rfl, h9', h10']
                have hde_eq : compDoneEdges G st'.mem queueBase (st.regs 8) (st.regs 10 + 1) =
                    compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10) + 1 := by
                  rw [compDoneEdges_congr G st'.mem st.mem queueBase (st.regs 8) (st.regs 10 + 1)
                    (fun i hi => hmem_other_q i (lt_of_lt_of_le hi hInv.qh_le))]
                  dsimp only [compDoneEdges]
                  have h8ne : st.regs 8 ≠ 0 := by clear hInv; omega
                  simp only [h8ne, ↓reduceIte, ← hcur_eq]
                  clear hInv; omega
                rw [hde_eq]
                clear hInv; omega
            · -- Already visited (st.mem (rootBase + nbr) ≠ n): mem unchanged, k += 1
              obtain ⟨hle9, h10', h11', hmem'⟩ := hskip hnew
              have hsame_root : st.mem (rootBase + q_entry.2.2) = st.regs 7 := by
                by_contra hne_r
                have hlt_r : st.mem (rootBase + q_entry.2.2) < st.regs 7 := by
                  rcases hInv.root_le_r q_entry.2.2 hnbr_lt with h1 | h2
                  · exact False.elim (hnew h1)
                  · exact Nat.lt_of_le_of_ne h2 hne_r
                rcases hInv.old_fin q_entry.2.2 hnbr_lt hlt_r with ⟨j, hj, hj_eq⟩
                simp only [hklt, ↓reduceIte] at hj
                have hj_q : j < st.regs 9 := by clear hInv; omega
                have hj_root : st.mem (rootBase + st.mem (queueBase + j)) = st.mem (rootBase + q_entry.2.2) := by
                  rw [hj_eq]
                -- (q_entry.1, ..., st.regs 12) ∈ csrIncAux q_entry.2.2 0 G.edges!
                have hedge_lt : q_entry.1 < G.edges.length := by simpa [Cited.Graph.m] using hq_em.1
                have hq_em_symm : Walk.EdgeMatches (G.edges.getD q_entry.1 (0, 0)) q_entry.2.2 (st.regs 12) := by
                  rcases hq_em.2.2.2 with h | h
                  · exact Or.inr ⟨h.2, h.1⟩
                  · exact Or.inl ⟨h.2, h.1⟩
                have hedge_mem := edge_mem_csrIncAux_of_ne (L := G.edges) (k := q_entry.1) (r := 0)
                  hedge_lt hq_em.2.2.1 hq_em_symm
                have hex_t : ∃ (t_back : ℕ) (htb : t_back < (csrIncAux q_entry.2.2 0 G.edges).length),
                    ((csrIncAux q_entry.2.2 0 G.edges)[t_back]'htb).2.2 = st.regs 12 := by
                  rcases hedge_mem with hm1 | hm1 <;>
                  · rcases List.getElem_of_mem hm1 with ⟨tb, htb, htb_eq⟩
                    exact ⟨tb, htb, by simp [htb_eq]⟩
                rcases hex_t with ⟨tb, htb, htb_eq⟩
                have hsp := hInv.scan_prev j (by simp only [hklt, ↓reduceIte]; exact hj) tb (by rw [hj_eq]; exact htb)
                have hcur_back : ((csrIncAux (st.mem (queueBase + j)) 0 G.edges)[tb]' (by rw [hj_eq]; exact htb)).2.2 =
                    st.regs 12 := by
                  simp only [hj_eq, htb_eq]
                rw [hcur_back, hj_eq, hcur_root_r] at hsp
                omega
              have hr_unch : st'.regs 7 = st.regs 7 := hle9 7 (by omega)
              have h12_unch : st'.regs 12 = st.regs 12 := h11' 12 (by decide) (by decide) (by decide)
              have h11_unch : st'.regs 11 = st.regs 11 := h11' 11 le_rfl (by decide) (by decide)
              have hscan_cur' : ∀ (t0 : ℕ) (ht0 : t0 < (csrIncAux (st.regs 12) 0 G.edges).length),
                  csrOff G (st.regs 12) + t0 < st.regs 10 + 1 →
                    st.mem (rootBase + ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0).2.2) =
                      st.mem (rootBase + st.regs 12) := by
                intro t0 ht0 hlt0
                by_cases ht_last : t0 = t
                · subst ht_last
                  have hz_eq : ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0).2.2 = q_entry.2.2 := by
                    rw [hq_def]
                  rw [hz_eq, hsame_root, hcur_root_r]
                · exact hInv.scan_cur hklt t0 ht0 (by clear hInv; omega)
              refine ⟨⟨by rw [hle9 0 (by omega), hInv.r0], by rw [hle9 1 (by omega), hInv.r1],
                  by rw [hle9 2 (by omega), hInv.r2], by rw [hle9 3 (by omega), hInv.r3],
                  by rw [hle9 4 (by omega), hInv.r4], by rw [hle9 5 (by omega), hInv.r5],
                  fun reg hreg => by
                    rw [h11' reg (by clear hInv; omega) (by clear hInv; omega) (by clear hInv; omega),
                      hInv.rhi reg hreg],
                  by rw [hr_unch]; exact hInv.r_le,
                  by rw [hle9 8 (by omega), hle9 9 le_rfl]; exact hInv.qh_le,
                  by rw [hle9 9 le_rfl]; exact hInv.qt_le,
                  by rw [h10', h11_unch]; exact hklt,
                  by rw [h11_unch]; exact hInv.kend_le,
                  by rw [hmem']; exact hInv.fr2,
                  by rw [hmem', hle9 9 le_rfl]; exact hInv.q_lt,
                  by rw [hmem', hle9 9 le_rfl]; exact hInv.q_inj,
                  by rw [hmem', hle9 9 le_rfl]; exact hInv.q_cov,
                  by rw [hmem', hr_unch]; exact hInv.r_pref,
                  by rw [hmem', hr_unch]; exact hInv.root_le_r,
                  by rw [hmem']; exact hInv.root_reach,
                  ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
              · right
                rw [hle9 8 (by omega), h12_unch, h10', h11_unch, hmem']
                exact ⟨hqh_pos, hcur_eq, hcur_n, by clear hInv; omega, hkend_eq⟩
              · intro _; rw [hr_unch]; exact hne
              · intro i hi1 hi2
                rw [hle9 9 le_rfl] at hi2
                rw [hmem', hr_unch]
                have h8_eq := hle9 8 (by omega)
                have hi1' : (if st.regs 10 < st.regs 11 then st.regs 8 - 1 else st.regs 8) ≤ i := by
                  simp only [hklt, ↓reduceIte]; rw [h8_eq] at hi1; split_ifs at hi1 <;> omega
                exact hInv.cur_r i hi1' hi2
              · intro x hx hlt
                rw [hmem'] at hlt ⊢; rw [hr_unch] at hlt
                rcases hInv.old_fin x hx hlt with ⟨i, hi, hi_eq⟩
                simp only [hklt, ↓reduceIte] at hi
                refine ⟨i, ?_, hi_eq⟩
                rw [hle9 8 (by omega)]; split_ifs <;> omega
              · intro i hi t0 ht0
                rw [hle9 8 (by omega)] at hi
                have ht0' : t0 < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by rwa [← hmem']
                have hget_eq : ((csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t0]'ht0).2.2 =
                    ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 := by simp only [hmem']
                rw [hget_eq, hmem']
                by_cases hi_prev : i < st.regs 8 - 1
                · exact hInv.scan_prev i (by simp only [hklt, ↓reduceIte]; exact hi_prev) t0 ht0'
                · have hi_eq : i = st.regs 8 - 1 := by split_ifs at hi <;> omega
                  have hnotlt : ¬ st'.regs 10 < st'.regs 11 := by
                    by_contra hc; simp only [hc, ↓reduceIte] at hi; omega
                  have hk_last : st.regs 10 + 1 = st.regs 11 := by
                    rw [h10', h11_unch] at hnotlt; clear hInv; omega
                  have ht0_cur : t0 < (csrIncAux (st.regs 12) 0 G.edges).length := by rw [hi_eq, ← hcur_eq] at ht0'; exact ht0'
                  have hget_eq2 : ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 =
                      ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0_cur).2.2 := by
                    simp only [hi_eq, ← hcur_eq]
                  rw [hget_eq2, hi_eq, ← hcur_eq]
                  have hlt0 : csrOff G (st.regs 12) + t0 < st.regs 10 + 1 := by
                    have hs := csrOff_succ G (st.regs 12)
                    clear hInv; omega
                  exact hscan_cur' t0 ht0_cur hlt0
              · intro hc t0 ht0 hlt0
                have ht0' : t0 < (csrIncAux (st.regs 12) 0 G.edges).length := by rwa [← h12_unch]
                have hget_eq : ((csrIncAux (st'.regs 12) 0 G.edges)[t0]'ht0).2.2 =
                    ((csrIncAux (st.regs 12) 0 G.edges)[t0]'ht0').2.2 := by simp only [h12_unch]
                rw [hget_eq, hmem', h12_unch]
                rw [h10', h12_unch] at hlt0
                exact hscan_cur' t0 ht0' hlt0
              · dsimp only [compMeas]
                rw [hr_unch, hle9 8 (by omega), hle9 9 le_rfl, h10', hmem']
                have hdone1 : compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10 + 1) =
                    compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10) + 1 := by
                  dsimp only [compDoneEdges]
                  have h8ne : st.regs 8 ≠ 0 := by clear hInv; omega
                  simp only [h8ne, ↓reduceIte, ← hcur_eq]
                  clear hInv; omega
                rw [hdone1]
                clear hInv; omega
        · intro h0_k; simp [hklt] at h0_k
      · -- Else: k = kEnd
        have hk_eq : st.regs 10 = st.regs 11 := by clear hInv; omega
        have hdone_eq_sum : compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10) =
            compDegSum G st.mem queueBase (st.regs 8) := by
          rcases hInv.csr_k with ⟨h8_0, h10_0, _⟩ | ⟨h8_pos, h12_q, _, _, hkend_eq⟩
          · simp [compDoneEdges, h8_0, compDegSum]
          · dsimp only [compDoneEdges]
            have h8ne : st.regs 8 ≠ 0 := by clear hInv; omega
            simp only [h8ne, ↓reduceIte]
            have hq_succ : st.regs 8 - 1 + 1 = st.regs 8 := Nat.sub_add_cancel h8_pos
            rw [← h12_q, hk_eq, hkend_eq]
            conv_rhs => rw [← hq_succ]
            dsimp only [compDegSum]
            rw [h12_q]
        have hdone_le2m : compDoneEdges G st.mem queueBase (st.regs 8) (st.regs 10) ≤ 2 * m := by
          rw [hdone_eq_sum, ← hm]
          exact compDegSum_le_two_mul_m G st.mem queueBase (st.regs 8)
            (fun i hi => hn ▸ (hInv.q_lt i (lt_of_lt_of_le hi hInv.qh_le)).1)
            (fun i hi j hj => hInv.q_inj i (lt_of_lt_of_le hi hInv.qh_le) j (lt_of_lt_of_le hj hInv.qh_le))
        have hec_q_w : (if st.regs 8 < st.regs 9 then 1 else 0) < 2 ^ w := by split_ifs <;> linarith only [h1_w]
        have hec_q : (Expr.bin .lt (.reg 8) (.reg 9)).eval w st =
            some (if st.regs 8 < st.regs 9 then 1 else 0) := by
          simp [Expr.eval, BinOp.eval, hec_q_w]
        by_cases hqlt : st.regs 8 < st.regs 9
        · -- Branch 2: pop qHead
          have hqn : st.regs 8 < n := lt_of_lt_of_le hqlt hInv.qt_le
          obtain ⟨nxt, hnxt_eq⟩ : ∃ v, v = st.mem (queueBase + st.regs 8) := ⟨_, rfl⟩
          have hnxt_n : nxt < n := by rw [hnxt_eq]; exact (hInv.q_lt _ hqlt).1
          have hoff0 : st.mem (csrAddr + nxt) = csrOff G nxt := hcsr_st.1 nxt (by rw [hn]; exact Nat.le_of_lt hnxt_n)
          have hoff1 : st.mem (csrAddr + nxt + 1) = csrOff G (nxt + 1) := by
            rw [Nat.add_assoc]; exact hcsr_st.1 (nxt + 1) (by rw [hn]; exact hnxt_n)
          have hq_addr_w : queueBase + st.regs 8 < 2 ^ w := by linarith only [hqn, hq_w]
          have hq1_w : st.regs 8 + 1 < 2 ^ w := by linarith only [hqn, hn_w]
          have hc0_w : csrAddr + nxt < 2 ^ w := by linarith only [hnxt_n, hcsr_w]
          have hc1_w : csrAddr + nxt + 1 < 2 ^ w := by linarith only [hnxt_n, hcsr_w]
          refine runs_start_le ?_
          refine runs_cond_le hec_k (fun h => by simp [hklt] at h) (fun _ => ?_)
          refine runs_cond_le hec_q (fun _ => ?_) (fun h => by simp [hqlt] at h)
          refine runs_triple_le
            (bfsComp_pop_triple st csrAddr queueBase (st.regs 8) nxt (csrOff G nxt) (csrOff G (nxt + 1))
              hInv.r2 hInv.r3 rfl hnxt_eq.symm hoff0 hoff1 hq_addr_w hq1_w hc0_w hc1_w h1_w)
            rfl ?_ (by simp only [Expr.size_reg, Expr.size_bin]; omega)
          intro o st' hpost
          cases o with
          | returned _ => exact False.elim hpost
          | normal =>
            rcases hpost with ⟨hle7, h8', h9', h10', h11', h12', hge13, hmem'⟩
            have hdone_new : compDoneEdges G st'.mem queueBase (st'.regs 8) (st'.regs 10) =
                compDegSum G st.mem queueBase (st.regs 8) := by
              rw [h8', h10', hmem']
              dsimp only [compDoneEdges]
              simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
              rw [← hnxt_eq, Nat.sub_self, Nat.add_zero]
            have hr_unch : st'.regs 7 = st.regs 7 := hle7 7 le_rfl
            refine ⟨⟨by rw [hle7 0 (by omega), hInv.r0], by rw [hle7 1 (by omega), hInv.r1],
                by rw [hle7 2 (by omega), hInv.r2], by rw [hle7 3 (by omega), hInv.r3],
                by rw [hle7 4 (by omega), hInv.r4], by rw [hle7 5 (by omega), hInv.r5],
                fun reg hreg => by rw [hge13 reg (by omega), hInv.rhi reg hreg],
                by rw [hr_unch]; exact hInv.r_le,
                by rw [h8', h9']; exact hqlt,
                by rw [h9']; exact hInv.qt_le,
                by rw [h10', h11']; exact csrOff_mono G (Nat.le_succ _),
                by rw [h11', ← hm]; exact csrOff_le_two_mul_m G (nxt + 1),
                by rw [hmem']; exact hInv.fr2,
                by rw [hmem', h9']; exact hInv.q_lt,
                by rw [hmem', h9']; exact hInv.q_inj,
                by rw [hmem', h9']; exact hInv.q_cov,
                by rw [hmem', hr_unch]; exact hInv.r_pref,
                by rw [hmem', hr_unch]; exact hInv.root_le_r,
                by rw [hmem']; exact hInv.root_reach,
                ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
            · right
              rw [h8', h12', h10', h11', hmem']
              exact ⟨Nat.succ_pos _, by simp [hnxt_eq], hnxt_n, le_rfl, rfl⟩
            · intro _; rw [hr_unch]; exact hne
            · intro i hi1 hi2
              rw [h9'] at hi2
              rw [hmem', hr_unch]
              have hfin_ge : st.regs 8 ≤ if st'.regs 10 < st'.regs 11 then st'.regs 8 - 1 else st'.regs 8 := by
                rw [h8']; split_ifs <;> omega
              exact hInv.cur_r i (by simp only [show ¬ st.regs 10 < st.regs 11 by omega, ↓reduceIte]; exact le_trans hfin_ge hi1) hi2
            · intro x hx hlt
              rw [hmem'] at hlt ⊢; rw [hr_unch] at hlt
              rcases hInv.old_fin x hx hlt with ⟨i, hi, hi_eq⟩
              simp only [show ¬ st.regs 10 < st.regs 11 by omega, ↓reduceIte] at hi
              refine ⟨i, ?_, hi_eq⟩
              rw [h8']; split_ifs <;> omega
            · intro i hi t0 ht0
              have ht0' : t0 < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by rwa [← hmem']
              have hget_eq : ((csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t0]'ht0).2.2 =
                  ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 := by simp only [hmem']
              rw [hget_eq, hmem']
              by_cases hi_old : i < st.regs 8
              · exact hInv.scan_prev i (by simp only [show ¬ st.regs 10 < st.regs 11 by omega, ↓reduceIte]; exact hi_old) t0 ht0'
              · -- Must be i = st.regs 8 and k' = kEnd' (0 edges!)
                have hnotlt : ¬ st'.regs 10 < st'.regs 11 := by
                  by_contra hc; rw [h8'] at hi; simp only [hc, ↓reduceIte] at hi; omega
                have hlen0 : (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length = 0 := by
                  have hi_eq : i = st.regs 8 := by rw [h8'] at hi; simp only [hnotlt, ↓reduceIte] at hi; omega
                  subst hi_eq
                  rw [← hnxt_eq]
                  have hs := csrOff_succ G nxt
                  rw [h10', h11'] at hnotlt
                  omega
                omega
            · intro hc t0 ht0 hlt0
              rw [h10', h12'] at hlt0
              omega
            · dsimp only [compMeas]
              rw [hr_unch, hdone_new, h8', h9', hdone_eq_sum]
              clear hInv; omega
        · -- Branch 3: k = kEnd and qHead = qTail
          have hqh_eq : st.regs 8 = st.regs 9 := by clear hInv; omega
          have hroot_r_w : rootBase + st.regs 7 < 2 ^ w := by linarith only [hne, hroot_w]
          have hqt_lt_n_of_new : st.mem (rootBase + st.regs 7) = n → st.regs 9 < n := by
            intro hrr
            by_contra hge
            have hqn : st.regs 9 = n := by clear hInv; omega
            have hinj : ∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n,
                st.mem (queueBase + a) = st.mem (queueBase + b) → a = b := fun a ha b hb heq =>
              hInv.q_inj a (by rw [hqn]; exact Finset.mem_range.mp ha)
                b (by rw [hqn]; exact Finset.mem_range.mp hb) heq
            have himg : (Finset.range n).image (fun i => st.mem (queueBase + i)) ⊆ Finset.range n := by
              intro z hz
              rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
              exact Finset.mem_range.mpr (hInv.q_lt i (by rw [hqn]; exact Finset.mem_range.mp hi)).1
            have hcard : ((Finset.range n).image (fun i => st.mem (queueBase + i))).card = n := by
              rw [Finset.card_image_of_injOn (fun a ha b hb heq => hinj a ha b hb heq), Finset.card_range]
            have heqset := Finset.eq_of_subset_of_card_le himg (by rw [hcard, Finset.card_range])
            have hmem_r : st.regs 7 ∈ (Finset.range n).image (fun i => st.mem (queueBase + i)) := by
              rw [heqset]; exact Finset.mem_range.mpr hne
            rcases Finset.mem_image.mp hmem_r with ⟨i, hi, hi_eq⟩
            have hi_lt : i < st.regs 9 := by rw [hqn]; exact Finset.mem_range.mp hi
            have := (hInv.q_lt i hi_lt).2
            rw [hi_eq, hrr] at this
            omega
          refine runs_start_le ?_
          refine runs_cond_le hec_k (fun h => by simp [hklt] at h) (fun _ => ?_)
          refine runs_cond_le hec_q (fun h => by simp [hqlt] at h) (fun _ => ?_)
          refine runs_triple_le
            (bfsComp_root_triple st n queueBase rootBase (st.regs 7) (st.regs 9)
              (st.mem (rootBase + st.regs 7)) hInv.r0 hInv.r3 hInv.r4 rfl rfl rfl h1_w hw4
              hroot_r_w (fun h => by linarith only [hqt_lt_n_of_new h, hq_w])
              (fun h => by linarith only [hqt_lt_n_of_new h, hq_w])
              (fun _ => by linarith only [hne, hn_w]))
            rfl ?_ (by simp only [Expr.size_reg, Expr.size_bin]; omega)
          intro o st' hpost
          cases o with
          | returned _ => exact False.elim hpost
          | normal =>
            rcases hpost with ⟨hnew, hdone_r⟩
            by_cases hrr : st.mem (rootBase + st.regs 7) = n
            · -- Branch 3a: start new component at r
              have hqn : st.regs 9 < n := hqt_lt_n_of_new hrr
              obtain ⟨hle8, h9', hge10, hmem'⟩ := hnew hrr
              have hr_unch : st'.regs 7 = st.regs 7 := hle8 7 (by omega)
              have h8_unch : st'.regs 8 = st.regs 8 := hle8 8 le_rfl
              have h10_unch : st'.regs 10 = st.regs 10 := hge10 10 le_rfl (by decide)
              have h11_unch : st'.regs 11 = st.regs 11 := hge10 11 (by omega) (by decide)
              have h12_unch : st'.regs 12 = st.regs 12 := hge10 12 (by omega) (by decide)
              have hr_ne_q : ∀ j < st.regs 9, st.mem (queueBase + j) ≠ st.regs 7 := fun j hj heq => by
                have := (hInv.q_lt j hj).2
                rw [heq, hrr] at this
                omega
              have hmem_other_q : ∀ j < st.regs 9, st'.mem (queueBase + j) = st.mem (queueBase + j) :=
                fun j hj => by
                  rw [hmem', Function.update_of_ne (by clear hInv; omega),
                    Function.update_of_ne (by rcases hdj_qr with h | h <;> (clear hInv; omega))]
              have hmem_other_r : ∀ y, y ≠ st.regs 7 → y < n → st'.mem (rootBase + y) = st.mem (rootBase + y) :=
                fun y hne_y hy_n => by
                  rw [hmem', Function.update_of_ne (by rcases hdj_qr with h | h <;> (clear hInv; omega)),
                    Function.update_of_ne (by clear hInv; omega)]
              have hmem_rr' : st'.mem (rootBase + st.regs 7) = st.regs 7 := by
                rw [hmem', Function.update_of_ne (by rcases hdj_qr with h | h <;> (clear hInv; omega)),
                  Function.update_self]
              have hmem_qr' : st'.mem (queueBase + st.regs 9) = st.regs 7 := by
                rw [hmem', Function.update_self]
              refine ⟨⟨by rw [hle8 0 (by omega), hInv.r0], by rw [hle8 1 (by omega), hInv.r1],
                  by rw [hle8 2 (by omega), hInv.r2], by rw [hle8 3 (by omega), hInv.r3],
                  by rw [hle8 4 (by omega), hInv.r4], by rw [hle8 5 (by omega), hInv.r5],
                  fun reg hreg => by rw [hge10 reg (by clear hInv; omega) (by clear hInv; omega), hInv.rhi reg hreg],
                  by rw [hr_unch]; exact hr_le,
                  by rw [h8_unch, h9']; exact Nat.le_succ_of_le hqh_le,
                  by rw [h9']; exact hqn,
                  by rw [h10_unch, h11_unch]; exact hk_le,
                  by rw [h11_unch]; exact hkend_le,
                  ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
              · intro addr ha1 ha2
                rw [hmem', Function.update_of_ne (by clear hInv; omega),
                  Function.update_of_ne (by clear hInv; omega)]
                exact hInv.fr2 addr ha1 ha2
              · intro i hi
                rw [h9'] at hi
                by_cases hi_last : i = st.regs 9
                · subst hi_last
                  rw [hmem_qr', hmem_rr']
                  exact ⟨hne, hne⟩
                · have hi' : i < st.regs 9 := by clear hInv; omega
                  rw [hmem_other_q i hi']
                  have hqi := hInv.q_lt i hi'
                  rw [hmem_other_r _ (hr_ne_q i hi') hqi.1]
                  exact hqi
              · intro i hi j hj heq
                rw [h9'] at hi hj
                by_cases hi_last : i = st.regs 9 <;> by_cases hj_last : j = st.regs 9
                · subst hi_last; subst hj_last; rfl
                · subst hi_last
                  have hj' : j < st.regs 9 := by clear hInv; omega
                  rw [hmem_qr', hmem_other_q j hj'] at heq
                  exact False.elim (hr_ne_q j hj' heq.symm)
                · subst hj_last
                  have hi' : i < st.regs 9 := by clear hInv; omega
                  rw [hmem_other_q i hi', hmem_qr'] at heq
                  exact False.elim (hr_ne_q i hi' heq)
                · have hi' : i < st.regs 9 := by clear hInv; omega
                  have hj' : j < st.regs 9 := by clear hInv; omega
                  rw [hmem_other_q i hi', hmem_other_q j hj'] at heq
                  exact hInv.q_inj i hi' j hj' heq
              · intro x hx hne_x
                rw [h9']
                by_cases hxr : x = st.regs 7
                · subst hxr; exact ⟨st.regs 9, by omega, hmem_qr'⟩
                · rw [hmem_other_r x hxr hx] at hne_x
                  rcases hInv.q_cov x hx hne_x with ⟨i, hi, hi_eq⟩
                  exact ⟨i, by omega, by rw [hmem_other_q i hi, hi_eq]⟩
              · intro x hx
                rw [hr_unch] at hx
                rw [hmem_other_r x (by clear hInv; omega) (by clear hInv; omega)]
                exact hInv.r_pref x hx
              · intro x hx
                rw [hr_unch]
                by_cases hxr : x = st.regs 7
                · subst hxr; right; rw [hmem_rr']
                · rw [hmem_other_r x hxr hx]
                  exact hInv.root_le_r x hx
              · intro x hx hne_x
                by_cases hxr : x = st.regs 7
                · subst hxr; rw [hmem_rr']; exact ⟨[st.regs 7], isPathAlong_singleton _ _⟩
                · rw [hmem_other_r x hxr hx] at hne_x ⊢
                  exact hInv.root_reach x hx hne_x
              · rcases hInv.csr_k with ⟨h8_0, h10_0, h11_0⟩ | ⟨h8_p, h12_q, h12_n, hoff, hkend⟩
                · left; rw [h8_unch, h10_unch, h11_unch]; exact ⟨h8_0, h10_0, h11_0⟩
                · right
                  rw [h8_unch, h12_unch, h10_unch, h11_unch, hmem_other_q (st.regs 8 - 1) (by clear hInv; omega)]
                  exact ⟨h8_p, h12_q, h12_n, hoff, hkend⟩
              · intro _; rw [hr_unch]; exact hne
              · intro i hi1 hi2
                rw [h10_unch, h11_unch, h8_unch] at hi1
                simp only [hklt, ↓reduceIte] at hi1
                rw [h9'] at hi2
                rw [hr_unch]
                have hi_eq : i = st.regs 9 := by clear hInv; omega
                subst hi_eq
                rw [hmem_qr', hmem_rr']
              · intro x hx hlt
                rw [hr_unch] at hlt
                by_cases hxr : x = st.regs 7
                · subst hxr; rw [hmem_rr'] at hlt; omega
                · rw [hmem_other_r x hxr hx] at hlt
                  rcases hInv.old_fin x hx hlt with ⟨i, hi, hi_eq⟩
                  simp only [hklt, ↓reduceIte] at hi
                  refine ⟨i, ?_, ?_⟩
                  · rw [h10_unch, h11_unch, h8_unch]; simp only [hklt, ↓reduceIte]; exact hi
                  · rw [hmem_other_q i (by clear hInv; omega), hi_eq]
              · intro i hi t0 ht0
                rw [h10_unch, h11_unch, h8_unch] at hi
                simp only [hklt, ↓reduceIte] at hi
                have hi_q : i < st.regs 9 := by clear hInv; omega
                have hqi_eq := hmem_other_q i hi_q
                have ht0' : t0 < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by rwa [← hqi_eq]
                have hget_eq : ((csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t0]'ht0).2.2 =
                    ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 := by simp only [hqi_eq]
                rw [hget_eq, hqi_eq]
                have hqi_n : st.mem (queueBase + i) < n := (hInv.q_lt i hi_q).1
                have hz_n : ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 < n := by
                  rw [← hn]; exact (csrIncAux_getElem_lt hval ht0').2.1
                have hold := hInv.scan_prev i (by simp only [hklt, ↓reduceIte]; exact hi) t0 ht0'
                have hz_ne : ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 ≠ st.regs 7 := by
                  intro heq; rw [heq, hrr] at hold
                  have := (hInv.q_lt i hi_q).2; omega
                rw [hmem_other_r _ hz_ne hz_n, hmem_other_r _ (hr_ne_q i hi_q) hqi_n, hold]
              · intro hc
                rw [h10_unch, h11_unch] at hc
                exact False.elim (hklt hc)
              · dsimp only [compMeas]
                rw [hr_unch, h8_unch, h9', h10_unch]
                rw [compDoneEdges_congr G st'.mem st.mem queueBase (st.regs 8) (st.regs 10)
                  (fun i hi => hmem_other_q i (lt_of_lt_of_le hi hqh_le))]
                clear hInv; omega
            · -- Branch 3b: r already visited, increment r := r + 1
              obtain ⟨hle6, h7', hge8, hmem'⟩ := hdone_r hrr
              have hr1_le : st'.regs 7 ≤ n := by rw [h7']; exact hne
              have h8_unch : st'.regs 8 = st.regs 8 := hge8 8 le_rfl (by decide)
              have h9_unch : st'.regs 9 = st.regs 9 := hge8 9 (by omega) (by decide)
              have h10_unch : st'.regs 10 = st.regs 10 := hge8 10 (by omega) (by decide)
              have h11_unch : st'.regs 11 = st.regs 11 := hge8 11 (by omega) (by decide)
              have h12_unch : st'.regs 12 = st.regs 12 := hge8 12 (by omega) (by decide)
              refine ⟨⟨by rw [hle6 0 (by omega), hInv.r0], by rw [hle6 1 (by omega), hInv.r1],
                  by rw [hle6 2 (by omega), hInv.r2], by rw [hle6 3 (by omega), hInv.r3],
                  by rw [hle6 4 (by omega), hInv.r4], by rw [hle6 5 (by omega), hInv.r5],
                  fun reg hreg => by rw [hge8 reg (by omega) (by omega), hInv.rhi reg hreg],
                  hr1_le,
                  by rw [h8_unch, h9_unch]; exact hqh_le,
                  by rw [h9_unch]; exact hqt_le,
                  by rw [h10_unch, h11_unch]; exact hk_le,
                  by rw [h11_unch]; exact hkend_le,
                  by rw [hmem']; exact hInv.fr2,
                  by rw [hmem', h9_unch]; exact hInv.q_lt,
                  by rw [hmem', h9_unch]; exact hInv.q_inj,
                  by rw [hmem', h9_unch]; exact hInv.q_cov,
                  ?_, ?_, by rw [hmem']; exact hInv.root_reach, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
              · intro x hx
                rw [h7'] at hx
                rw [hmem']
                by_cases hxr : x = st.regs 7
                · subst hxr
                  rcases hInv.root_le_r _ hne with h1 | h2
                  · exact False.elim (hrr h1)
                  · exact lt_of_le_of_lt h2 hne
                · exact hInv.r_pref x (by clear hInv; omega)
              · intro x hx
                rw [h7', hmem']
                rcases hInv.root_le_r x hx with h1 | h2
                · left; exact h1
                · right; omega
              · rw [h8_unch, h10_unch, h11_unch, h12_unch, hmem']
                exact hInv.csr_k
              · intro hc
                rw [h10_unch, h11_unch, h8_unch, h9_unch] at hc
                rcases hc with hc1 | hc2
                · exact False.elim (hklt hc1)
                · exact False.elim (hqlt hc2)
              · intro i hi1 hi2
                rw [h10_unch, h11_unch, h8_unch] at hi1
                simp only [hklt, ↓reduceIte] at hi1
                rw [h9_unch] at hi2
                clear hInv; omega
              · intro x hx hlt
                rw [h7', hmem'] at hlt
                have hne_x : st.mem (rootBase + x) ≠ n := by clear hInv; omega
                rcases hInv.q_cov x hx hne_x with ⟨i, hi, hi_eq⟩
                refine ⟨i, ?_, by rw [hmem', hi_eq]⟩
                rw [h10_unch, h11_unch, h8_unch]; simp only [hklt, ↓reduceIte]; rw [hqh_eq]
                exact hi
              · intro i hi t0 ht0
                rw [h10_unch, h11_unch, h8_unch] at hi
                simp only [hklt, ↓reduceIte] at hi
                have ht0' : t0 < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by rwa [← hmem']
                have hget_eq : ((csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t0]'ht0).2.2 =
                    ((csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t0]'ht0').2.2 := by simp only [hmem']
                rw [hget_eq, hmem']
                exact hInv.scan_prev i (by simp only [hklt, ↓reduceIte]; exact hi) t0 ht0'
              · intro hc
                rw [h10_unch, h11_unch] at hc
                exact False.elim (hklt hc)
              · dsimp only [compMeas]
                rw [h7', h8_unch, h9_unch, h10_unch, hmem']
                clear hInv; omega)

/-! ## 6. `bfsLabelsCore_triple` and `bfsLabelsProc` contract -/

private lemma bfsLabelsCore_triple {w : ℕ} {p : Program}
    (n m csrAddr queueBase rootBase : ℕ) (G : Cited.Graph)
    (memBase : ℕ → ℕ) (st0 : State)
    (hn : G.n = n) (hm : G.m = m) (hval : G.IsValid)
    (hcsr : HasCsrAt memBase csrAddr G)
    (hdj_cq : csrAddr + 2 * n + 1 + 4 * m ≤ queueBase ∨ queueBase + n ≤ csrAddr)
    (hdj_cr : csrAddr + 2 * n + 1 + 4 * m ≤ rootBase ∨ rootBase + n ≤ csrAddr)
    (hdj_qr : queueBase + n ≤ rootBase ∨ rootBase + n ≤ queueBase)
    (hcsr_w : csrAddr + 2 * n + 1 + 4 * m < 2 ^ w)
    (hq_w : queueBase + n < 2 ^ w) (hroot_w : rootBase + n < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hr0 : st0.regs 0 = n) (hr1 : st0.regs 1 = m) (hr2 : st0.regs 2 = csrAddr)
    (hr3 : st0.regs 3 = queueBase) (hr4 : st0.regs 4 = rootBase)
    (hmem0 : st0.mem = memBase) :
    Triple w p (fun st => st = st0) bfsLabelsCore
      (normalPost fun st' =>
        (∀ r ≤ 4, st'.regs r = st0.regs r) ∧
        (∀ r ≥ 15, st'.regs r = st0.regs r) ∧
        (∀ addr, (addr < queueBase ∨ queueBase + n ≤ addr) →
          (addr < rootBase ∨ rootBase + n ≤ addr) → st'.mem addr = memBase addr) ∧
        (∀ x < n, st'.mem (rootBase + x) < n) ∧
        (∀ x < n, ∀ y < n,
          st'.mem (rootBase + x) = st'.mem (rootBase + y) ↔
            (compLabels G).getD x 0 = (compLabels G).getD y 0))
      (fun _ => 152 * n + 92 * m + 36) := by
  have h1_w : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 4) hw4
  have hn_w : n < 2 ^ w := by linarith only [hroot_w]
  obtain ⟨adjVBase, hadj_def⟩ : ∃ v, v = csrAddr + 2 * n + 1 := ⟨_, rfl⟩
  have hadj_w : adjVBase < 2 ^ w := by linarith only [hadj_def, hcsr_w]
  have h2n_w : 2 * n < 2 ^ w := by linarith only [hadj_def, hcsr_w]
  have hca2n_w : csrAddr + 2 * n < 2 ^ w := by linarith only [hadj_def, hcsr_w]
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  dsimp only [bfsLabelsCore, seqStmts]
  wram_step
  wram_step
  obtain ⟨regs1, hregs1_def⟩ : ∃ f : ℕ → ℕ, f = fun r => if r = 5 then adjVBase else st.regs r := ⟨_, rfl⟩
  refine runs_seq_triple_le
    (bfsComp_zero_loop n rootBase memBase regs1 _ (by simp [hr0]) (by simp [hr4])
      (by simp)
      (fun r hr => by
        dsimp only
        rw [Function.update_of_ne (by omega : r ≠ 6), Function.update_of_ne (by omega : r ≠ 5), hregs1_def]
        dsimp only
        split_ifs <;> [omega; rfl])
      (by simp [hregs1_def, hadj_def])
      (fun r hr => by
        dsimp only
        rw [Function.update_of_ne (by omega : r ≠ 6), Function.update_of_ne (by omega : r ≠ 5), hregs1_def]
        dsimp only
        split_ifs <;> [omega; rfl])
      (by rw [hmem0]; exact fun _ _ => rfl) hroot_w hn_w h1_w hw4)
    rfl (fun st1 h1p => ?_)
  rcases h1p with ⟨hle4, h5_eq, hge15, hfr1, hroot_init⟩
  have hs1_0 : st1.regs 0 = n := by rw [hle4 0 (by omega), hregs1_def]; simp [hr0]
  have hs1_1 : st1.regs 1 = m := by rw [hle4 1 (by omega), hregs1_def]; simp [hr1]
  have hs1_2 : st1.regs 2 = csrAddr := by rw [hle4 2 (by omega), hregs1_def]; simp [hr2]
  have hs1_3 : st1.regs 3 = queueBase := by rw [hle4 3 (by omega), hregs1_def]; simp [hr3]
  have hs1_4 : st1.regs 4 = rootBase := by rw [hle4 4 (by omega), hregs1_def]; simp [hr4]
  have hs1_5 : st1.regs 5 = adjVBase := by rw [h5_eq, hregs1_def]; simp
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  have hloop := bfsComp_main_loop (p := p) n m csrAddr queueBase rootBase adjVBase G memBase st.regs
    hn hm hval hcsr hdj_cq hdj_cr hdj_qr hcsr_w hq_w hroot_w hw4 hadj_def
  refine runs_triple_le hloop ?_ ?_ ?_
  · refine ⟨by simp [hs1_0], by simp [hs1_1], by simp [hs1_2], by simp [hs1_3], by simp [hs1_4],
        by simp [hs1_5], fun r hr => by
          dsimp only
          rw [Function.update_of_ne (by omega : r ≠ 11), Function.update_of_ne (by omega : r ≠ 10),
            Function.update_of_ne (by omega : r ≠ 9), Function.update_of_ne (by omega : r ≠ 8),
            Function.update_of_ne (by omega : r ≠ 7), hge15 r hr, hregs1_def]
          dsimp only
          split_ifs <;> [omega; rfl],
        by simp, by simp, by simp, by simp,
        by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro addr ha1 ha2
      exact hfr1 addr ha2
    · intro i hi; simp at hi
    · intro i hi; simp at hi
    · intro x hx hne; exact False.elim (hne (hroot_init x hx))
    · intro x hx; simp at hx
    · intro x hx; left; exact hroot_init x hx
    · intro x hx hne; exact False.elim (hne (hroot_init x hx))
    · left; simp
    · intro h; simp at h
    · intro i hi1 hi2; simp at hi2
    · intro x hx hlt; simp at hlt
    · intro i hi; simp at hi
    · intro h; simp at h
  · intro o st2 h2p
    cases o with
    | returned _ => exact False.elim h2p
    | normal =>
      rcases h2p with ⟨hInv2, h7_eq⟩
      dsimp only [normalPost]
      refine ⟨fun r hr => ?_, hInv2.rhi, hInv2.fr2, fun x hx => ?_, fun x hx y hy => ?_⟩
      · rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl | rfl
        · exact hInv2.r0.trans hr0.symm
        · exact hInv2.r1.trans hr1.symm
        · exact hInv2.r2.trans hr2.symm
        · exact hInv2.r3.trans hr3.symm
        · exact hInv2.r4.trans hr4.symm
      · exact hInv2.r_pref x (h7_eq ▸ hx)
      · have hfinished_q : st2.regs 8 = st2.regs 9 ∧ st2.regs 10 = st2.regs 11 := by
          by_contra hc
          have hc' : st2.regs 10 < st2.regs 11 ∨ st2.regs 8 < st2.regs 9 := by
            have hk_le := hInv2.k_le
            have hqh_le := hInv2.qh_le
            omega
          have hlt := hInv2.active_lt hc'
          omega
        have hqt_n : st2.regs 9 = n := by
          have hinj : ∀ a ∈ Finset.range (st2.regs 9), ∀ b ∈ Finset.range (st2.regs 9),
              st2.mem (queueBase + a) = st2.mem (queueBase + b) → a = b := fun a ha b hb =>
            hInv2.q_inj a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb)
          have hcov : Finset.range n ⊆ (Finset.range (st2.regs 9)).image (fun i => st2.mem (queueBase + i)) := by
            intro z hz
            have hzn : z < n := Finset.mem_range.mp hz
            have hzp := hInv2.r_pref z (h7_eq ▸ hzn)
            rcases hInv2.q_cov z hzn (by omega) with ⟨i, hi, rfl⟩
            exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
          have hc := Finset.card_le_card hcov
          rw [Finset.card_range, Finset.card_image_of_injOn (fun a ha b hb => hinj a ha b hb),
            Finset.card_range] at hc
          have hqt_le := hInv2.qt_le
          omega
        have hedge_eq : ∀ e ∈ G.edges, st2.mem (rootBase + e.1) = st2.mem (rootBase + e.2) := by
          intro e he
          rcases hval e he with ⟨he1, he2⟩
          by_cases h12 : e.1 = e.2
          · rw [h12]
          · have he1_n : e.1 < n := by rw [← hn]; exact he1
            rcases hInv2.q_cov e.1 he1_n (by have := hInv2.r_pref e.1 (h7_eq ▸ he1_n); omega) with ⟨i, hi, hi_eq⟩
            have hi_fin : i < (if st2.regs 10 < st2.regs 11 then st2.regs 8 - 1 else st2.regs 8) := by
              simp only [hfinished_q.2, lt_self_iff_false, ↓reduceIte, hfinished_q.1]; exact hi
            rcases List.getElem?_of_mem he with ⟨idx, hidx⟩
            have hidx_len : idx < G.edges.length := (List.getElem?_eq_some_iff.mp hidx).1
            have hm_mem := edge_mem_csrIncAux_of_ne (L := G.edges) (k := idx) (r := 0)
              hidx_len h12 (by simp [Walk.EdgeMatches, List.getD_eq_getElem?_getD, hidx])
            have hex_t : ∃ (t : ℕ) (ht : t < (csrIncAux e.1 0 G.edges).length),
                ((csrIncAux e.1 0 G.edges)[t]'ht).2.2 = e.2 := by
              rcases hm_mem with h | h <;>
              · rcases List.getElem_of_mem h with ⟨t, ht, ht_eq⟩; exact ⟨t, ht, by rw [ht_eq]⟩
            rcases hex_t with ⟨t, ht, ht_eq⟩
            have hsp := hInv2.scan_prev i hi_fin t (by rw [hi_eq]; exact ht)
            simpa [hi_eq, ht_eq] using hsp.symm
        constructor
        · intro heq
          have hx_n : x < n := hx
          have hy_n : y < n := hy
          have hxp := hInv2.r_pref x (h7_eq ▸ hx_n)
          have hyp := hInv2.r_pref y (h7_eq ▸ hy_n)
          rcases hInv2.root_reach x hx_n (by omega) with ⟨Px, hPx⟩
          rcases hInv2.root_reach y hy_n (by omega) with ⟨Py, hPy⟩
          rw [heq] at hPx
          have hPxy : ∃ P, IsPathAlong G.edges x y P :=
            ⟨Px.dropLast ++ Py.reverse, isPathAlong_append hPx (isPathAlong_reverse hPy)⟩
          exact (compLabels_eq_iff_reachable hval (hn.symm ▸ hx_n) (hn.symm ▸ hy_n)).mpr hPxy
        · intro heq
          rcases (compLabels_eq_iff_reachable hval (hn.symm ▸ hx) (hn.symm ▸ hy)).mp heq with ⟨P, hP⟩
          exact isPathAlong_of_edges_mem hedge_eq hP
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, compMeas, compDoneEdges,
      Function.update_apply, Nat.reduceEqDiff, ite_false, ite_true, Nat.sub_zero]
    omega


lemma partsOf_eq_compLabels_of_fiber (G : Cited.Graph) (label : List ℕ)
    (_hlen : label.length = G.n)
    (hfiber : ∀ x < G.n, ∀ y < G.n,
      label.getD x 0 = label.getD y 0 ↔ (compLabels G).getD x 0 = (compLabels G).getD y 0) :
    Cited.partsOf G label = Cited.partsOf G (compLabels G) := by
  ext X
  simp only [Cited.partsOf, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    ext x
    simp only [Finset.mem_filter, Cited.Graph.verts, Finset.mem_range]
    exact and_congr_right fun hx => (hfiber x hx v (Finset.mem_range.mp hv)).symm
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    ext x
    simp only [Finset.mem_filter, Cited.Graph.verts, Finset.mem_range]
    exact and_congr_right fun hx => hfiber x hx v (Finset.mem_range.mp hv)

/-- Contract for `bfsLabelsProc`: `args = [n, m, csrAddr, queueBase, rootBase]`.
Computes a component labeling `label` of length `G.n` at `[rootBase, rootBase + G.n)`
with `Cited.partsOf G label = Cited.partsOf G (compLabels G)` in `O(n + m + 1)` time. -/
noncomputable def bfsLabelsContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n m csrAddr queueBase rootBase : ℕ) (G : Cited.Graph),
      args = [n, m, csrAddr, queueBase, rootBase] ∧
      G.n = n ∧ G.m = m ∧ G.IsValid ∧
      HasCsrAt mem csrAddr G ∧
      (csrAddr + 2 * n + 1 + 4 * m ≤ queueBase ∨ queueBase + n ≤ csrAddr) ∧
      (csrAddr + 2 * n + 1 + 4 * m ≤ rootBase ∨ rootBase + n ≤ csrAddr) ∧
      (queueBase + n ≤ rootBase ∨ rootBase + n ≤ queueBase) ∧
      csrAddr + 2 * n + 1 + 4 * m < 2 ^ w ∧
      queueBase + n < 2 ^ w ∧ rootBase + n < 2 ^ w ∧ 4 ≤ 2 ^ w
  post args mem _v mem' :=
    let n := args.getD 0 0
    let queueBase := args.getD 3 0
    let rootBase := args.getD 4 0
    (∀ addr, (addr < queueBase ∨ queueBase + n ≤ addr) →
      (addr < rootBase ∨ rootBase + n ≤ addr) → mem' addr = mem addr) ∧
    ∀ G : Cited.Graph, G.n = n → G.m = args.getD 1 0 → G.IsValid →
      HasCsrAt mem (args.getD 2 0) G →
      let label := (List.range n).map fun x => mem' (rootBase + x)
      label.length = G.n ∧
      (∀ x < G.n, mem' (rootBase + x) < G.n) ∧
      Cited.partsOf G label = Cited.partsOf G (compLabels G)
  cost args _mem := 152 * args.getD 0 0 + 92 * args.getD 1 0 + 40

private lemma reachable_of_hasCsrAt {mem : ℕ → ℕ} {csrAddr : ℕ} {G1 G2 : Cited.Graph}
    (h1 : HasCsrAt mem csrAddr G1) (h2 : HasCsrAt mem csrAddr G2)
    (hv1 : G1.IsValid) (hv2 : G2.IsValid) (hn : G1.n = G2.n) (_hm : G1.m = G2.m) :
    ∀ {u v : ℕ} {P : List ℕ}, IsPathAlong G1.edges u v P → ∃ Q, IsPathAlong G2.edges u v Q := by
  have hadj : ∀ {a b : ℕ}, (a, b) ∈ G1.edges → a = b ∨
      ((a, b) ∈ G2.edges ∨ (b, a) ∈ G2.edges) := by
    intro a b hab
    by_cases hne : a = b
    · left; exact hne
    · right
      rcases List.getElem?_of_mem hab with ⟨idx, hidx⟩
      have hidx_len : idx < G1.edges.length := (List.getElem?_eq_some_iff.mp hidx).1
      have ha1 : a < G1.n := (hv1 (a, b) hab).1
      have ha2 : a < G2.n := hn ▸ ha1
      have hm_mem := edge_mem_csrIncAux_of_ne (L := G1.edges) (k := idx) (r := 0)
        hidx_len hne (by simp [Walk.EdgeMatches, List.getD_eq_getElem?_getD, hidx])
      have hex_t1 : ∃ (t : ℕ) (ht : t < (csrIncAux a 0 G1.edges).length),
          ((csrIncAux a 0 G1.edges)[t]'ht).2.2 = b := by
        rcases hm_mem with h | h <;>
        · rcases List.getElem_of_mem h with ⟨t, ht, ht_eq⟩; exact ⟨t, ht, by rw [ht_eq]⟩
      rcases hex_t1 with ⟨t, ht1, ht1_eq⟩
      have hoff0 : csrOff G1 a = csrOff G2 a := by rw [← h1.1 a (Nat.le_of_lt ha1), h2.1 a (Nat.le_of_lt ha2)]
      have hoff1 : csrOff G1 (a + 1) = csrOff G2 (a + 1) := by rw [← h1.1 (a + 1) ha1, h2.1 (a + 1) ha2]
      have ht2 : t < (csrIncAux a 0 G2.edges).length := by
        have s1 := csrOff_succ G1 a; have s2 := csrOff_succ G2 a; omega
      have hmem_v1 := (h1.2 a ha1 t ht1).1
      have hmem_v2 := (h2.2 a ha2 t ht2).1
      have haddr_eq : csrAddr + 2 * G1.n + 1 + csrOff G1 a + t =
          csrAddr + 2 * G2.n + 1 + csrOff G2 a + t := by rw [hn, hoff0]
      rw [haddr_eq] at hmem_v1
      have hnbr2 : ((csrIncAux a 0 G2.edges)[t]'ht2).2.2 = b := by
        rw [← hmem_v2, hmem_v1, ht1_eq]
      have hem2 := (csrIncAux_edgeMatches hv2 ht2).2.2.2
      rw [hnbr2] at hem2
      have hlen2 : ((csrIncAux a 0 G2.edges)[t]'ht2).1 < G2.edges.length := by
        simpa [Cited.Graph.m] using (csrIncAux_edgeMatches hv2 ht2).1
      have he_mem2 : G2.edges.getD ((csrIncAux a 0 G2.edges)[t]'ht2).1 (0, 0) ∈ G2.edges := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen2, Option.getD_some]
        exact List.getElem_mem hlen2
      rcases hem2 with h | h
      · left; rwa [← h.1, ← h.2]
      · right; rwa [← h.1, ← h.2]
  intro u v P hP
  induction P generalizing u with
  | nil => simp [IsPathAlong] at hP
  | cons x rest ih =>
    rcases hP with ⟨hh, hl, hc⟩
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl; exact ⟨[x], isPathAlong_singleton _ _⟩
    | cons y ys =>
      rw [List.isChain_cons_cons] at hc
      rcases ih (u := y) ⟨rfl, hl, hc.2⟩ with ⟨Q, hQ⟩
      have hstep : x = y ∨ ((x, y) ∈ G2.edges ∨ (y, x) ∈ G2.edges) := by
        rcases hc.1 with h | h
        · exact hadj h
        · rcases hadj h with heq | hs
          · left; exact heq.symm
          · right; exact hs.symm
      rcases hstep with rfl | hxy
      · exact ⟨Q, hQ⟩
      · exact ⟨x :: Q, isPathAlong_cons hxy hQ⟩

theorem bfsLabels_spec (w : ℕ) (p : Program) (b : ℕ) (hp : p.HasAt b [bfsLabelsProc]) :
    MeetsContract w p b (bfsLabelsContract w) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨n, m, csrAddr, queueBase, rootBase, G, hargs, hn, hm, hval, hcsr,
      hdj_cq, hdj_cr, hdj_qr, hcsr_w, hq_w, hroot_w, hw4⟩
  subst hargs
  have hproc : p.procs[b]? = some bfsLabelsProc := by
    simpa using hp 0 (by simp)
  have htriple_core := bfsLabelsCore_triple (p := p) n m csrAddr queueBase rootBase G mem
    (startState [n, m, csrAddr, queueBase, rootBase] mem pos) hn hm hval hcsr hdj_cq hdj_cr hdj_qr
    hcsr_w hq_w hroot_w hw4
    (by simp [startState]) (by simp [startState]) (by simp [startState])
    (by simp [startState]) (by simp [startState]) rfl
  have hfull : Triple w p
      (fun st => st = startState [n, m, csrAddr, queueBase, rootBase] mem pos)
      bfsLabelsProc
      (fun o st' => o = Outcome.returned 0 ∧
        (bfsLabelsContract w).post [n, m, csrAddr, queueBase, rootBase] mem 0 st'.mem)
      (fun _ => 152 * n + 92 * m + 40) := by
    intro st ω' hs; rw [hs]; refine runs_start_le ?_
    dsimp only [bfsLabelsProc]
    refine runs_seq_triple_le htriple_core rfl (fun st' hst' => ?_)
    wram_run
    · refine ⟨rfl, ?_, fun G' hGn' hGm' hGval' hGcsr' => ?_⟩
      · simpa using hst'.2.2.1
      · have hGn : G'.n = n := by simpa [List.getD_eq_getElem?_getD] using hGn'
        have hGm : G'.m = m := by simpa [List.getD_eq_getElem?_getD] using hGm'
        obtain ⟨_, _, _, hlt, hfib⟩ := hst'
        let label := (List.range n).map fun x => st'.mem (rootBase + x)
        have hlen : label.length = G'.n := by simp [label, hGn]
        have hlt' : ∀ x < G'.n, st'.mem (rootBase + x) < G'.n := fun x hx =>
          hGn.symm ▸ hlt x (hGn ▸ hx)
        have hfib_G : ∀ x < G'.n, ∀ y < G'.n,
            label.getD x 0 = label.getD y 0 ↔ (compLabels G').getD x 0 = (compLabels G').getD y 0 := by
          intro x hx y hy
          have hxn : x < n := hGn ▸ hx
          have hyn : y < n := hGn ▸ hy
          have hlx : label.getD x 0 = st'.mem (rootBase + x) := by
            simp [label, List.getD_eq_getElem?_getD, hxn]
          have hly : label.getD y 0 = st'.mem (rootBase + y) := by
            simp [label, List.getD_eq_getElem?_getD, hyn]
          rw [hlx, hly, hfib x hxn y hyn,
            compLabels_eq_iff_reachable hval (hn.symm ▸ hxn) (hn.symm ▸ hyn),
            compLabels_eq_iff_reachable hGval' hx hy]
          exact ⟨fun ⟨P, hP⟩ => reachable_of_hasCsrAt hcsr hGcsr' hval hGval' (hn.trans hGn.symm) (hm.trans hGm.symm) hP,
            fun ⟨P, hP⟩ => reachable_of_hasCsrAt hGcsr' hcsr hGval' hval (hGn.trans hn.symm) (hGm.trans hm.symm) hP⟩
        exact ⟨hlen, hlt', partsOf_eq_compLabels_of_fiber G' label hlen hfib_G⟩
    · simp only [Expr.size_const]; omega
  obtain ⟨o, st', c, hrun, ⟨rfl, hpost⟩, hcost⟩ := hfull _ ω rfl
  refine ⟨bfsLabelsProc, hproc, .returned 0, st', c, hrun, ?_, ?_⟩
  · simpa [Outcome.value] using hpost
  · simpa [bfsLabelsContract] using hcost

/-! ## 7. Scatter Passes (3–6) for `bfsCompsProc` -/

/-- Vertices `< n` with label `root x = c`, in strictly increasing order. -/
def compVerts (n : ℕ) (root : ℕ → ℕ) (c : ℕ) : List ℕ :=
  (List.range n).filter (fun x => decide (root x = c))

/-- Roots `c < n` whose component has at least 2 vertices. -/
def compRoots (n : ℕ) (root : ℕ → ℕ) : List ℕ :=
  (List.range n).filter (fun c => decide (2 ≤ (compVerts n root c).length))

/-- Nontrivial connected components for `(n, root)`, strictly ordered. -/
def bfsCompsList (n : ℕ) (root : ℕ → ℕ) : List (List ℕ) :=
  (compRoots n root).map (compVerts n root)

/-- Exact output encoding of `bfsCompsProc` at `outAddr`. -/
def bfsCompsEncode (comps : List (List ℕ)) : List ℕ :=
  [comps.length] ++ comps.flatMap (fun c => c.length :: c)

lemma compVerts_pairwise_lt (n : ℕ) (root : ℕ → ℕ) (c : ℕ) :
    (compVerts n root c).Pairwise (· < ·) := by
  unfold compVerts
  refine List.Pairwise.filter _ ?_
  exact List.pairwise_lt_range

lemma mem_compVerts_iff {n : ℕ} {root : ℕ → ℕ} {c x : ℕ} :
    x ∈ compVerts n root c ↔ x < n ∧ root x = c := by
  simp [compVerts]

lemma bfsCompsList_mem_props {n : ℕ} {root : ℕ → ℕ} {cs : List ℕ}
    (hcs : cs ∈ bfsCompsList n root) :
    cs.Pairwise (· < ·) ∧ 2 ≤ cs.length ∧ ∀ x ∈ cs, x < n := by
  unfold bfsCompsList compRoots at hcs
  rcases List.mem_map.mp hcs with ⟨c, hc, rfl⟩
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
  exact ⟨compVerts_pairwise_lt n root c, hc.2, fun x hx => (mem_compVerts_iff.mp hx).1⟩

lemma bfsCompsList_pairwise_disjoint {n : ℕ} (root : ℕ → ℕ) :
    (bfsCompsList n root).Pairwise (fun a b => a.Disjoint b) := by
  unfold bfsCompsList compRoots
  rw [List.pairwise_map]
  refine List.Pairwise.imp ?_ (List.pairwise_lt_range.filter _)
  intro a b hab x hxa hxb
  have h1 := (mem_compVerts_iff.mp hxa).2
  have h2 := (mem_compVerts_iff.mp hxb).2
  omega

private def compOffset (outAddr n : ℕ) (root : ℕ → ℕ) (c : ℕ) : ℕ :=
  outAddr + 1 +
    (((List.range c).filter (fun c' => decide (2 ≤ (compVerts n root c').length))).map
      (fun c' => 1 + (compVerts n root c').length)).sum

private lemma filter_range_len_sum_le (n : ℕ) (root : ℕ → ℕ) :
    ∀ c, (((List.range c).filter (fun c' => decide (2 ≤ (compVerts n root c').length))).map
      (fun c' => (compVerts n root c').length)).sum ≤
      ((List.range n).filter (fun x => decide (root x < c))).length := by
  intro c
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append]
    have hr_split : ((List.range n).filter (fun x => decide (root x < c + 1))).length =
        ((List.range n).filter (fun x => decide (root x < c))).length +
        (compVerts n root c).length := by
      unfold compVerts
      clear ih
      induction (List.range n) with
      | nil => simp
      | cons y ys ihl =>
        simp only [List.filter_cons]
        by_cases h1 : root y < c
        · have h1' : root y < c + 1 := by omega
          have hne : root y ≠ c := by omega
          rw [decide_eq_true h1, decide_eq_true h1', decide_eq_false hne]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ihl]
          omega
        · by_cases h2 : root y = c
          · have h2' : root y < c + 1 := by omega
            rw [decide_eq_false h1, decide_eq_true h2', decide_eq_true h2]
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ihl]
            omega
          · have h3 : ¬ (root y < c + 1) := by omega
            rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3]
            simp only [Bool.false_eq_true, ↓reduceIte, ihl]
    rw [hr_split]
    simp only [List.filter_cons, List.filter_nil]
    by_cases h2 : 2 ≤ (compVerts n root c).length
    · simp only [h2, decide_true, ↓reduceIte,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at *
      omega
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_nil, List.sum_nil] at *
      omega

private lemma compOffset_step {outAddr n : ℕ} {root : ℕ → ℕ} {c : ℕ} :
    compOffset outAddr n root (c + 1) =
      compOffset outAddr n root c +
        (if 2 ≤ (compVerts n root c).length then 1 + (compVerts n root c).length else 0) := by
  unfold compOffset
  rw [List.range_succ, List.filter_append, List.map_append, List.sum_append]
  simp only [List.filter_cons, List.filter_nil]
  by_cases h2 : 2 ≤ (compVerts n root c).length
  · simp only [h2, decide_true, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, List.map_nil, List.sum_nil, add_zero]

private lemma compOffset_mono {outAddr n : ℕ} {root : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b) :
    compOffset outAddr n root a ≤ compOffset outAddr n root b := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (by rw [compOffset_step]; omega)

private lemma compOffset_le {outAddr n : ℕ} (root : ℕ → ℕ) (c : ℕ) :
    compOffset outAddr n root c ≤ outAddr + 1 + 2 * n := by
  unfold compOffset
  have h1 : (((List.range c).filter (fun c' => decide (2 ≤ (compVerts n root c').length))).map
      (fun c' => 1 + (compVerts n root c').length)).sum ≤
      2 * (((List.range c).filter (fun c' => decide (2 ≤ (compVerts n root c').length))).map
        (fun c' => (compVerts n root c').length)).sum := by
    generalize hf : (List.range c).filter (fun c' => decide (2 ≤ (compVerts n root c').length)) = L
    have hge : ∀ c' ∈ L, 2 ≤ (compVerts n root c').length := fun c' hc' => by
      rw [← hf] at hc'
      exact (List.mem_filter.mp hc').2 |> decide_eq_true_eq.mp
    clear hf
    induction L with
    | nil => simp
    | cons x xs ih =>
      have hx := hge x List.mem_cons_self
      have ih' := ih fun y hy => hge y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.sum_cons] at ih' ⊢
      omega
  have h2 := filter_range_len_sum_le n root c
  have h3 : ((List.range n).filter (fun x => decide (root x < c))).length ≤ n := by
    simpa [List.length_range] using List.length_filter_le (fun x => decide (root x < c)) (List.range n)
  omega

private lemma pass3_zero_loop {w : ℕ} {p : Program} (n workAddr outAddr sizeBase writePtrBase : ℕ)
    (root : ℕ → ℕ) (memBase : ℕ → ℕ)
    (hsize : sizeBase = workAddr + n) (hwp : writePtrBase = workAddr + 2 * n)
    (hwork_w : workAddr + 3 * n < 2 ^ w) (h1_w : 1 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 3 = sizeBase ∧ st.regs 5 = writePtrBase ∧
        st.regs 6 ≤ n ∧ st.regs 16 = outAddr ∧ st.regs 17 = workAddr ∧
        (∀ x < n, st.mem (workAddr + x) = root x) ∧
        MemFrame memBase st.mem workAddr (workAddr + 3 * n) ∧
        ∀ i < st.regs 6, st.mem (sizeBase + i) = 0)
      (.loop (.bin .lt (.reg 6) (.reg 0))
        (.seq (.store (.bin .add (.reg 3) (.reg 6)) (.const 0))
          (.assign 6 (.bin .add (.reg 6) (.const 1)))))
      (normalPost fun st' =>
        st'.regs 0 = n ∧ st'.regs 3 = sizeBase ∧ st'.regs 5 = writePtrBase ∧
        st'.regs 16 = outAddr ∧ st'.regs 17 = workAddr ∧
        (∀ x < n, st'.mem (workAddr + x) = root x) ∧
        MemFrame memBase st'.mem workAddr (workAddr + 3 * n) ∧
        ∀ i < n, st'.mem (sizeBase + i) = 0)
      (fun st => (3 + 10 + 1) * (n - st.regs 6) + 3 + 1) := by
  have h0_w : 0 < 2 ^ w := lt_of_lt_of_le (by decide : 0 < 4) hw4
  refine Triple.loop_const_normal (fun st => n - st.regs 6)
    (fun st => if st.regs 6 < st.regs 0 then 1 else 0) 10
    (fun st hInv => by have h0 := hInv.1; eval_expr)
    (fun st hInv h0 => by
      rcases hInv with ⟨hr0, hr3, hr5, h6le, h16, h17, hrt, hfr, hall⟩
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, hr0] at h0
      have h6eq : st.regs 6 = n := by clear hrt hfr hall; omega
      exact ⟨hr0, hr3, hr5, h16, h17, hrt, hfr, fun i hi => hall i (h6eq ▸ hi)⟩)
    (fun st hInv hne => by
      rcases hInv with ⟨hr0, hr3, hr5, h6le, h16, h17, hrt, hfr, hall⟩
      simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, hr0] at hne
      have haddr_w : sizeBase + st.regs 6 < 2 ^ w := by clear hrt hfr hall; omega
      have h61_w : st.regs 6 + 1 < 2 ^ w := by clear hrt hfr hall; omega
      intro s ω hs; rw [hs]; refine runs_start_le ?_
      have hea : (Expr.bin .add (.reg 3) (.reg 6)).eval w st = some (sizeBase + st.regs 6) := by
        simp [Expr.eval, BinOp.eval, hr3, haddr_w]
      have hev : (Expr.const 0).eval w st = some 0 := by simp [Expr.eval, h0_w]
      refine runs_seq_store_le hea hev ?_
      have he6 : (Expr.bin .add (.reg 6) (.const 1)).eval w
          { st with mem := Function.update st.mem (sizeBase + st.regs 6) 0 } = some (st.regs 6 + 1) := by
        simp [Expr.eval, BinOp.eval, h1_w, h61_w]
      refine runs_assign_le he6 ?_ ?_
      · dsimp only [normalPost]
        refine ⟨⟨hr0, hr3, hr5, by simp; clear hrt hfr hall; omega, h16, h17, ?_, ?_, ?_⟩,
          by simp; clear hrt hfr hall; omega⟩
        · intro x hx
          rw [Function.update_of_ne (by clear hrt hfr hall; omega)]; exact hrt x hx
        · exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
        · intro i hi
          rw [Function.update_self] at hi
          by_cases hir : i = st.regs 6
          · subst hir; rw [Function.update_self]
          · rw [Function.update_of_ne (by clear hrt hfr hall; omega)]; exact hall i (by clear hrt hfr hall; omega)
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega)

private lemma pass4_count_loop {w : ℕ} {p : Program} (n workAddr outAddr sizeBase writePtrBase : ℕ)
    (root : ℕ → ℕ) (memBase : ℕ → ℕ)
    (hroot_lt : ∀ x < n, root x < n)
    (hsize : sizeBase = workAddr + n) (hwp : writePtrBase = workAddr + 2 * n)
    (hwork_w : workAddr + 3 * n < 2 ^ w) (h1_w : 1 < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 3 = sizeBase ∧ st.regs 5 = writePtrBase ∧
        st.regs 6 ≤ n ∧ st.regs 16 = outAddr ∧ st.regs 17 = workAddr ∧
        (∀ x < n, st.mem (workAddr + x) = root x) ∧
        MemFrame memBase st.mem workAddr (workAddr + 3 * n) ∧
        ∀ c < n, st.mem (sizeBase + c) = ((List.range (st.regs 6)).filter (fun x => decide (root x = c))).length)
      (.loop (.bin .lt (.reg 6) (.reg 0))
        (seqStmts [
          .assign 7 (.load (.bin .add (.reg 17) (.reg 6))),
          .assign 8 (.load (.bin .add (.reg 3) (.reg 7))),
          .store (.bin .add (.reg 3) (.reg 7)) (.bin .add (.reg 8) (.const 1)),
          .assign 6 (.bin .add (.reg 6) (.const 1))]))
      (normalPost fun st' =>
        st'.regs 0 = n ∧ st'.regs 3 = sizeBase ∧ st'.regs 5 = writePtrBase ∧
        st'.regs 16 = outAddr ∧ st'.regs 17 = workAddr ∧
        (∀ x < n, st'.mem (workAddr + x) = root x) ∧
        MemFrame memBase st'.mem workAddr (workAddr + 3 * n) ∧
        ∀ c < n, st'.mem (sizeBase + c) = (compVerts n root c).length)
      (fun st => (3 + 24 + 1) * (n - st.regs 6) + 3 + 1) := by
  refine Triple.loop_const_normal (fun st => n - st.regs 6)
    (fun st => if st.regs 6 < st.regs 0 then 1 else 0) 24
    (fun st hInv => by have h0 := hInv.1; eval_expr)
    (fun st hInv h0 => by
      rcases hInv with ⟨hr0, hr3, hr5, h6le, h16, h17, hrt, hfr, hcnt⟩
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, hr0] at h0
      have h6eq : st.regs 6 = n := by clear hrt hfr hcnt; omega
      exact ⟨hr0, hr3, hr5, h16, h17, hrt, hfr, fun c hc => by
        simpa [compVerts, h6eq] using hcnt c hc⟩)
    (fun st hInv hne => by
      rcases hInv with ⟨hr0, hr3, hr5, h6le, h16, h17, hrt, hfr, hcnt⟩
      simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, hr0] at hne
      obtain ⟨c0, hc0_def⟩ : ∃ v, v = root (st.regs 6) := ⟨_, rfl⟩
      have hc0_n : c0 < n := hc0_def ▸ hroot_lt _ hne
      have hrt6 : st.mem (workAddr + st.regs 6) = c0 := (hrt _ hne).trans hc0_def.symm
      obtain ⟨sz0, hsz0_def⟩ : ∃ v, v = st.mem (sizeBase + c0) := ⟨_, rfl⟩
      have hsz0_le : sz0 ≤ st.regs 6 := by
        rw [hsz0_def, hcnt c0 hc0_n]
        simpa [List.length_range] using List.length_filter_le (fun x => decide (root x = c0)) (List.range (st.regs 6))
      have hw6_w : workAddr + st.regs 6 < 2 ^ w := by clear hrt hfr hcnt; omega
      have hsc_w : sizeBase + c0 < 2 ^ w := by clear hrt hfr hcnt; omega
      have hsz1_w : sz0 + 1 < 2 ^ w := by clear hrt hfr hcnt; omega
      have h61_w : st.regs 6 + 1 < 2 ^ w := by clear hrt hfr hcnt; omega
      intro s ω hs; rw [hs]; refine runs_start_le ?_
      have he7 : (Expr.load (.bin .add (.reg 17) (.reg 6))).eval w st = some c0 := by
        simp [Expr.eval, BinOp.eval, h17, hw6_w, hrt6]
      refine runs_seq_assign_le he7 ?_
      let st1 : State := { st with regs := Function.update st.regs 7 c0 }
      have he8 : (Expr.load (.bin .add (.reg 3) (.reg 7))).eval w st1 = some sz0 := by
        simp [Expr.eval, BinOp.eval, st1, hr3, hsc_w, hsz0_def]
      refine runs_seq_assign_le he8 ?_
      let st2 : State := { st1 with regs := Function.update st1.regs 8 sz0 }
      have hes_a : (Expr.bin .add (.reg 3) (.reg 7)).eval w st2 = some (sizeBase + c0) := by
        simp [Expr.eval, BinOp.eval, st2, st1, hr3, hsc_w]
      have hes_v : (Expr.bin .add (.reg 8) (.const 1)).eval w st2 = some (sz0 + 1) := by
        simp [Expr.eval, BinOp.eval, st2, h1_w, hsz1_w]
      refine runs_seq_store_le hes_a hes_v ?_
      have he6 : (Expr.bin .add (.reg 6) (.const 1)).eval w
          { st2 with mem := Function.update st2.mem (sizeBase + c0) (sz0 + 1) } =
          some (st.regs 6 + 1) := by
        simp [Expr.eval, BinOp.eval, st2, st1, h1_w, h61_w]
      refine runs_assign_le he6 ?_ ?_
      · dsimp only [normalPost]
        refine ⟨⟨hr0, hr3, hr5, by simp; clear hrt hfr hcnt; omega, h16, h17, ?_, ?_, ?_⟩,
          by simp; clear hrt hfr hcnt; omega⟩
        · intro x hx
          rw [Function.update_of_ne (by clear hrt hfr hcnt; omega)]; exact hrt x hx
        · exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
        · intro c hc
          rw [Function.update_self, List.range_succ, List.filter_append, List.length_append]
          by_cases hcc : c = c0
          · subst hcc
            rw [Function.update_self]
            simp only [List.filter_cons, List.filter_nil, ← hc0_def, decide_true, ↓reduceIte,
              List.length_singleton]
            rw [hsz0_def, hcnt c hc]
          · rw [Function.update_of_ne (by clear hrt hfr hcnt; omega)]
            have hne_rt : root (st.regs 6) ≠ c := by rw [← hc0_def]; exact Ne.symm hcc
            simp [hne_rt, hcnt c hc]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega)

private lemma pass5_prefix_loop {w : ℕ} {p : Program} (n workAddr outAddr sizeBase writePtrBase : ℕ)
    (root : ℕ → ℕ) (mem4 : ℕ → ℕ)
    (hsize : sizeBase = workAddr + n) (hwp : writePtrBase = workAddr + 2 * n)
    (hdj_wo : workAddr + 3 * n ≤ outAddr ∨ outAddr + 2 * n + 1 ≤ workAddr)
    (hmem4_sz : ∀ c < n, mem4 (sizeBase + c) = (compVerts n root c).length)
    (hwork_w : workAddr + 3 * n < 2 ^ w) (hout_w : outAddr + 2 * n + 1 < 2 ^ w)
    (h1_w : 1 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 3 = sizeBase ∧ st.regs 5 = writePtrBase ∧
        st.regs 6 ≤ n ∧
        st.regs 7 = ((List.range (st.regs 6)).filter (fun c => decide (2 ≤ (compVerts n root c).length))).length ∧
        st.regs 8 = compOffset outAddr n root (st.regs 6) ∧
        st.regs 16 = outAddr ∧ st.regs 17 = workAddr ∧
        (∀ addr, (addr < writePtrBase ∨ writePtrBase + n ≤ addr) →
          (addr < outAddr ∨ outAddr + 2 * n + 1 ≤ addr) → st.mem addr = mem4 addr) ∧
        ∀ c < st.regs 6, 2 ≤ (compVerts n root c).length →
          st.mem (compOffset outAddr n root c) = (compVerts n root c).length ∧
          st.mem (writePtrBase + c) = compOffset outAddr n root c + 1)
      (.loop (.bin .lt (.reg 6) (.reg 0))
        (seqStmts [
          .assign 9 (.load (.bin .add (.reg 3) (.reg 6))),
          .cond (.bin .lt (.const 1) (.reg 9))
            (seqStmts [
              .store (.reg 8) (.reg 9),
              .store (.bin .add (.reg 5) (.reg 6)) (.bin .add (.reg 8) (.const 1)),
              .assign 8 (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 9)),
              .assign 7 (.bin .add (.reg 7) (.const 1))])
            .nop,
          .assign 6 (.bin .add (.reg 6) (.const 1))]))
      (normalPost fun st' =>
        st'.regs 0 = n ∧ st'.regs 3 = sizeBase ∧ st'.regs 5 = writePtrBase ∧
        st'.regs 6 = n ∧ st'.regs 7 = (bfsCompsList n root).length ∧
        st'.regs 8 = compOffset outAddr n root n ∧
        st'.regs 16 = outAddr ∧ st'.regs 17 = workAddr ∧
        (∀ addr, (addr < writePtrBase ∨ writePtrBase + n ≤ addr) →
          (addr < outAddr ∨ outAddr + 2 * n + 1 ≤ addr) → st'.mem addr = mem4 addr) ∧
        ∀ c < n, 2 ≤ (compVerts n root c).length →
          st'.mem (compOffset outAddr n root c) = (compVerts n root c).length ∧
          st'.mem (writePtrBase + c) = compOffset outAddr n root c + 1)
      (fun st => (3 + 38 + 1) * (n - st.regs 6) + 3 + 1) := by
  refine Triple.loop_const_normal (fun st => n - st.regs 6)
    (fun st => if st.regs 6 < st.regs 0 then 1 else 0) 38
    (fun st hInv => by have h0 := hInv.1; eval_expr)
    (fun st hInv h0 => by
      rcases hInv with ⟨hr0, hr3, hr5, h6le, h7, h8, h16, h17, hfr2, hc_inv⟩
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, hr0] at h0
      have h6eq : st.regs 6 = n := by clear hfr2 hc_inv; omega
      refine ⟨hr0, hr3, hr5, h6eq, ?_, by rw [h6eq] at h8; exact h8, h16, h17, hfr2, fun c hc h2 => hc_inv c (h6eq ▸ hc) h2⟩
      rw [h7, h6eq]; simp [bfsCompsList, compRoots])
    (fun st hInv hne => by
      rcases hInv with ⟨hr0, hr3, hr5, h6le, h7, h8, h16, h17, hfr2, hc_inv⟩
      simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, hr0] at hne
      obtain ⟨c, hc_def⟩ : ∃ v, v = st.regs 6 := ⟨_, rfl⟩
      obtain ⟨sz, hsz_def⟩ : ∃ v, v = (compVerts n root c).length := ⟨_, rfl⟩
      have hsz_le : sz ≤ n := by
        rw [hsz_def]; simpa [compVerts, List.length_range] using List.length_filter_le _ (List.range n)
      have hmem_sz : st.mem (sizeBase + c) = sz := by
        rw [hfr2 _ (by clear hfr2 hc_inv; omega)
          (by rcases hdj_wo with h | h <;> [left; right] <;> (clear hfr2 hc_inv; omega)),
          hmem4_sz c (hc_def ▸ hne), hsz_def]
      have hsz_eq_mem : st.mem (sizeBase + st.regs 6) = sz := by rw [← hc_def, hmem_sz]
      have hsc_w : sizeBase + c < 2 ^ w := by clear hfr2 hc_inv; omega
      have h61_w : c + 1 < 2 ^ w := by clear hfr2 hc_inv; omega
      have hc_le_n : c < n := hc_def ▸ hne
      have h7_le : st.regs 7 ≤ c := by
        rw [h7, ← hc_def]
        simpa [List.length_range] using List.length_filter_le _ (List.range c)
      have hoff_ge : outAddr + 1 ≤ compOffset outAddr n root c := by
        dsimp only [compOffset]; omega
      have hoff_next_le : compOffset outAddr n root (c + 1) ≤ outAddr + 1 + 2 * n :=
        compOffset_le root (c + 1)
      have hoff_step := @compOffset_step outAddr n root c
      have h8_w : 1 < sz → st.regs 8 + 1 + sz < 2 ^ w := by
        intro h1sz
        rw [h8, ← hc_def]
        have h2l : 2 ≤ (compVerts n root c).length := hsz_def ▸ h1sz
        have : compOffset outAddr n root (c + 1) = compOffset outAddr n root c + 1 + sz := by
          rw [hoff_step]; simp only [h2l, ↓reduceIte]; omega
        linarith only [this, hoff_next_le, hout_w]
      have hwp_w : writePtrBase + c < 2 ^ w := by clear hfr2 hc_inv; omega
      have h71_w : st.regs 7 + 1 < 2 ^ w := by linarith only [h7_le, hc_le_n, hout_w]
      have h8_1_w : 1 < sz → st.regs 8 + 1 < 2 ^ w := fun h1sz => by linarith only [h8_w h1sz]
      have hw0 : w ≠ 0 := fun h => by simp [h] at hw4
      intro s ω hs; rw [hs]; refine runs_start_le ?_
      have he9 : (Expr.load (.bin .add (.reg 3) (.reg 6))).eval w st = some sz := by
        simp [Expr.eval, BinOp.eval, hr3, ← hc_def, hsc_w, hmem_sz]
      refine runs_seq_assign_le he9 ?_
      let st1 : State := { st with regs := Function.update st.regs 9 sz }
      have h0_w : (if 1 < sz then 1 else 0) < 2 ^ w := by split_ifs <;> linarith only [h1_w]
      have hec : (Expr.bin .lt (.const 1) (.reg 9)).eval w st1 = some (if 1 < sz then 1 else 0) := by
        simp [Expr.eval, BinOp.eval, st1, h0_w, hw0]
      have hcond_triple : Triple w p (fun s => s = st1)
          (.cond (.bin .lt (.const 1) (.reg 9))
            (seqStmts [
              .store (.reg 8) (.reg 9),
              .store (.bin .add (.reg 5) (.reg 6)) (.bin .add (.reg 8) (.const 1)),
              .assign 8 (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 9)),
              .assign 7 (.bin .add (.reg 7) (.const 1))])
            .nop)
          (normalPost fun st2 =>
            (1 < sz →
              (∀ reg ≤ 5, st2.regs reg = st.regs reg) ∧ st2.regs 6 = c ∧
              st2.regs 7 = st.regs 7 + 1 ∧ st2.regs 8 = st.regs 8 + 1 + sz ∧
              st2.regs 16 = outAddr ∧ st2.regs 17 = workAddr ∧
              st2.mem = Function.update (Function.update st.mem (st.regs 8) sz)
                (writePtrBase + c) (st.regs 8 + 1)) ∧
            (¬ 1 < sz →
              (∀ reg ≤ 8, st2.regs reg = st.regs reg) ∧
              st2.regs 16 = outAddr ∧ st2.regs 17 = workAddr ∧ st2.mem = st.mem))
          (fun _ => 27) := by
        intro s ω' hs; subst hs; refine runs_start_le ?_
        refine runs_cond_le hec ?_ ?_
        · intro hne2
          have h1sz : 1 < sz := by
            simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne2
            exact hne2
          have hs1_a : (Expr.reg 8).eval w st1 = some (st.regs 8) := by simp [Expr.eval, st1]
          have hs1_v : (Expr.reg 9).eval w st1 = some sz := by simp [Expr.eval, st1]
          refine runs_seq_store_le hs1_a hs1_v ?_
          have hs2_a : (Expr.bin .add (.reg 5) (.reg 6)).eval w
              { st1 with mem := Function.update st1.mem (st.regs 8) sz } = some (writePtrBase + c) := by
            simp [Expr.eval, BinOp.eval, st1, hr5, ← hc_def, hwp_w]
          have hs2_v : (Expr.bin .add (.reg 8) (.const 1)).eval w
              { st1 with mem := Function.update st1.mem (st.regs 8) sz } = some (st.regs 8 + 1) := by
            simp [Expr.eval, BinOp.eval, st1, h1_w, h8_1_w h1sz]
          refine runs_seq_store_le hs2_a hs2_v ?_
          let mem1a : ℕ → ℕ := Function.update (Function.update st1.mem (st.regs 8) sz) (writePtrBase + c) (st.regs 8 + 1)
          have hea8 : (Expr.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 9)).eval w { st1 with mem := mem1a } =
              some (st.regs 8 + 1 + sz) := by
            simp [Expr.eval, BinOp.eval, st1, h1_w, h8_w h1sz, h8_1_w h1sz]
          refine runs_seq_assign_le hea8 ?_
          let st1a : State := { st1 with
            regs := Function.update st1.regs 8 (st.regs 8 + 1 + sz),
            mem := Function.update (Function.update st1.mem (st.regs 8) sz)
              (writePtrBase + c) (st.regs 8 + 1) }
          have hea7 : (Expr.bin .add (.reg 7) (.const 1)).eval w st1a = some (st.regs 7 + 1) := by
            simp [Expr.eval, BinOp.eval, st1a, st1, h1_w, h71_w]
          refine runs_assign_le hea7 ?_ ?_
          · dsimp only [normalPost]
            refine ⟨fun _ => ⟨fun reg hr => by
                rw [Function.update_of_ne (by omega : reg ≠ 7)]; simp [st1,
                  Function.update_of_ne (by omega : reg ≠ 8), Function.update_of_ne (by omega : reg ≠ 9)],
              by rw [Function.update_of_ne (by decide : (6 : ℕ) ≠ 7)]; simp [st1, ← hc_def],
              by simp, by simp [st1],
              by rw [Function.update_of_ne (by decide : (16 : ℕ) ≠ 7)]; simp [st1, h16],
              by rw [Function.update_of_ne (by decide : (17 : ℕ) ≠ 7)]; simp [st1, h17],
              rfl⟩, fun hn => False.elim (hn h1sz)⟩
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega
        · intro h02
          have hn1sz : ¬ 1 < sz := by
            simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h02
            exact h02
          refine runs_nop_le ?_ ?_
          · dsimp only [normalPost]
            refine ⟨fun h => False.elim (hn1sz h), fun _ => ⟨fun reg hr => by
                simp [st1, Function.update_of_ne (by omega : reg ≠ 9)],
              by simp [st1, h16], by simp [st1, h17], rfl⟩⟩
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega
      refine runs_seq_triple_le hcond_triple rfl (fun st2 h2p => ?_)
      rcases h2p with ⟨hbranch, hskip⟩
      have h6_2 : st2.regs 6 = c := by
        by_cases h : 1 < sz
        · exact (hbranch h).2.1
        · rw [(hskip h).1 6 (by omega), hc_def]
      have he6 : (Expr.bin .add (.reg 6) (.const 1)).eval w st2 = some (c + 1) := by
        simp [Expr.eval, BinOp.eval, h6_2, h1_w, h61_w]
      refine runs_assign_le he6 ?_ ?_
      · dsimp only [normalPost]
        by_cases h : 1 < sz
        · obtain ⟨hle5, _, h7', h8', h16', h17', hmem'⟩ := hbranch h
          have hc2 : 2 ≤ (compVerts n root c).length := by rw [← hsz_def]; omega
          have hoff_eq_c : st.regs 8 = compOffset outAddr n root c := by rw [h8, ← hc_def]
          refine ⟨⟨by rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 6), hle5 0 (by omega), hr0],
              by rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 6), hle5 3 (by omega), hr3],
              by rw [Function.update_of_ne (by decide : (5 : ℕ) ≠ 6), hle5 5 (by omega), hr5],
              by simp; clear hfr2 hc_inv; omega, ?_, ?_,
              by rw [Function.update_of_ne (by decide : (16 : ℕ) ≠ 6), h16'],
              by rw [Function.update_of_ne (by decide : (17 : ℕ) ≠ 6), h17'], ?_, ?_⟩,
            by simp; rw [← hc_def]; clear hfr2 hc_inv; omega⟩
          · rw [Function.update_self, Function.update_of_ne (by decide : (7 : ℕ) ≠ 6), h7', h7, ← hc_def,
              List.range_succ, List.filter_append, List.length_append]
            simp [hc2]
          · rw [Function.update_self, Function.update_of_ne (by decide : (8 : ℕ) ≠ 6), h8', h8, ← hc_def, hoff_step]
            simp only [hc2, ↓reduceIte]
            rw [← hsz_def]
            clear hfr2 hc_inv; omega
          · intro addr ha1 ha2
            have hoff_next_ub : compOffset outAddr n root c + 1 + sz ≤ outAddr + 1 + 2 * n := by
              rw [hoff_step] at hoff_next_le
              simp only [hc2, ↓reduceIte] at hoff_next_le
              rw [← hsz_def] at hoff_next_le
              omega
            have hco_lt_end : compOffset outAddr n root c < outAddr + 2 * n + 1 := by
              linarith only [hoff_next_ub, h]
            have hco_gt : outAddr + 1 ≤ compOffset outAddr n root c := by
              dsimp [compOffset]; omega
            rw [hmem', Function.update_of_ne (by
                intro heq
                rcases ha1 with h1 | h2
                · linarith only [h1, heq]
                · linarith only [h2, heq, hc_le_n]),
              Function.update_of_ne (by
                rw [hoff_eq_c]; intro heq
                rcases ha2 with h1 | h2 <;> [linarith only [h1, hco_gt, heq]; linarith only [h2, hco_lt_end, heq]])]
            exact hfr2 addr ha1 ha2
          · intro c' hc' hc2'
            have hc'_lt : c' < c + 1 := by simpa using hc'
            have hoff_next_ub : compOffset outAddr n root c + 1 + sz ≤ outAddr + 1 + 2 * n := by
              rw [hoff_step] at hoff_next_le
              simp only [hc2, ↓reduceIte] at hoff_next_le
              rw [← hsz_def] at hoff_next_le
              omega
            have hco_lt_end : compOffset outAddr n root c < outAddr + 2 * n + 1 := by
              linarith only [hoff_next_ub, h]
            by_cases hcc' : c' = c
            · subst hcc'
              rw [hmem', hoff_eq_c]
              have hne_ow : compOffset outAddr n root c' ≠ writePtrBase + c' := by
                rcases hdj_wo with h1 | h2
                · linarith only [h1, hoff_ge, hwp, hc_le_n]
                · linarith only [h2, hco_lt_end, hwp]
              exact ⟨by rw [Function.update_of_ne hne_ow, Function.update_self, hsz_def],
                by rw [Function.update_self]⟩
            · have hlt' : c' < c := by omega
              obtain ⟨hco, hcw⟩ := hc_inv c' (hc_def ▸ hlt') hc2'
              have hdiff : compOffset outAddr n root c' + 1 + (compVerts n root c').length ≤
                  compOffset outAddr n root c := by
                have := compOffset_mono (outAddr := outAddr) (n := n) (root := root)
                  (Nat.succ_le_of_lt hlt')
                have hs' := @compOffset_step outAddr n root c'
                rw [hs'] at this; simp only [hc2', ↓reduceIte] at this; omega
              have hco'_gt : outAddr + 1 ≤ compOffset outAddr n root c' := by
                dsimp [compOffset]; omega
              have hne_c'_wp : compOffset outAddr n root c' ≠ writePtrBase + c := by
                rcases hdj_wo with h1 | h2
                · linarith only [h1, hco'_gt, hwp, hc_le_n]
                · linarith only [h2, hco_lt_end, hdiff, hwp]
              have hne_c'_8 : compOffset outAddr n root c' ≠ st.regs 8 := by
                rw [hoff_eq_c]; linarith only [hdiff]
              have hne_wp'_wp : writePtrBase + c' ≠ writePtrBase + c := by omega
              have hne_wpo : writePtrBase + c' ≠ st.regs 8 := by
                rw [hoff_eq_c]
                rcases hdj_wo with h1 | h2
                · linarith only [h1, hoff_ge, hwp, hlt', hc_le_n]
                · linarith only [h2, hco_lt_end, hwp]
              rw [hmem', Function.update_of_ne hne_c'_wp, Function.update_of_ne hne_c'_8]
              refine ⟨hco, ?_⟩
              rw [Function.update_of_ne hne_wp'_wp, Function.update_of_ne hne_wpo]
              exact hcw
        · obtain ⟨hle8, h16', h17', hmem'⟩ := hskip h
          have hnc2 : ¬ 2 ≤ (compVerts n root c).length := by rw [← hsz_def]; omega
          refine ⟨⟨by rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 6), hle8 0 (by omega), hr0],
              by rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 6), hle8 3 (by omega), hr3],
              by rw [Function.update_of_ne (by decide : (5 : ℕ) ≠ 6), hle8 5 (by omega), hr5],
              by simp; clear hfr2 hc_inv; omega, ?_, ?_,
              by rw [Function.update_of_ne (by decide : (16 : ℕ) ≠ 6), h16'],
              by rw [Function.update_of_ne (by decide : (17 : ℕ) ≠ 6), h17'],
              by rw [hmem']; exact hfr2,
              fun c' hc' hc2' => by
                have hc'_lt : c' < c + 1 := by simpa using hc'
                have hlt' : c' < c := by
                  have hne_c : c' ≠ c := fun heq => hnc2 (heq ▸ hc2')
                  omega
                rw [hmem']; exact hc_inv c' (hc_def ▸ hlt') hc2'⟩,
            by simp; rw [← hc_def]; clear hfr2 hc_inv; omega⟩
          · rw [Function.update_self, Function.update_of_ne (by decide : (7 : ℕ) ≠ 6), hle8 7 (by omega), h7, ← hc_def,
              List.range_succ, List.filter_append, List.length_append]
            simp [hnc2]
          · rw [Function.update_self, Function.update_of_ne (by decide : (8 : ℕ) ≠ 6), hle8 8 le_rfl, h8, ← hc_def, hoff_step]
            simp only [hnc2, ↓reduceIte, Nat.add_zero]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega)

private lemma pass6_scatter_loop {w : ℕ} {p : Program} (n workAddr outAddr sizeBase writePtrBase : ℕ)
    (root : ℕ → ℕ) (mem5 : ℕ → ℕ)
    (hroot_lt : ∀ x < n, root x < n)
    (hsize : sizeBase = workAddr + n) (hwp : writePtrBase = workAddr + 2 * n)
    (hdj_wo : workAddr + 3 * n ≤ outAddr ∨ outAddr + 2 * n + 1 ≤ workAddr)
    (hmem5_rt : ∀ x < n, mem5 (workAddr + x) = root x)
    (hmem5_sz : ∀ c < n, mem5 (sizeBase + c) = (compVerts n root c).length)
    (hwork_w : workAddr + 3 * n < 2 ^ w) (hout_w : outAddr + 2 * n + 1 < 2 ^ w)
    (h1_w : 1 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 3 = sizeBase ∧ st.regs 5 = writePtrBase ∧
        st.regs 6 ≤ n ∧ st.regs 8 = compOffset outAddr n root n ∧
        st.regs 16 = outAddr ∧ st.regs 17 = workAddr ∧
        st.mem outAddr = (bfsCompsList n root).length ∧
        (∀ addr, (addr < writePtrBase ∨ writePtrBase + n ≤ addr) →
          (addr < outAddr ∨ outAddr + 2 * n + 1 ≤ addr) → st.mem addr = mem5 addr) ∧
        ∀ c < n, 2 ≤ (compVerts n root c).length →
          st.mem (compOffset outAddr n root c) = (compVerts n root c).length ∧
          st.mem (writePtrBase + c) = compOffset outAddr n root c + 1 +
            ((List.range (st.regs 6)).filter (fun y => decide (root y = c))).length ∧
          ∀ j, (hj : j < ((List.range (st.regs 6)).filter (fun y => decide (root y = c))).length) →
            st.mem (compOffset outAddr n root c + 1 + j) =
              ((List.range (st.regs 6)).filter (fun y => decide (root y = c)))[j]'hj)
      (.loop (.bin .lt (.reg 6) (.reg 0))
        (seqStmts [
          .assign 7 (.load (.bin .add (.reg 17) (.reg 6))),
          .assign 9 (.load (.bin .add (.reg 3) (.reg 7))),
          .cond (.bin .lt (.const 1) (.reg 9))
            (seqStmts [
              .assign 10 (.load (.bin .add (.reg 5) (.reg 7))),
              .store (.reg 10) (.reg 6),
              .store (.bin .add (.reg 5) (.reg 7)) (.bin .add (.reg 10) (.const 1))])
            .nop,
          .assign 6 (.bin .add (.reg 6) (.const 1))]))
      (normalPost fun st' =>
        st'.regs 0 = n ∧ st'.regs 8 = compOffset outAddr n root n ∧
        st'.regs 16 = outAddr ∧ st'.regs 17 = workAddr ∧
        st'.mem outAddr = (bfsCompsList n root).length ∧
        (∀ addr, (addr < writePtrBase ∨ writePtrBase + n ≤ addr) →
          (addr < outAddr ∨ outAddr + 2 * n + 1 ≤ addr) → st'.mem addr = mem5 addr) ∧
        ∀ c < n, 2 ≤ (compVerts n root c).length →
          st'.mem (compOffset outAddr n root c) = (compVerts n root c).length ∧
          ∀ j, (hj : j < (compVerts n root c).length) →
            st'.mem (compOffset outAddr n root c + 1 + j) = (compVerts n root c)[j]'hj)
      (fun st => (3 + 38 + 1) * (n - st.regs 6) + 3 + 1) := by
  have pref_lt_comp : ∀ x < n,
      ((List.range x).filter (fun y => decide (root y = root x))).length < (compVerts n root (root x)).length := by
    intro x hx
    have hsplit : List.range x ++ x :: (List.range (n - (x + 1))).map (· + (x + 1)) = List.range n := by
      have hm_eq : n = x + 1 + (n - (x + 1)) := by omega
      obtain ⟨m, rfl⟩ : ∃ m, n = x + 1 + m := ⟨n - (x + 1), hm_eq⟩
      clear hm_eq hx hroot_lt hsize hwp hdj_wo hmem5_rt hmem5_sz hwork_w hout_w h1_w hw4
      simp only [Nat.add_sub_cancel_left]
      induction m with
      | zero => simp [List.range_succ]
      | succ k ih =>
        conv_rhs => rw [show x + 1 + (k + 1) = (x + 1 + k) + 1 by omega, List.range_succ, ← ih]
        rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc, List.cons_append]
        congr 2; simp [Nat.add_comm]
    unfold compVerts
    rw [← hsplit, List.filter_append, List.filter_cons]
    simp only [decide_true, ↓reduceIte, List.length_append, List.length_cons]
    omega
  refine Triple.loop_const_normal (fun st => n - st.regs 6)
    (fun st => if st.regs 6 < st.regs 0 then 1 else 0) 38
    (fun st hInv => by have h0 := hInv.1; eval_expr)
    (fun st hInv h0 => by
      rcases hInv with ⟨hr0, hr3, hr5, h6le, h8, h16, h17, ho0, hfr2, hc_inv⟩
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, hr0] at h0
      have h6eq : st.regs 6 = n := by clear hfr2 hc_inv hmem5_rt hmem5_sz; omega
      refine ⟨hr0, h8, h16, h17, ho0, hfr2, fun c hc h2 => ?_⟩
      obtain ⟨hco, _, hcj⟩ := hc_inv c hc h2
      refine ⟨hco, fun j hj => ?_⟩
      have hj' : j < ((List.range (st.regs 6)).filter (fun y => decide (root y = c))).length := by
        simpa [compVerts, h6eq] using hj
      have := hcj j hj'
      have heq_get : ((List.range (st.regs 6)).filter (fun y => decide (root y = c)))[j]'hj' =
          (compVerts n root c)[j]'hj := by
        simp [compVerts, h6eq]
      rwa [heq_get] at this)
    (fun st hInv hne => by
      rcases hInv with ⟨hr0, hr3, hr5, h6le, h8, h16, h17, ho0, hfr2, hc_inv⟩
      simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, hr0] at hne
      obtain ⟨x, hx_def⟩ : ∃ v, v = st.regs 6 := ⟨_, rfl⟩
      have hx_n : x < n := hx_def ▸ hne
      obtain ⟨c0, hc0_def⟩ : ∃ v, v = root x := ⟨_, rfl⟩
      have hc0_n : c0 < n := hc0_def ▸ hroot_lt x hx_n
      obtain ⟨sz, hsz_def⟩ : ∃ v, v = (compVerts n root c0).length := ⟨_, rfl⟩
      have hmem_rt : st.mem (workAddr + x) = c0 := by
        rw [hfr2 _ (by clear hfr2 hc_inv; omega)
          (by rcases hdj_wo with h1 | h2 <;> [left; right] <;> (clear hfr2 hc_inv; omega)),
          hmem5_rt x hx_n, hc0_def]
      have hmem_sz : st.mem (sizeBase + c0) = sz := by
        rw [hfr2 _ (by clear hfr2 hc_inv; omega)
          (by rcases hdj_wo with h1 | h2 <;> [left; right] <;> (clear hfr2 hc_inv; omega)),
          hmem5_sz c0 hc0_n, hsz_def]
      have hwx_w : workAddr + x < 2 ^ w := by clear hfr2 hc_inv; omega
      have hsc_w : sizeBase + c0 < 2 ^ w := by clear hfr2 hc_inv; omega
      have hwc_w : writePtrBase + c0 < 2 ^ w := by clear hfr2 hc_inv; omega
      have hx1_w : x + 1 < 2 ^ w := by clear hfr2 hc_inv; omega
      have hw0 : w ≠ 0 := fun h => by simp [h] at hw4
      intro s ω hs; rw [hs]; refine runs_start_le ?_
      have he7 : (Expr.load (.bin .add (.reg 17) (.reg 6))).eval w st = some c0 := by
        simp [Expr.eval, BinOp.eval, h17, ← hx_def, hwx_w, hmem_rt]
      refine runs_seq_assign_le he7 ?_
      let st1 : State := { st with regs := Function.update st.regs 7 c0 }
      have he9 : (Expr.load (.bin .add (.reg 3) (.reg 7))).eval w st1 = some sz := by
        simp [Expr.eval, BinOp.eval, st1, hr3, hsc_w, hmem_sz]
      refine runs_seq_assign_le he9 ?_
      let st2 : State := { st1 with regs := Function.update st1.regs 9 sz }
      have h0_w : (if 1 < sz then 1 else 0) < 2 ^ w := by split_ifs <;> linarith only [h1_w]
      have hec : (Expr.bin .lt (.const 1) (.reg 9)).eval w st2 = some (if 1 < sz then 1 else 0) := by
        simp [Expr.eval, BinOp.eval, st2, h0_w, hw0]
      have hcond_triple : Triple w p (fun s => s = st2)
          (.cond (.bin .lt (.const 1) (.reg 9))
            (seqStmts [
              .assign 10 (.load (.bin .add (.reg 5) (.reg 7))),
              .store (.reg 10) (.reg 6),
              .store (.bin .add (.reg 5) (.reg 7)) (.bin .add (.reg 10) (.const 1))])
            .nop)
          (normalPost fun st3 =>
            (1 < sz →
              (∀ reg ≤ 6, st3.regs reg = st.regs reg) ∧ st3.regs 8 = st.regs 8 ∧
              st3.regs 16 = outAddr ∧ st3.regs 17 = workAddr ∧
              st3.mem = Function.update (Function.update st.mem (st.mem (writePtrBase + c0)) x)
                (writePtrBase + c0) (st.mem (writePtrBase + c0) + 1)) ∧
            (¬ 1 < sz →
              (∀ reg ≤ 6, st3.regs reg = st.regs reg) ∧ st3.regs 8 = st.regs 8 ∧
              st3.regs 16 = outAddr ∧ st3.regs 17 = workAddr ∧ st3.mem = st.mem))
          (fun _ => 21) := by
        intro s ω' hs; subst hs; refine runs_start_le ?_
        refine runs_cond_le hec ?_ ?_
        · intro hne2
          have h1sz : 1 < sz := by
            simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne2
            exact hne2
          have hc2 : 2 ≤ (compVerts n root c0).length := by rw [← hsz_def]; omega
          obtain ⟨_, hwp_eq, _⟩ := hc_inv c0 hc0_n hc2
          have hpref_lt : ((List.range x).filter (fun y => decide (root y = c0))).length < sz := by
            rw [hsz_def, hc0_def]; exact pref_lt_comp x hx_n
          have hptr_eq : st.mem (writePtrBase + c0) = compOffset outAddr n root c0 + 1 +
              ((List.range x).filter (fun y => decide (root y = c0))).length := by
            rw [hwp_eq, ← hx_def]
          have hptr_lt_next : st.mem (writePtrBase + c0) < compOffset outAddr n root (c0 + 1) := by
            have hs' := @compOffset_step outAddr n root c0
            rw [hs']; simp only [hc2, ↓reduceIte]; rw [← hsz_def]
            clear hfr2 hc_inv hmem5_rt hmem5_sz; omega
          have hptr_le_max : compOffset outAddr n root (c0 + 1) ≤ outAddr + 1 + 2 * n :=
            compOffset_le root (c0 + 1)
          have hptr_w : st.mem (writePtrBase + c0) < 2 ^ w := by linarith only [hptr_lt_next, hptr_le_max, hout_w]
          have hptr1_w : st.mem (writePtrBase + c0) + 1 < 2 ^ w := by linarith only [hptr_lt_next, hptr_le_max, hout_w]
          have he10 : (Expr.load (.bin .add (.reg 5) (.reg 7))).eval w st2 =
              some (st.mem (writePtrBase + c0)) := by
            simp [Expr.eval, BinOp.eval, st2, st1, hr5, hwc_w]
          refine runs_seq_assign_le he10 ?_
          let st3 : State := { st2 with regs := Function.update st2.regs 10 (st.mem (writePtrBase + c0)) }
          have hs1_a : (Expr.reg 10).eval w st3 = some (st.mem (writePtrBase + c0)) := by
            simp [Expr.eval, st3]
          have hs1_v : (Expr.reg 6).eval w st3 = some x := by
            simp [Expr.eval, st3, st2, st1, ← hx_def]
          refine runs_seq_store_le hs1_a hs1_v ?_
          have hs2_a : (Expr.bin .add (.reg 5) (.reg 7)).eval w
              { st3 with mem := Function.update st3.mem (st.mem (writePtrBase + c0)) x } =
              some (writePtrBase + c0) := by
            simp [Expr.eval, BinOp.eval, st3, st2, st1, hr5, hwc_w]
          have hs2_v : (Expr.bin .add (.reg 10) (.const 1)).eval w
              { st3 with mem := Function.update st3.mem (st.mem (writePtrBase + c0)) x } =
              some (st.mem (writePtrBase + c0) + 1) := by
            simp [Expr.eval, BinOp.eval, st3, h1_w, hptr1_w]
          refine runs_store_le hs2_a hs2_v ?_ ?_
          · dsimp only [normalPost]
            refine ⟨fun _ => ⟨fun reg hreg => by
                simp only [st2, st1, Function.update_of_ne (by omega : reg ≠ 10),
                  Function.update_of_ne (by omega : reg ≠ 9), Function.update_of_ne (by omega : reg ≠ 7)],
              by simp only [st2, st1, Function.update_of_ne (by decide : (8 : ℕ) ≠ 10),
                Function.update_of_ne (by decide : (8 : ℕ) ≠ 9), Function.update_of_ne (by decide : (8 : ℕ) ≠ 7)],
              by simp only [st2, st1, h16, Function.update_of_ne (by decide : (16 : ℕ) ≠ 10),
                Function.update_of_ne (by decide : (16 : ℕ) ≠ 9), Function.update_of_ne (by decide : (16 : ℕ) ≠ 7)],
              by simp only [st2, st1, h17, Function.update_of_ne (by decide : (17 : ℕ) ≠ 10),
                Function.update_of_ne (by decide : (17 : ℕ) ≠ 9), Function.update_of_ne (by decide : (17 : ℕ) ≠ 7)],
              rfl⟩,
              fun hn => False.elim (hn h1sz)⟩
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
        · intro h02
          have hn1sz : ¬ 1 < sz := by
            simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h02
            exact h02
          refine runs_nop_le ?_ ?_
          · dsimp only [normalPost]
            refine ⟨fun h => False.elim (hn1sz h), fun _ => ⟨fun reg hreg => by
                simp only [st2, st1, Function.update_of_ne (by omega : reg ≠ 9),
                  Function.update_of_ne (by omega : reg ≠ 7)],
              by simp only [st2, st1, Function.update_of_ne (by decide : (8 : ℕ) ≠ 9),
                Function.update_of_ne (by decide : (8 : ℕ) ≠ 7)],
              by simp [st2, st1, h16], by simp [st2, st1, h17], rfl⟩⟩
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega
      refine runs_seq_triple_le hcond_triple rfl (fun st3 h3p => ?_)
      rcases h3p with ⟨hbranch, hskip⟩
      have h6_3 : st3.regs 6 = x := by
        by_cases h : 1 < sz
        · exact ((hbranch h).1 6 le_rfl).trans hx_def.symm
        · rw [(hskip h).1 6 (by omega), hx_def]
      have he6 : (Expr.bin .add (.reg 6) (.const 1)).eval w st3 = some (x + 1) := by
        simp [Expr.eval, BinOp.eval, h6_3, h1_w, hx1_w]
      refine runs_assign_le he6 ?_ ?_
      · dsimp only [normalPost]
        by_cases h : 1 < sz
        · obtain ⟨hle6, h8', h16', h17', hmem'⟩ := hbranch h
          have hc2 : 2 ≤ (compVerts n root c0).length := by rw [← hsz_def]; omega
          obtain ⟨hco0, hwp0, hcj0⟩ := hc_inv c0 hc0_n hc2
          have hpref_lt : ((List.range x).filter (fun y => decide (root y = c0))).length < sz := by
            rw [hsz_def, hc0_def]; exact pref_lt_comp x hx_n
          have hptr_eq : st.mem (writePtrBase + c0) = compOffset outAddr n root c0 + 1 +
              ((List.range x).filter (fun y => decide (root y = c0))).length := by
            rw [hwp0, ← hx_def]
          have hptr_ge : outAddr + 1 ≤ st.mem (writePtrBase + c0) := by
            rw [hptr_eq]; dsimp only [compOffset]; omega
          have hptr_lt_next : st.mem (writePtrBase + c0) < compOffset outAddr n root (c0 + 1) := by
            have hs' := @compOffset_step outAddr n root c0
            rw [hs']; simp only [hc2, ↓reduceIte]; rw [← hsz_def]; clear hfr2 hc_inv hmem5_rt hmem5_sz; omega
          have hptr_lt_end : st.mem (writePtrBase + c0) < outAddr + 2 * n + 1 := by
            linarith only [hptr_lt_next, @compOffset_le outAddr n root (c0 + 1)]
          have hne_out0 : outAddr ≠ st.mem (writePtrBase + c0) := by omega
          have hne_out_wp : outAddr ≠ writePtrBase + c0 := by
            rcases hdj_wo with h1 | h2 <;> (clear hfr2 hc_inv hmem5_rt hmem5_sz; omega)
          refine ⟨⟨by rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 6), hle6 0 (by omega), hr0],
              by rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 6), hle6 3 (by omega), hr3],
              by rw [Function.update_of_ne (by decide : (5 : ℕ) ≠ 6), hle6 5 (by omega), hr5],
              by simp; clear hfr2 hc_inv hmem5_rt hmem5_sz; omega,
              by rw [Function.update_of_ne (by decide : (8 : ℕ) ≠ 6), h8', h8],
              by rw [Function.update_of_ne (by decide : (16 : ℕ) ≠ 6), h16'],
              by rw [Function.update_of_ne (by decide : (17 : ℕ) ≠ 6), h17'],
              ?_, ?_, ?_⟩, by simp; rw [← hx_def]; clear hfr2 hc_inv hmem5_rt hmem5_sz; omega⟩
          · rw [hmem', Function.update_of_ne hne_out_wp, Function.update_of_ne hne_out0, ho0]
          · intro addr ha1 ha2
            rw [hmem', Function.update_of_ne (by clear hfr2 hc_inv hmem5_rt hmem5_sz; omega),
              Function.update_of_ne (by clear hfr2 hc_inv hmem5_rt hmem5_sz; omega)]
            exact hfr2 addr ha1 ha2
          · intro c hc hc2
            obtain ⟨hco, hwp_c, hcj⟩ := hc_inv c hc hc2
            have h6_up : (Function.update st3.regs 6 (x + 1)) 6 = x + 1 := Function.update_self _ _ _
            rw [h6_up]
            rw [hmem', List.range_succ, List.filter_append]
            by_cases hcc : c = c0
            · subst hcc
              simp only [List.filter_cons, List.filter_nil, ← hc0_def, decide_true, ↓reduceIte,
                List.length_append, List.length_singleton]
              have hne_co_wp : compOffset outAddr n root c ≠ writePtrBase + c := by
                have hgt_o : outAddr + 1 ≤ compOffset outAddr n root c := by dsimp [compOffset]; omega
                have hlt_o : compOffset outAddr n root c < outAddr + 2 * n + 1 := by
                  linarith only [hptr_lt_next, hptr_lt_end, hptr_eq]
                rcases hdj_wo with h1 | h2
                · linarith only [h1, hgt_o, hwp, hc]
                · linarith only [h2, hlt_o, hwp]
              have hne_co_ptr : compOffset outAddr n root c ≠ st.mem (writePtrBase + c) := by
                rw [hptr_eq]; omega
              refine ⟨by rw [Function.update_of_ne hne_co_wp, Function.update_of_ne hne_co_ptr, hco],
                by rw [Function.update_self, hptr_eq]; omega, fun j hj => ?_⟩
              have hne_j_wp : compOffset outAddr n root c + 1 + j ≠ writePtrBase + c := by
                have hlt_n := @compOffset_le outAddr n root (c + 1)
                have hs' := @compOffset_step outAddr n root c
                rw [hs'] at hlt_n; simp only [hc2, ↓reduceIte] at hlt_n
                have hj_le : j ≤ ((List.range x).filter (fun y => decide (root y = c))).length := by omega
                have hj_lt_sz : j < (compVerts n root c).length := lt_of_le_of_lt hj_le (hsz_def ▸ hpref_lt)
                have hlt_end : compOffset outAddr n root c + 1 + j < outAddr + 2 * n + 1 := by
                  linarith only [hlt_n, hj_lt_sz]
                have hgt_o : outAddr + 1 ≤ compOffset outAddr n root c + 1 + j := by
                  dsimp [compOffset]; omega
                rcases hdj_wo with h1 | h2
                · linarith only [h1, hgt_o, hwp, hc]
                · linarith only [h2, hlt_end, hwp]
              rw [Function.update_of_ne hne_j_wp]
              by_cases hj_last : j = ((List.range x).filter (fun y => decide (root y = c))).length
              · subst hj_last; rw [← hptr_eq, Function.update_self]
                simp
              · have hj' : j < ((List.range x).filter (fun y => decide (root y = c))).length := by omega
                rw [Function.update_of_ne (by rw [hptr_eq]; omega)]
                have hcold := hcj j (by rw [← hx_def]; exact hj')
                have heq1 : ((List.range (st.regs 6)).filter (fun y => decide (root y = c)))[j]'(by rw [← hx_def]; exact hj') =
                    ((List.range x).filter (fun y => decide (root y = c)))[j]'hj' := by
                  simp [← hx_def]
                rw [hcold, heq1]
                exact (List.getElem_append_left hj').symm
            · simp only [List.filter_cons, List.filter_nil, ← hc0_def, decide_eq_false (Ne.symm hcc),
                Bool.false_eq_true, ↓reduceIte, List.append_nil]
              have hc_gt_o : outAddr + 1 ≤ compOffset outAddr n root c := by dsimp [compOffset]; omega
              have hce_lt_end : compOffset outAddr n root (c + 1) ≤ outAddr + 1 + 2 * n := compOffset_le root (c + 1)
              have hc_lt_end : compOffset outAddr n root c < outAddr + 2 * n + 1 := by
                have hs' := @compOffset_step outAddr n root c
                rw [hs'] at hce_lt_end; simp only [hc2, ↓reduceIte] at hce_lt_end
                have hlen_pos : 0 < (compVerts n root c).length := by omega
                linarith only [hce_lt_end, hlen_pos]
              have hc'_next_eq : compOffset outAddr n root (c + 1) =
                  compOffset outAddr n root c + 1 + (compVerts n root c).length := by
                have hs' := @compOffset_step outAddr n root c
                rw [hs']; simp only [hc2, ↓reduceIte]; omega
              have hne_co_wp : compOffset outAddr n root c ≠ writePtrBase + c0 := by
                rcases hdj_wo with h1 | h2
                · linarith only [h1, hc_gt_o, hwp, hc0_n]
                · linarith only [h2, hc_lt_end, hwp]
              have hne_co_ptr : compOffset outAddr n root c ≠ st.mem (writePtrBase + c0) := by
                rcases lt_trichotomy c c0 with hlt | heq | hgt
                · have h1 := compOffset_mono (outAddr := outAddr) (n := n) (root := root) (Nat.succ_le_of_lt hlt)
                  linarith only [h1, hc'_next_eq, hptr_eq]
                · exact False.elim (hcc heq)
                · have h1 := compOffset_mono (outAddr := outAddr) (n := n) (root := root) (Nat.succ_le_of_lt hgt)
                  linarith only [h1, hptr_lt_next]
              have hne_wp_wp : writePtrBase + c ≠ writePtrBase + c0 := fun heq => hcc (by omega)
              have hne_wp_ptr : writePtrBase + c ≠ st.mem (writePtrBase + c0) := by
                rcases hdj_wo with h1 | h2
                · linarith only [h1, hwp, hc, hptr_ge]
                · linarith only [h2, hwp, hptr_lt_end]
              refine ⟨by rw [Function.update_of_ne hne_co_wp, Function.update_of_ne hne_co_ptr, hco],
                by rw [Function.update_of_ne hne_wp_wp, Function.update_of_ne hne_wp_ptr, hwp_c, ← hx_def],
                fun j hj => ?_⟩
              have hj_comp : j < (compVerts n root c).length := by
                refine lt_of_lt_of_le hj ?_
                have hx_le : x ≤ n := Nat.le_of_lt hx_n
                clear hfr2 hc_inv hmem5_rt hmem5_sz
                unfold compVerts
                have : List.range n = List.range x ++ (List.range (n - x)).map (· + x) := by
                  refine List.ext_getElem (by simp; omega) fun i _ _ => ?_
                  simp only [List.getElem_append, List.length_range, List.getElem_range]
                  split_ifs; all_goals simp; all_goals omega
                rw [this, List.filter_append, List.length_append]; omega
              have hj_lt_next : compOffset outAddr n root c + 1 + j < compOffset outAddr n root (c + 1) := by
                rw [hc'_next_eq]; omega
              have hne_j_wp : compOffset outAddr n root c + 1 + j ≠ writePtrBase + c0 := by
                rcases hdj_wo with h1 | h2
                · linarith only [h1, hc_gt_o, hwp, hc0_n]
                · linarith only [h2, hj_lt_next, hce_lt_end, hwp]
              have hne_j_ptr : compOffset outAddr n root c + 1 + j ≠ st.mem (writePtrBase + c0) := by
                rcases lt_trichotomy c c0 with hlt | heq | hgt
                · have h1 := compOffset_mono (outAddr := outAddr) (n := n) (root := root) (Nat.succ_le_of_lt hlt)
                  linarith only [h1, hj_lt_next, hptr_eq]
                · exact False.elim (hcc heq)
                · have h1 := compOffset_mono (outAddr := outAddr) (n := n) (root := root) (Nat.succ_le_of_lt hgt)
                  linarith only [h1, hptr_lt_next]
              rw [Function.update_of_ne hne_j_wp, Function.update_of_ne hne_j_ptr]
              simpa [← hx_def] using hcj j (by rw [← hx_def]; exact hj)
        · obtain ⟨hle6, h8', h16', h17', hmem'⟩ := hskip h
          have hnc2 : ¬ 2 ≤ (compVerts n root c0).length := by rw [← hsz_def]; omega
          refine ⟨⟨by rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 6), hle6 0 (by omega), hr0],
              by rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 6), hle6 3 (by omega), hr3],
              by rw [Function.update_of_ne (by decide : (5 : ℕ) ≠ 6), hle6 5 (by omega), hr5],
              by simp; clear hfr2 hc_inv hmem5_rt hmem5_sz; omega,
              by rw [Function.update_of_ne (by decide : (8 : ℕ) ≠ 6), h8', h8],
              by rw [Function.update_of_ne (by decide : (16 : ℕ) ≠ 6), h16'],
              by rw [Function.update_of_ne (by decide : (17 : ℕ) ≠ 6), h17'],
              by rw [hmem']; exact ho0, by rw [hmem']; exact hfr2, fun c hc hc2 => ?_⟩,
            by simp; rw [← hx_def]; clear hfr2 hc_inv hmem5_rt hmem5_sz; omega⟩
          have hcc : c ≠ c0 := fun heq => hnc2 (heq ▸ hc2)
          obtain ⟨hco, hwp_c, hcj⟩ := hc_inv c hc hc2
          rw [Function.update_self, hmem', List.range_succ, List.filter_append]
          simp only [List.filter_cons, List.filter_nil, ← hc0_def, decide_eq_false (Ne.symm hcc),
            Bool.false_eq_true, ↓reduceIte, List.append_nil]
          simp only [← hx_def] at hwp_c hcj
          exact ⟨hco, hwp_c, fun j hj => hcj j hj⟩
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega)

private lemma listAt_bfsCompsEncode {mem : ℕ → ℕ} {outAddr n : ℕ} {root : ℕ → ℕ}
    (ho0 : mem outAddr = (bfsCompsList n root).length)
    (hcells : ∀ c < n, 2 ≤ (compVerts n root c).length →
      mem (compOffset outAddr n root c) = (compVerts n root c).length ∧
      ∀ j, (hj : j < (compVerts n root c).length) →
        mem (compOffset outAddr n root c + 1 + j) = (compVerts n root c)[j]'hj) :
    ListAt mem outAddr (bfsCompsEncode (bfsCompsList n root)) := by
  intro i hi
  dsimp only [bfsCompsEncode] at hi ⊢
  cases i with
  | zero => simp [ho0]
  | succ i' =>
    simp only [List.singleton_append, List.getElem_cons_succ]
    have hhi : i' < ((bfsCompsList n root).flatMap (fun c => c.length :: c)).length := by
      simpa using hi
    -- Prove generally for any prefix k ≤ n
    have hgen : ∀ k ≤ n, ∀ idx,
        idx < (((List.range k).filter (fun c => decide (2 ≤ (compVerts n root c).length))).map
          (compVerts n root) |>.flatMap (fun c => c.length :: c)).length →
        mem (outAddr + 1 + idx) =
          ((((List.range k).filter (fun c => decide (2 ≤ (compVerts n root c).length))).map
            (compVerts n root)).flatMap (fun c => c.length :: c)).getD idx 0 := by
      intro k hk
      induction k with
      | zero => intro idx hidx; simp at hidx
      | succ k ih =>
        intro idx hidx
        rw [List.range_succ, List.filter_append, List.map_append, List.flatMap_append] at hidx ⊢
        simp only [List.filter_cons, List.filter_nil] at hidx ⊢
        by_cases hk2 : 2 ≤ (compVerts n root k).length
        · simp only [hk2, decide_true, ↓reduceIte, List.map_cons, List.map_nil, List.flatMap_cons,
            List.flatMap_nil, List.append_nil] at hidx ⊢
          set prefFlat := (((List.range k).filter (fun c => decide (2 ≤ (compVerts n root c).length))).map
            (compVerts n root)).flatMap (fun c => c.length :: c)
          have hpref_len : outAddr + 1 + prefFlat.length = compOffset outAddr n root k := by
            dsimp only [prefFlat, compOffset]
            congr 1
            induction (List.range k) with
            | nil => simp
            | cons a as iha =>
              simp only [List.filter_cons]
              split_ifs; all_goals simp [iha]; all_goals omega
          by_cases hlt : idx < prefFlat.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
            simpa [List.getD_eq_getElem?_getD, hlt] using ih (by omega) idx hlt
          · have hidx_sub : idx - prefFlat.length < ((compVerts n root k).length :: compVerts n root k).length := by
              rw [List.length_append] at hidx; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              List.getElem?_eq_getElem hidx_sub, Option.getD_some]
            have haddr_eq : outAddr + 1 + idx = compOffset outAddr n root k + (idx - prefFlat.length) := by
              omega
            rw [haddr_eq]
            obtain ⟨hco, hcj⟩ := hcells k (by omega) hk2
            by_cases hrem0 : idx - prefFlat.length = 0
            · simp [hrem0, hco]
            · obtain ⟨j, hj_eq⟩ := Nat.exists_eq_succ_of_ne_zero hrem0
              have hj : j < (compVerts n root k).length := by
                rw [List.length_cons] at hidx_sub; omega
              simpa [hj_eq, Nat.add_assoc, Nat.add_comm 1 j] using hcj j hj
        · simp only [hk2, decide_false, Bool.false_eq_true, ↓reduceIte, List.map_nil, List.flatMap_nil,
            List.append_nil] at hidx ⊢
          exact ih (by omega) idx hidx
    have := hgen n le_rfl i' hhi
    simp only [bfsCompsList, compRoots, Nat.add_assoc, Nat.add_comm 1 i', List.getD_eq_getElem?_getD] at this hhi ⊢
    rw [List.getElem?_eq_getElem hhi, Option.getD_some] at this
    exact this

private lemma bfsScatterCore_triple {w : ℕ} {p : Program}
    (n workAddr outAddr : ℕ) (root : ℕ → ℕ) (mem1 : ℕ → ℕ) (st0 : State)
    (hroot_lt : ∀ x < n, root x < n)
    (hdj_wo : workAddr + 3 * n ≤ outAddr ∨ outAddr + 2 * n + 1 ≤ workAddr)
    (hwork_w : workAddr + 3 * n < 2 ^ w) (hout_w : outAddr + 2 * n + 1 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hr0 : st0.regs 0 = n) (hr16 : st0.regs 16 = outAddr) (hr17 : st0.regs 17 = workAddr)
    (hmem_rt : ∀ x < n, st0.mem (workAddr + x) = root x)
    (hmem0 : st0.mem = mem1) :
    Triple w p (fun st => st = st0) bfsScatterCore
      (fun o st' => o = Outcome.returned (compOffset outAddr n root n) ∧
        (∀ addr, (addr < workAddr + n ∨ workAddr + 3 * n ≤ addr) →
          (addr < outAddr ∨ outAddr + 2 * n + 1 ≤ addr) → st'.mem addr = mem1 addr) ∧
        ListAt st'.mem outAddr (bfsCompsEncode (bfsCompsList n root)))
      (fun _ => 130 * n + 70) := by
  have h1_w : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 4) hw4
  have h0_w : 0 < 2 ^ w := lt_of_lt_of_le (by decide : 0 < 4) hw4
  obtain ⟨sizeBase, hsize_def⟩ : ∃ v, v = workAddr + n := ⟨_, rfl⟩
  obtain ⟨writePtrBase, hwp_def⟩ : ∃ v, v = workAddr + 2 * n := ⟨_, rfl⟩
  have hsb_w : sizeBase < 2 ^ w := by linarith only [hsize_def, hwork_w]
  have hwp_w : writePtrBase < 2 ^ w := by linarith only [hwp_def, hwork_w]
  have hou1_w : outAddr + 1 < 2 ^ w := by linarith only [hout_w]
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  dsimp only [bfsScatterCore, seqStmts]
  wram_step
  wram_step
  wram_step
  have hl3 := pass3_zero_loop (p := p) n workAddr outAddr sizeBase writePtrBase root mem1
    hsize_def hwp_def hwork_w h1_w hw4
  refine runs_seq_triple_le hl3 ?_ (fun st1 h1p => ?_)
  · refine ⟨by simp [hr0], by simp [hr0, hsize_def], by simp [hr0, hwp_def]; omega,
        by simp, by simp [hr16], by simp [hr17], fun x hx => by simp [hmem_rt x hx],
        ?_, fun i hi => by simp at hi⟩
    rw [hmem0]; exact fun _ _ => rfl
  · rcases h1p with ⟨h1_0, h1_3, h1_5, h1_16, h1_17, h1_rt, h1_fr, h1_zero⟩
    wram_step
    have hl4 := pass4_count_loop (p := p) n workAddr outAddr sizeBase writePtrBase root mem1
      hroot_lt hsize_def hwp_def hwork_w h1_w
    refine runs_seq_triple_le hl4 ?_ (fun st2 h2p => ?_)
    · refine ⟨by simp [h1_0], by simp [h1_3], by simp [h1_5], by simp, by simp [h1_16],
          by simp [h1_17], fun x hx => by simp [h1_rt x hx], by simp [h1_fr], fun c hc => ?_⟩
      simp [h1_zero c hc]
    · rcases h2p with ⟨h2_0, h2_3, h2_5, h2_16, h2_17, h2_rt, h2_fr, h2_sz⟩
      wram_step
      wram_step
      wram_step
      have hl5 := pass5_prefix_loop (p := p) n workAddr outAddr sizeBase writePtrBase root st2.mem
        hsize_def hwp_def hdj_wo h2_sz hwork_w hout_w h1_w hw4
      refine runs_seq_triple_le hl5 ?_ (fun st3 h3p => ?_)
      · refine ⟨by simp [h2_0], by simp [h2_3], by simp [h2_5], by simp, by simp,
            by simp [compOffset, h2_16], by simp [h2_16], by simp [h2_17],
            fun addr _ _ => rfl, fun c hc _ => by simp at hc⟩
      · rcases h3p with ⟨h3_0, h3_3, h3_5, _, h3_7, h3_8, h3_16, h3_17, h3_fr2, h3_cells⟩
        have h7_w : st3.regs 7 < 2 ^ w := by
          rw [h3_7]
          have : (bfsCompsList n root).length ≤ n := by
            simp only [bfsCompsList, compRoots, List.length_map]
            simpa [List.length_range] using List.length_filter_le _ (List.range n)
          linarith only [this, hout_w]
        wram_step
        wram_step
        have hl6 := pass6_scatter_loop (p := p) n workAddr outAddr sizeBase writePtrBase root st2.mem
          hroot_lt hsize_def hwp_def hdj_wo h2_rt h2_sz hwork_w hout_w h1_w hw4
        refine runs_seq_triple_le hl6 ?_ (fun st4 h4p => ?_)
        · refine ⟨by simp [h3_0], by simp [h3_3], by simp [h3_5], by simp, by simp [h3_8],
              by simp [h3_16], by simp [h3_17], by simp, fun addr ha1 ha2 => ?_, fun c hc hc2 => ?_⟩
          · have hne_o : addr ≠ outAddr := by rcases ha2 with h | h <;> linarith only [h]
            dsimp only
            rw [Function.update_of_ne hne_o]
            exact h3_fr2 addr ha1 ha2
          · obtain ⟨hco, hcw⟩ := h3_cells c hc hc2
            have hco_gt : outAddr < compOffset outAddr n root c := by dsimp [compOffset]; omega
            have hne_wp : writePtrBase + c ≠ outAddr := by
              intro heq
              rcases hdj_wo with h1 | h2
              · linarith only [h1, hwp_def, heq, hc]
              · linarith only [h2, hco_gt, hwp_def, heq]
            dsimp only
            exact ⟨by rw [Function.update_of_ne (Ne.symm (Nat.ne_of_lt hco_gt)), hco],
              by rw [Function.update_self, Function.update_of_ne hne_wp, hcw]; simp,
              fun j hj => by rw [Function.update_self] at hj; simp at hj⟩
        · rcases h4p with ⟨_, h4_8, h4_16, _, h4_o0, h4_fr2, h4_cells⟩
          wram_run
          · refine ⟨rfl, fun addr ha1 ha2 => ?_, listAt_bfsCompsEncode h4_o0 h4_cells⟩
            have hne_st2 : st2.mem addr = mem1 addr := by
              rcases ha1 with h | h
              · by_cases hw : addr < workAddr
                · exact h2_fr addr (Or.inl hw)
                · have hx : addr - workAddr < n := Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hw) h
                  rw [(Nat.add_sub_of_le (Nat.le_of_not_lt hw)).symm, h2_rt _ hx, ← hmem_rt _ hx, hmem0]
              · exact h2_fr addr (Or.inr h)
            rw [← hne_st2]
            refine h4_fr2 addr ?_ ha2
            rcases ha1 with h | h <;> [left; right] <;> linarith only [h, hsize_def, hwp_def]
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin,
              Function.update_self, Nat.sub_zero]
            linarith only

/-! ## 8. `bfsCompsContract`, `bfsComps_spec`, and `bfsCompsProcs` -/

lemma listAt_bfsCompsEncode_length (comps : List (List ℕ)) :
    (bfsCompsEncode comps).length = 1 + (comps.map fun c => 1 + c.length).sum := by
  simp only [bfsCompsEncode, List.length_append, List.length_singleton]
  congr 1
  induction comps with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.map_cons,
      List.sum_cons, ih]
    omega

/-- Contract for `bfsCompsProc`: `args = [n, m, csrAddr, workAddr, outAddr]`.
Writes `ListAt mem' outAddr (bfsCompsEncode comps)` returning end address `v = outAddr + (bfsCompsEncode comps).length`
in `270 * n + 80 * m + 90` steps, using workspace `[workAddr, workAddr + 3*n)`. -/
noncomputable def bfsCompsContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n m csrAddr workAddr outAddr : ℕ) (G : Cited.Graph),
      args = [n, m, csrAddr, workAddr, outAddr] ∧
      G.n = n ∧ G.m = m ∧ G.IsValid ∧
      HasCsrAt mem csrAddr G ∧
      (csrAddr + 2 * n + 1 + 4 * m ≤ workAddr ∨ workAddr + 3 * n ≤ csrAddr) ∧
      (csrAddr + 2 * n + 1 + 4 * m ≤ outAddr ∨ outAddr + 2 * n + 1 ≤ csrAddr) ∧
      (workAddr + 3 * n ≤ outAddr ∨ outAddr + 2 * n + 1 ≤ workAddr) ∧
      csrAddr + 2 * n + 1 + 4 * m < 2 ^ w ∧
      workAddr + 3 * n < 2 ^ w ∧ outAddr + 2 * n + 1 < 2 ^ w ∧ 4 ≤ 2 ^ w
  post args mem v mem' :=
    let n := args.getD 0 0
    let workAddr := args.getD 3 0
    let outAddr := args.getD 4 0
    (∀ addr, (addr < workAddr ∨ workAddr + 3 * n ≤ addr) →
      (addr < outAddr ∨ outAddr + 2 * n + 1 ≤ addr) → mem' addr = mem addr) ∧
    ∀ G : Cited.Graph, G.n = n → G.m = args.getD 1 0 → G.IsValid →
      HasCsrAt mem (args.getD 2 0) G →
      ∃ comps : List (List ℕ),
        ListAt mem' outAddr (bfsCompsEncode comps) ∧
        v = outAddr + (bfsCompsEncode comps).length ∧
        comps.Pairwise (fun a b => a.Disjoint b) ∧
        (∀ c ∈ comps, c.Pairwise (· < ·) ∧ 2 ≤ c.length ∧
          c.toFinset ∈ Cited.partsOf G (compLabels G) ∧
          G.cut c.toFinset = 0 ∧
          (∀ φ : ℝ, φ ≤ 1 / (G.m + 1) → G.IsConductanceExpanderOn c.toFinset φ)) ∧
        (G.IsLoopless → ∀ e ∈ G.edges, ∃ c ∈ comps, e.1 ∈ c ∧ e.2 ∈ c)
  cost args _mem := 285 * args.getD 0 0 + 95 * args.getD 1 0 + 130

theorem bfsComps_spec (w : ℕ) (p : Program) (b : ℕ) (hp : p.HasAt b [bfsCompsProc]) :
    MeetsContract w p b (bfsCompsContract w) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨n, m, csrAddr, workAddr, outAddr, G, hargs, hn, hm, hval, hcsr,
      hdj_cw, hdj_co, hdj_wo, hcsr_w, hwork_w, hout_w, hw4⟩
  subst hargs
  have hproc : p.procs[b]? = some bfsCompsProc := by simpa using hp 0 (by simp)
  have h1_w : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 4) hw4
  have hfull : Triple w p
      (fun st => st = startState [n, m, csrAddr, workAddr, outAddr] mem pos)
      bfsCompsProc
      (fun o st' => ∃ v, o = Outcome.returned v ∧
        (bfsCompsContract w).post [n, m, csrAddr, workAddr, outAddr] mem v st'.mem)
      (fun _ => 285 * n + 95 * m + 130) := by
    intro st ω' hs; rw [hs]; refine runs_start_le ?_
    dsimp only [bfsCompsProc, seqStmts]
    wram_step
    wram_step
    wram_step
    wram_step
    have hl1 := bfsLabelsCore_triple (p := p) n m csrAddr (workAddr + n) workAddr G mem
      { startState [n, m, csrAddr, workAddr, outAddr] mem pos with
        regs := Function.update (Function.update (Function.update (Function.update
          (startState [n, m, csrAddr, workAddr, outAddr] mem pos).regs 17 workAddr) 16 outAddr) 4 workAddr) 3 (workAddr + n) }
      hn hm hval hcsr
      (by rcases hdj_cw with h | h <;> [left; right] <;> omega)
      (by rcases hdj_cw with h | h <;> [left; right] <;> omega)
      (Or.inr le_rfl)
      hcsr_w (by linarith only [hwork_w]) (by linarith only [hwork_w]) hw4
      (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp [startState])
      (by simp [startState]) rfl
    refine runs_seq_triple_le hl1 rfl (fun st1 h1p => ?_)
    rcases h1p with ⟨hle4, hge15, hfr1, hrt_lt, hfib⟩
    obtain ⟨root, hroot_def⟩ : ∃ f : ℕ → ℕ, f = fun x => st1.mem (workAddr + x) := ⟨_, rfl⟩
    have hrt_lt' : ∀ x < n, root x < n := fun x hx => hroot_def ▸ hrt_lt x hx
    have hl2 := bfsScatterCore_triple (p := p) n workAddr outAddr root st1.mem st1
      hrt_lt' hdj_wo hwork_w hout_w hw4
      (by rw [hle4 0 (by omega)]; simp [startState])
      (by rw [hge15 16 (by omega)]; simp [startState])
      (by rw [hge15 17 (by omega)]; simp [startState])
      (fun x hx => by rw [hroot_def]) rfl
    refine runs_triple_le hl2 rfl ?_ ?_
    · intro o st2 ⟨ho, hfr2, hlat⟩
      refine ⟨compOffset outAddr n root n, ho, ?_, fun G' hGn' hGm' hGval' hGcsr' => ?_⟩
      · intro addr ha1 ha2
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some] at ha1 ha2
        have h1 : st2.mem addr = st1.mem addr :=
          hfr2 addr (by rcases ha1 with h | h <;> [left; right] <;> omega) ha2
        have h2 : st1.mem addr = mem addr :=
          hfr1 addr (by rcases ha1 with h | h <;> [left; right] <;> omega)
            (by rcases ha1 with h | h <;> [left; right] <;> omega)
        exact h1.trans h2
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some] at hGn' hGm' hGcsr' ⊢
        have hGn : G'.n = n := hGn'
        have hGm : G'.m = m := hGm'
        refine ⟨bfsCompsList n root, hlat, ?_, bfsCompsList_pairwise_disjoint root, fun c hc => ?_, fun hll e he => ?_⟩
        · rw [listAt_bfsCompsEncode_length]
          dsimp only [compOffset, bfsCompsList, compRoots]
          simp only [List.map_map, Function.comp_def]
          omega
        · obtain ⟨hc_lt, hc_len, hc_n⟩ := bfsCompsList_mem_props hc
          have hpart : c.toFinset ∈ Cited.partsOf G' (compLabels G') := by
            unfold bfsCompsList compRoots at hc
            rcases List.mem_map.mp hc with ⟨c0, hc0, rfl⟩
            simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hc0
            obtain ⟨z, hz⟩ : ∃ z, z ∈ compVerts n root c0 :=
              List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (by decide : 0 < 2) hc0.2))
            have hz_n : z < n := (mem_compVerts_iff.mp hz).1
            have hz_rt : root z = c0 := (mem_compVerts_iff.mp hz).2
            have hGeq : ∀ x < n, ∀ y < n, root x = root y ↔
                (compLabels G').getD x 0 = (compLabels G').getD y 0 := by
              intro x hx y hy
              have hG_rt := hfib x hx y hy
              rw [hroot_def]
              dsimp only
              rw [hG_rt, compLabels_eq_iff_reachable hval (hn.symm ▸ hx) (hn.symm ▸ hy),
                compLabels_eq_iff_reachable hGval' (hGn.symm ▸ hx) (hGn.symm ▸ hy)]
              exact ⟨fun ⟨P, hP⟩ => reachable_of_hasCsrAt hcsr hGcsr' hval hGval' (hn.trans hGn.symm) (hm.trans hGm.symm) hP,
                fun ⟨P, hP⟩ => reachable_of_hasCsrAt hGcsr' hcsr hGval' hval (hGn.trans hn.symm) (hGm.trans hm.symm) hP⟩
            unfold Cited.partsOf
            refine Finset.mem_image.mpr ⟨z, Finset.mem_range.mpr (hGn.symm ▸ hz_n), ?_⟩
            ext x
            simp only [Finset.mem_filter, Cited.Graph.verts, Finset.mem_range, List.mem_toFinset,
              mem_compVerts_iff]
            constructor
            · rintro ⟨hx, hx_lbl⟩
              have hx_n : x < n := hGn ▸ hx
              have := (hGeq x hx_n z hz_n).mpr hx_lbl
              exact ⟨hx_n, this.trans hz_rt⟩
            · rintro ⟨hx_n, hx_rt⟩
              refine ⟨hGn.symm ▸ hx_n, (hGeq x hx_n z hz_n).mp (hx_rt.trans hz_rt.symm)⟩
          have hcut0 : G'.cut c.toFinset = 0 := cut_part_compLabels_eq_zero hGval' hpart
          refine ⟨hc_lt, hc_len, hpart, hcut0, fun φ hφ S hSX hSne hSXne => ?_⟩
          have hcut1 : (1 : ℝ) ≤ (G'.cutIn c.toFinset S : ℝ) := by
            exact_mod_cast cutIn_ge_one_of_part_compLabels hGval' hpart hSX hSne hSXne
          have hsum_v : G'.volIn c.toFinset S + G'.volIn c.toFinset (c.toFinset \ S) =
              2 * (G'.inside c.toFinset).length := volIn_add_volIn_sdiff G' c.toFinset S hSX
          have hmin_le : min (G'.volIn c.toFinset S) (G'.volIn c.toFinset (c.toFinset \ S)) ≤ G'.m := by
            have := inside_length_le_m G' c.toFinset; omega
          have hmin_r : min (G'.volIn c.toFinset S : ℝ) (G'.volIn c.toFinset (c.toFinset \ S) : ℝ) ≤
              (G'.m : ℝ) + 1 := by
            have : (min (G'.volIn c.toFinset S) (G'.volIn c.toFinset (c.toFinset \ S)) : ℝ) ≤
                (G'.m : ℝ) + 1 := by exact_mod_cast (by omega)
            exact_mod_cast this
          calc φ * min (G'.volIn c.toFinset S : ℝ) (G'.volIn c.toFinset (c.toFinset \ S) : ℝ)
              ≤ (1 / ((G'.m : ℝ) + 1)) * ((G'.m : ℝ) + 1) := by
                by_cases hφ0 : 0 ≤ φ
                · exact mul_le_mul hφ hmin_r (by positivity) (by positivity)
                · push Not at hφ0
                  have : φ * min (G'.volIn c.toFinset S : ℝ) (G'.volIn c.toFinset (c.toFinset \ S) : ℝ) ≤ 0 :=
                    mul_nonpos_of_nonpos_of_nonneg hφ0.le (by positivity)
                  linarith [show (0 : ℝ) ≤ (1 / ((G'.m : ℝ) + 1)) * ((G'.m : ℝ) + 1) by positivity]
            _ = 1 := by field_simp
            _ ≤ (G'.cutIn c.toFinset S : ℝ) := hcut1
        · have hG_rt_edge : ∀ e' ∈ G'.edges, root e'.1 = root e'.2 := by
            intro e' he'
            rcases hGval' e' he' with ⟨he1, he2⟩
            have hfib_G := hfib e'.1 (hGn ▸ he1) e'.2 (hGn ▸ he2)
            rw [hroot_def]
            dsimp only
            rw [hfib_G, compLabels_eq_iff_reachable hval (hn.symm ▸ hGn ▸ he1) (hn.symm ▸ hGn ▸ he2)]
            have : ∃ P, IsPathAlong G'.edges e'.1 e'.2 P :=
              ⟨[e'.1, e'.2], rfl, rfl, List.isChain_cons_cons.mpr ⟨Or.inl he', List.isChain_singleton _⟩⟩
            exact reachable_of_hasCsrAt hGcsr' hcsr hGval' hval (hGn.trans hn.symm) (hGm.trans hm.symm) this.choose_spec
          rcases hGval' e he with ⟨he1, he2⟩
          have he1_n : e.1 < n := hGn ▸ he1
          have he2_n : e.2 < n := hGn ▸ he2
          have hne : e.1 ≠ e.2 := hll e he
          have heq_rt := hG_rt_edge e he
          obtain ⟨c0, hc0_eq⟩ : ∃ v, v = root e.1 := ⟨_, rfl⟩
          have hc0_n : c0 < n := hc0_eq ▸ hrt_lt' e.1 he1_n
          have he1_mem : e.1 ∈ compVerts n root c0 := mem_compVerts_iff.mpr ⟨he1_n, hc0_eq.symm⟩
          have he2_mem : e.2 ∈ compVerts n root c0 := mem_compVerts_iff.mpr ⟨he2_n, heq_rt.symm.trans hc0_eq.symm⟩
          have hc2 : 2 ≤ (compVerts n root c0).length := by
            have hsub : [e.1, e.2] ⊆ compVerts n root c0 := by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
            have := (List.nodup_cons.mpr ⟨by simp [hne], List.nodup_singleton e.2⟩).length_le_of_subset hsub
            simpa using this
          refine ⟨compVerts n root c0, ?_, he1_mem, he2_mem⟩
          unfold bfsCompsList compRoots
          exact List.mem_map.mpr ⟨c0, List.mem_filter.mpr ⟨List.mem_range.mpr hc0_n, decide_eq_true hc2⟩, rfl⟩
    · simp only [Expr.size_reg, Expr.size_bin]; clear hl1 hl2 hfr1 hfib; omega
  obtain ⟨o, st', c, hrun, ⟨v, rfl, hpost⟩, hcost⟩ := hfull _ ω rfl
  refine ⟨bfsCompsProc, hproc, .returned v, st', c, hrun, ?_, ?_⟩
  · simpa [Outcome.value] using hpost
  · simpa [bfsCompsContract] using hcost

/-- Combined CSR + BFS connected components programs (`[buildCsrProc, bfsLabelsProc, bfsCompsProc]`). -/
def bfsCompsProcs : List Stmt := [buildCsrProc, bfsLabelsProc, bfsCompsProc]

lemma bfsCompsProcs_noRand : ∀ s ∈ bfsCompsProcs, s.NoRand := by
  intro s hs
  simp only [bfsCompsProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact buildCsrProc_noRand
  · exact bfsLabelsProc_noRand
  · exact bfsCompsProc_noRand

end

end MinCostFlow.Expander
