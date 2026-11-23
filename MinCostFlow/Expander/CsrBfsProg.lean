module

public import WordRAM.Logic
public import WordRAM.Link
public import WordRAM.Tactic
public import WordRAM.Entry
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.Expander.GraphCompression

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# CSR Construction and BFS Shortest-Path Procedures (`buildCsrProc`, `bfsPathProc`)

Implements deterministic (`NoRand`) linear-time Word-RAM procedures over `Cited.Graph`:
- `buildCsrProc` (`O(n + m + 1)` time, `2 * n + 1 + 4 * m` words): builds compressed sparse row
  adjacency `(off, adjVert, adjHalf)` skipping self-loops (`a = b`), where each entry
  `(adjHalf[k] / 2, adjHalf[k] % 2 == 1, adjVert[k])` matches `incEdgesAux u 0 G.edges`
  in exact index order.
- `bfsPathProc` (`O(n + m + 1)` time, `4 * n` scratch + `2 * n + 2` output words): single flat
  BFS loop over masked vertices (`vMaskAddr`) and masked edges (`eMaskAddr`), emitting a simple
  `WalkAt` path `[P.verts.length] ++ P.verts ++ [P.edges.length] ++ P.edges` whenever `v` is
  reachable from `u` in `(G \ deleted)[R]`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Pure CSR half-edge specifications and prefix sums -/

/-- Non-loop half-edges incident to `u` starting at edge index `k`, matching `PruningState.incEdgesAux`. -/
def csrIncAux (u : ℕ) : ℕ → List (ℕ × ℕ) → List (ℕ × Bool × ℕ)
  | _, [] => []
  | idx, (a, b) :: rest =>
    let tail := csrIncAux u (idx + 1) rest
    if a = b then tail
    else if a = u then (idx, false, b) :: tail
    else if b = u then (idx, true, a) :: tail
    else tail

lemma csrIncAux_append_singleton (u r : ℕ) (L : List (ℕ × ℕ)) (a b : ℕ) :
    csrIncAux u r (L ++ [(a, b)]) =
      csrIncAux u r L ++
        (if a = b then [] else if a = u then [(r + L.length, false, b)]
         else if b = u then [(r + L.length, true, a)] else []) := by
  induction L generalizing r with
  | nil => simp [csrIncAux]
  | cons e rest ih =>
    rcases e with ⟨x, y⟩
    have ih' := ih (r + 1)
    simp only [List.cons_append, csrIncAux] at ih' ⊢
    rw [ih']
    have hadd : r + 1 + rest.length = r + (rest.length + 1) := by omega
    rw [hadd]
    split_ifs <;> simp

lemma csrIncAux_take_length_le (u : ℕ) (L : List (ℕ × ℕ)) (k : ℕ) :
    (csrIncAux u 0 (L.take k)).length ≤ (csrIncAux u 0 L).length := by
  have hsplit : L = L.take k ++ L.drop k := (List.take_append_drop k L).symm
  suffices ∀ (A B : List (ℕ × ℕ)) (r : ℕ),
      (csrIncAux u r A).length ≤ (csrIncAux u r (A ++ B)).length by
    conv_rhs => rw [hsplit]
    exact this (L.take k) (L.drop k) 0
  intro A B r
  induction A generalizing r with
  | nil => simp [csrIncAux]
  | cons e rest ih =>
    rcases e with ⟨x, y⟩
    simp only [List.cons_append, csrIncAux]
    have := ih (r + 1)
    split_ifs <;> simp <;> omega

lemma csrIncAux_sum_le (n : ℕ) (L : List (ℕ × ℕ)) (r : ℕ) :
    (Finset.range n).sum (fun u => (csrIncAux u r L).length) ≤ 2 * L.length := by
  induction L generalizing r with
  | nil => simp [csrIncAux]
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    have hpt : ∀ u, (csrIncAux u r ((a, b) :: rest)).length =
        (if a = b then 0 else if a = u then 1 else if b = u then 1 else 0) +
          (csrIncAux u (r + 1) rest).length := by
      intro u
      simp only [csrIncAux]
      split_ifs <;> simp <;> omega
    simp only [List.length_cons]
    calc (Finset.range n).sum (fun u => (csrIncAux u r ((a, b) :: rest)).length)
        = (Finset.range n).sum (fun u =>
            (if a = b then 0 else if a = u then 1 else if b = u then 1 else 0)) +
          (Finset.range n).sum (fun u => (csrIncAux u (r + 1) rest).length) := by
          simp_rw [hpt]; exact Finset.sum_add_distrib
      _ ≤ 2 + 2 * rest.length := by
          have h1 : (Finset.range n).sum (fun u =>
              if a = b then 0 else if a = u then 1 else if b = u then 1 else 0) ≤ 2 := by
            by_cases hab : a = b
            · simp [hab]
            · simp only [hab, ↓reduceIte]
              have hsplit : ∀ u ∈ Finset.range n,
                  (if a = u then 1 else if b = u then 1 else 0) =
                    (if u = a then 1 else 0) + (if u = b then 1 else 0) := by
                intro u _
                by_cases ha : a = u <;> by_cases hb : b = u
                · exact False.elim (hab (ha.trans hb.symm))
                · simp [ha, hb, eq_comm]
                · simp [ha, hb, eq_comm]
                · simp [ha, hb, eq_comm]
              rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
              have ha_le : (Finset.range n).sum (fun u => if u = a then 1 else 0) ≤ 1 := by
                simp only [Finset.sum_ite_eq', Finset.mem_range]
                split_ifs <;> omega
              have hb_le : (Finset.range n).sum (fun u => if u = b then 1 else 0) ≤ 1 := by
                simp only [Finset.sum_ite_eq', Finset.mem_range]
                split_ifs <;> omega
              omega
          have h2 := ih (r + 1)
          omega
      _ = 2 * (rest.length + 1) := by ring

lemma csrIncAux_getElem_lt {G : Cited.Graph} (hv : G.IsValid) {u : ℕ}
    {j : ℕ} (hj : j < (csrIncAux u 0 G.edges).length) :
    let q := (csrIncAux u 0 G.edges)[j]
    q.1 < G.m ∧ q.2.2 < G.n ∧ q.2.2 ≠ u ∧
      Walk.EdgeMatches (G.edges.getD q.1 (0, 0)) u q.2.2 := by
  have hgen : ∀ (L : List (ℕ × ℕ)) (r : ℕ)
      (hL : ∀ e ∈ L, e.1 < G.n ∧ e.2 < G.n)
      (q : ℕ × Bool × ℕ), q ∈ csrIncAux u r L →
      r ≤ q.1 ∧ q.1 < r + L.length ∧ q.2.2 < G.n ∧ q.2.2 ≠ u ∧
        Walk.EdgeMatches (L.getD (q.1 - r) (0, 0)) u q.2.2 := by
    intro L r hL q hq
    induction L generalizing r with
    | nil => simp [csrIncAux] at hq
    | cons e rest ih =>
      rcases e with ⟨a, b⟩
      have he := hL (a, b) (by simp)
      have hrest : ∀ e' ∈ rest, e'.1 < G.n ∧ e'.2 < G.n := fun e' he' => hL e' (by simp [he'])
      simp only [csrIncAux] at hq
      split_ifs at hq with h1 h2 h3
      · rcases ih (r + 1) hrest hq with ⟨h_ge, h_lt, h_n, h_ne, h_em⟩
        have hsub : q.1 - r = (q.1 - (r + 1)) + 1 := by omega
        refine ⟨by omega, by simp; omega, h_n, h_ne, ?_⟩
        simpa [hsub] using h_em
      · rcases List.mem_cons.mp hq with rfl | hq'
        · refine ⟨le_rfl, by simp, he.2, fun h => h1 (h2.trans h.symm), ?_⟩
          simp [Walk.EdgeMatches, h2]
        · rcases ih (r + 1) hrest hq' with ⟨h_ge, h_lt, h_n, h_ne, h_em⟩
          have hsub : q.1 - r = (q.1 - (r + 1)) + 1 := by omega
          refine ⟨by omega, by simp; omega, h_n, h_ne, ?_⟩
          simpa [hsub] using h_em
      · rcases List.mem_cons.mp hq with rfl | hq'
        · refine ⟨le_rfl, by simp, he.1, fun h => h1 (h.trans h3.symm), ?_⟩
          simp [Walk.EdgeMatches, h3]
        · rcases ih (r + 1) hrest hq' with ⟨h_ge, h_lt, h_n, h_ne, h_em⟩
          have hsub : q.1 - r = (q.1 - (r + 1)) + 1 := by omega
          refine ⟨by omega, by simp; omega, h_n, h_ne, ?_⟩
          simpa [hsub] using h_em
      · rcases ih (r + 1) hrest hq with ⟨h_ge, h_lt, h_n, h_ne, h_em⟩
        have hsub : q.1 - r = (q.1 - (r + 1)) + 1 := by omega
        refine ⟨by omega, by simp; omega, h_n, h_ne, ?_⟩
        simpa [hsub] using h_em
  have hmem := hgen G.edges 0 hv _ (List.getElem_mem hj)
  refine ⟨by simpa [Cited.Graph.m] using hmem.2.1, hmem.2.2.1, hmem.2.2.2.1, ?_⟩
  simpa using hmem.2.2.2.2

lemma edge_mem_csrIncAux_of_ne {L : List (ℕ × ℕ)} {k r u v : ℕ}
    (hk : k < L.length) (hne : u ≠ v) (hm : Walk.EdgeMatches (L.getD k (0, 0)) u v) :
    (r + k, false, v) ∈ csrIncAux u r L ∨ (r + k, true, v) ∈ csrIncAux u r L := by
  induction L generalizing k r with
  | nil => simp at hk
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, Walk.EdgeMatches] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; simp [csrIncAux, hne]
      · right; simp [csrIncAux, hne.symm]
    | succ k' =>
      simp only [List.length_cons] at hk
      simp only [List.getD_cons_succ] at hm
      have ih' := ih (k := k') (r := r + 1) (by omega) hm
      have hadd : r + (k' + 1) = (r + 1) + k' := by omega
      rw [hadd]
      rcases ih' with h | h <;>
        [left; right] <;>
        · simp only [csrIncAux]
          split_ifs <;> simp [h]

lemma csrIncAux_take_length_le_two_mul_m {G : Cited.Graph} {u : ℕ} (hu : u < G.n) (k : ℕ) :
    (csrIncAux u 0 (G.edges.take k)).length ≤ 2 * G.m := by
  have h1 := csrIncAux_take_length_le u G.edges k
  have h2 := Finset.single_le_sum (f := fun v => (csrIncAux v 0 G.edges).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hu)
  have h3 : (Finset.range G.n).sum (fun v => (csrIncAux v 0 G.edges).length) ≤ 2 * G.m := by
    simpa [Cited.Graph.m] using csrIncAux_sum_le G.n G.edges 0
  omega

/-- Prefix-sum offset table for CSR adjacency of `G` (`csrOff G k` = total non-loop half-edges
for vertices `0 .. k - 1`). -/
def csrOff (G : Cited.Graph) (k : ℕ) : ℕ :=
  (Finset.range k).sum fun u => (csrIncAux u 0 G.edges).length

lemma csrOff_zero (G : Cited.Graph) : csrOff G 0 = 0 := by
  simp [csrOff]

lemma csrOff_succ (G : Cited.Graph) (k : ℕ) :
    csrOff G (k + 1) = csrOff G k + (csrIncAux k 0 G.edges).length := by
  simp [csrOff, Finset.sum_range_succ]

lemma csrOff_mono (G : Cited.Graph) {i j : ℕ} (hij : i ≤ j) : csrOff G i ≤ csrOff G j := by
  unfold csrOff
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

lemma csrOff_le_two_mul_m (G : Cited.Graph) (k : ℕ) : csrOff G k ≤ 2 * G.m := by
  simpa [csrOff, Cited.Graph.m] using csrIncAux_sum_le k G.edges 0

/-- Memory layout predicate asserting that CSR of `G` is stored at `csrAddr` in `2*G.n + 1 + 4*G.m`
words: `off[0..n]` at `csrAddr`, `adjVert[0..off[n]-1]` at `csrAddr + 2*G.n + 1`, and
`adjHalf[0..off[n]-1]` at `csrAddr + 2*G.n + 1 + 2*G.m`. -/
def HasCsrAt (mem : ℕ → ℕ) (csrAddr : ℕ) (G : Cited.Graph) : Prop :=
  (∀ u ≤ G.n, mem (csrAddr + u) = csrOff G u) ∧
  (∀ u < G.n, ∀ j (hj : j < (csrIncAux u 0 G.edges).length),
    let q := (csrIncAux u 0 G.edges)[j]'hj
    mem (csrAddr + 2 * G.n + 1 + csrOff G u + j) = q.2.2 ∧
    mem (csrAddr + 2 * G.n + 1 + 2 * G.m + csrOff G u + j) =
      2 * q.1 + (if q.2.1 then 1 else 0))

/-- Right-associative sequencing helper for clean Word-RAM procedures without deep parens. -/
abbrev seqStmts : List Stmt → Stmt
  | [] => .nop
  | [s] => s
  | s :: ss => .seq s (seqStmts ss)

lemma seqStmts_noRand : ∀ L : List Stmt, (∀ s ∈ L, s.NoRand) → (seqStmts L).NoRand
  | [], _ => by simp [Stmt.NoRand]
  | [s], h => h s (by simp)
  | s :: s' :: rest, h => by
    simp only [Stmt.NoRand]
    exact ⟨h s (by simp), seqStmts_noRand (s' :: rest) (fun x hx => h x (by simp [hx]))⟩

/-! ## 2. `buildCsrProc` (`O(n + m + 1)`) -/

/-- `buildCsrProc`: `args = [gAddr, csrAddr]`, builds `HasCsrAt mem' csrAddr G` in `O(n + m + 1)`
steps using `2*n + 1 + 4*m` words at `csrAddr`. -/
def buildCsrProc : Stmt :=
  seqStmts [
    .assign 2 (.load (.reg 0)), -- n := mem[gAddr]
    .assign 3 (.load (.bin .add (.reg 0) (.const 1))), -- m := mem[gAddr + 1]
    .assign 4 (.bin .add (.bin .add (.reg 1) (.reg 2)) (.const 1)), -- curBase
    .assign 5 (.bin .add (.reg 4) (.reg 2)), -- adjVBase
    .assign 6 (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 3))), -- adjHBase
    .assign 7 (.const 0), -- i := 0
    .loop (.bin .lt (.reg 7) (.reg 2))
      (.seq (.store (.bin .add (.reg 4) (.reg 7)) (.const 0))
        (.assign 7 (.bin .add (.reg 7) (.const 1)))),
    .assign 7 (.const 0), -- j := 0
    .loop (.bin .lt (.reg 7) (.reg 3))
      (seqStmts [
        .assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 7)))),
        .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 2) (.reg 7)))),
        .cond (.bin .eq (.reg 8) (.reg 9))
          .nop
          (seqStmts [
            .assign 10 (.load (.bin .add (.reg 4) (.reg 8))),
            .store (.bin .add (.reg 4) (.reg 8)) (.bin .add (.reg 10) (.const 1)),
            .assign 10 (.load (.bin .add (.reg 4) (.reg 9))),
            .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1))]),
        .assign 7 (.bin .add (.reg 7) (.const 1))]),
    .store (.reg 1) (.const 0), -- off[0] := 0
    .assign 8 (.const 0), -- acc := 0
    .assign 7 (.const 0), -- u := 0
    .loop (.bin .lt (.reg 7) (.reg 2))
      (seqStmts [
        .assign 9 (.load (.bin .add (.reg 4) (.reg 7))),
        .store (.bin .add (.reg 4) (.reg 7)) (.reg 8),
        .assign 8 (.bin .add (.reg 8) (.reg 9)),
        .store (.bin .add (.bin .add (.reg 1) (.reg 7)) (.const 1)) (.reg 8),
        .assign 7 (.bin .add (.reg 7) (.const 1))]),
    .assign 7 (.const 0), -- j := 0
    .loop (.bin .lt (.reg 7) (.reg 3))
      (seqStmts [
        .assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 7)))),
        .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 2) (.reg 7)))),
        .cond (.bin .eq (.reg 8) (.reg 9))
          .nop
          (.seq
            (seqStmts [
              .assign 10 (.load (.bin .add (.reg 4) (.reg 8))),
              .store (.bin .add (.reg 4) (.reg 8)) (.bin .add (.reg 10) (.const 1)),
              .store (.bin .add (.reg 5) (.reg 10)) (.reg 9),
              .store (.bin .add (.reg 6) (.reg 10)) (.bin .mul (.const 2) (.reg 7))])
            (seqStmts [
              .assign 11 (.load (.bin .add (.reg 4) (.reg 9))),
              .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 11) (.const 1)),
              .store (.bin .add (.reg 5) (.reg 11)) (.reg 8),
              .store (.bin .add (.reg 6) (.reg 11)) (.bin .add (.bin .mul (.const 2) (.reg 7)) (.const 1))])),
        .assign 7 (.bin .add (.reg 7) (.const 1))]),
    .ret (.const 0)
  ]

lemma buildCsrProc_noRand : buildCsrProc.NoRand := by
  simp [buildCsrProc, Stmt.NoRand]

/-- Contract for `buildCsrProc`: args `[gAddr, csrAddr]`. -/
def buildCsrContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr csrAddr : ℕ) (G : Cited.Graph),
      args = [gAddr, csrAddr] ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      gAddr + G.encode.length ≤ csrAddr ∧
      csrAddr + 2 * G.n + 1 + 4 * G.m < 2 ^ w ∧
      4 ≤ 2 ^ w
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let csrAddr := args.getD 1 0
    let G := Cited.readGraph mem gAddr
    v = 0 ∧
    HasCsrAt mem' csrAddr G ∧
    MemFrame mem mem' csrAddr (csrAddr + 2 * G.n + 1 + 4 * G.m)
  cost args mem :=
    let G := Cited.readGraph mem (args.getD 0 0)
    200 * (G.n + G.m + 1)

private lemma buildCsr_loop1 {w : ℕ} {p : Program}
    (gAddr csrAddr curBase adjVBase adjHBase : ℕ) (G : Cited.Graph) (mem : ℕ → ℕ)
    (hwbound : csrAddr + 2 * G.n + 1 + 4 * G.m < 2 ^ w)
    (hcb : curBase = csrAddr + G.n + 1) :
    let Inv1 : State → Prop := fun st =>
      st.regs 0 = gAddr ∧ st.regs 1 = csrAddr ∧ st.regs 2 = G.n ∧ st.regs 3 = G.m ∧
      st.regs 4 = curBase ∧ st.regs 5 = adjVBase ∧ st.regs 6 = adjHBase ∧
      st.regs 7 ≤ G.n ∧
      MemFrame mem st.mem curBase (curBase + G.n) ∧
      (∀ i < st.regs 7, st.mem (curBase + i) = 0)
    Triple w p Inv1
      (.loop (.bin .lt (.reg 7) (.reg 2))
        (.seq (.store (.bin .add (.reg 4) (.reg 7)) (.const 0))
          (.assign 7 (.bin .add (.reg 7) (.const 1)))))
      (normalPost fun st' => Inv1 st' ∧ st'.regs 7 = G.n)
      (fun st => (3 + 12 + 1) * (G.n - st.regs 7) + 3 + 1) := by
  intro Inv1
  refine Triple.loop_const_normal (fun st => G.n - st.regs 7)
    (fun st => if st.regs 7 < G.n then 1 else 0) 12
    (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
    (fun st hInv h0 => by
      simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
      exact ⟨hInv, by rcases hInv with ⟨_, _, _, _, _, _, _, h7n, _⟩; omega⟩)
    (fun st hInv hne => ?_)
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hfr, hz⟩
  have hlt_cur : st.regs 4 + st.regs 7 < 2 ^ w := by rw [hr4, hcb]; omega
  wram_enter
  · subst hpre
    wram_run
    · refine ⟨⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, by simp; omega, ?_, ?_⟩, by simp; omega⟩
      · exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
      · intro i hi
        simp at hi
        dsimp only
        by_cases hii : i = st.regs 7
        · subst hii; rw [Function.update_self]
        · rw [Function.update_of_ne (by omega)]; exact hz i (by omega)
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega

private lemma loop2_ne_triple {w : ℕ} {p : Program}
    (st0 : State) (curBase a b cntA cntB : ℕ)
    (h4 : st0.regs 4 = curBase) (h8 : st0.regs 8 = a) (h9 : st0.regs 9 = b)
    (hne_ab : curBase + b ≠ curBase + a)
    (hmA : st0.mem (curBase + a) = cntA) (hmB : st0.mem (curBase + b) = cntB)
    (hca_w : curBase + a < 2 ^ w) (hcb_w2 : curBase + b < 2 ^ w)
    (h1_w : 1 < 2 ^ w) (hcA1 : cntA + 1 < 2 ^ w) (hcB1 : cntB + 1 < 2 ^ w) :
    Triple w p (fun st => st = st0)
      (seqStmts [
        .assign 10 (.load (.bin .add (.reg 4) (.reg 8))),
        .store (.bin .add (.reg 4) (.reg 8)) (.bin .add (.reg 10) (.const 1)),
        .assign 10 (.load (.bin .add (.reg 4) (.reg 9))),
        .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1))])
      (normalPost fun st' =>
        (∀ r ≤ 9, st'.regs r = st0.regs r) ∧
        st'.mem = Function.update (Function.update st0.mem (curBase + a) (cntA + 1))
          (curBase + b) (cntB + 1))
      (fun _ => 30) := by
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  have h4n : (4 : ℕ) ≠ 10 := by decide
  have h8n : (8 : ℕ) ≠ 10 := by decide
  have h9n : (9 : ℕ) ≠ 10 := by decide
  have he1 : (Expr.load (Expr.bin .add (.reg 4) (.reg 8))).eval w st = some cntA := by
    simp [Expr.eval, BinOp.eval, h4, h8, hca_w, hmA]
  refine runs_seq_assign_le he1 ?_
  have ha1 : (Expr.bin .add (.reg 4) (.reg 8)).eval w
      ({ mem := st.mem, regs := Function.update st.regs 10 cntA, pos := st.pos } : State) =
      some (curBase + a) := by
    simp [Expr.eval, BinOp.eval, h4, h8, hca_w]
  have hv1 : (Expr.bin .add (.reg 10) (.const 1)).eval w
      ({ mem := st.mem, regs := Function.update st.regs 10 cntA, pos := st.pos } : State) =
      some (cntA + 1) := by
    simp [Expr.eval, BinOp.eval, Function.update_self, h1_w, hcA1]
  refine runs_seq_store_le ha1 hv1 ?_
  have hmb' : Function.update st.mem (curBase + a) (cntA + 1) (curBase + b) = cntB := by
    rw [Function.update_of_ne hne_ab, hmB]
  have he2 : (Expr.load (Expr.bin .add (.reg 4) (.reg 9))).eval w
      ({ mem := Function.update st.mem (curBase + a) (cntA + 1),
         regs := Function.update st.regs 10 cntA, pos := st.pos } : State) = some cntB := by
    simp [Expr.eval, BinOp.eval, h4, h9, hcb_w2, hmb']
  refine runs_seq_assign_le he2 ?_
  have ha2 : (Expr.bin .add (.reg 4) (.reg 9)).eval w
      ({ mem := Function.update st.mem (curBase + a) (cntA + 1),
         regs := Function.update (Function.update st.regs 10 cntA) 10 cntB,
         pos := st.pos } : State) = some (curBase + b) := by
    simp [Expr.eval, BinOp.eval, h4, h9, hcb_w2]
  have hv2 : (Expr.bin .add (.reg 10) (.const 1)).eval w
      ({ mem := Function.update st.mem (curBase + a) (cntA + 1),
         regs := Function.update (Function.update st.regs 10 cntA) 10 cntB,
         pos := st.pos } : State) = some (cntB + 1) := by
    simp [Expr.eval, BinOp.eval, Function.update_self, h1_w, hcB1]
  refine runs_store_le ha2 hv2 ?_ ?_
  · refine ⟨fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10)], rfl⟩
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma buildCsr_loop2 {w : ℕ} {p : Program}
    (gAddr csrAddr curBase adjVBase adjHBase : ℕ) (G : Cited.Graph) (mem1 : ℕ → ℕ)
    (hG : GraphAt mem1 gAddr G) (hval : G.IsValid)
    (hdisj : gAddr + G.encode.length ≤ csrAddr)
    (hwbound : csrAddr + 2 * G.n + 1 + 4 * G.m < 2 ^ w)
    (hcb : curBase = csrAddr + G.n + 1) :
    let Inv2 : State → Prop := fun st =>
      st.regs 0 = gAddr ∧ st.regs 1 = csrAddr ∧ st.regs 2 = G.n ∧ st.regs 3 = G.m ∧
      st.regs 4 = curBase ∧ st.regs 5 = adjVBase ∧ st.regs 6 = adjHBase ∧
      st.regs 7 ≤ G.m ∧
      MemFrame mem1 st.mem curBase (curBase + G.n) ∧
      (∀ u < G.n, st.mem (curBase + u) = (csrIncAux u 0 (G.edges.take (st.regs 7))).length)
    Triple w p Inv2
      (.loop (.bin .lt (.reg 7) (.reg 3))
        (seqStmts [
          .assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 7)))),
          .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 2) (.reg 7)))),
          .cond (.bin .eq (.reg 8) (.reg 9))
            .nop
            (seqStmts [
              .assign 10 (.load (.bin .add (.reg 4) (.reg 8))),
              .store (.bin .add (.reg 4) (.reg 8)) (.bin .add (.reg 10) (.const 1)),
              .assign 10 (.load (.bin .add (.reg 4) (.reg 9))),
              .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 10) (.const 1))]),
          .assign 7 (.bin .add (.reg 7) (.const 1))]))
      (normalPost fun st' => Inv2 st' ∧ st'.regs 7 = G.m)
      (fun st => (3 + 65 + 1) * (G.m - st.regs 7) + 3 + 1) := by
  intro Inv2
  have henc_len : G.encode.length = 2 + 2 * G.m := graph_encode_length G
  refine Triple.loop_const_normal (fun st => G.m - st.regs 7)
    (fun st => if st.regs 7 < G.m then 1 else 0) 65
    (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
    (fun st hInv h0 => by
      simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
      exact ⟨hInv, by rcases hInv with ⟨_, _, _, _, _, _, _, h7m, _⟩; omega⟩)
    (fun st hInv hne => ?_)
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hfr, hdeg⟩
  have hj_lt : st.regs 7 < G.m := hne
  have hjE : st.regs 7 < G.edges.length := by simpa [Cited.Graph.m] using hj_lt
  have ha_eq : st.mem (gAddr + 2 + 2 * st.regs 7) = (G.edges[st.regs 7]'hjE).1 := by
    rw [hfr _ (Or.inl (by omega))]; exact graphAt_edge_fst hG hjE
  have hb_eq : st.mem (gAddr + 3 + 2 * st.regs 7) = (G.edges[st.regs 7]'hjE).2 := by
    rw [hfr _ (Or.inl (by omega))]; exact graphAt_edge_snd hG hjE
  have ha_lt_n : st.mem (gAddr + 2 + 2 * st.regs 7) < G.n := by
    rw [ha_eq]; exact (hval _ (List.getElem_mem hjE)).1
  have hb_lt_n : st.mem (gAddr + 3 + 2 * st.regs 7) < G.n := by
    rw [hb_eq]; exact (hval _ (List.getElem_mem hjE)).2
  have ha_cnt_lt : st.mem (curBase + st.mem (gAddr + 2 + 2 * st.regs 7)) + 1 < 2 ^ w := by
    rw [hdeg _ ha_lt_n]
    have := csrIncAux_take_length_le_two_mul_m ha_lt_n (st.regs 7)
    omega
  have hb_cnt_lt : st.mem (curBase + st.mem (gAddr + 3 + 2 * st.regs 7)) + 1 < 2 ^ w := by
    rw [hdeg _ hb_lt_n]
    have := csrIncAux_take_length_le_two_mul_m hb_lt_n (st.regs 7)
    omega
  have htake_succ : G.edges.take (st.regs 7 + 1) =
      G.edges.take (st.regs 7) ++ [(G.edges[st.regs 7]'hjE)] := List.take_succ_eq_append_getElem hjE
  wram_enter
  · subst hpre
    wram_step; wram_step; wram_step
    · -- a = b
      have hab_eq : (G.edges[st.regs 7]'hjE).1 = (G.edges[st.regs 7]'hjE).2 := by
        simpa [hr0, ha_eq, hb_eq] using hcond
      wram_run
      · refine ⟨⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, by simp; omega, hfr, ?_⟩, by simp; omega⟩
        intro u hu
        simp only [Function.update_self]
        rw [htake_succ, csrIncAux_append_singleton]
        simp only [hab_eq, ↓reduceIte, List.append_nil]
        exact hdeg u hu
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
    · -- a ≠ b
      have hab_ne : st.mem (gAddr + 2 + 2 * st.regs 7) ≠ st.mem (gAddr + 3 + 2 * st.regs 7) := by
        simpa [hr0] using hcond
      have ha_neq_b_mem : curBase + st.mem (gAddr + 2 + 2 * st.regs 7) ≠
          curBase + st.mem (gAddr + 3 + 2 * st.regs 7) := by omega
      have h1_w : 1 < 2 ^ w := by
        have := csrIncAux_take_length_le_two_mul_m ha_lt_n (st.regs 7); omega
      refine runs_seq_triple_le
        (loop2_ne_triple
          ({ mem := st.mem,
             regs := Function.update
               (Function.update st.regs 8 (st.mem (gAddr + 2 + 2 * st.regs 7)))
               9 (st.mem (st.regs 0 + 3 + 2 * st.regs 7)),
             pos := st.pos } : State)
          curBase
          (st.mem (gAddr + 2 + 2 * st.regs 7)) (st.mem (gAddr + 3 + 2 * st.regs 7))
          (st.mem (curBase + st.mem (gAddr + 2 + 2 * st.regs 7)))
          (st.mem (curBase + st.mem (gAddr + 3 + 2 * st.regs 7)))
          (by simp [hr4])
          (by simp)
          (by simp [hr0]) ha_neq_b_mem.symm
          rfl rfl (by omega) (by omega) h1_w ha_cnt_lt hb_cnt_lt)
        rfl (fun stA hA => ?_)
      rcases hA with ⟨hA_r, hA_mem⟩
      have hA_eq : ∀ u < 8, stA.regs u = st.regs u := by
        intro u hu
        rw [hA_r u (by omega)]
        have hu8 : u ≠ 8 := by omega
        have hu9 : u ≠ 9 := by omega
        simp [hu8, hu9]
      have hA_r7 : stA.regs 7 = st.regs 7 := hA_eq 7 (by omega)
      have he7 : (Expr.bin .add (.reg 7) (.const 1)).eval w stA = some (st.regs 7 + 1) := by
        simp [Expr.eval, BinOp.eval, hA_r7, h1_w, show st.regs 7 + 1 < 2 ^ w by omega]
      refine runs_assign_le he7 ?_ ?_
      · dsimp only [normalPost]
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simpa [Function.update_of_ne (by decide : (0 : ℕ) ≠ 7)] using
            by rw [hA_eq 0 (by omega), hr0]
        · simpa [Function.update_of_ne (by decide : (1 : ℕ) ≠ 7)] using
            by rw [hA_eq 1 (by omega), hr1]
        · simpa [Function.update_of_ne (by decide : (2 : ℕ) ≠ 7)] using
            by rw [hA_eq 2 (by omega), hr2]
        · simpa [Function.update_of_ne (by decide : (3 : ℕ) ≠ 7)] using
            by rw [hA_eq 3 (by omega), hr3]
        · simpa [Function.update_of_ne (by decide : (4 : ℕ) ≠ 7)] using
            by rw [hA_eq 4 (by omega), hr4]
        · simpa [Function.update_of_ne (by decide : (5 : ℕ) ≠ 7)] using
            by rw [hA_eq 5 (by omega), hr5]
        · simpa [Function.update_of_ne (by decide : (6 : ℕ) ≠ 7)] using
            by rw [hA_eq 6 (by omega), hr6]
        · dsimp only; rw [Function.update_self]; omega
        · dsimp only at hA_mem ⊢
          rw [hA_mem]
          exact memFrame_trans hfr (memFrame_trans
            (memFrame_update (by omega) (by omega))
            (memFrame_update (by omega) (by omega)))
        · intro u hu
          dsimp only at hA_mem ⊢
          rw [Function.update_self, hA_mem, htake_succ, csrIncAux_append_singleton,
            show (G.edges[st.regs 7]'hjE).1 = st.mem (gAddr + 2 + 2 * st.regs 7) from ha_eq.symm,
            show (G.edges[st.regs 7]'hjE).2 = st.mem (gAddr + 3 + 2 * st.regs 7) from hb_eq.symm]
          simp only [hab_ne, ↓reduceIte]
          by_cases hua : u = st.mem (gAddr + 2 + 2 * st.regs 7)
          · subst hua
            simp only [↓reduceIte, Function.update_of_ne ha_neq_b_mem, Function.update_self,
              hdeg _ ha_lt_n, List.length_append, List.length_singleton]
          · simp only [Ne.symm hua, ↓reduceIte]
            by_cases hub : u = st.mem (gAddr + 3 + 2 * st.regs 7)
            · subst hub
              simp only [↓reduceIte, Function.update_self,
                hdeg _ hb_lt_n, List.length_append, List.length_singleton]
            · simp only [Ne.symm hub, ↓reduceIte,
                Function.update_of_ne (by omega : curBase + u ≠ curBase + st.mem (gAddr + 3 + 2 * st.regs 7)),
                Function.update_of_ne (by omega : curBase + u ≠ curBase + st.mem (gAddr + 2 + 2 * st.regs 7)),
                List.append_nil]
              exact hdeg u hu
        · simp only [Function.update_self]; omega
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma buildCsr_loop3 {w : ℕ} {p : Program}
    (gAddr csrAddr curBase adjVBase adjHBase : ℕ) (G : Cited.Graph) (mem2 : ℕ → ℕ)
    (hwbound : csrAddr + 2 * G.n + 1 + 4 * G.m < 2 ^ w)
    (hcb : curBase = csrAddr + G.n + 1) (hav : adjVBase = curBase + G.n)
    (hdeg2 : ∀ u < G.n, mem2 (curBase + u) = (csrIncAux u 0 G.edges).length) :
    let Inv3 : State → Prop := fun st =>
      st.regs 0 = gAddr ∧ st.regs 1 = csrAddr ∧ st.regs 2 = G.n ∧ st.regs 3 = G.m ∧
      st.regs 4 = curBase ∧ st.regs 5 = adjVBase ∧ st.regs 6 = adjHBase ∧
      st.regs 7 ≤ G.n ∧
      st.regs 8 = csrOff G (st.regs 7) ∧
      MemFrame mem2 st.mem csrAddr adjVBase ∧
      (∀ u ≤ st.regs 7, st.mem (csrAddr + u) = csrOff G u) ∧
      (∀ u < st.regs 7, st.mem (curBase + u) = csrOff G u) ∧
      (∀ u, st.regs 7 ≤ u → u < G.n → st.mem (curBase + u) = mem2 (curBase + u))
    Triple w p Inv3
      (.loop (.bin .lt (.reg 7) (.reg 2))
        (seqStmts [
          .assign 9 (.load (.bin .add (.reg 4) (.reg 7))),
          .store (.bin .add (.reg 4) (.reg 7)) (.reg 8),
          .assign 8 (.bin .add (.reg 8) (.reg 9)),
          .store (.bin .add (.bin .add (.reg 1) (.reg 7)) (.const 1)) (.reg 8),
          .assign 7 (.bin .add (.reg 7) (.const 1))]))
      (normalPost fun st' => Inv3 st' ∧ st'.regs 7 = G.n)
      (fun st => (3 + 40 + 1) * (G.n - st.regs 7) + 3 + 1) := by
  intro Inv3
  refine Triple.loop_const_normal (fun st => G.n - st.regs 7)
    (fun st => if st.regs 7 < G.n then 1 else 0) 40
    (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
    (fun st hInv h0 => by
      simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
      exact ⟨hInv, by rcases hInv with ⟨_, _, _, _, _, _, _, h7n, _⟩; omega⟩)
    (fun st hInv hne => ?_)
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hfr, hoff, hcur_done, hcur_rem⟩
  have hu_lt : st.regs 7 < G.n := hne
  have hd_val : st.mem (curBase + st.regs 7) = (csrIncAux (st.regs 7) 0 G.edges).length := by
    rw [hcur_rem _ le_rfl hu_lt, hdeg2 _ hu_lt]
  have hacc_lt : st.regs 8 + st.mem (curBase + st.regs 7) < 2 ^ w := by
    rw [hr8, hd_val, ← csrOff_succ]
    have := csrOff_le_two_mul_m G (st.regs 7 + 1)
    omega
  wram_enter
  · subst hpre
    wram_run
    · refine ⟨⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, by simp; omega,
        by simp; rw [hr8, hd_val, csrOff_succ], ?_, ?_, ?_, ?_⟩, by simp; omega⟩
      · rw [hr1, hr4]
        exact memFrame_trans hfr (memFrame_trans
          (memFrame_update (by omega) (by omega))
          (memFrame_update (by omega) (by omega)))
      · intro u hu
        simp only [Function.update_self] at hu
        dsimp only
        by_cases huu : u = st.regs 7 + 1
        · subst huu
          rw [hr1, hr4, show csrAddr + (st.regs 7 + 1) = csrAddr + st.regs 7 + 1 by omega,
            Function.update_self, hr8, hd_val, csrOff_succ]
        · rw [hr1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hoff u (by omega)
      · intro u hu
        simp only [Function.update_self] at hu
        dsimp only
        by_cases huu : u = st.regs 7
        · subst huu
          rw [hr1, hr4, Function.update_of_ne (by omega), Function.update_self, hr8]
        · rw [hr1, hr4, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hcur_done u (by omega)
      · intro u hu1 hu2
        simp only [Function.update_self] at hu1
        dsimp only
        rw [hr1, hr4, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hcur_rem u (by omega) hu2
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma loop4_half_triple {w : ℕ} {p : Program}
    (rTmp rU rV : ℕ) (eEdge : Expr) (st0 : State) (u v posU valE ec : ℕ)
    (hrTmp : 10 ≤ rTmp)
    (hrU : rU = 8 ∨ rU = 9) (hrV : rV = 8 ∨ rV = 9)
    (hu_eq : st0.regs rU = u) (hv_eq : st0.regs rV = v)
    (hposU : st0.mem (st0.regs 4 + u) = posU)
    (haddrU_lt : st0.regs 4 + u < 2 ^ w)
    (hposU1 : posU + 1 < 2 ^ w)
    (h5pos : st0.regs 5 + posU < 2 ^ w) (h6pos : st0.regs 6 + posU < 2 ^ w)
    (hd1 : st0.regs 4 + u < st0.regs 5 + posU) (hd2 : st0.regs 5 + posU < st0.regs 6 + posU)
    (h1_lt : 1 < 2 ^ w)
    (heval : ∀ regs, (∀ r ≤ 9, regs r = st0.regs r) → ∀ mem pos,
      eEdge.eval w ⟨mem, regs, pos⟩ = some valE)
    (hecost : eEdge.size ≤ ec) :
    Triple w p (fun st => st = st0)
      (seqStmts [
        .assign rTmp (.load (.bin .add (.reg 4) (.reg rU))),
        .store (.bin .add (.reg 4) (.reg rU)) (.bin .add (.reg rTmp) (.const 1)),
        .store (.bin .add (.reg 5) (.reg rTmp)) (.reg rV),
        .store (.bin .add (.reg 6) (.reg rTmp)) eEdge])
      (normalPost fun st' =>
        (∀ r ≤ 9, st'.regs r = st0.regs r) ∧
        st'.mem (st0.regs 4 + u) = posU + 1 ∧
        st'.mem (st0.regs 5 + posU) = v ∧
        st'.mem (st0.regs 6 + posU) = valE ∧
        ∀ addr, addr ≠ st0.regs 4 + u → addr ≠ st0.regs 5 + posU → addr ≠ st0.regs 6 + posU →
          st'.mem addr = st0.mem addr)
      (fun _ => 25 + ec) := by
  intro st ω hpre
  subst hpre
  refine runs_start_le ?_
  have h4_ne : (4 : ℕ) ≠ rTmp := by omega
  have h5_ne : (5 : ℕ) ≠ rTmp := by omega
  have h6_ne : (6 : ℕ) ≠ rTmp := by omega
  have hu_ne : rU ≠ rTmp := by rcases hrU with rfl | rfl <;> omega
  have hv_ne : rV ≠ rTmp := by rcases hrV with rfl | rfl <;> omega
  have he1 : (Expr.load (Expr.bin .add (.reg 4) (.reg rU))).eval w st = some posU := by
    simp [Expr.eval, BinOp.eval, hu_eq, haddrU_lt, hposU]
  refine runs_seq_assign_le he1 ?_
  have ha1 : (Expr.bin .add (.reg 4) (.reg rU)).eval w
      ({ mem := st.mem, regs := Function.update st.regs rTmp posU, pos := st.pos } : State) =
      some (st.regs 4 + u) := by
    simp [Expr.eval, BinOp.eval, Function.update_of_ne h4_ne, Function.update_of_ne hu_ne,
      hu_eq, haddrU_lt]
  have hv1 : (Expr.bin .add (.reg rTmp) (.const 1)).eval w
      ({ mem := st.mem, regs := Function.update st.regs rTmp posU, pos := st.pos } : State) =
      some (posU + 1) := by
    simp [Expr.eval, BinOp.eval, Function.update_self, h1_lt, hposU1]
  refine runs_seq_store_le ha1 hv1 ?_
  have ha2 : (Expr.bin .add (.reg 5) (.reg rTmp)).eval w
      ({ mem := Function.update st.mem (st.regs 4 + u) (posU + 1),
         regs := Function.update st.regs rTmp posU, pos := st.pos } : State) =
      some (st.regs 5 + posU) := by
    simp [Expr.eval, BinOp.eval, Function.update_of_ne h5_ne, Function.update_self, h5pos]
  have hv2 : (Expr.reg rV).eval w
      ({ mem := Function.update st.mem (st.regs 4 + u) (posU + 1),
         regs := Function.update st.regs rTmp posU, pos := st.pos } : State) =
      some v := by
    simp [Expr.eval, Function.update_of_ne hv_ne, hv_eq]
  refine runs_seq_store_le ha2 hv2 ?_
  have ha3 : (Expr.bin .add (.reg 6) (.reg rTmp)).eval w
      ({ mem := Function.update (Function.update st.mem (st.regs 4 + u) (posU + 1))
          (st.regs 5 + posU) v,
         regs := Function.update st.regs rTmp posU, pos := st.pos } : State) =
      some (st.regs 6 + posU) := by
    simp [Expr.eval, BinOp.eval, Function.update_of_ne h6_ne, Function.update_self, h6pos]
  have hv3 := heval (Function.update st.regs rTmp posU)
    (fun r hr => by rw [Function.update_of_ne (by omega)])
    (Function.update (Function.update st.mem (st.regs 4 + u) (posU + 1)) (st.regs 5 + posU) v)
    st.pos
  refine runs_store_le ha3 hv3 ?_ ?_
  · refine ⟨fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)], ?_, ?_, ?_, ?_⟩
    · dsimp only
      have hne1 : st.regs 4 + u ≠ st.regs 6 + posU := by omega
      have hne2 : st.regs 4 + u ≠ st.regs 5 + posU := by omega
      rw [Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_self]
    · dsimp only
      have hne1 : st.regs 5 + posU ≠ st.regs 6 + posU := by omega
      rw [Function.update_of_ne hne1, Function.update_self]
    · dsimp only; rw [Function.update_self]
    · intro addr ha1' ha2' ha3'
      dsimp only
      rw [Function.update_of_ne ha3', Function.update_of_ne ha2', Function.update_of_ne ha1']
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma loop4_fill_step (G : Cited.Graph)
    (curBase adjVBase adjHBase a b posA posB j : ℕ)
    (hav : adjVBase = curBase + G.n) (hah : adjHBase = adjVBase + 2 * G.m)
    (ha_lt : a < G.n) (hb_lt : b < G.n) (hab_ne : a ≠ b)
    (hposA_eq : posA = csrOff G a + (csrIncAux a 0 (G.edges.take j)).length)
    (hposB_eq : posB = csrOff G b + (csrIncAux b 0 (G.edges.take j)).length)
    (hposA_lt : posA < 2 * G.m) (hposB_lt : posB < 2 * G.m)
    (hposAB_ne : posA ≠ posB)
    (hincA_lt : (csrIncAux a 0 (G.edges.take j)).length < (csrIncAux a 0 G.edges).length)
    (hincB_lt : (csrIncAux b 0 (G.edges.take j)).length < (csrIncAux b 0 G.edges).length)
    (hinc_ne : ∀ u, csrIncAux u 0 (G.edges.take (j + 1)) =
      csrIncAux u 0 (G.edges.take j) ++
        (if u = a then [(j, false, b)] else if u = b then [(j, true, a)] else []))
    {mPre mMid mPost : ℕ → ℕ}
    (hfill : ∀ u < G.n, ∀ t (ht : t < (csrIncAux u 0 (G.edges.take j)).length),
      let q := (csrIncAux u 0 (G.edges.take j))[t]'ht
      mPre (adjVBase + csrOff G u + t) = q.2.2 ∧
      mPre (adjHBase + csrOff G u + t) = 2 * q.1 + (if q.2.1 then 1 else 0))
    (hA_V : mMid (adjVBase + posA) = b) (hA_H : mMid (adjHBase + posA) = 2 * j)
    (hA_oth : ∀ addr, addr ≠ curBase + a → addr ≠ adjVBase + posA → addr ≠ adjHBase + posA →
      mMid addr = mPre addr)
    (hB_V : mPost (adjVBase + posB) = a) (hB_H : mPost (adjHBase + posB) = 2 * j + 1)
    (hB_oth : ∀ addr, addr ≠ curBase + b → addr ≠ adjVBase + posB → addr ≠ adjHBase + posB →
      mPost addr = mMid addr) :
    ∀ u < G.n, ∀ t (ht : t < (csrIncAux u 0 (G.edges.take (j + 1))).length),
      let q := (csrIncAux u 0 (G.edges.take (j + 1)))[t]'ht
      mPost (adjVBase + csrOff G u + t) = q.2.2 ∧
      mPost (adjHBase + csrOff G u + t) = 2 * q.1 + (if q.2.1 then 1 else 0) := by
  intro u hu t ht
  simp only [hinc_ne] at ht ⊢
  have hle_m : csrOff G u + t < 2 * G.m := by
    by_cases hua : u = a
    · simp only [hua, ↓reduceIte, List.length_append, List.length_singleton] at ht
      have hOffA := csrOff_le_two_mul_m G (a + 1); rw [csrOff_succ] at hOffA
      rw [hua]; omega
    · simp only [hua, ↓reduceIte] at ht
      by_cases hub : u = b
      · simp only [hub, ↓reduceIte, List.length_append, List.length_singleton] at ht
        have hOffB := csrOff_le_two_mul_m G (b + 1); rw [csrOff_succ] at hOffB
        rw [hub]; omega
      · simp only [hub, ↓reduceIte, List.append_nil] at ht
        have hOffU := csrOff_le_two_mul_m G (u + 1); rw [csrOff_succ] at hOffU
        have := csrIncAux_take_length_le u G.edges j
        omega
  by_cases hua : u = a
  · simp only [hua, ↓reduceIte] at ht ⊢
    set lenA := (csrIncAux a 0 (G.edges.take j)).length
    by_cases ht_last : t = lenA
    · subst ht_last
      have hget_last : (csrIncAux a 0 (G.edges.take j) ++ [(j, false, b)])[lenA]'ht = (j, false, b) := by
        simp [lenA]
      rw [hget_last]
      have hV_eq : adjVBase + csrOff G a + lenA = adjVBase + posA := by
        rw [Nat.add_assoc, ← hposA_eq]
      have hH_eq : adjHBase + csrOff G a + lenA = adjHBase + posA := by
        rw [Nat.add_assoc, ← hposA_eq]
      rw [hV_eq, hH_eq]
      have hne_BV : adjVBase + posA ≠ adjVBase + posB := fun h => hposAB_ne (by omega)
      have hne_BH : adjHBase + posA ≠ adjHBase + posB := fun h => hposAB_ne (by omega)
      refine ⟨?_, ?_⟩
      · rw [hB_oth (adjVBase + posA) (by omega) hne_BV (by omega), hA_V]
      · rw [hB_oth (adjHBase + posA) (by omega) (by omega) hne_BH, hA_H]; simp
    · have ht_old : t < lenA := by
        simp only [List.length_append, List.length_singleton] at ht; omega
      simp only [List.getElem_append_left ht_old]
      have hne_A : adjVBase + csrOff G a + t ≠ adjVBase + posA ∧
          adjHBase + csrOff G a + t ≠ adjHBase + posA := by rw [hposA_eq]; omega
      have hne_B : adjVBase + csrOff G a + t ≠ adjVBase + posB ∧
          adjHBase + csrOff G a + t ≠ adjHBase + posB := by
        rw [hposB_eq]
        rcases lt_trichotomy a b with h | h | h
        · have h1 : t < (csrIncAux a 0 G.edges).length :=
            lt_of_lt_of_le ht_old (csrIncAux_take_length_le a G.edges j)
          have h2 := csrOff_mono G (show a + 1 ≤ b by omega)
          rw [csrOff_succ] at h2; omega
        · exact False.elim (hab_ne h)
        · have h2 := csrOff_mono G (show b + 1 ≤ a by omega)
          rw [csrOff_succ] at h2; omega
      have hold := hfill a ha_lt t ht_old
      refine ⟨?_, ?_⟩
      · rw [hB_oth _ (by omega) hne_B.1 (by omega), hA_oth _ (by omega) hne_A.1 (by omega)]
        exact hold.1
      · rw [hB_oth _ (by omega) (by omega) hne_B.2, hA_oth _ (by omega) (by omega) hne_A.2]
        exact hold.2
  · simp only [hua, ↓reduceIte] at ht ⊢
    by_cases hub : u = b
    · simp only [hub, ↓reduceIte] at ht ⊢
      set lenB := (csrIncAux b 0 (G.edges.take j)).length
      by_cases ht_last : t = lenB
      · subst ht_last
        have hget_last : (csrIncAux b 0 (G.edges.take j) ++ [(j, true, a)])[lenB]'ht = (j, true, a) := by
          simp [lenB]
        rw [hget_last]
        have hV_eq : adjVBase + csrOff G b + lenB = adjVBase + posB := by
          rw [Nat.add_assoc, ← hposB_eq]
        have hH_eq : adjHBase + csrOff G b + lenB = adjHBase + posB := by
          rw [Nat.add_assoc, ← hposB_eq]
        rw [hV_eq, hH_eq]
        refine ⟨hB_V, by rw [hB_H]; simp⟩
      · have ht_old : t < lenB := by
          simp only [List.length_append, List.length_singleton] at ht; omega
        simp only [List.getElem_append_left ht_old]
        have hne_B : adjVBase + csrOff G b + t ≠ adjVBase + posB ∧
            adjHBase + csrOff G b + t ≠ adjHBase + posB := by rw [hposB_eq]; omega
        have hne_A : adjVBase + csrOff G b + t ≠ adjVBase + posA ∧
            adjHBase + csrOff G b + t ≠ adjHBase + posA := by
          rw [hposA_eq]
          rcases lt_trichotomy b a with h | h | h
          · have h1 : t < (csrIncAux b 0 G.edges).length :=
              lt_of_lt_of_le ht_old (csrIncAux_take_length_le b G.edges j)
            have h2 := csrOff_mono G (show b + 1 ≤ a by omega)
            rw [csrOff_succ] at h2; omega
          · exact False.elim (hab_ne h.symm)
          · have h2 := csrOff_mono G (show a + 1 ≤ b by omega)
            rw [csrOff_succ] at h2; omega
        have hold := hfill b hb_lt t ht_old
        refine ⟨?_, ?_⟩
        · rw [hB_oth _ (by omega) hne_B.1 (by omega), hA_oth _ (by omega) hne_A.1 (by omega)]
          exact hold.1
        · rw [hB_oth _ (by omega) (by omega) hne_B.2, hA_oth _ (by omega) (by omega) hne_A.2]
          exact hold.2
    · simp only [hub, ↓reduceIte, List.append_nil] at ht ⊢
      have hne_A : adjVBase + csrOff G u + t ≠ adjVBase + posA ∧
          adjHBase + csrOff G u + t ≠ adjHBase + posA := by
        rw [hposA_eq]
        rcases lt_trichotomy u a with h | h | h
        · have h1 : t < (csrIncAux u 0 G.edges).length :=
            lt_of_lt_of_le ht (csrIncAux_take_length_le u G.edges j)
          have h2 := csrOff_mono G (show u + 1 ≤ a by omega)
          rw [csrOff_succ] at h2; omega
        · exact False.elim (hua h)
        · have h2 := csrOff_mono G (show a + 1 ≤ u by omega)
          rw [csrOff_succ] at h2; omega
      have hne_B : adjVBase + csrOff G u + t ≠ adjVBase + posB ∧
          adjHBase + csrOff G u + t ≠ adjHBase + posB := by
        rw [hposB_eq]
        rcases lt_trichotomy u b with h | h | h
        · have h1 : t < (csrIncAux u 0 G.edges).length :=
            lt_of_lt_of_le ht (csrIncAux_take_length_le u G.edges j)
          have h2 := csrOff_mono G (show u + 1 ≤ b by omega)
          rw [csrOff_succ] at h2; omega
        · exact False.elim (hub h)
        · have h2 := csrOff_mono G (show b + 1 ≤ u by omega)
          rw [csrOff_succ] at h2; omega
      have hold := hfill u hu t ht
      refine ⟨?_, ?_⟩
      · rw [hB_oth _ (by omega) hne_B.1 (by omega), hA_oth _ (by omega) hne_A.1 (by omega)]
        exact hold.1
      · rw [hB_oth _ (by omega) (by omega) hne_B.2, hA_oth _ (by omega) (by omega) hne_A.2]
        exact hold.2

private lemma buildCsr_loop4 {w : ℕ} {p : Program}
    (gAddr csrAddr curBase adjVBase adjHBase : ℕ) (G : Cited.Graph) (mem3 : ℕ → ℕ)
    (hG : GraphAt mem3 gAddr G) (hval : G.IsValid)
    (hdisj : gAddr + G.encode.length ≤ csrAddr)
    (hwbound : csrAddr + 2 * G.n + 1 + 4 * G.m < 2 ^ w)
    (hcb : curBase = csrAddr + G.n + 1) (hav : adjVBase = curBase + G.n)
    (hah : adjHBase = adjVBase + 2 * G.m)
    (hw4 : 4 ≤ 2 ^ w) :
    let Inv4 : State → Prop := fun st =>
      st.regs 0 = gAddr ∧ st.regs 1 = csrAddr ∧ st.regs 2 = G.n ∧ st.regs 3 = G.m ∧
      st.regs 4 = curBase ∧ st.regs 5 = adjVBase ∧ st.regs 6 = adjHBase ∧
      st.regs 7 ≤ G.m ∧
      MemFrame mem3 st.mem curBase (csrAddr + 2 * G.n + 1 + 4 * G.m) ∧
      (∀ u < G.n, st.mem (curBase + u) = csrOff G u + (csrIncAux u 0 (G.edges.take (st.regs 7))).length) ∧
      (∀ u < G.n, ∀ t (ht : t < (csrIncAux u 0 (G.edges.take (st.regs 7))).length),
        let q := (csrIncAux u 0 (G.edges.take (st.regs 7)))[t]'ht
        st.mem (adjVBase + csrOff G u + t) = q.2.2 ∧
        st.mem (adjHBase + csrOff G u + t) = 2 * q.1 + (if q.2.1 then 1 else 0))
    Triple w p Inv4
      (.loop (.bin .lt (.reg 7) (.reg 3))
        (seqStmts [
          .assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 7)))),
          .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 2) (.reg 7)))),
          .cond (.bin .eq (.reg 8) (.reg 9))
            .nop
            (.seq
              (seqStmts [
                .assign 10 (.load (.bin .add (.reg 4) (.reg 8))),
                .store (.bin .add (.reg 4) (.reg 8)) (.bin .add (.reg 10) (.const 1)),
                .store (.bin .add (.reg 5) (.reg 10)) (.reg 9),
                .store (.bin .add (.reg 6) (.reg 10)) (.bin .mul (.const 2) (.reg 7))])
              (seqStmts [
                .assign 11 (.load (.bin .add (.reg 4) (.reg 9))),
                .store (.bin .add (.reg 4) (.reg 9)) (.bin .add (.reg 11) (.const 1)),
                .store (.bin .add (.reg 5) (.reg 11)) (.reg 8),
                .store (.bin .add (.reg 6) (.reg 11)) (.bin .add (.bin .mul (.const 2) (.reg 7)) (.const 1))])),
          .assign 7 (.bin .add (.reg 7) (.const 1))]))
      (normalPost fun st' => Inv4 st' ∧ st'.regs 7 = G.m)
      (fun st => (3 + 100 + 1) * (G.m - st.regs 7) + 3 + 1) := by
  intro Inv4
  have henc_len : G.encode.length = 2 + 2 * G.m := graph_encode_length G
  refine Triple.loop_const_normal (fun st => G.m - st.regs 7)
    (fun st => if st.regs 7 < G.m then 1 else 0) 100
    (fun st hInv => by rcases hInv with ⟨_, _, _, _⟩; eval_expr)
    (fun st hInv h0 => by
      simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
      exact ⟨hInv, by rcases hInv with ⟨_, _, _, _, _, _, _, h7m, _⟩; omega⟩)
    (fun st hInv hne => ?_)
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hfr, hcur, hfill⟩
  have hj_lt : st.regs 7 < G.m := hne
  have hjE : st.regs 7 < G.edges.length := by simpa [Cited.Graph.m] using hj_lt
  have ha_eq : st.mem (gAddr + 2 + 2 * st.regs 7) = (G.edges[st.regs 7]'hjE).1 := by
    rw [hfr _ (Or.inl (by omega))]; exact graphAt_edge_fst hG hjE
  have hb_eq : st.mem (gAddr + 3 + 2 * st.regs 7) = (G.edges[st.regs 7]'hjE).2 := by
    rw [hfr _ (Or.inl (by omega))]; exact graphAt_edge_snd hG hjE
  have ha_lt_n : st.mem (gAddr + 2 + 2 * st.regs 7) < G.n := by
    rw [ha_eq]; exact (hval _ (List.getElem_mem hjE)).1
  have hb_lt_n : st.mem (gAddr + 3 + 2 * st.regs 7) < G.n := by
    rw [hb_eq]; exact (hval _ (List.getElem_mem hjE)).2
  let a := st.mem (gAddr + 2 + 2 * st.regs 7)
  let b := st.mem (gAddr + 3 + 2 * st.regs 7)
  have htake_succ : G.edges.take (st.regs 7 + 1) =
      G.edges.take (st.regs 7) ++ [(a, b)] := by
    have hs := List.take_succ_eq_append_getElem hjE
    rw [hs, show G.edges[st.regs 7]'hjE = (a, b) from Prod.ext ha_eq.symm hb_eq.symm]
  have htake_len : (G.edges.take (st.regs 7)).length = st.regs 7 := by
    rw [List.length_take]; exact min_eq_left (le_of_lt hjE)
  have hinc_a_lt : (csrIncAux a 0 (G.edges.take (st.regs 7))).length <
      (csrIncAux a 0 G.edges).length →
      csrOff G a + (csrIncAux a 0 (G.edges.take (st.regs 7))).length < csrOff G (a + 1) := by
    intro h; rw [csrOff_succ]; omega
  have hinc_b_lt : (csrIncAux b 0 (G.edges.take (st.regs 7))).length <
      (csrIncAux b 0 G.edges).length →
      csrOff G b + (csrIncAux b 0 (G.edges.take (st.regs 7))).length < csrOff G (b + 1) := by
    intro h; rw [csrOff_succ]; omega
  have hbounds_ne : a ≠ b →
      csrOff G a + (csrIncAux a 0 (G.edges.take (st.regs 7))).length < 2 * G.m ∧
      csrOff G b + (csrIncAux b 0 (G.edges.take (st.regs 7))).length < 2 * G.m ∧
      (csrIncAux a 0 (G.edges.take (st.regs 7))).length < (csrIncAux a 0 G.edges).length ∧
      (csrIncAux b 0 (G.edges.take (st.regs 7))).length < (csrIncAux b 0 G.edges).length := by
    intro hab
    have hA := csrIncAux_take_length_le a G.edges (st.regs 7 + 1)
    have hB := csrIncAux_take_length_le b G.edges (st.regs 7 + 1)
    rw [htake_succ, csrIncAux_append_singleton] at hA
    simp only [hab, ↓reduceIte, List.length_append, List.length_singleton] at hA
    rw [htake_succ, csrIncAux_append_singleton] at hB
    simp only [hab, ↓reduceIte, List.length_append, List.length_singleton] at hB
    have hOffA := csrOff_le_two_mul_m G (a + 1)
    have hOffB := csrOff_le_two_mul_m G (b + 1)
    rw [csrOff_succ] at hOffA hOffB
    refine ⟨by omega, by omega, hA, hB⟩
  have ha_pos_bound : a ≠ b → st.mem (curBase + a) + 1 < 2 ^ w ∧
      adjVBase + st.mem (curBase + a) < 2 ^ w ∧
      adjHBase + st.mem (curBase + a) < 2 ^ w := by
    intro hab
    have hbnd := hbounds_ne hab
    rw [hcur a ha_lt_n]
    omega
  have hb_pos_bound : a ≠ b → st.mem (curBase + b) + 1 < 2 ^ w ∧
      adjVBase + st.mem (curBase + b) < 2 ^ w ∧
      adjHBase + st.mem (curBase + b) < 2 ^ w := by
    intro hab
    have hbnd := hbounds_ne hab
    rw [hcur b hb_lt_n]
    omega
  wram_enter
  · subst hpre
    wram_step; wram_step; wram_step
    · -- a = b
      have hab_eq : a = b := by simpa [hr0] using hcond
      have hinc_eq : ∀ u, csrIncAux u 0 (G.edges.take (st.regs 7 + 1)) =
          csrIncAux u 0 (G.edges.take (st.regs 7)) := by
        intro u; rw [htake_succ, csrIncAux_append_singleton]; simp [hab_eq]
      wram_run
      · refine ⟨⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, by simp; omega, hfr, ?_, ?_⟩,
          by simp; omega⟩
        · intro u hu
          simp only [Function.update_self, hinc_eq]
          exact hcur u hu
        · intro u hu t ht
          simp only [Function.update_self, hinc_eq] at ht ⊢
          exact hfill u hu t ht
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
    · -- a ≠ b
      have hab_ne : a ≠ b := by simpa [hr0] using hcond
      have hbnd := hbounds_ne hab_ne
      have hpa := ha_pos_bound hab_ne
      have hpb := hb_pos_bound hab_ne
      let posA := st.mem (curBase + a)
      let posB := st.mem (curBase + b)
      have hposA_eq : posA = csrOff G a + (csrIncAux a 0 (G.edges.take (st.regs 7))).length :=
        hcur a ha_lt_n
      have hposB_eq : posB = csrOff G b + (csrIncAux b 0 (G.edges.take (st.regs 7))).length :=
        hcur b hb_lt_n
      have hposA_lt_all : posA < 2 * G.m := by rw [hposA_eq]; exact hbnd.1
      have hposB_lt_all : posB < 2 * G.m := by rw [hposB_eq]; exact hbnd.2.1
      have hposAB_ne : posA ≠ posB := by
        rw [hposA_eq, hposB_eq]
        rcases lt_trichotomy a b with h | h | h
        · have h1 := hinc_a_lt hbnd.2.2.1
          have h2 := csrOff_mono G (show a + 1 ≤ b by omega)
          omega
        · exact False.elim (hab_ne h)
        · have h1 := hinc_b_lt hbnd.2.2.2
          have h2 := csrOff_mono G (show b + 1 ≤ a by omega)
          omega
      have hinc_ne : ∀ u, csrIncAux u 0 (G.edges.take (st.regs 7 + 1)) =
          csrIncAux u 0 (G.edges.take (st.regs 7)) ++
            (if u = a then [(st.regs 7, false, b)]
             else if u = b then [(st.regs 7, true, a)] else []) := by
        intro u
        rw [htake_succ, csrIncAux_append_singleton]
        simp only [hab_ne, ↓reduceIte, htake_len]
        congr 1
        by_cases hua : u = a
        · subst hua; simp
        · simp [hua, Ne.symm hua]
          by_cases hub : u = b
          · subst hub; simp
          · simp [hub, Ne.symm hub]
      have h2_lt : 2 < 2 ^ w := by omega
      have h1_lt : 1 < 2 ^ w := by omega
      have h2j_lt : 2 * st.regs 7 < 2 ^ w := by omega
      have h2j1_lt : 2 * st.regs 7 + 1 < 2 ^ w := by omega
      refine runs_seq_assoc_le ?_
      refine runs_seq_triple_le
        (loop4_half_triple 10 8 9 (.bin .mul (.const 2) (.reg 7)) _ a b posA (2 * st.regs 7) 3
          (by omega) (Or.inl rfl) (Or.inr rfl)
          (by simp [hr0]; rfl) (by simp [hr0]; rfl)
          (by simp [hr4]; rfl)
          (by simp [hr4]; omega) hpa.1
          (by simp [hr5]; exact hpa.2.1) (by simp [hr6]; exact hpa.2.2)
          (by simp [hr4, hr5]; omega) (by simp [hr5, hr6]; omega) h1_lt
          (fun regs hr _ _ => by
            have hr7' : regs 7 = st.regs 7 := by simpa using hr 7 (by omega)
            simp [Expr.eval, BinOp.eval, hr7', h2_lt, h2j_lt])
          (by simp [Expr.size_const, Expr.size_reg, Expr.size_bin]))
        rfl (fun stA hA => ?_)
      rcases hA with ⟨hA_r, hA_cur, hA_V, hA_H, hA_oth⟩
      simp only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 9),
        Function.update_of_ne (by decide : (4 : ℕ) ≠ 8),
        Function.update_of_ne (by decide : (5 : ℕ) ≠ 9),
        Function.update_of_ne (by decide : (5 : ℕ) ≠ 8),
        Function.update_of_ne (by decide : (6 : ℕ) ≠ 9),
        Function.update_of_ne (by decide : (6 : ℕ) ≠ 8),
        hr4, hr5, hr6] at hA_cur hA_V hA_H hA_oth
      have hA4 : stA.regs 4 = curBase := by simpa [hr4] using hA_r 4 (by omega)
      have hA5 : stA.regs 5 = adjVBase := by simpa [hr5] using hA_r 5 (by omega)
      have hA6 : stA.regs 6 = adjHBase := by simpa [hr6] using hA_r 6 (by omega)
      have hA7 : stA.regs 7 = st.regs 7 := by simpa using hA_r 7 (by omega)
      have hA8 : stA.regs 8 = a := by simpa [hr0] using hA_r 8 (by omega)
      have hA9 : stA.regs 9 = b := by simpa [hr0] using hA_r 9 (by omega)
      have hA_curB : stA.mem (stA.regs 4 + b) = posB := by
        rw [hA4, hA_oth (curBase + b) (by omega) (by omega) (by omega)]
      refine runs_seq_triple_le
        (loop4_half_triple 11 9 8 (.bin .add (.bin .mul (.const 2) (.reg 7)) (.const 1))
          stA b a posB (2 * st.regs 7 + 1) 5
          (by omega) (Or.inr rfl) (Or.inl rfl)
          hA9 hA8 hA_curB
          (by rw [hA4]; omega) hpb.1
          (by rw [hA5]; exact hpb.2.1) (by rw [hA6]; exact hpb.2.2)
          (by rw [hA4, hA5]; omega) (by rw [hA5, hA6]; omega) h1_lt
          (fun regs hr _ _ => by
            have hr7' : regs 7 = st.regs 7 := by rw [hr 7 (by omega), hA7]
            simp [Expr.eval, BinOp.eval, hr7', h2_lt, h1_lt, h2j_lt, h2j1_lt])
          (by simp [Expr.size_const, Expr.size_reg, Expr.size_bin]))
        rfl (fun stB hB => ?_)
      rcases hB with ⟨hB_r, hB_cur, hB_V, hB_H, hB_oth⟩
      rw [hA4] at hB_cur hB_oth
      rw [hA5] at hB_V hB_oth
      rw [hA6] at hB_H hB_oth
      have hB_eq : ∀ u < 8, stB.regs u = st.regs u := by
        intro u hu
        have hu1 := hB_r u (by omega)
        have hu2 := hA_r u (by omega)
        rw [hu1, hu2]
        have hu8 : u ≠ 8 := by omega
        have hu9 : u ≠ 9 := by omega
        simp [hu8, hu9]
      have hB_r0 : stB.regs 0 = gAddr := by rw [hB_eq 0 (by omega), hr0]
      have hB_r1 : stB.regs 1 = csrAddr := by rw [hB_eq 1 (by omega), hr1]
      have hB_r2 : stB.regs 2 = G.n := by rw [hB_eq 2 (by omega), hr2]
      have hB_r3 : stB.regs 3 = G.m := by rw [hB_eq 3 (by omega), hr3]
      have hB_r4 : stB.regs 4 = curBase := by rw [hB_eq 4 (by omega), hr4]
      have hB_r5 : stB.regs 5 = adjVBase := by rw [hB_eq 5 (by omega), hr5]
      have hB_r6 : stB.regs 6 = adjHBase := by rw [hB_eq 6 (by omega), hr6]
      have hB_r7 : stB.regs 7 = st.regs 7 := hB_eq 7 (by omega)
      clear hA_r hB_r hB_eq
      have hca_rng : curBase ≤ curBase + a ∧ curBase + a < csrAddr + 2 * G.n + 1 + 4 * G.m :=
        ⟨Nat.le_add_right _ _, by linarith only [hcb, ha_lt_n]⟩
      have hcb_rng : curBase ≤ curBase + b ∧ curBase + b < csrAddr + 2 * G.n + 1 + 4 * G.m :=
        ⟨Nat.le_add_right _ _, by linarith only [hcb, hb_lt_n]⟩
      have hva_rng : curBase ≤ adjVBase + posA ∧ adjVBase + posA < csrAddr + 2 * G.n + 1 + 4 * G.m :=
        ⟨by linarith only [hav], by linarith only [hcb, hav, hposA_lt_all]⟩
      have hvb_rng : curBase ≤ adjVBase + posB ∧ adjVBase + posB < csrAddr + 2 * G.n + 1 + 4 * G.m :=
        ⟨by linarith only [hav], by linarith only [hcb, hav, hposB_lt_all]⟩
      have hha_rng : curBase ≤ adjHBase + posA ∧ adjHBase + posA < csrAddr + 2 * G.n + 1 + 4 * G.m :=
        ⟨by linarith only [hav, hah], by linarith only [hcb, hav, hah, hposA_lt_all]⟩
      have hhb_rng : curBase ≤ adjHBase + posB ∧ adjHBase + posB < csrAddr + 2 * G.n + 1 + 4 * G.m :=
        ⟨by linarith only [hav, hah], by linarith only [hcb, hav, hah, hposB_lt_all]⟩
      have he7 : (Expr.bin .add (.reg 7) (.const 1)).eval w stB = some (st.regs 7 + 1) := by
        simp [Expr.eval, BinOp.eval, hB_r7, h1_lt, show st.regs 7 + 1 < 2 ^ w by linarith only [hne, hwbound]]
      refine runs_assign_le he7 ?_ ?_
      · dsimp only [normalPost]
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simpa [Function.update_of_ne (by decide : (0 : ℕ) ≠ 7)] using hB_r0
        · simpa [Function.update_of_ne (by decide : (1 : ℕ) ≠ 7)] using hB_r1
        · simpa [Function.update_of_ne (by decide : (2 : ℕ) ≠ 7)] using hB_r2
        · simpa [Function.update_of_ne (by decide : (3 : ℕ) ≠ 7)] using hB_r3
        · simpa [Function.update_of_ne (by decide : (4 : ℕ) ≠ 7)] using hB_r4
        · simpa [Function.update_of_ne (by decide : (5 : ℕ) ≠ 7)] using hB_r5
        · simpa [Function.update_of_ne (by decide : (6 : ℕ) ≠ 7)] using hB_r6
        · dsimp only; rw [Function.update_self]; linarith only [hne]
        · intro x hx
          dsimp only
          have hmemA_eq : stA.mem x = st.mem x := hA_oth x
            (by rcases hx with h | h <;> linarith only [h, hca_rng])
            (by rcases hx with h | h <;> linarith only [h, hva_rng])
            (by rcases hx with h | h <;> linarith only [h, hha_rng])
          have hmemB_eq : stB.mem x = stA.mem x := hB_oth x
            (by rcases hx with h | h <;> linarith only [h, hcb_rng])
            (by rcases hx with h | h <;> linarith only [h, hvb_rng])
            (by rcases hx with h | h <;> linarith only [h, hhb_rng])
          rw [hmemB_eq, hmemA_eq]; exact hfr x hx
        · intro u hu
          dsimp only
          rw [Function.update_self, hinc_ne]
          by_cases hua : u = a
          · subst hua
            simp only [↓reduceIte, List.length_append, List.length_singleton]
            rw [hB_oth (curBase + a)
              (fun h => hab_ne (by linarith only [h]))
              (by linarith only [hav, ha_lt_n])
              (by linarith only [hav, hah, ha_lt_n]),
              hA_cur, hposA_eq, Nat.add_assoc]
          · simp only [hua, ↓reduceIte]
            by_cases hub : u = b
            · subst hub
              simp only [↓reduceIte, List.length_append, List.length_singleton]
              rw [hB_cur, hposB_eq, Nat.add_assoc]
            · simp only [hub, ↓reduceIte, List.append_nil]
              rw [hB_oth (curBase + u)
                  (fun h => hub (by linarith only [h]))
                  (by linarith only [hav, hu])
                  (by linarith only [hav, hah, hu]),
                hA_oth (curBase + u)
                  (fun h => hua (by linarith only [h]))
                  (by linarith only [hav, hu])
                  (by linarith only [hav, hah, hu]),
                hcur u hu]
        · intro u hu t ht
          dsimp only at ht ⊢
          simp only [Function.update_self] at ht ⊢
          exact loop4_fill_step G curBase adjVBase adjHBase a b posA posB (st.regs 7)
            hav hah ha_lt_n hb_lt_n hab_ne hposA_eq hposB_eq hposA_lt_all hposB_lt_all hposAB_ne
            hbnd.2.2.1 hbnd.2.2.2 hinc_ne hfill hA_V hA_H hA_oth hB_V hB_H hB_oth u hu t ht
        · rw [Function.update_self]; omega
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

theorem buildCsr_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [buildCsrProc]) :
    MeetsContract w p b (buildCsrContract w) := by
  intro args mem pos ω hwords hpre
  dsimp only [buildCsrContract] at hpre
  rcases hpre with ⟨gAddr, csrAddr, G, rfl, hG, hval, hdisj, hwbound, hw4⟩
  have hproc : p.procs[b]? = some buildCsrProc := hp 0 (by simp)
  have hlt_g : gAddr < 2 ^ w := hwords gAddr (by simp)
  have hlt_c : csrAddr < 2 ^ w := hwords csrAddr (by simp)
  have hread : Cited.readGraph mem gAddr = G := graphAt_iff_readGraph.mp hG
  have hn_mem : mem gAddr = G.n := graphAt_n hG
  have hm_mem : mem (gAddr + 1) = G.m := graphAt_m hG
  have henc_len : G.encode.length = 2 + 2 * G.m := graph_encode_length G
  obtain ⟨curBase, hcb⟩ : ∃ x, x = csrAddr + G.n + 1 := ⟨_, rfl⟩
  obtain ⟨adjVBase, hav⟩ : ∃ x, x = curBase + G.n := ⟨_, rfl⟩
  obtain ⟨adjHBase, hah⟩ : ∃ x, x = adjVBase + 2 * G.m := ⟨_, rfl⟩
  have hadjV_eq : adjVBase = csrAddr + 2 * G.n + 1 := by omega
  have hadjH_eq : adjHBase = csrAddr + 2 * G.n + 1 + 2 * G.m := by omega
  have hle_cb : csrAddr ≤ curBase := by omega
  have hb_cur_end : curBase + G.n ≤ csrAddr + 2 * G.n + 1 + 4 * G.m := by omega
  have hb_adjV_end : adjVBase ≤ csrAddr + 2 * G.n + 1 + 4 * G.m := by omega
  have hcu_lt_cb : ∀ u ≤ G.n, csrAddr + u < curBase := fun u hu => by omega
  have hl1 := buildCsr_loop1 (p := p) gAddr csrAddr curBase adjVBase adjHBase G mem hwbound hcb
  have htriple :
      Triple w p
        (fun st => st = startState [gAddr, csrAddr] mem pos)
        buildCsrProc
        (fun o st' => o = .returned 0 ∧
          HasCsrAt st'.mem csrAddr G ∧
          MemFrame mem st'.mem csrAddr (csrAddr + 2 * G.n + 1 + 4 * G.m))
        (fun _ => 200 * (G.n + G.m + 1)) := by
    wram_enter
    · subst hpre
      dsimp only [buildCsrProc]
      wram_step; wram_step; wram_step; wram_step; wram_step; wram_step
      refine runs_seq_triple_le hl1 ?_ (fun st1 hst1 => ?_)
      · refine ⟨by simp [startState], by simp [startState], by simp [startState, hn_mem],
          by simp [startState, hm_mem], by simp [startState, hn_mem, hcb],
          by simp [startState, hn_mem, hav, hcb],
          by simp [startState, hn_mem, hm_mem, hah, hav, hcb],
          by simp, memFrame_refl _ _ _, fun i hi => by simp at hi⟩
      rcases hst1 with ⟨⟨hs1_0, hs1_1, hs1_2, hs1_3, hs1_4, hs1_5, hs1_6, _, hfr1, hz1⟩, hs1_7⟩
      have hG1 : GraphAt st1.mem gAddr G :=
        hG.of_agree_below hdisj fun k hk => hfr1 k (Or.inl (by omega))
      have hl2 := buildCsr_loop2 (p := p) gAddr csrAddr curBase adjVBase adjHBase G st1.mem
        hG1 hval hdisj hwbound hcb
      wram_step
      refine runs_seq_triple_le hl2 ?_ (fun st2 hst2 => ?_)
      · refine ⟨hs1_0, hs1_1, hs1_2, hs1_3, hs1_4, hs1_5, hs1_6, Nat.zero_le _,
          memFrame_refl _ _ _, ?_⟩
        intro u hu
        simp only [Function.update_self, List.take_zero, csrIncAux, List.length_nil]
        exact hz1 u (hs1_7 ▸ hu)
      rcases hst2 with ⟨⟨hs2_0, hs2_1, hs2_2, hs2_3, hs2_4, hs2_5, hs2_6, _, hfr2, hdeg2⟩, hs2_7⟩
      have hdeg2' : ∀ u < G.n, st2.mem (curBase + u) = (csrIncAux u 0 G.edges).length := by
        intro u hu
        have := hdeg2 u hu
        rwa [hs2_7, List.take_of_length_le (by simp [Cited.Graph.m])] at this
      have hl3 := buildCsr_loop3 (p := p) gAddr csrAddr curBase adjVBase adjHBase G st2.mem
        hwbound hcb hav hdeg2'
      wram_step; wram_step; wram_step
      refine runs_seq_triple_le hl3 ?_ (fun st3 hst3 => ?_)
      · refine ⟨hs2_0, hs2_1, hs2_2, hs2_3, hs2_4, hs2_5, hs2_6, Nat.zero_le _,
          by simp [csrOff_zero], memFrame_update le_rfl (by omega),
          ?_, fun u hu => by simp at hu, ?_⟩
        · intro u hu
          have hu0 : u = 0 := by simp at hu; omega
          subst hu0; simp [Function.update_self, csrOff_zero]
        · intro u hu2' hu2
          dsimp only at hu2' ⊢
          rw [Function.update_of_ne (by omega)]
      rcases hst3 with ⟨⟨hs3_0, hs3_1, hs3_2, hs3_3, hs3_4, hs3_5, hs3_6, _, _, hfr3, hoff3, hcur3, _⟩, hs3_7⟩
      clear hl1 hl2 hl3
      have hoff_all : ∀ u ≤ G.n, st3.mem (csrAddr + u) = csrOff G u := fun u hu => hoff3 u (hs3_7 ▸ hu)
      have hcur_all : ∀ u < G.n, st3.mem (curBase + u) = csrOff G u := fun u hu => hcur3 u (hs3_7 ▸ hu)
      have hle_cb : csrAddr ≤ curBase := by
        rw [hcb]; exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      have hG3 : GraphAt st3.mem gAddr G :=
        hG.of_agree_below hdisj fun k hk => by
          have hk1 : k < curBase := Nat.lt_of_lt_of_le hk hle_cb
          rw [hfr3 k (Or.inl hk), hfr2 k (Or.inl hk1), hfr1 k (Or.inl hk1)]
      have hl4 := buildCsr_loop4 (p := p) gAddr csrAddr curBase adjVBase adjHBase G st3.mem
        hG3 hval hdisj hwbound hcb hav hah hw4
      wram_step
      refine runs_seq_triple_le hl4 ?_ (fun stEnd hstEnd => ?_)
      · refine ⟨hs3_0, hs3_1, hs3_2, hs3_3, hs3_4, hs3_5, hs3_6, Nat.zero_le _,
          memFrame_refl _ _ _, ?_, fun u hu t ht => by simp [csrIncAux] at ht⟩
        intro u hu
        simp only [Function.update_self, List.take_zero, csrIncAux, List.length_nil, Nat.add_zero]
        exact hcur_all u hu
      · wram_step
        · rcases hstEnd with ⟨⟨_, _, _, _, _, _, _, _, hfr4, _, hfill4⟩, hr7_eq⟩
          have hfr_all : MemFrame mem stEnd.mem csrAddr (csrAddr + 2 * G.n + 1 + 4 * G.m) := by
            have h1 := memFrame_mono hfr1 hle_cb hb_cur_end
            have h2 := memFrame_mono hfr2 hle_cb hb_cur_end
            have h3 := memFrame_mono hfr3 le_rfl hb_adjV_end
            have h4 := memFrame_mono hfr4 hle_cb le_rfl
            exact memFrame_trans (memFrame_trans h1 h2) (memFrame_trans h3 h4)
          refine ⟨rfl, ⟨fun u hu => ?_, fun u hu j hj => ?_⟩, hfr_all⟩
          · rw [hfr4 (csrAddr + u) (Or.inl (hcu_lt_cb u hu))]
            exact hoff_all u hu
          · have htake_eq : G.edges.take (stEnd.regs 7) = G.edges :=
              List.take_of_length_le (by rw [hr7_eq]; simp [Cited.Graph.m])
            have hj' : j < (csrIncAux u 0 (G.edges.take (stEnd.regs 7))).length := by rwa [htake_eq]
            have hget := hfill4 u hu j hj'
            simpa only [htake_eq, hadjV_eq, hadjH_eq] using hget
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin,
            Function.update_apply, ite_true, Nat.sub_zero, startState, hn_mem, hm_mem]
          linarith
  obtain ⟨o, st', c, hrun, ⟨rfl, hcsr, hfr⟩, hcost⟩ := htriple (startState [gAddr, csrAddr] mem pos) ω rfl
  refine ⟨buildCsrProc, hproc, .returned 0, st', c, hrun, ⟨rfl, ?_, ?_⟩, ?_⟩
  · simpa [hread] using hcsr
  · simpa [hread] using hfr
  · simpa [buildCsrContract, hread] using hcost

/-! ## 3. Pure BFS reachability and backtrack walk helpers -/

/-- Recursive vertex sequence produced by following `parV` backward `k` steps from `x`. -/
def bfsWalkVerts (parV : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, x => [x]
  | k + 1, x => bfsWalkVerts parV k (parV x) ++ [x]

/-- Recursive edge sequence produced by following `parV` / `parE` backward `k` steps from `x`. -/
def bfsWalkEdges (parV parE : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, x => bfsWalkEdges parV parE k (parV x) ++ [parE x]

lemma bfsWalkVerts_length (parV : ℕ → ℕ) (k x : ℕ) : (bfsWalkVerts parV k x).length = k + 1 := by
  induction k generalizing x with
  | zero => simp [bfsWalkVerts]
  | succ k ih => simp [bfsWalkVerts, ih]

lemma bfsWalkEdges_length (parV parE : ℕ → ℕ) (k x : ℕ) : (bfsWalkEdges parV parE k x).length = k := by
  induction k generalizing x with
  | zero => simp [bfsWalkEdges]
  | succ k ih => simp [bfsWalkEdges, ih]

lemma bfsWalkVerts_getElem {dist parV : ℕ → ℕ} {u k x : ℕ}
    (hstep : ∀ y, 2 ≤ dist y → dist (parV y) + 1 = dist y)
    (hdist : dist x = k + 1) (hu : ∀ y, dist y = 1 → y = u) :
    ∀ i (hi : i < (bfsWalkVerts parV k x).length),
      let z := (bfsWalkVerts parV k x)[i]
      dist z = i + 1 ∧ (i = 0 → z = u) ∧ (i = k → z = x) := by
  induction k generalizing x with
  | zero =>
    intro i hi
    simp only [bfsWalkVerts, List.length_singleton] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [bfsWalkVerts, List.getElem_singleton]
    exact ⟨hdist, fun _ => hu x hdist, by simp⟩
  | succ k ih =>
    intro i hi
    have hpx : dist (parV x) = k + 1 := by
      have := hstep x (by omega); omega
    have ih' := ih hpx
    rw [bfsWalkVerts_length] at hi
    by_cases hil : i = k + 1
    · subst hil
      have hget_r : (bfsWalkVerts parV (k + 1) x)[k + 1]'(by simp [bfsWalkVerts_length]) = x := by
        change (bfsWalkVerts parV k (parV x) ++ [x])[k + 1]'(by simp [bfsWalkVerts_length]) = x
        have hlen_eq : (bfsWalkVerts parV k (parV x)).length = k + 1 := bfsWalkVerts_length _ _ _
        simp [hlen_eq]
      rw [hget_r]
      exact ⟨hdist, fun h => by omega, by simp⟩
    · have hi_prev : i < (bfsWalkVerts parV k (parV x)).length := by
        rw [bfsWalkVerts_length]; omega
      simp only [bfsWalkVerts, List.getElem_append_left hi_prev]
      rcases ih' i hi_prev with ⟨hd, hz, _⟩
      exact ⟨hd, hz, fun h => by omega⟩

lemma bfsWalk_isWalk {G : Cited.Graph} {dist parV parE vMask eMask : ℕ → ℕ} {u v L : ℕ}
    (hL : 2 ≤ L) (hdv : dist v = L) (hu_lt : u < G.n) (hv_lt : v < G.n)
    (hu_uniq : ∀ y, dist y = 1 → y = u)
    (hinv : ∀ y, 2 ≤ dist y →
      dist (parV y) + 1 = dist y ∧ y < G.n ∧ parV y < G.n ∧
      vMask y ≠ 0 ∧ parE y < G.m ∧ eMask (parE y) ≠ 0 ∧
      Walk.EdgeMatches (G.edges.getD (parE y) (0, 0)) (parV y) y)
    (hvm_u : vMask u ≠ 0) :
    let P : Walk := ⟨bfsWalkVerts parV (L - 1) v, bfsWalkEdges parV parE (L - 1) v⟩
    P.IsWalk G u v ∧
    P.verts.Nodup ∧
    (∀ e ∈ P.edges, eMask e ≠ 0) ∧
    (∀ z ∈ P.verts, z < G.n ∧ vMask z ≠ 0) := by
  intro P
  have hstep : ∀ y, 2 ≤ dist y → dist (parV y) + 1 = dist y := fun y hy => (hinv y hy).1
  have hv_props : ∀ i (hi : i < (bfsWalkVerts parV (L - 1) v).length),
      let z := (bfsWalkVerts parV (L - 1) v)[i]
      dist z = i + 1 ∧ (i = 0 → z = u) ∧ (i = L - 1 → z = v) :=
    bfsWalkVerts_getElem hstep (by omega) hu_uniq
  have hLenV : P.verts.length = L := by
    simp [P, bfsWalkVerts_length]; omega
  have hLenE : P.edges.length = L - 1 := by
    simp [P, bfsWalkEdges_length]
  have hEdgeStep : ∀ (k x : ℕ), dist x = k + 1 →
      ∀ i (hi : i < k),
        let e := (bfsWalkEdges parV parE k x)[i]'(by rw [bfsWalkEdges_length]; exact hi)
        let a := (bfsWalkVerts parV k x)[i]'(by rw [bfsWalkVerts_length]; omega)
        let b := (bfsWalkVerts parV k x)[i + 1]'(by rw [bfsWalkVerts_length]; omega)
        e < G.m ∧ eMask e ≠ 0 ∧ Walk.EdgeMatches (G.edges.getD e (0, 0)) a b := by
    intro k
    induction k with
    | zero => intro x _ i hi; omega
    | succ k ih =>
      intro x hdx i hi
      have hx := hinv x (by omega)
      have hpx : dist (parV x) = k + 1 := by omega
      by_cases hik : i = k
      · have h_lenV : (bfsWalkVerts parV k (parV x)).length = k + 1 := bfsWalkVerts_length _ _ _
        have h_lenE : (bfsWalkEdges parV parE k (parV x)).length = k := bfsWalkEdges_length _ _ _ _
        have hk_prev : k < (bfsWalkVerts parV k (parV x)).length := by omega
        have ha : (bfsWalkVerts parV (k + 1) x)[i]'(by rw [bfsWalkVerts_length]; omega) = parV x := by
          have ha0 : (bfsWalkVerts parV (k + 1) x)[k]'(by rw [bfsWalkVerts_length]; omega) = parV x := by
            simp only [bfsWalkVerts, List.getElem_append_left hk_prev]
            exact ((bfsWalkVerts_getElem hstep hpx hu_uniq k hk_prev).2.2 rfl)
          simpa [hik] using ha0
        have hb : (bfsWalkVerts parV (k + 1) x)[i + 1]'(by rw [bfsWalkVerts_length]; omega) = x := by
          have hb0 : (bfsWalkVerts parV (k + 1) x)[k + 1]'(by rw [bfsWalkVerts_length]; omega) = x := by
            change (bfsWalkVerts parV k (parV x) ++ [x])[k + 1]'(by simp [h_lenV]) = x
            simp [h_lenV]
          simpa [hik] using hb0
        have he : (bfsWalkEdges parV parE (k + 1) x)[i]'(by rw [bfsWalkEdges_length]; omega) = parE x := by
          have he0 : (bfsWalkEdges parV parE (k + 1) x)[k]'(by rw [bfsWalkEdges_length]; omega) = parE x := by
            change (bfsWalkEdges parV parE k (parV x) ++ [parE x])[k]'(by simp [h_lenE]) = parE x
            simp [h_lenE]
          simpa [hik] using he0
        rw [he, ha, hb]
        exact ⟨hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2⟩
      · have hi_k : i < k := by omega
        have hih := ih (parV x) hpx i hi_k
        have he_eq : (bfsWalkEdges parV parE (k + 1) x)[i]'(by rw [bfsWalkEdges_length]; exact hi) =
            (bfsWalkEdges parV parE k (parV x))[i]'(by rw [bfsWalkEdges_length]; exact hi_k) := by
          simp [bfsWalkEdges, List.getElem_append_left, bfsWalkEdges_length, hi_k]
        have ha_eq : (bfsWalkVerts parV (k + 1) x)[i]'(by rw [bfsWalkVerts_length]; omega) =
            (bfsWalkVerts parV k (parV x))[i]'(by rw [bfsWalkVerts_length]; omega) := by
          simp [bfsWalkVerts, List.getElem_append_left, bfsWalkVerts_length, show i < k + 1 by omega]
        have hb_eq : (bfsWalkVerts parV (k + 1) x)[i + 1]'(by rw [bfsWalkVerts_length]; omega) =
            (bfsWalkVerts parV k (parV x))[i + 1]'(by rw [bfsWalkVerts_length]; omega) := by
          simp [bfsWalkVerts, List.getElem_append_left, bfsWalkVerts_length, show i + 1 < k + 1 by omega]
        rw [he_eq, ha_eq, hb_eq]
        exact hih
  have hEAll : ∀ i (hi : i < L - 1),
      let e := (bfsWalkEdges parV parE (L - 1) v)[i]'(by rw [bfsWalkEdges_length]; exact hi)
      let a := (bfsWalkVerts parV (L - 1) v)[i]'(by rw [bfsWalkVerts_length]; omega)
      let b := (bfsWalkVerts parV (L - 1) v)[i + 1]'(by rw [bfsWalkVerts_length]; omega)
      e < G.m ∧ eMask e ≠ 0 ∧ Walk.EdgeMatches (G.edges.getD e (0, 0)) a b :=
    fun i hi => hEdgeStep (L - 1) v (by omega) i hi
  refine ⟨⟨hu_lt, hv_lt, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · intro heq; have : P.edges.length = 0 := by simp [heq]
    omega
  · omega
  · have h0 : 0 < P.verts.length := by omega
    have h0' : 0 < (bfsWalkVerts parV (L - 1) v).length := h0
    cases hv_eq : P.verts with
    | nil => simp [hv_eq] at h0
    | cons x xs =>
      simp only [List.head?_cons]
      congr 1
      have hget0 := (hv_props 0 h0').2.1 rfl
      have hpx : P.verts[0] = x := by simp [hv_eq]
      exact hpx.symm.trans hget0
  · have hpos : 0 < P.verts.length := by omega
    rw [List.getLast?_eq_getElem?]
    simp only [hLenV]
    have hlt : L - 1 < P.verts.length := by omega
    rw [List.getElem?_eq_getElem hlt]
    congr 1
    exact (hv_props (L - 1) hlt).2.2 rfl
  · intro e he
    rcases List.getElem_of_mem he with ⟨i, hi, rfl⟩
    exact (hEAll i (by simpa [hLenE] using hi)).1
  · intro i hi
    have hi' : i < L - 1 := by simpa [hLenE] using hi
    have hmi := (hEAll i hi').2.2
    have hiE_len : i < (bfsWalkEdges parV parE (L - 1) v).length := by
      rw [bfsWalkEdges_length]; exact hi'
    have hiV_len : i < (bfsWalkVerts parV (L - 1) v).length := by
      rw [bfsWalkVerts_length]; omega
    have hi1V_len : i + 1 < (bfsWalkVerts parV (L - 1) v).length := by
      rw [bfsWalkVerts_length]; omega
    have hei : P.edges.getD i 0 = (bfsWalkEdges parV parE (L - 1) v)[i]'hiE_len := by
      simp [P, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiE_len]
    have hai : P.verts.getD i 0 = (bfsWalkVerts parV (L - 1) v)[i]'hiV_len := by
      simp [P, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiV_len]
    have hbi : P.verts.getD (i + 1) 0 = (bfsWalkVerts parV (L - 1) v)[i + 1]'hi1V_len := by
      simp [P, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1V_len]
    rw [hei, hai, hbi]
    exact hmi
  · rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hdi := (hv_props i.1 i.2).1
    have hdj := (hv_props j.1 j.2).1
    have hveq : (bfsWalkVerts parV (L - 1) v)[i.1] = (bfsWalkVerts parV (L - 1) v)[j.1] := hij
    rw [hveq] at hdi
    ext; omega
  · intro e he
    rcases List.getElem_of_mem he with ⟨i, hi, rfl⟩
    exact (hEAll i (by simpa [hLenE] using hi)).2.1
  · intro z hz
    rcases List.getElem_of_mem hz with ⟨i, hi, rfl⟩
    have hdi := (hv_props i hi).1
    by_cases hi0 : i = 0
    · have hzu := (hv_props i hi).2.1 hi0
      rw [hzu]; exact ⟨hu_lt, hvm_u⟩
    · have hz2 := hinv (bfsWalkVerts parV (L - 1) v)[i] (by omega)
      exact ⟨hz2.2.1, hz2.2.2.2.1⟩

/-- Disjointness outside two intervals `[lo1, hi1)` and `[lo2, hi2)`. -/
def PreservedOutside2 (mem mem' : ℕ → ℕ) (lo1 hi1 lo2 hi2 : ℕ) : Prop :=
  ∀ a, (a < lo1 ∨ hi1 ≤ a) → (a < lo2 ∨ hi2 ≤ a) → mem' a = mem a

lemma memFrame_to_preservedOutside2 {mem mem' mem'' : ℕ → ℕ} {lo1 hi1 lo2 hi2 : ℕ}
    (h1 : MemFrame mem mem' lo1 hi1) (h2 : MemFrame mem' mem'' lo2 hi2) :
    PreservedOutside2 mem mem'' lo1 hi1 lo2 hi2 := by
  intro a ha1 ha2
  rw [h2 a ha2, h1 a ha1]

/-! ## 4. `bfsPathProc` (`O(n + m + 1)`) -/

/-- `bfsPathProc`: `args = [n, m, csrAddr, vMaskAddr, eMaskAddr, u, v, workAddr, outAddr]`.
Single flat BFS loop + backtrack writing `WalkAt mem' outAddr P`; returns `1` if found, `0` if
unreachable. Workspace `[workAddr, workAddr + 4*n)`, output `[outAddr, outAddr + 2*n + 2)`. -/
def bfsPathProc : Stmt :=
  .cond (.bin .eq (.reg 5) (.reg 6))
    (seqStmts [
      .store (.reg 8) (.const 0),
      .store (.bin .add (.reg 8) (.const 1)) (.const 0),
      .ret (.const 1)])
    (seqStmts [
      .assign 9 (.bin .add (.reg 7) (.reg 0)), -- parVBase = workAddr + n
      .assign 10 (.bin .add (.reg 9) (.reg 0)), -- parEBase = workAddr + 2*n
      .assign 11 (.bin .add (.reg 10) (.reg 0)), -- queueBase = workAddr + 3*n
      .assign 12 (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 0))) (.const 1)), -- adjVBase
      .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 1))), -- adjHBase
      .assign 14 (.const 0), -- i := 0
      .loop (.bin .lt (.reg 14) (.reg 0))
        (.seq (.store (.bin .add (.reg 7) (.reg 14)) (.const 0))
          (.assign 14 (.bin .add (.reg 14) (.const 1)))),
      .store (.bin .add (.reg 7) (.reg 5)) (.const 1), -- dist[u] := 1
      .store (.reg 11) (.reg 5), -- queue[0] := u
      .assign 14 (.const 0), -- qHead := 0
      .assign 15 (.const 1), -- qTail := 1
      .assign 16 (.const 0), -- k := 0
      .assign 17 (.const 0), -- kEnd := 0
      .assign 18 (.const 0), -- cur := 0
      .assign 19 (.const 1), -- running := 1
      .loop (.reg 19)
        (.cond (.bin .lt (.reg 16) (.reg 17))
          (seqStmts [
            .assign 20 (.load (.bin .add (.reg 12) (.reg 16))), -- nbr := adjVert[k]
            .assign 21 (.load (.bin .add (.reg 13) (.reg 16))), -- half := adjHalf[k]
            .assign 22 (.bin .div (.reg 21) (.const 2)), -- edgeIdx := half / 2
            .assign 23 (.load (.bin .add (.reg 7) (.reg 20))), -- dist[nbr]
            .cond (.bin .eq (.reg 23) (.const 0))
              (seqStmts [
                .assign 24 (.load (.bin .add (.reg 3) (.reg 20))), -- vMask[nbr]
                .cond (.bin .lt (.const 0) (.reg 24))
                  (seqStmts [
                    .assign 25 (.load (.bin .add (.reg 4) (.reg 22))), -- eMask[edgeIdx]
                    .cond (.bin .lt (.const 0) (.reg 25))
                      (seqStmts [
                        .assign 26 (.load (.bin .add (.reg 7) (.reg 18))), -- dcur := dist[cur]
                        .store (.bin .add (.reg 7) (.reg 20)) (.bin .add (.reg 26) (.const 1)),
                        .store (.bin .add (.reg 9) (.reg 20)) (.reg 18),
                        .store (.bin .add (.reg 10) (.reg 20)) (.reg 22),
                        .store (.bin .add (.reg 11) (.reg 15)) (.reg 20),
                        .assign 15 (.bin .add (.reg 15) (.const 1))])
                      .nop])
                  .nop])
              .nop,
            .assign 16 (.bin .add (.reg 16) (.const 1))])
          (.cond (.bin .lt (.reg 14) (.reg 15))
            (seqStmts [
              .assign 18 (.load (.bin .add (.reg 11) (.reg 14))), -- cur := queue[qHead]
              .assign 14 (.bin .add (.reg 14) (.const 1)), -- qHead++
              .assign 16 (.load (.bin .add (.reg 2) (.reg 18))), -- k := off[cur]
              .assign 17 (.load (.bin .add (.bin .add (.reg 2) (.reg 18)) (.const 1)))]) -- kEnd := off[cur+1]
            (.assign 19 (.const 0)))),
      .assign 20 (.load (.bin .add (.reg 7) (.reg 6))), -- L := dist[v]
      .cond (.bin .eq (.reg 20) (.const 0))
        (.ret (.const 0))
        (seqStmts [
          .store (.reg 8) (.reg 20), -- out[0] := L
          .store (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 20)) (.bin .sub (.reg 20) (.const 1)),
          .store (.bin .add (.reg 8) (.const 1)) (.reg 5), -- out[1] := u
          .assign 21 (.reg 6), -- x := v
          .assign 22 (.bin .sub (.reg 20) (.const 1)), -- idx := L - 1
          .loop (.bin .lt (.const 0) (.reg 22))
            (seqStmts [
              .store (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 22)) (.reg 21),
              .assign 23 (.load (.bin .add (.reg 10) (.reg 21))),
              .store (.bin .add (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 20))
                (.bin .sub (.reg 22) (.const 1))) (.reg 23),
              .assign 21 (.load (.bin .add (.reg 9) (.reg 21))),
              .assign 22 (.bin .sub (.reg 22) (.const 1))]),
          .ret (.const 1)])])

lemma bfsPathProc_noRand : bfsPathProc.NoRand := by
  simp [bfsPathProc, Stmt.NoRand]

/-- Contract for `bfsPathProc`: args `[n, m, csrAddr, vMaskAddr, eMaskAddr, u, v, workAddr, outAddr]`. -/
def bfsPathContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr : ℕ) (G : Cited.Graph),
      args = [n, m, csrAddr, vMaskAddr, eMaskAddr, u, v, workAddr, outAddr] ∧
      G.n = n ∧ G.m = m ∧ G.IsValid ∧
      HasCsrAt mem csrAddr G ∧
      u < n ∧ v < n ∧
      mem (vMaskAddr + u) ≠ 0 ∧ mem (vMaskAddr + v) ≠ 0 ∧
      (workAddr + 4 * n ≤ outAddr ∨ outAddr + 2 * n + 2 ≤ workAddr) ∧
      (csrAddr + 2 * n + 1 + 4 * m ≤ workAddr ∨ workAddr + 4 * n ≤ csrAddr) ∧
      (csrAddr + 2 * n + 1 + 4 * m ≤ outAddr ∨ outAddr + 2 * n + 2 ≤ csrAddr) ∧
      (vMaskAddr + n ≤ workAddr ∨ workAddr + 4 * n ≤ vMaskAddr) ∧
      (vMaskAddr + n ≤ outAddr ∨ outAddr + 2 * n + 2 ≤ vMaskAddr) ∧
      (eMaskAddr + m ≤ workAddr ∨ workAddr + 4 * n ≤ eMaskAddr) ∧
      (eMaskAddr + m ≤ outAddr ∨ outAddr + 2 * n + 2 ≤ eMaskAddr) ∧
      csrAddr + 2 * n + 1 + 4 * m < 2 ^ w ∧
      vMaskAddr + n < 2 ^ w ∧
      eMaskAddr + m < 2 ^ w ∧
      workAddr + 4 * n < 2 ^ w ∧
      outAddr + 2 * n + 2 < 2 ^ w ∧
      4 ≤ 2 ^ w
  post args mem res mem' :=
    let n := args.getD 0 0
    let m := args.getD 1 0
    let csrAddr := args.getD 2 0
    let vMaskAddr := args.getD 3 0
    let eMaskAddr := args.getD 4 0
    let u := args.getD 5 0
    let v := args.getD 6 0
    let workAddr := args.getD 7 0
    let outAddr := args.getD 8 0
    (res = 0 ∨ res = 1) ∧
    PreservedOutside2 mem mem' workAddr (workAddr + 4 * n) outAddr (outAddr + 2 * n + 2) ∧
    (∀ G : Cited.Graph, G.n = n → G.m = m → G.IsValid → HasCsrAt mem csrAddr G →
      (res = 1 →
        ∃ P : Walk, WalkAt mem' outAddr P ∧ P.IsWalk G u v ∧ P.verts.Nodup ∧
          (∀ e ∈ P.edges, mem (eMaskAddr + e) ≠ 0) ∧
          (∀ x ∈ P.verts, mem (vMaskAddr + x) ≠ 0) ∧
          P.edges.length < n) ∧
      (res = 0 →
        ∃ S : Finset ℕ, u ∈ S ∧ v ∉ S ∧ S ⊆ Finset.range n ∧
          (∀ x ∈ S, mem (vMaskAddr + x) ≠ 0) ∧
          (∀ j < m, mem (eMaskAddr + j) ≠ 0 →
            ∀ x ∈ S, ∀ y, Walk.EdgeMatches (G.edges.getD j (0, 0)) x y →
              y < n → mem (vMaskAddr + y) ≠ 0 → y ∈ S)))
  cost args _ :=
    let n := args.getD 0 0
    let m := args.getD 1 0
    350 * (n + m + 1)

/-- Shortest-path specification of `bfsPathProc`: same precondition and running time as
`bfsPathContract w`, strengthened when `res = 1` so the returned walk `P` has the fewest edges
among all walks from `u` to `v` in the unmasked subgraph (`vMask ≠ 0` on vertices, `eMask ≠ 0` on
edges). -/
def bfsShortestPathContract (w : ℕ) : Contract where
  pre args mem := (bfsPathContract w).pre args mem
  post args mem res mem' :=
    let n := args.getD 0 0
    let m := args.getD 1 0
    let csrAddr := args.getD 2 0
    let vMaskAddr := args.getD 3 0
    let eMaskAddr := args.getD 4 0
    let u := args.getD 5 0
    let v := args.getD 6 0
    let outAddr := args.getD 8 0
    (bfsPathContract w).post args mem res mem' ∧
    (∀ G : Cited.Graph, G.n = n → G.m = m → G.IsValid → HasCsrAt mem csrAddr G →
      res = 1 →
      ∃ P : Walk, WalkAt mem' outAddr P ∧ P.IsWalk G u v ∧ P.verts.Nodup ∧
        (∀ e ∈ P.edges, mem (eMaskAddr + e) ≠ 0) ∧
        (∀ x ∈ P.verts, mem (vMaskAddr + x) ≠ 0) ∧
        P.edges.length < n ∧
        (∀ W : Walk, W.IsWalk G u v →
          (∀ e ∈ W.edges, mem (eMaskAddr + e) ≠ 0) →
          (∀ x ∈ W.verts, mem (vMaskAddr + x) ≠ 0) →
          P.edges.length ≤ W.edges.length))
  cost args mem := (bfsPathContract w).cost args mem

/-- Any procedure meeting `bfsShortestPathContract w` also meets `bfsPathContract w`. -/
theorem meets_bfsPathContract_of_shortest {w : ℕ} {p : Program} {b : ℕ}
    (h : MeetsContract w p b (bfsShortestPathContract w)) :
    MeetsContract w p b (bfsPathContract w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨body, hp, o, st, c, hrun, hpost, hcost⟩ := h args mem pos ω hwords hpre
  exact ⟨body, hp, o, st, c, hrun, hpost.1, hcost⟩

end MinCostFlow.Expander
