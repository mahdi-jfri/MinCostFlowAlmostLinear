module

public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.Expander.BfsShortestLemmas

import Mathlib.Tactic.Linarith

/-!
# Proof of `bfsPathContract` and Bundled CSR/BFS Procedures

Proves `bfsPath_spec : MeetsContract w p b (bfsPathContract w)` in four modular stages
(`bfs_zero_loop`, `bfs_push_triple`, `bfs_main_loop`, `bfs_backtrack_loop`), and exports
the bundled deterministic procedure table `csrBfsProcs` meeting `buildCsrContract` and
`bfsPathContract`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.Cited

/-! ## 1. Layout and Pure Walk Helpers -/

lemma listAt_of_getElem {mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (h : ∀ i (hi : i < xs.length), mem (a + i) = xs[i]'hi) : ListAt mem a xs := by
  induction xs generalizing a with
  | nil => simp [ListAt]
  | cons x xs ih =>
    rw [listAt_cons]
    refine ⟨by have h0 := h 0 (by simp); simpa using h0, ?_⟩
    exact ih fun i hi => by
      rw [show a + 1 + i = a + (i + 1) by omega]
      exact h (i + 1) (by simp; omega)

lemma walkAt_empty_of_cells {mem : ℕ → ℕ} {a : ℕ}
    (h0 : mem a = 0) (h1 : mem (a + 1) = 0) : WalkAt mem a Walk.empty := by
  rw [walkAt_iff]
  refine ⟨h0, by simp [ListAt, Walk.empty], h1, by simp [ListAt, Walk.empty]⟩

lemma walkAt_of_cells {mem : ℕ → ℕ} {a : ℕ} {P : Walk}
    (hvLen : mem a = P.verts.length)
    (heLen : mem (a + 1 + P.verts.length) = P.edges.length)
    (hVerts : ∀ i (hi : i < P.verts.length), mem (a + 1 + i) = P.verts[i]'hi)
    (hEdges : ∀ i (hi : i < P.edges.length), mem (a + 2 + P.verts.length + i) = P.edges[i]'hi) :
    WalkAt mem a P := by
  rw [walkAt_iff]
  exact ⟨hvLen, listAt_of_getElem hVerts, heLen, listAt_of_getElem hEdges⟩

lemma bfsWalkVerts_last (parV : ℕ → ℕ) (k x : ℕ) :
    (bfsWalkVerts parV k x)[k]'(by rw [bfsWalkVerts_length]; omega) = x := by
  cases k with
  | zero => simp [bfsWalkVerts]
  | succ k =>
    have hlen : (bfsWalkVerts parV k (parV x)).length = k + 1 := bfsWalkVerts_length _ _ _
    simp [bfsWalkVerts, hlen]

lemma bfsWalk_step_eq (parV parE : ℕ → ℕ) :
    ∀ (k x idx : ℕ) (h1 : idx + 1 ≤ k) (y : ℕ),
      (bfsWalkVerts parV k x)[idx + 1]'(by rw [bfsWalkVerts_length]; omega) = y →
      (bfsWalkVerts parV k x)[idx]'(by rw [bfsWalkVerts_length]; omega) = parV y ∧
      (bfsWalkEdges parV parE k x)[idx]'(by rw [bfsWalkEdges_length]; omega) = parE y := by
  intro k
  induction k with
  | zero => intro x idx h1; omega
  | succ k ih =>
    intro x idx h1 y hy
    by_cases hlast : idx = k
    · subst idx
      have hy_x : y = x := by
        have hlast_v := bfsWalkVerts_last parV (k + 1) x
        exact hy.symm.trans hlast_v
      subst y
      have hv_prev : (bfsWalkVerts parV (k + 1) x)[k]'(by rw [bfsWalkVerts_length]; omega) = parV x := by
        have hlen : k < (bfsWalkVerts parV k (parV x)).length := by rw [bfsWalkVerts_length]; omega
        simp only [bfsWalkVerts, List.getElem_append_left hlen]
        exact bfsWalkVerts_last parV k (parV x)
      have he_prev : (bfsWalkEdges parV parE (k + 1) x)[k]'(by rw [bfsWalkEdges_length]; omega) = parE x := by
        have hlen : (bfsWalkEdges parV parE k (parV x)).length = k := bfsWalkEdges_length _ _ _ _
        simp [bfsWalkEdges, hlen]
      rw [bfsWalkVerts_last]
      exact ⟨hv_prev, he_prev⟩
    · have h1' : idx + 1 ≤ k := by omega
      have hlen_v1 : idx + 1 < (bfsWalkVerts parV k (parV x)).length := by rw [bfsWalkVerts_length]; omega
      have hlen_v0 : idx < (bfsWalkVerts parV k (parV x)).length := by rw [bfsWalkVerts_length]; omega
      have hlen_e : idx < (bfsWalkEdges parV parE k (parV x)).length := by rw [bfsWalkEdges_length]; omega
      have hy' : (bfsWalkVerts parV k (parV x))[idx + 1]'hlen_v1 = y := by
        simpa [bfsWalkVerts, List.getElem_append_left hlen_v1] using hy
      have ih_res := ih (parV x) idx h1' y hy'
      refine ⟨?_, ?_⟩
      · simpa [bfsWalkVerts, List.getElem_append_left hlen_v0] using ih_res.1
      · simpa [bfsWalkEdges, List.getElem_append_left hlen_e] using ih_res.2

private lemma card_inj_insert_le {n qTail y : ℕ} {q : ℕ → ℕ}
    (hq : ∀ i < qTail, q i < n)
    (hinj : ∀ i < qTail, ∀ j < qTail, q i = q j → i = j)
    (hy : y < n) (hy_new : ∀ i < qTail, q i ≠ y) :
    qTail + 1 ≤ n := by
  let S := (Finset.range qTail).image q
  have hS_card : S.card = qTail := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  have hy_not : y ∉ S := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨i, hi, hi_eq⟩
    exact hy_new i (Finset.mem_range.mp hi) hi_eq
  have hsub : insert y S ⊆ Finset.range n := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzS
    · exact Finset.mem_range.mpr hy
    · rcases Finset.mem_image.mp hzS with ⟨i, hi, rfl⟩
      exact Finset.mem_range.mpr (hq i (Finset.mem_range.mp hi))
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hy_not, hS_card, Finset.card_range] at hle
  exact hle

/-! ## 2. Loop 1: Zero `dist[0..n-1]` -/

private lemma bfs_zero_loop {w : ℕ} {p : Program}
    (n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase : ℕ)
    (mem : ℕ → ℕ)
    (hwork_w : workAddr + 4 * n < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    let Inv0 : State → Prop := fun st =>
      st.regs 0 = n ∧ st.regs 1 = m ∧ st.regs 2 = csrAddr ∧
      st.regs 3 = vMaskAddr ∧ st.regs 4 = eMaskAddr ∧ st.regs 5 = u ∧ st.regs 6 = v ∧
      st.regs 7 = workAddr ∧ st.regs 8 = outAddr ∧ st.regs 9 = parVBase ∧
      st.regs 10 = parEBase ∧ st.regs 11 = queueBase ∧ st.regs 12 = adjVBase ∧
      st.regs 13 = adjHBase ∧ st.regs 14 ≤ n ∧
      MemFrame mem st.mem workAddr (workAddr + n) ∧
      (∀ i < st.regs 14, st.mem (workAddr + i) = 0)
    Triple w p Inv0
      (.loop (.bin .lt (.reg 14) (.reg 0))
        (.seq (.store (.bin .add (.reg 7) (.reg 14)) (.const 0))
          (.assign 14 (.bin .add (.reg 14) (.const 1)))))
      (normalPost fun st' => Inv0 st' ∧ st'.regs 14 = n)
      (fun st => (3 + 12 + 1) * (n - st.regs 14) + 3 + 1) := by
  intro Inv0
  have h1_w : 1 < 2 ^ w := by omega
  refine Triple.loop_const_normal (fun st => n - st.regs 14)
    (fun st => if st.regs 14 < n then 1 else 0) 12
    (fun st hInv => by rcases hInv with ⟨_, _⟩; eval_expr)
    (fun st hInv h0 => by
      simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
      exact ⟨hInv, by rcases hInv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h14, _⟩; omega⟩)
    (fun st hInv hne => ?_)
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hfr, hz⟩
  have hlt_w : st.regs 7 + st.regs 14 < 2 ^ w := by rw [hr7]; omega
  wram_enter
  · subst hpre
    wram_run
    · refine ⟨⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
          by simp; omega, ?_, ?_⟩, by simp; omega⟩
      · exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
      · intro i hi
        simp at hi
        dsimp only
        by_cases hii : i = st.regs 14
        · subst hii; simp [Function.update_self]
        · rw [Function.update_of_ne (by omega)]; exact hz i (by omega)
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega

/-! ## 3. Inner Push Helper for Loop 2 -/

private lemma bfs_push_triple {w : ℕ} {p : Program} (st0 : State)
    (workAddr parVBase parEBase queueBase cur nbr edgeIdx dcur qTail n : ℕ)
    (h7 : st0.regs 7 = workAddr) (h9 : st0.regs 9 = parVBase) (h10 : st0.regs 10 = parEBase)
    (h11 : st0.regs 11 = queueBase) (h15 : st0.regs 15 = qTail) (h18 : st0.regs 18 = cur)
    (h20 : st0.regs 20 = nbr) (h22 : st0.regs 22 = edgeIdx)
    (hpv : parVBase = workAddr + n) (hpe : parEBase = workAddr + 2 * n)
    (hqb : queueBase = workAddr + 3 * n)
    (hd_eq : st0.mem (workAddr + cur) = dcur)
    (hcur_lt : cur < n) (hnbr_lt : nbr < n) (hq_lt : qTail < n)
    (hd_le : dcur ≤ n) (hw_lt : workAddr + 4 * n < 2 ^ w) (h1_w : 1 < 2 ^ w) :
    Triple w p (fun st => st = st0)
      (seqStmts [
        .assign 26 (.load (.bin .add (.reg 7) (.reg 18))),
        .store (.bin .add (.reg 7) (.reg 20)) (.bin .add (.reg 26) (.const 1)),
        .store (.bin .add (.reg 9) (.reg 20)) (.reg 18),
        .store (.bin .add (.reg 10) (.reg 20)) (.reg 22),
        .store (.bin .add (.reg 11) (.reg 15)) (.reg 20),
        .assign 15 (.bin .add (.reg 15) (.const 1))])
      (normalPost fun st' =>
        (∀ r ≤ 14, st'.regs r = st0.regs r) ∧
        st'.regs 15 = qTail + 1 ∧
        (∀ r, 16 ≤ r → r ≤ 19 → st'.regs r = st0.regs r) ∧
        st'.mem = Function.update (Function.update (Function.update
          (Function.update st0.mem (workAddr + nbr) (dcur + 1))
          (parVBase + nbr) cur) (parEBase + nbr) edgeIdx) (queueBase + qTail) nbr)
      (fun _ => 40) := by
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  have hcur_w : workAddr + cur < 2 ^ w := by omega
  have hnbr_w : workAddr + nbr < 2 ^ w := by omega
  have hpvn_w : parVBase + nbr < 2 ^ w := by omega
  have hpen_w : parEBase + nbr < 2 ^ w := by omega
  have hqbq_w : queueBase + qTail < 2 ^ w := by omega
  have hd1_w : dcur + 1 < 2 ^ w := by omega
  have hq1_w : qTail + 1 < 2 ^ w := by omega
  have he1 : (Expr.load (Expr.bin .add (.reg 7) (.reg 18))).eval w st = some dcur := by
    simp [Expr.eval, BinOp.eval, h7, h18, hcur_w, hd_eq]
  refine runs_seq_assign_le he1 ?_
  have ha1 : (Expr.bin .add (.reg 7) (.reg 20)).eval w
      ({ mem := st.mem, regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some (workAddr + nbr) := by
    simp [Expr.eval, BinOp.eval, h7, h20, hnbr_w]
  have hv1 : (Expr.bin .add (.reg 26) (.const 1)).eval w
      ({ mem := st.mem, regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some (dcur + 1) := by
    simp [Expr.eval, BinOp.eval, Function.update_self, h1_w, hd1_w]
  refine runs_seq_store_le ha1 hv1 ?_
  have ha2 : (Expr.bin .add (.reg 9) (.reg 20)).eval w
      ({ mem := Function.update st.mem (workAddr + nbr) (dcur + 1),
         regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some (parVBase + nbr) := by
    simp [Expr.eval, BinOp.eval, h9, h20, hpvn_w]
  have hv2 : (Expr.reg 18).eval w
      ({ mem := Function.update st.mem (workAddr + nbr) (dcur + 1),
         regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some cur := by
    simp [Expr.eval, h18]
  refine runs_seq_store_le ha2 hv2 ?_
  have ha3 : (Expr.bin .add (.reg 10) (.reg 20)).eval w
      ({ mem := Function.update (Function.update st.mem (workAddr + nbr) (dcur + 1)) (parVBase + nbr) cur,
         regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some (parEBase + nbr) := by
    simp [Expr.eval, BinOp.eval, h10, h20, hpen_w]
  have hv3 : (Expr.reg 22).eval w
      ({ mem := Function.update (Function.update st.mem (workAddr + nbr) (dcur + 1)) (parVBase + nbr) cur,
         regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some edgeIdx := by
    simp [Expr.eval, h22]
  refine runs_seq_store_le ha3 hv3 ?_
  have ha4 : (Expr.bin .add (.reg 11) (.reg 15)).eval w
      ({ mem := Function.update (Function.update (Function.update st.mem
          (workAddr + nbr) (dcur + 1)) (parVBase + nbr) cur) (parEBase + nbr) edgeIdx,
         regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some (queueBase + qTail) := by
    simp [Expr.eval, BinOp.eval, h11, h15, hqbq_w]
  have hv4 : (Expr.reg 20).eval w
      ({ mem := Function.update (Function.update (Function.update st.mem
          (workAddr + nbr) (dcur + 1)) (parVBase + nbr) cur) (parEBase + nbr) edgeIdx,
         regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some nbr := by
    simp [Expr.eval, h20]
  refine runs_seq_store_le ha4 hv4 ?_
  have he5 : (Expr.bin .add (.reg 15) (.const 1)).eval w
      ({ mem := Function.update (Function.update (Function.update (Function.update st.mem
          (workAddr + nbr) (dcur + 1)) (parVBase + nbr) cur) (parEBase + nbr) edgeIdx)
          (queueBase + qTail) nbr,
         regs := Function.update st.regs 26 dcur, pos := st.pos } : State) =
      some (qTail + 1) := by
    simp [Expr.eval, BinOp.eval, h15, h1_w, hq1_w]
  refine runs_assign_le he5 ?_ ?_
  · dsimp only [normalPost]
    refine ⟨fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 15),
        Function.update_of_ne (by omega : r ≠ 26)],
      by simp,
      fun r hr1 hr2 => by simp [Function.update_of_ne (by omega : r ≠ 15),
        Function.update_of_ne (by omega : r ≠ 26)],
      rfl⟩
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

/-! ## 4. Loop 2: Main BFS Traversal -/

private def bfsPoppedSet (_G : Cited.Graph) (queueBase qHead : ℕ) (mem : ℕ → ℕ) : Finset ℕ :=
  (Finset.range qHead).image (fun i => mem (queueBase + i))

private def bfsDoneDeg (G : Cited.Graph) (queueBase qHead : ℕ) (mem : ℕ → ℕ) : ℕ :=
  (bfsPoppedSet G queueBase qHead mem).sum (fun x => (csrIncAux x 0 G.edges).length)

private lemma bfsDoneDeg_le (G : Cited.Graph) (queueBase qHead : ℕ) (mem : ℕ → ℕ)
    (hq : ∀ i < qHead, mem (queueBase + i) < G.n) :
    bfsDoneDeg G queueBase qHead mem ≤ csrOff G G.n := by
  have hsub : bfsPoppedSet G queueBase qHead mem ⊆ Finset.range G.n := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact Finset.mem_range.mpr (hq i (Finset.mem_range.mp hi))
  simpa [bfsDoneDeg, csrOff] using
    Finset.sum_le_sum_of_subset (f := fun x => (csrIncAux x 0 G.edges).length) hsub

private lemma bfsDoneDeg_congr (G : Cited.Graph) (queueBase qHead : ℕ) {mem1 mem2 : ℕ → ℕ}
    (heq : ∀ i < qHead, mem1 (queueBase + i) = mem2 (queueBase + i)) :
    bfsDoneDeg G queueBase qHead mem1 = bfsDoneDeg G queueBase qHead mem2 := by
  unfold bfsDoneDeg bfsPoppedSet
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_range]
  constructor <;> rintro ⟨i, hi, rfl⟩ <;> exact ⟨i, hi, by simp [heq i hi]⟩

private lemma bfsDoneDeg_succ (G : Cited.Graph) (queueBase qHead : ℕ) (mem : ℕ → ℕ)
    (hnew : ∀ i < qHead, mem (queueBase + i) ≠ mem (queueBase + qHead)) :
    bfsDoneDeg G queueBase (qHead + 1) mem =
      bfsDoneDeg G queueBase qHead mem + (csrIncAux (mem (queueBase + qHead)) 0 G.edges).length := by
  unfold bfsDoneDeg
  have himg : bfsPoppedSet G queueBase (qHead + 1) mem =
      insert (mem (queueBase + qHead)) (bfsPoppedSet G queueBase qHead mem) := by
    unfold bfsPoppedSet
    rw [Finset.range_add_one, Finset.image_insert]
  have hnot : mem (queueBase + qHead) ∉ bfsPoppedSet G queueBase qHead mem := by
    intro hm
    rcases Finset.mem_image.mp hm with ⟨i, hi, hi_eq⟩
    exact hnew i (Finset.mem_range.mp hi) hi_eq
  rw [himg, Finset.sum_insert hnot, Nat.add_comm]

private def BfsMainInv
    (n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase : ℕ)
    (G : Cited.Graph) (memInit memBase : ℕ → ℕ) (st : State) : Prop :=
  st.regs 0 = n ∧ st.regs 1 = m ∧ st.regs 2 = csrAddr ∧
  st.regs 3 = vMaskAddr ∧ st.regs 4 = eMaskAddr ∧ st.regs 5 = u ∧ st.regs 6 = v ∧
  st.regs 7 = workAddr ∧ st.regs 8 = outAddr ∧ st.regs 9 = parVBase ∧
  st.regs 10 = parEBase ∧ st.regs 11 = queueBase ∧ st.regs 12 = adjVBase ∧
  st.regs 13 = adjHBase ∧
  (st.regs 19 = 0 ∨ st.regs 19 = 1) ∧
  st.regs 14 ≤ st.regs 15 ∧ st.regs 15 ≤ n ∧ 0 < st.regs 15 ∧
  MemFrame memBase st.mem workAddr (workAddr + 4 * n) ∧
  (∀ i < st.regs 15, st.mem (queueBase + i) < n ∧ st.mem (workAddr + st.mem (queueBase + i)) ≠ 0) ∧
  (∀ i < st.regs 15, ∀ j < st.regs 15,
    st.mem (queueBase + i) = st.mem (queueBase + j) → i = j) ∧
  (∀ x < n, st.mem (workAddr + x) ≠ 0 → ∃ i < st.regs 15, st.mem (queueBase + i) = x) ∧
  (∀ x < n, st.mem (workAddr + x) ≤ st.regs 15) ∧
  st.mem (workAddr + u) = 1 ∧
  (∀ x < n, st.mem (workAddr + x) = 1 → x = u) ∧
  (∀ x < n, st.mem (workAddr + x) ≠ 0 → memInit (vMaskAddr + x) ≠ 0) ∧
  (∀ x < n, 2 ≤ st.mem (workAddr + x) →
    st.mem (workAddr + st.mem (parVBase + x)) + 1 = st.mem (workAddr + x) ∧
    st.mem (parVBase + x) < n ∧
    st.mem (parEBase + x) < m ∧
    memInit (eMaskAddr + st.mem (parEBase + x)) ≠ 0 ∧
    Walk.EdgeMatches (G.edges.getD (st.mem (parEBase + x)) (0, 0)) (st.mem (parVBase + x)) x) ∧
  ((st.regs 16 = 0 ∧ st.regs 17 = 0 ∧ st.regs 14 = 0 ∧ st.regs 19 = 1) ∨
    (0 < st.regs 14 ∧ st.regs 18 = st.mem (queueBase + (st.regs 14 - 1)) ∧
     st.regs 18 < n ∧
     csrOff G (st.regs 18) ≤ st.regs 16 ∧ st.regs 16 ≤ st.regs 17 ∧
     st.regs 17 = csrOff G (st.regs 18 + 1))) ∧
  (∀ i, i + 1 < st.regs 14 →
    let x := st.mem (queueBase + i)
    ∀ t (ht : t < (csrIncAux x 0 G.edges).length),
      let q := (csrIncAux x 0 G.edges)[t]'ht
      memInit (vMaskAddr + q.2.2) ≠ 0 → memInit (eMaskAddr + q.1) ≠ 0 →
      st.mem (workAddr + q.2.2) ≠ 0) ∧
  (0 < st.regs 14 →
    ∀ t (ht : t < (csrIncAux (st.regs 18) 0 G.edges).length),
      csrOff G (st.regs 18) + t < st.regs 16 →
      let q := (csrIncAux (st.regs 18) 0 G.edges)[t]'ht
      memInit (vMaskAddr + q.2.2) ≠ 0 → memInit (eMaskAddr + q.1) ≠ 0 →
      st.mem (workAddr + q.2.2) ≠ 0) ∧
  (st.regs 19 = 0 → st.regs 14 = st.regs 15 ∧ st.regs 17 ≤ st.regs 16) ∧
  BfsShortestInv n workAddr parVBase queueBase vMaskAddr eMaskAddr G memInit st

private def bfsMeas (G : Cited.Graph) (n queueBase : ℕ) (st : State) : ℕ :=
  (csrOff G n - bfsDoneDeg G queueBase (st.regs 14) st.mem) +
  (st.regs 17 - st.regs 16) + (n - st.regs 14) + st.regs 19

private lemma bfs_main_skip_inv
    {n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase : ℕ}
    {G : Cited.Graph} {memInit memBase : ℕ → ℕ} {st st' : State}
    (hn : G.n = n) (hval : G.IsValid)
    (hInv : BfsMainInv n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase G memInit memBase st)
    (h19_eq : st.regs 19 = 1)
    (hcur_pos : 0 < st.regs 14)
    (hcur_eq : st.regs 18 = st.mem (queueBase + (st.regs 14 - 1)))
    (hcur_n : st.regs 18 < n)
    (hcur_le : csrOff G (st.regs 18) ≤ st.regs 16)
    (hk_lt : st.regs 16 < st.regs 17)
    (hkEnd_eq : st.regs 17 = csrOff G (st.regs 18 + 1))
    (hmem : st'.mem = st.mem)
    (hr14 : ∀ r ≤ 15, st'.regs r = st.regs r)
    (hr16 : st'.regs 16 = st.regs 16 + 1)
    (hr17 : st'.regs 17 = st.regs 17) (hr18 : st'.regs 18 = st.regs 18)
    (hr19 : st'.regs 19 = 1)
    (hstep_ok :
      let q_entry := (csrIncAux (st.regs 18) 0 G.edges)[st.regs 16 - csrOff G (st.regs 18)]'(by rw [hkEnd_eq, csrOff_succ] at hk_lt; omega)
      memInit (vMaskAddr + q_entry.2.2) ≠ 0 → memInit (eMaskAddr + q_entry.1) ≠ 0 →
      st.mem (workAddr + q_entry.2.2) ≠ 0) :
    BfsMainInv n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase G memInit memBase st' ∧
    bfsMeas G n queueBase st' < bfsMeas G n queueBase st := by
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    _, h14_15, h15_n, h15_pos, hfr, hq_lt, hq_inj, hdist_q, hdist_le, hdu, hdu_uniq,
    hd_vm, hpar_inv, _, hscan_prev, hscan_cur, _, hshort⟩
  have hdd_le : bfsDoneDeg G queueBase (st.regs 14) st.mem ≤ csrOff G n := by
    rw [← hn]
    exact bfsDoneDeg_le G queueBase (st.regs 14) st.mem fun i hi =>
      by simpa [hn] using (hq_lt i (by omega)).1
  have hr14_eq : st'.regs 14 = st.regs 14 := hr14 14 (by omega)
  have hr15_eq : st'.regs 15 = st.regs 15 := hr14 15 (by omega)
  refine ⟨⟨by rw [hr14 0 (by omega), hr0], by rw [hr14 1 (by omega), hr1],
    by rw [hr14 2 (by omega), hr2], by rw [hr14 3 (by omega), hr3],
    by rw [hr14 4 (by omega), hr4], by rw [hr14 5 (by omega), hr5],
    by rw [hr14 6 (by omega), hr6], by rw [hr14 7 (by omega), hr7],
    by rw [hr14 8 (by omega), hr8], by rw [hr14 9 (by omega), hr9],
    by rw [hr14 10 (by omega), hr10], by rw [hr14 11 (by omega), hr11],
    by rw [hr14 12 (by omega), hr12], by rw [hr14 13 (by omega), hr13],
    Or.inr hr19, by omega, by omega, by omega,
    by rw [hmem]; exact hfr,
    by rw [hmem, hr15_eq]; exact hq_lt,
    by rw [hmem, hr15_eq]; exact hq_inj,
    by rw [hmem, hr15_eq]; exact hdist_q,
    by rw [hmem, hr15_eq]; exact hdist_le,
    by rw [hmem]; exact hdu,
    by rw [hmem]; exact hdu_uniq,
    by rw [hmem]; exact hd_vm,
    by rw [hmem]; exact hpar_inv,
    Or.inr ⟨by rw [hr14_eq]; exact hcur_pos, by rw [hmem, hr18, hr14_eq]; exact hcur_eq,
      by rw [hr18]; exact hcur_n, by rw [hr18, hr16]; omega,
      by rw [hr16, hr17]; omega, by rw [hr17, hr18]; exact hkEnd_eq⟩,
    by rw [hmem, hr14_eq]; exact hscan_prev,
    ?_, fun h => by omega, ?_⟩, ?_⟩
  · dsimp only
    intro _ t ht hlt_new hvm_q hem_q
    rw [hmem]
    have ht' : t < (csrIncAux (st.regs 18) 0 G.edges).length := by rwa [← hr18]
    have hget_eq : (csrIncAux (st'.regs 18) 0 G.edges)[t]'ht =
        (csrIncAux (st.regs 18) 0 G.edges)[t]'ht' := by simp only [hr18]
    rw [hget_eq] at hvm_q hem_q ⊢
    rw [hr16] at hlt_new
    by_cases hlt_old : csrOff G (st.regs 18) + t < st.regs 16
    · exact hscan_cur hcur_pos t ht' hlt_old hvm_q hem_q
    · have ht_eq : t = st.regs 16 - csrOff G (st.regs 18) := by
        rw [hr18] at hlt_new; omega
      subst ht_eq
      exact hstep_ok hvm_q hem_q
  · exact bfsShortestInv_skip hn hval hq_lt (fun x hx h => (hpar_inv x hx h).1) h14_15 hcur_pos
      hcur_eq hcur_le hk_lt hkEnd_eq hmem hr14_eq hr15_eq hr16 hr18 hstep_ok hshort
  · unfold bfsMeas
    have hdd_eq : bfsDoneDeg G queueBase (st'.regs 14) st'.mem =
        bfsDoneDeg G queueBase (st.regs 14) st.mem := by
      rw [hmem, hr14_eq]
    rw [hdd_eq, hr14_eq, hr16, hr17, hr19, h19_eq]
    omega

private lemma bfs_main_push_inv
    {n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase : ℕ}
    {G : Cited.Graph} {memInit memBase : ℕ → ℕ} {st st' : State} {nbr edgeIdx dcur : ℕ}
    (hn : G.n = n) (_hm : G.m = m) (hval : G.IsValid)
    (hpv : parVBase = workAddr + n) (hpe : parEBase = workAddr + 2 * n)
    (hqb : queueBase = workAddr + 3 * n)
    (hInv : BfsMainInv n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase G memInit memBase st)
    (h19_eq : st.regs 19 = 1)
    (hcur_pos : 0 < st.regs 14)
    (hcur_eq : st.regs 18 = st.mem (queueBase + (st.regs 14 - 1)))
    (hcur_n : st.regs 18 < n)
    (hcur_le : csrOff G (st.regs 18) ≤ st.regs 16)
    (hk_lt : st.regs 16 < st.regs 17)
    (hkEnd_eq : st.regs 17 = csrOff G (st.regs 18 + 1))
    (hd_cur : st.mem (workAddr + st.regs 18) = dcur)
    (hd_nbr0 : st.mem (workAddr + nbr) = 0)
    (hu_n : u < n) (hnbr_lt : nbr < n) (hedge_lt : edgeIdx < m)
    (hvm_nbr : memInit (vMaskAddr + nbr) ≠ 0)
    (hem_edge : memInit (eMaskAddr + edgeIdx) ≠ 0)
    (hmatch : Walk.EdgeMatches (G.edges.getD edgeIdx (0, 0)) (st.regs 18) nbr)
    (hq_entry_eq :
      let t := st.regs 16 - csrOff G (st.regs 18)
      let q_entry := (csrIncAux (st.regs 18) 0 G.edges)[t]'(by rw [hkEnd_eq, csrOff_succ] at hk_lt; omega)
      q_entry.2.2 = nbr ∧ q_entry.1 = edgeIdx)
    (hmem : st'.mem = Function.update (Function.update (Function.update
      (Function.update st.mem (workAddr + nbr) (dcur + 1))
      (parVBase + nbr) (st.regs 18)) (parEBase + nbr) edgeIdx) (queueBase + st.regs 15) nbr)
    (hr14 : ∀ r ≤ 14, st'.regs r = st.regs r)
    (hr15 : st'.regs 15 = st.regs 15 + 1)
    (hr16 : st'.regs 16 = st.regs 16 + 1)
    (hr17 : st'.regs 17 = st.regs 17) (hr18 : st'.regs 18 = st.regs 18)
    (hr19 : st'.regs 19 = 1) :
    BfsMainInv n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase G memInit memBase st' ∧
    bfsMeas G n queueBase st' < bfsMeas G n queueBase st := by
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    _, h14_15, h15_n, h15_pos, hfr, hq_lt, hq_inj, hdist_q, hdist_le, hdu, hdu_uniq,
    hd_vm, hpar_inv, _, hscan_prev, hscan_cur, _, hshort⟩
  have hdd_le : bfsDoneDeg G queueBase (st.regs 14) st.mem ≤ csrOff G n := by
    rw [← hn]
    exact bfsDoneDeg_le G queueBase (st.regs 14) st.mem fun i hi =>
      by simpa [hn] using (hq_lt i (by omega)).1
  have hcur_dist_nz : st.mem (workAddr + st.regs 18) ≠ 0 := by
    rw [hcur_eq]
    exact (hq_lt (st.regs 14 - 1) (by omega)).2
  have hdcur_pos : 1 ≤ dcur := by omega
  have hdcur_le : dcur ≤ st.regs 15 := by rw [← hd_cur]; exact hdist_le _ hcur_n
  have hnbr_new : ∀ i < st.regs 15, st.mem (queueBase + i) ≠ nbr := by
    intro i hi heq
    have hnz := (hq_lt i hi).2
    rw [heq] at hnz
    exact hnz hd_nbr0
  have hq15_n : st.regs 15 + 1 ≤ n :=
    card_inj_insert_le (fun i hi => (hq_lt i hi).1) hq_inj hnbr_lt hnbr_new
  have hmem_dist : ∀ x < n, st'.mem (workAddr + x) =
      if x = nbr then dcur + 1 else st.mem (workAddr + x) := by
    intro x hx
    rw [hmem]
    rw [Function.update_of_ne (by omega : workAddr + x ≠ queueBase + st.regs 15),
      Function.update_of_ne (by omega : workAddr + x ≠ parEBase + nbr),
      Function.update_of_ne (by omega : workAddr + x ≠ parVBase + nbr)]
    by_cases hxn : x = nbr
    · subst hxn; simp [Function.update_self]
    · simp [hxn]
  have hmem_parV : st'.mem (parVBase + nbr) = st.regs 18 := by
    rw [hmem, Function.update_of_ne (by omega : parVBase + nbr ≠ queueBase + st.regs 15),
      Function.update_of_ne (by omega : parVBase + nbr ≠ parEBase + nbr), Function.update_self]
  have hmem_parE : st'.mem (parEBase + nbr) = edgeIdx := by
    rw [hmem, Function.update_of_ne (by omega : parEBase + nbr ≠ queueBase + st.regs 15),
      Function.update_self]
  have hmem_parV_ne : ∀ x < n, x ≠ nbr → st'.mem (parVBase + x) = st.mem (parVBase + x) := by
    intro x hx hne
    rw [hmem, Function.update_of_ne (by omega : parVBase + x ≠ queueBase + st.regs 15),
      Function.update_of_ne (by omega : parVBase + x ≠ parEBase + nbr),
      Function.update_of_ne (by omega : parVBase + x ≠ parVBase + nbr),
      Function.update_of_ne (by omega : parVBase + x ≠ workAddr + nbr)]
  have hmem_parE_ne : ∀ x < n, x ≠ nbr → st'.mem (parEBase + x) = st.mem (parEBase + x) := by
    intro x hx hne
    rw [hmem, Function.update_of_ne (by omega : parEBase + x ≠ queueBase + st.regs 15),
      Function.update_of_ne (by omega : parEBase + x ≠ parEBase + nbr),
      Function.update_of_ne (by omega : parEBase + x ≠ parVBase + nbr),
      Function.update_of_ne (by omega : parEBase + x ≠ workAddr + nbr)]
  have hmem_q : ∀ i < st.regs 15 + 1, st'.mem (queueBase + i) =
      if i = st.regs 15 then nbr else st.mem (queueBase + i) := by
    intro i hi
    rw [hmem]
    by_cases hiq : i = st.regs 15
    · subst hiq; simp [Function.update_self]
    · simp [hiq, Function.update_of_ne (by omega : queueBase + i ≠ parEBase + nbr),
        Function.update_of_ne (by omega : queueBase + i ≠ parVBase + nbr),
        Function.update_of_ne (by omega : queueBase + i ≠ workAddr + nbr)]
  have hfr' : MemFrame memBase st'.mem workAddr (workAddr + 4 * n) := by
    rw [hmem]
    refine memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
      (memFrame_trans (memFrame_update (by omega) (by omega))
      (memFrame_trans (memFrame_update (by omega) (by omega))
      (memFrame_update (by omega) (by omega)))))
  have hr14_eq : st'.regs 14 = st.regs 14 := hr14 14 (by omega)
  have hu_ne_nbr : u ≠ nbr := by intro heq; rw [← heq, hdu] at hd_nbr0; omega
  have hcur_ne_nbr : st.regs 18 ≠ nbr := by intro heq; rw [heq, hd_nbr0] at hcur_dist_nz; exact hcur_dist_nz rfl
  refine ⟨⟨by rw [hr14 0 (by omega), hr0], by rw [hr14 1 (by omega), hr1],
    by rw [hr14 2 (by omega), hr2], by rw [hr14 3 (by omega), hr3],
    by rw [hr14 4 (by omega), hr4], by rw [hr14 5 (by omega), hr5],
    by rw [hr14 6 (by omega), hr6], by rw [hr14 7 (by omega), hr7],
    by rw [hr14 8 (by omega), hr8], by rw [hr14 9 (by omega), hr9],
    by rw [hr14 10 (by omega), hr10], by rw [hr14 11 (by omega), hr11],
    by rw [hr14 12 (by omega), hr12], by rw [hr14 13 (by omega), hr13],
    Or.inr hr19, by omega, by omega, by omega, hfr', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h => by omega, ?_⟩, ?_⟩
  · intro i hi
    rw [hr15] at hi
    rw [hmem_q i hi]
    split_ifs with hiq
    · refine ⟨hnbr_lt, ?_⟩; rw [hmem_dist nbr hnbr_lt]; simp
    · have hi' : i < st.regs 15 := by omega
      have hqi := hq_lt i hi'
      refine ⟨hqi.1, ?_⟩
      rw [hmem_dist _ hqi.1]
      split_ifs <;> [omega; exact hqi.2]
  · intro i hi j hj heq
    rw [hr15] at hi hj
    rw [hmem_q i hi, hmem_q j hj] at heq
    by_cases hiq : i = st.regs 15 <;> by_cases hjq : j = st.regs 15
    · omega
    · simp only [hiq, hjq, ↓reduceIte] at heq
      exact False.elim (hnbr_new j (by omega) heq.symm)
    · simp only [hiq, hjq, ↓reduceIte] at heq
      exact False.elim (hnbr_new i (by omega) heq)
    · simp only [hiq, hjq, ↓reduceIte] at heq
      exact hq_inj i (by omega) j (by omega) heq
  · intro x hx hnz
    rw [hr15]
    rw [hmem_dist x hx] at hnz
    by_cases hxn : x = nbr
    · subst hxn
      refine ⟨st.regs 15, by omega, ?_⟩
      rw [hmem_q _ (by omega)]; simp
    · simp only [hxn, ↓reduceIte] at hnz
      rcases hdist_q x hx hnz with ⟨i, hi, hi_eq⟩
      refine ⟨i, by omega, ?_⟩
      rw [hmem_q i (by omega)]
      simp [show i ≠ st.regs 15 by omega, hi_eq]
  · intro x hx
    rw [hr15, hmem_dist x hx]
    split_ifs <;> [omega; exact le_trans (hdist_le x hx) (Nat.le_succ _)]
  · rw [hmem_dist u (by omega)]
    simp [hu_ne_nbr, hdu]
  · intro x hx hd1
    rw [hmem_dist x hx] at hd1
    split_ifs at hd1 with hxn
    · omega
    · exact hdu_uniq x hx hd1
  · intro x hx hnz
    rw [hmem_dist x hx] at hnz
    split_ifs at hnz with hxn
    · subst hxn; exact hvm_nbr
    · exact hd_vm x hx hnz
  · intro x hx hge2
    rw [hmem_dist x hx] at hge2 ⊢
    by_cases hxn : x = nbr
    · subst hxn
      simp only [↓reduceIte]
      rw [hmem_parV, hmem_parE, hmem_dist _ hcur_n]
      simp only [hcur_ne_nbr, ↓reduceIte, hd_cur]
      exact ⟨trivial, hcur_n, hedge_lt, hem_edge, hmatch⟩
    · simp only [hxn, ↓reduceIte] at hge2 ⊢
      have hp := hpar_inv x hx hge2
      have hne_px : st.mem (parVBase + x) ≠ nbr := by
        intro heq
        have hnz : st.mem (workAddr + st.mem (parVBase + x)) ≠ 0 := by omega
        rw [heq, hd_nbr0] at hnz; exact hnz rfl
      rw [hmem_parV_ne x hx hxn, hmem_parE_ne x hx hxn, hmem_dist _ hp.2.1]
      simpa [hne_px] using hp
  · refine Or.inr ⟨by rw [hr14_eq]; exact hcur_pos, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr18, hr14_eq, hmem_q _ (by omega)]
      simp [show st.regs 14 - 1 ≠ st.regs 15 by omega, hcur_eq]
    · rw [hr18]; exact hcur_n
    · rw [hr18, hr16]; omega
    · rw [hr16, hr17]; omega
    · rw [hr17, hr18]; exact hkEnd_eq
  · dsimp only
    intro i hi t ht hvm_q hem_q
    rw [hr14_eq] at hi
    have hi_ne : i ≠ st.regs 15 := by omega
    have ht' : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by
      simpa [hmem_q i (by omega), hi_ne] using ht
    have hget_eq : (csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t]'ht =
        (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht' := by
      simp only [hmem_q i (by omega), hi_ne, ↓reduceIte]
    rw [hget_eq] at hvm_q hem_q ⊢
    have hq_prev := hscan_prev i hi t ht' hvm_q hem_q
    have hqn : (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t].2.2 < n := by
      rw [← hn]; exact (csrIncAux_getElem_lt hval ht').2.1
    rw [hmem_dist _ hqn]
    split_ifs <;> [omega; exact hq_prev]
  · dsimp only
    intro _ t ht hlt_new hvm_q hem_q
    rw [hr16] at hlt_new
    have ht' : t < (csrIncAux (st.regs 18) 0 G.edges).length := by rwa [← hr18]
    have hget_eq : (csrIncAux (st'.regs 18) 0 G.edges)[t]'ht =
        (csrIncAux (st.regs 18) 0 G.edges)[t]'ht' := by simp only [hr18]
    rw [hget_eq] at hvm_q hem_q ⊢
    rw [hr18] at hlt_new
    have hqn : (csrIncAux (st.regs 18) 0 G.edges)[t].2.2 < n := by
      rw [← hn]; exact (csrIncAux_getElem_lt hval ht').2.1
    rw [hmem_dist _ hqn]
    by_cases hlt_old : csrOff G (st.regs 18) + t < st.regs 16
    · have hprev := hscan_cur hcur_pos t ht' hlt_old hvm_q hem_q
      split_ifs <;> [omega; exact hprev]
    · have ht_eq : t = st.regs 16 - csrOff G (st.regs 18) := by omega
      subst ht_eq
      rcases hq_entry_eq with ⟨h22, h1⟩
      rw [h22]
      simp only [↓reduceIte]
      omega
  · exact bfsShortestInv_push hn hval hq_lt (fun x hx h => (hpar_inv x hx h).1) hscan_prev
      hscan_cur h14_15 hcur_pos hcur_eq hcur_n hnbr_lt hcur_le hk_lt hkEnd_eq hd_cur hd_nbr0
      hdcur_pos hcur_ne_nbr hq_entry_eq.1 hmem_dist hmem_parV hmem_parV_ne hmem_q hr14_eq hr15
      hr16 hr18 hshort
  · unfold bfsMeas
    have hdd_eq : bfsDoneDeg G queueBase (st'.regs 14) st'.mem =
        bfsDoneDeg G queueBase (st.regs 14) st.mem := by
      rw [hr14_eq]
      refine bfsDoneDeg_congr G queueBase (st.regs 14) fun i hi => ?_
      rw [hmem_q i (by omega)]; simp [show i ≠ st.regs 15 by omega]
    rw [hdd_eq, hr14_eq, hr16, hr17, hr19, h19_eq]
    omega

private lemma bfs_scan_body_triple {w : ℕ} {p : Program} (st0 : State)
    (n m vMaskAddr eMaskAddr workAddr parVBase parEBase queueBase adjVBase adjHBase : ℕ)
    (cur k nbr half edgeIdx distNbr vmNbr emEdge dcur qTail : ℕ)
    (h3 : st0.regs 3 = vMaskAddr) (h4 : st0.regs 4 = eMaskAddr) (h7 : st0.regs 7 = workAddr)
    (h9 : st0.regs 9 = parVBase) (h10 : st0.regs 10 = parEBase) (h11 : st0.regs 11 = queueBase)
    (h12 : st0.regs 12 = adjVBase) (h13 : st0.regs 13 = adjHBase) (h15 : st0.regs 15 = qTail)
    (h16 : st0.regs 16 = k) (h18 : st0.regs 18 = cur)
    (hpv : parVBase = workAddr + n) (hpe : parEBase = workAddr + 2 * n) (hqb : queueBase = workAddr + 3 * n)
    (hadjV_eq : st0.mem (adjVBase + k) = nbr)
    (hadjH_eq : st0.mem (adjHBase + k) = half)
    (hdiv_eq : half / 2 = edgeIdx)
    (hdist_eq : st0.mem (workAddr + nbr) = distNbr)
    (hvm_eq : st0.mem (vMaskAddr + nbr) = vmNbr)
    (hem_eq : st0.mem (eMaskAddr + edgeIdx) = emEdge)
    (hdcur_eq : st0.mem (workAddr + cur) = dcur)
    (hcur_lt : cur < n) (hnbr_lt : nbr < n) (hedge_lt : edgeIdx < m)
    (hdcur_le : dcur ≤ n)
    (hq_lt_push : distNbr = 0 → 0 < vmNbr → 0 < emEdge → qTail < n)
    (hadjV_k_w : adjVBase + k < 2 ^ w) (hadjH_k_w : adjHBase + k < 2 ^ w)
    (hwork_w : workAddr + 4 * n < 2 ^ w)
    (hvm_w : vMaskAddr + n < 2 ^ w) (hem_w : eMaskAddr + m < 2 ^ w)
    (hk1_w : k + 1 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st0)
      (seqStmts [
        .assign 20 (.load (.bin .add (.reg 12) (.reg 16))),
        .assign 21 (.load (.bin .add (.reg 13) (.reg 16))),
        .assign 22 (.bin .div (.reg 21) (.const 2)),
        .assign 23 (.load (.bin .add (.reg 7) (.reg 20))),
        .cond (.bin .eq (.reg 23) (.const 0))
          (seqStmts [
            .assign 24 (.load (.bin .add (.reg 3) (.reg 20))),
            .cond (.bin .lt (.const 0) (.reg 24))
              (seqStmts [
                .assign 25 (.load (.bin .add (.reg 4) (.reg 22))),
                .cond (.bin .lt (.const 0) (.reg 25))
                  (seqStmts [
                    .assign 26 (.load (.bin .add (.reg 7) (.reg 18))),
                    .store (.bin .add (.reg 7) (.reg 20)) (.bin .add (.reg 26) (.const 1)),
                    .store (.bin .add (.reg 9) (.reg 20)) (.reg 18),
                    .store (.bin .add (.reg 10) (.reg 20)) (.reg 22),
                    .store (.bin .add (.reg 11) (.reg 15)) (.reg 20),
                    .assign 15 (.bin .add (.reg 15) (.const 1))])
                  .nop])
              .nop])
          .nop,
        .assign 16 (.bin .add (.reg 16) (.const 1))])
      (normalPost fun st' =>
        (distNbr = 0 ∧ 0 < vmNbr ∧ 0 < emEdge →
          (∀ r ≤ 14, st'.regs r = st0.regs r) ∧
          st'.regs 15 = qTail + 1 ∧ st'.regs 16 = k + 1 ∧
          (∀ r, 17 ≤ r → r ≤ 19 → st'.regs r = st0.regs r) ∧
          st'.mem = Function.update (Function.update (Function.update
            (Function.update st0.mem (workAddr + nbr) (dcur + 1))
            (parVBase + nbr) cur) (parEBase + nbr) edgeIdx) (queueBase + qTail) nbr) ∧
        (¬ (distNbr = 0 ∧ 0 < vmNbr ∧ 0 < emEdge) →
          (∀ r ≤ 15, st'.regs r = st0.regs r) ∧
          st'.regs 16 = k + 1 ∧
          (∀ r, 17 ≤ r → r ≤ 19 → st'.regs r = st0.regs r) ∧
          st'.mem = st0.mem))
      (fun _ => 105) := by
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hite_w : ∀ c : Prop, ∀ [Decidable c], (if c then 1 else 0) < 2 ^ w := fun c => by
    split_ifs <;> omega
  have hedge_w : edgeIdx < 2 ^ w := by omega
  have hwn_w : workAddr + nbr < 2 ^ w := by omega
  have hvmn_w : vMaskAddr + nbr < 2 ^ w := by omega
  have heme_w : eMaskAddr + edgeIdx < 2 ^ w := by omega
  have he20 : (Expr.load (.bin .add (.reg 12) (.reg 16))).eval w st = some nbr := by
    simp [Expr.eval, BinOp.eval, h12, h16, hadjV_k_w, hadjV_eq]
  refine runs_seq_assign_le he20 ?_
  let st1 : State := { st with regs := Function.update st.regs 20 nbr }
  have he21 : (Expr.load (.bin .add (.reg 13) (.reg 16))).eval w st1 = some half := by
    simp [Expr.eval, BinOp.eval, st1, h13, h16, hadjH_k_w, hadjH_eq]
  refine runs_seq_assign_le he21 ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 21 half }
  have he22 : (Expr.bin .div (.reg 21) (.const 2)).eval w st2 = some edgeIdx := by
    simp [Expr.eval, BinOp.eval, st2, Function.update_self, h2_w, hdiv_eq, hedge_w]
  refine runs_seq_assign_le he22 ?_
  let st3 : State := { st2 with regs := Function.update st2.regs 22 edgeIdx }
  have he23 : (Expr.load (.bin .add (.reg 7) (.reg 20))).eval w st3 = some distNbr := by
    simp [Expr.eval, BinOp.eval, st3, st2, st1, h7, hwn_w, hdist_eq]
  refine runs_seq_assign_le he23 ?_
  let st4 : State := { st3 with regs := Function.update st3.regs 23 distNbr }
  have hr_le19 : ∀ r ≤ 19, st4.regs r = st.regs r := fun r hr => by
    simp [st4, st3, st2, st1, Function.update_of_ne (by omega : r ≠ 23),
      Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 21),
      Function.update_of_ne (by omega : r ≠ 20)]
  have hr20_4 : st4.regs 20 = nbr := by
    simp [st4, st3, st2, st1]
  have hr22_4 : st4.regs 22 = edgeIdx := by
    simp [st4, st3, Function.update_self]
  have hr23_4 : st4.regs 23 = distNbr := by simp [st4, Function.update_self]
  have hmem_4 : st4.mem = st.mem := rfl
  have hcond_triple :
      Triple w p (fun s => s = st4)
        (.cond (.bin .eq (.reg 23) (.const 0))
          (seqStmts [
            .assign 24 (.load (.bin .add (.reg 3) (.reg 20))),
            .cond (.bin .lt (.const 0) (.reg 24))
              (seqStmts [
                .assign 25 (.load (.bin .add (.reg 4) (.reg 22))),
                .cond (.bin .lt (.const 0) (.reg 25))
                  (seqStmts [
                    .assign 26 (.load (.bin .add (.reg 7) (.reg 18))),
                    .store (.bin .add (.reg 7) (.reg 20)) (.bin .add (.reg 26) (.const 1)),
                    .store (.bin .add (.reg 9) (.reg 20)) (.reg 18),
                    .store (.bin .add (.reg 10) (.reg 20)) (.reg 22),
                    .store (.bin .add (.reg 11) (.reg 15)) (.reg 20),
                    .assign 15 (.bin .add (.reg 15) (.const 1))])
                  .nop])
              .nop])
          .nop)
        (normalPost fun st' =>
          (distNbr = 0 ∧ 0 < vmNbr ∧ 0 < emEdge →
            (∀ r ≤ 14, st'.regs r = st.regs r) ∧
            st'.regs 15 = qTail + 1 ∧ st'.regs 16 = k ∧
            (∀ r, 17 ≤ r → r ≤ 19 → st'.regs r = st.regs r) ∧
            st'.mem = Function.update (Function.update (Function.update
              (Function.update st.mem (workAddr + nbr) (dcur + 1))
              (parVBase + nbr) cur) (parEBase + nbr) edgeIdx) (queueBase + qTail) nbr) ∧
          (¬ (distNbr = 0 ∧ 0 < vmNbr ∧ 0 < emEdge) →
            (∀ r ≤ 19, st'.regs r = st.regs r) ∧ st'.mem = st.mem))
        (fun _ => 70) := by
    intro s ω' hs; subst hs; refine runs_start_le ?_
    have hec1 : (Expr.bin .eq (.reg 23) (.const 0)).eval w st4 =
        some (if distNbr = 0 then 1 else 0) := by
      simp [Expr.eval, BinOp.eval, hr23_4, hite_w]
    refine runs_cond_le hec1 ?_ ?_
    · intro hne
      have hd0 : distNbr = 0 := by
        simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
        exact hne
      have he24 : (Expr.load (.bin .add (.reg 3) (.reg 20))).eval w st4 = some vmNbr := by
        simp [Expr.eval, BinOp.eval, hr_le19 3 (by omega), h3, hr20_4, hvmn_w, hmem_4, hvm_eq]
      refine runs_seq_assign_le he24 ?_
      let st5a : State := { st4 with regs := Function.update st4.regs 24 vmNbr }
      have hec2 : (Expr.bin .lt (.const 0) (.reg 24)).eval w st5a =
          some (if 0 < vmNbr then 1 else 0) := by
        simp [Expr.eval, BinOp.eval, st5a, Function.update_self, hite_w]
      refine runs_cond_le hec2 ?_ ?_
      · intro hne2
        have hvm_pos : 0 < vmNbr := by
          simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne2
          exact hne2
        have he25 : (Expr.load (.bin .add (.reg 4) (.reg 22))).eval w st5a = some emEdge := by
          simp [Expr.eval, BinOp.eval, st5a, hr_le19 4 (by omega), h4, hr22_4, heme_w, hmem_4, hem_eq]
        refine runs_seq_assign_le he25 ?_
        let st5b : State := { st5a with regs := Function.update st5a.regs 25 emEdge }
        have hec3 : (Expr.bin .lt (.const 0) (.reg 25)).eval w st5b =
            some (if 0 < emEdge then 1 else 0) := by
          simp [Expr.eval, BinOp.eval, st5b, Function.update_self, hite_w]
        refine runs_cond_le hec3 ?_ ?_
        · intro hne3
          have hem_pos : 0 < emEdge := by
            simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne3
            exact hne3
          have hq_n : qTail < n := hq_lt_push hd0 hvm_pos hem_pos
          have hr_5b : ∀ r ≤ 19, st5b.regs r = st.regs r := fun r hr => by
            simp [st5b, st5a, Function.update_of_ne (by omega : r ≠ 25),
              Function.update_of_ne (by omega : r ≠ 24), hr_le19 r hr]
          have h20_5b : st5b.regs 20 = nbr := by
            simpa [st5b, st5a, Function.update_of_ne (by decide : (20 : ℕ) ≠ 25),
              Function.update_of_ne (by decide : (20 : ℕ) ≠ 24)] using hr20_4
          have h22_5b : st5b.regs 22 = edgeIdx := by
            simpa [st5b, st5a, Function.update_of_ne (by decide : (22 : ℕ) ≠ 25),
              Function.update_of_ne (by decide : (22 : ℕ) ≠ 24)] using hr22_4
          have hmem_5b : st5b.mem = st.mem := rfl
          refine runs_triple_le
            (bfs_push_triple st5b workAddr parVBase parEBase queueBase cur nbr edgeIdx dcur qTail n
              (by rw [hr_5b 7 (by omega), h7]) (by rw [hr_5b 9 (by omega), h9])
              (by rw [hr_5b 10 (by omega), h10]) (by rw [hr_5b 11 (by omega), h11])
              (by rw [hr_5b 15 (by omega), h15]) (by rw [hr_5b 18 (by omega), h18])
              h20_5b h22_5b hpv hpe hqb hdcur_eq hcur_lt hnbr_lt hq_n hdcur_le hwork_w h1_w)
            rfl ?_ ?_
          · intro o st' hpost
            cases o with
            | returned _ => exact False.elim hpost
            | normal =>
              rcases hpost with ⟨hle14, h15', h16_19, hmem'⟩
              refine ⟨fun _ => ⟨fun r hr => by rw [hle14 r hr, hr_5b r (by omega)],
                  h15', by rw [h16_19 16 (by omega) (by omega), hr_5b 16 (by omega), h16],
                  fun r h1 h2 => by rw [h16_19 r (by omega) h2, hr_5b r (by omega)], hmem'⟩,
                fun hneg => False.elim (hneg ⟨hd0, hvm_pos, hem_pos⟩)⟩
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
        · intro he0
          have hem0 : emEdge = 0 := by
            simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, Nat.le_zero] at he0
            exact he0
          refine runs_nop_le ?_ ?_
          · dsimp only [normalPost]
            refine ⟨fun h => by omega, fun _ => ⟨fun r hr => ?_, rfl⟩⟩
            simp [Function.update_of_ne (by omega : r ≠ 25),
              Function.update_of_ne (by omega : r ≠ 24), hr_le19 r hr]
          · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
      · intro hv0
        have hvm0 : vmNbr = 0 := by
          simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, Nat.le_zero] at hv0
          exact hv0
        refine runs_nop_le ?_ ?_
        · dsimp only [normalPost]
          refine ⟨fun h => by omega, fun _ => ⟨fun r hr => ?_, rfl⟩⟩
          simp [Function.update_of_ne (by omega : r ≠ 24), hr_le19 r hr]
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
    · intro hd_nz
      have hd_ne : distNbr ≠ 0 := by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false] at hd_nz
        exact hd_nz
      refine runs_nop_le ?_ ?_
      · dsimp only [normalPost]
        exact ⟨fun h => False.elim (hd_ne h.1), fun _ => ⟨hr_le19, rfl⟩⟩
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega
  refine runs_seq_triple_le hcond_triple rfl (fun st5 h5 => ?_)
  · rcases h5 with ⟨hpush, hskip⟩
    have h16_5 : st5.regs 16 = k := by
      by_cases hcond_all : distNbr = 0 ∧ 0 < vmNbr ∧ 0 < emEdge
      · exact (hpush hcond_all).2.2.1
      · rw [(hskip hcond_all).1 16 (by omega), h16]
    have he16 : (Expr.bin .add (.reg 16) (.const 1)).eval w st5 = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, h16_5, h1_w, hk1_w]
    refine runs_assign_le he16 ?_ ?_
    · dsimp only [normalPost]
      refine ⟨fun hcond_all => ?_, fun hcond_all => ?_⟩
      · obtain ⟨hle14, h15', _, h17_19, hmem'⟩ := hpush hcond_all
        refine ⟨fun r hr => by rw [Function.update_of_ne (by omega : r ≠ 16), hle14 r hr],
          by rw [Function.update_of_ne (by decide : (15 : ℕ) ≠ 16), h15'],
          by simp,
          fun r h1 h2 => by rw [Function.update_of_ne (by omega : r ≠ 16), h17_19 r h1 h2], hmem'⟩
      · obtain ⟨hle19, hmem'⟩ := hskip hcond_all
        refine ⟨fun r hr => by rw [Function.update_of_ne (by omega : r ≠ 16), hle19 r (by omega)],
          by simp,
          fun r h1 h2 => by rw [Function.update_of_ne (by omega : r ≠ 16), hle19 r (by omega)], hmem'⟩
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma bfs_pop_triple {w : ℕ} {p : Program} (st0 : State)
    (csrAddr queueBase qHead nxt off0 off1 : ℕ)
    (h2 : st0.regs 2 = csrAddr) (h11 : st0.regs 11 = queueBase) (h14 : st0.regs 14 = qHead)
    (hq_eq : st0.mem (queueBase + qHead) = nxt)
    (hoff0_eq : st0.mem (csrAddr + nxt) = off0)
    (hoff1_eq : st0.mem (csrAddr + nxt + 1) = off1)
    (hq_w : queueBase + qHead < 2 ^ w) (hq1_w : qHead + 1 < 2 ^ w)
    (hc0_w : csrAddr + nxt < 2 ^ w) (hc1_w : csrAddr + nxt + 1 < 2 ^ w)
    (h1_w : 1 < 2 ^ w) :
    Triple w p (fun st => st = st0)
      (seqStmts [
        .assign 18 (.load (.bin .add (.reg 11) (.reg 14))),
        .assign 14 (.bin .add (.reg 14) (.const 1)),
        .assign 16 (.load (.bin .add (.reg 2) (.reg 18))),
        .assign 17 (.load (.bin .add (.bin .add (.reg 2) (.reg 18)) (.const 1)))])
      (normalPost fun st' =>
        (∀ r ≤ 13, st'.regs r = st0.regs r) ∧
        st'.regs 14 = qHead + 1 ∧ st'.regs 15 = st0.regs 15 ∧
        st'.regs 16 = off0 ∧ st'.regs 17 = off1 ∧
        st'.regs 18 = nxt ∧ st'.regs 19 = st0.regs 19 ∧
        st'.mem = st0.mem)
      (fun _ => 25) := by
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  have he18 : (Expr.load (.bin .add (.reg 11) (.reg 14))).eval w st = some nxt := by
    simp [Expr.eval, BinOp.eval, h11, h14, hq_w, hq_eq]
  refine runs_seq_assign_le he18 ?_
  let st1 : State := { st with regs := Function.update st.regs 18 nxt }
  have he14 : (Expr.bin .add (.reg 14) (.const 1)).eval w st1 = some (qHead + 1) := by
    simp [Expr.eval, BinOp.eval, st1, h14, h1_w, hq1_w]
  refine runs_seq_assign_le he14 ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 14 (qHead + 1) }
  have he16 : (Expr.load (.bin .add (.reg 2) (.reg 18))).eval w st2 = some off0 := by
    simp [Expr.eval, BinOp.eval, st2, st1, h2, hc0_w, hoff0_eq]
  refine runs_seq_assign_le he16 ?_
  let st3 : State := { st2 with regs := Function.update st2.regs 16 off0 }
  have he17 : (Expr.load (.bin .add (.bin .add (.reg 2) (.reg 18)) (.const 1))).eval w st3 = some off1 := by
    simp [Expr.eval, BinOp.eval, st3, st2, st1, h2, h1_w, hc0_w, hc1_w, hoff1_eq]
  refine runs_assign_le he17 ?_ ?_
  · dsimp only [normalPost]
    refine ⟨fun r hr => by
        simp [Function.update_of_ne (by omega : r ≠ 17),
          Function.update_of_ne (by omega : r ≠ 16), Function.update_of_ne (by omega : r ≠ 14),
          Function.update_of_ne (by omega : r ≠ 18)],
      by simp,
      by simp,
      by simp,
      by simp,
      by simp,
      by simp, rfl⟩
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma bfs_main_loop {w : ℕ} {p : Program}
    (n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase : ℕ)
    (G : Cited.Graph) (memInit memBase : ℕ → ℕ)
    (hn : G.n = n) (hm : G.m = m) (hval : G.IsValid) (hu_n : u < n)
    (hcsr : HasCsrAt memInit csrAddr G)
    (hfr_init : MemFrame memInit memBase workAddr (workAddr + 4 * n))
    (hdj_cw : csrAddr + 2 * n + 1 + 4 * m ≤ workAddr ∨ workAddr + 4 * n ≤ csrAddr)
    (hdj_vw : vMaskAddr + n ≤ workAddr ∨ workAddr + 4 * n ≤ vMaskAddr)
    (hdj_ew : eMaskAddr + m ≤ workAddr ∨ workAddr + 4 * n ≤ eMaskAddr)
    (hcsr_w : csrAddr + 2 * n + 1 + 4 * m < 2 ^ w)
    (hvm_w : vMaskAddr + n < 2 ^ w) (hem_w : eMaskAddr + m < 2 ^ w)
    (hwork_w : workAddr + 4 * n < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hpv : parVBase = workAddr + n) (hpe : parEBase = workAddr + 2 * n)
    (hqb : queueBase = workAddr + 3 * n) (hav : adjVBase = csrAddr + 2 * n + 1)
    (hah : adjHBase = adjVBase + 2 * m) :
    Triple w p
      (BfsMainInv n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase G memInit memBase)
      (.loop (.reg 19)
        (.cond (.bin .lt (.reg 16) (.reg 17))
          (seqStmts [
            .assign 20 (.load (.bin .add (.reg 12) (.reg 16))),
            .assign 21 (.load (.bin .add (.reg 13) (.reg 16))),
            .assign 22 (.bin .div (.reg 21) (.const 2)),
            .assign 23 (.load (.bin .add (.reg 7) (.reg 20))),
            .cond (.bin .eq (.reg 23) (.const 0))
              (seqStmts [
                .assign 24 (.load (.bin .add (.reg 3) (.reg 20))),
                .cond (.bin .lt (.const 0) (.reg 24))
                  (seqStmts [
                    .assign 25 (.load (.bin .add (.reg 4) (.reg 22))),
                    .cond (.bin .lt (.const 0) (.reg 25))
                      (seqStmts [
                        .assign 26 (.load (.bin .add (.reg 7) (.reg 18))),
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
              .assign 18 (.load (.bin .add (.reg 11) (.reg 14))),
              .assign 14 (.bin .add (.reg 14) (.const 1)),
              .assign 16 (.load (.bin .add (.reg 2) (.reg 18))),
              .assign 17 (.load (.bin .add (.bin .add (.reg 2) (.reg 18)) (.const 1)))])
            (.assign 19 (.const 0)))))
      (normalPost fun st' =>
        BfsMainInv n m csrAddr vMaskAddr eMaskAddr u v workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase G memInit memBase st' ∧
        st'.regs 19 = 0)
      (fun st => (1 + 110 + 1) * bfsMeas G n queueBase st + 1 + 1) := by
  refine Triple.loop_const_normal (bfsMeas G n queueBase) (fun st => st.regs 19) 110
    (fun st hInv => by simp [Expr.eval])
    (fun st hInv h0 => ⟨hInv, h0⟩)
    (fun st hInv hne => ?_)
  have hInv_copy := hInv
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    h19_01, h14_15, h15_n, h15_pos, hfr, hq_lt, hq_inj, hdist_q, hdist_le, hdu, hdu_uniq,
    hd_vm, hpar_inv, hcur_act, hscan_prev, hscan_cur, _, hshort⟩
  have h19_eq1 : st.regs 19 = 1 := by omega
  have hfr_init_st : MemFrame memInit st.mem workAddr (workAddr + 4 * n) :=
    memFrame_trans hfr_init hfr
  have heq_csr : ∀ addr, csrAddr ≤ addr → addr < csrAddr + 2 * n + 1 + 4 * m →
      st.mem addr = memInit addr := fun addr ha hb =>
    hfr_init_st addr (by rcases hdj_cw with h | h <;> [left; right] <;> omega)
  have heq_vm : ∀ x < n, st.mem (vMaskAddr + x) = memInit (vMaskAddr + x) := fun x hx =>
    hfr_init_st (vMaskAddr + x) (by rcases hdj_vw with h | h <;> [left; right] <;> omega)
  have heq_em : ∀ j < m, st.mem (eMaskAddr + j) = memInit (eMaskAddr + j) := fun j hj =>
    hfr_init_st (eMaskAddr + j) (by rcases hdj_ew with h | h <;> [left; right] <;> omega)
  have hcsr_st : HasCsrAt st.mem csrAddr G := by
    refine ⟨fun u' hu' => ?_, fun u' hu' j hj => ?_⟩
    · rw [heq_csr (csrAddr + u') (by omega) (by omega)]
      exact hcsr.1 u' hu'
    · have hOff := csrOff_le_two_mul_m G (u' + 1); rw [csrOff_succ] at hOff
      rw [heq_csr (csrAddr + 2 * G.n + 1 + csrOff G u' + j) (by omega) (by omega),
          heq_csr (csrAddr + 2 * G.n + 1 + 2 * G.m + csrOff G u' + j) (by omega) (by omega)]
      exact hcsr.2 u' hu' j hj
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  wram_enter
  · subst hpre
    wram_step
    · -- Branch A: k < kEnd
      have hk_lt : st.regs 16 < st.regs 17 := by simpa using hcond
      rcases hcur_act with ⟨_, _, _, _⟩ | ⟨h14_pos, h18_eq, h18_n, hcur_le, hk_le, hkEnd_eq⟩
      · omega
      have ht_len : st.regs 16 - csrOff G (st.regs 18) < (csrIncAux (st.regs 18) 0 G.edges).length := by
        rw [hkEnd_eq, csrOff_succ] at hk_lt; omega
      let cur := st.regs 18
      let t := st.regs 16 - csrOff G cur
      let q_entry := (csrIncAux cur 0 G.edges)[t]'ht_len
      have hq_props := csrIncAux_getElem_lt hval ht_len
      have hadj_v_mem : st.mem (adjVBase + st.regs 16) = q_entry.2.2 := by
        have hk_eq : adjVBase + st.regs 16 = csrAddr + 2 * G.n + 1 + csrOff G cur + t := by
          dsimp only [cur, t]; rw [hav, hn]; omega
        rw [hk_eq]; exact (hcsr_st.2 cur (hn.symm ▸ h18_n) t ht_len).1
      have hadj_h_mem : st.mem (adjHBase + st.regs 16) = 2 * q_entry.1 + (if q_entry.2.1 then 1 else 0) := by
        have hk_eq : adjHBase + st.regs 16 = csrAddr + 2 * G.n + 1 + 2 * G.m + csrOff G cur + t := by
          dsimp only [cur, t]; rw [hah, hav, hn, hm]; omega
        rw [hk_eq]; exact (hcsr_st.2 cur (hn.symm ▸ h18_n) t ht_len).2
      have hdiv_eq : (2 * q_entry.1 + (if q_entry.2.1 then 1 else 0)) / 2 = q_entry.1 := by
        cases q_entry.2.1
        · simp
        · simp; clear hInv_copy hfr hq_lt hq_inj hdist_q hdist_le hpar_inv hscan_prev hscan_cur; omega
      have hnbr_lt : q_entry.2.2 < n := by rw [← hn]; exact hq_props.2.1
      have hedge_lt : q_entry.1 < m := by rw [← hm]; exact hq_props.1
      have hk16_le : st.regs 16 < 2 * m := by
        have := csrOff_le_two_mul_m G (cur + 1)
        dsimp only [cur] at *; rw [← hm]; omega
      have hk1_w : st.regs 16 + 1 < 2 ^ w := by omega
      have hadjV_k_w : adjVBase + st.regs 16 < 2 ^ w := by omega
      have hadjH_k_w : adjHBase + st.regs 16 < 2 ^ w := by omega
      have hdcur_le : st.mem (workAddr + st.regs 18) ≤ n := le_trans (hdist_le _ h18_n) h15_n
      have hq_push_n : st.mem (workAddr + q_entry.2.2) = 0 →
          0 < st.mem (vMaskAddr + q_entry.2.2) → 0 < st.mem (eMaskAddr + q_entry.1) →
          st.regs 15 < n := by
        intro hd0 _ _
        have hnbr_new : ∀ i < st.regs 15, st.mem (queueBase + i) ≠ q_entry.2.2 := by
          intro i hi heq
          have hnz := (hq_lt i hi).2
          rw [heq] at hnz; exact hnz hd0
        have := card_inj_insert_le (fun i hi => (hq_lt i hi).1) hq_inj hnbr_lt hnbr_new
        omega
      refine runs_triple_le
        (bfs_scan_body_triple st n m vMaskAddr eMaskAddr workAddr parVBase parEBase queueBase
          adjVBase adjHBase (st.regs 18) (st.regs 16) q_entry.2.2
          (2 * q_entry.1 + (if q_entry.2.1 then 1 else 0)) q_entry.1
          (st.mem (workAddr + q_entry.2.2)) (st.mem (vMaskAddr + q_entry.2.2))
          (st.mem (eMaskAddr + q_entry.1)) (st.mem (workAddr + st.regs 18)) (st.regs 15)
          hr3 hr4 hr7 hr9 hr10 hr11 hr12 hr13 rfl rfl rfl hpv hpe hqb
          hadj_v_mem hadj_h_mem hdiv_eq rfl rfl rfl rfl
          h18_n hnbr_lt hedge_lt hdcur_le hq_push_n hadjV_k_w hadjH_k_w hwork_w hvm_w hem_w hk1_w hw4)
        rfl ?_ (by simp only [Expr.size_reg, Expr.size_bin]; omega)
      intro o st' hpost
      cases o with
      | returned _ => exact False.elim hpost
      | normal =>
        rcases hpost with ⟨hpush, hskip⟩
        by_cases hcond_all :
            st.mem (workAddr + q_entry.2.2) = 0 ∧
            0 < st.mem (vMaskAddr + q_entry.2.2) ∧
            0 < st.mem (eMaskAddr + q_entry.1)
        · obtain ⟨hle14, h15', h16', h17_19, hmem'⟩ := hpush hcond_all
          refine bfs_main_push_inv hn hm hval hpv hpe hqb hInv_copy h19_eq1 h14_pos h18_eq h18_n hcur_le
            hk_lt hkEnd_eq rfl hcond_all.1 hu_n hnbr_lt hedge_lt
            (by rw [← heq_vm _ hnbr_lt]; omega)
            (by rw [← heq_em _ hedge_lt]; omega)
            hq_props.2.2.2 ⟨rfl, rfl⟩ hmem'
            hle14 h15' h16'
            (h17_19 17 (by omega) (by omega))
            (h17_19 18 (by omega) (by omega))
            (by rw [h17_19 19 (by omega) (by omega), h19_eq1])
        · obtain ⟨hle15, h16', h17_19, hmem'⟩ := hskip hcond_all
          refine bfs_main_skip_inv hn hval hInv_copy h19_eq1 h14_pos h18_eq h18_n hcur_le hk_lt hkEnd_eq
            hmem' hle15 h16'
            (h17_19 17 (by omega) (by omega))
            (h17_19 18 (by omega) (by omega))
            (by rw [h17_19 19 (by omega) (by omega), h19_eq1])
            (fun hvm_q hem_q => by
              by_contra hd0
              have hvm_nz : 0 < st.mem (vMaskAddr + q_entry.2.2) := by
                rw [heq_vm _ hnbr_lt]; exact Nat.pos_of_ne_zero hvm_q
              have hem_nz : 0 < st.mem (eMaskAddr + q_entry.1) := by
                rw [heq_em _ hedge_lt]; exact Nat.pos_of_ne_zero hem_q
              exact hcond_all ⟨hd0, hvm_nz, hem_nz⟩)
    · -- Branch B/C: k ≥ kEnd
      have hk_ge : st.regs 17 ≤ st.regs 16 := by simpa using hcond
      have hdd_le : bfsDoneDeg G queueBase (st.regs 14) st.mem ≤ csrOff G n := by
        rw [← hn]
        exact bfsDoneDeg_le G queueBase (st.regs 14) st.mem fun i hi =>
          by simpa [hn] using (hq_lt i (by omega)).1
      wram_step
      · -- Branch B: qHead < qTail
        have h14_lt : st.regs 14 < st.regs 15 := by simpa using hcond
        have hq_next_n : st.mem (queueBase + st.regs 14) < n := (hq_lt _ h14_lt).1
        have hpop_addr_w : queueBase + st.regs 14 < 2 ^ w := by linarith only [h14_lt, h15_n, hqb, hwork_w]
        have hq1_w : st.regs 14 + 1 < 2 ^ w := by linarith only [h14_lt, h15_n, hwork_w]
        have hcsr_addr0 : csrAddr + st.mem (queueBase + st.regs 14) < 2 ^ w := by
          linarith only [hq_next_n, hcsr_w]
        have hcsr_addr1 : csrAddr + st.mem (queueBase + st.regs 14) + 1 < 2 ^ w := by
          linarith only [hq_next_n, hcsr_w]
        have hpop_inj : ∀ i < st.regs 14, st.mem (queueBase + i) ≠ st.mem (queueBase + st.regs 14) :=
          fun i hi heq => absurd (hq_inj i (by omega) (st.regs 14) h14_lt heq) (by omega)
        have hoff0 : st.mem (csrAddr + st.mem (queueBase + st.regs 14)) =
            csrOff G (st.mem (queueBase + st.regs 14)) :=
          hcsr_st.1 _ (by rw [hn]; omega)
        have hoff1 : st.mem (csrAddr + st.mem (queueBase + st.regs 14) + 1) =
            csrOff G (st.mem (queueBase + st.regs 14) + 1) := by
          rw [Nat.add_assoc]; exact hcsr_st.1 _ (by rw [hn]; omega)
        refine runs_triple_le
          (bfs_pop_triple st csrAddr queueBase (st.regs 14) (st.mem (queueBase + st.regs 14))
            (csrOff G (st.mem (queueBase + st.regs 14)))
            (csrOff G (st.mem (queueBase + st.regs 14) + 1))
            hr2 hr11 rfl rfl hoff0 hoff1 hpop_addr_w hq1_w hcsr_addr0 hcsr_addr1 h1_w)
          rfl ?_ (by simp only [Expr.size_reg, Expr.size_bin]; omega)
        intro o st' hpost
        cases o with
        | returned _ => exact False.elim hpost
        | normal =>
          rcases hpost with ⟨hle13, h14', h15', h16', h17', h18', h19', hmem'⟩
          refine ⟨⟨by rw [hle13 0 (by omega), hr0], by rw [hle13 1 (by omega), hr1],
              by rw [hle13 2 (by omega), hr2], by rw [hle13 3 (by omega), hr3],
              by rw [hle13 4 (by omega), hr4], by rw [hle13 5 (by omega), hr5],
              by rw [hle13 6 (by omega), hr6], by rw [hle13 7 (by omega), hr7],
              by rw [hle13 8 (by omega), hr8], by rw [hle13 9 (by omega), hr9],
              by rw [hle13 10 (by omega), hr10], by rw [hle13 11 (by omega), hr11],
              by rw [hle13 12 (by omega), hr12], by rw [hle13 13 (by omega), hr13],
              Or.inr (by rw [h19', h19_eq1]), by rw [h14', h15']; omega,
              by rw [h15']; exact h15_n, by rw [h15']; exact h15_pos,
              by rw [hmem']; exact hfr, by rw [hmem', h15']; exact hq_lt,
              by rw [hmem', h15']; exact hq_inj, by rw [hmem', h15']; exact hdist_q,
              by rw [hmem', h15']; exact hdist_le, by rw [hmem']; exact hdu,
              by rw [hmem']; exact hdu_uniq, by rw [hmem']; exact hd_vm,
              by rw [hmem']; exact hpar_inv, ?_, ?_, ?_, fun h => by rw [h19', h19_eq1] at h; omega, ?_⟩, ?_⟩
          · refine Or.inr ⟨by rw [h14']; omega, ?_, ?_, ?_, ?_, ?_⟩
            · rw [h18', hmem', h14']; simp
            · rw [h18']; exact hq_next_n
            · rw [h16', h18']
            · rw [h16', h17']; exact csrOff_mono G (Nat.le_succ _)
            · rw [h17', h18']
          · dsimp only
            intro i hi t ht hvm_q hem_q
            rw [h14'] at hi
            have ht' : t < (csrIncAux (st.mem (queueBase + i)) 0 G.edges).length := by
              rwa [← hmem']
            have hget_eq : (csrIncAux (st'.mem (queueBase + i)) 0 G.edges)[t]'ht =
                (csrIncAux (st.mem (queueBase + i)) 0 G.edges)[t]'ht' := by
              simp only [hmem']
            rw [hget_eq] at hvm_q hem_q ⊢
            rw [hmem']
            by_cases hi_last : i + 1 = st.regs 14
            · rcases hcur_act with ⟨_, _, _, _⟩ | ⟨h14_pos, h18_eq, _, _, _, hkEnd_eq⟩
              · omega
              · have hi_idx : i = st.regs 14 - 1 := by omega
                subst hi_idx
                have ht'' : t < (csrIncAux (st.regs 18) 0 G.edges).length := by
                  rw [← h18_eq] at ht'; exact ht'
                have hget_eq2 : (csrIncAux (st.mem (queueBase + (st.regs 14 - 1))) 0 G.edges)[t]'ht' =
                    (csrIncAux (st.regs 18) 0 G.edges)[t]'ht'' := by
                  simp only [h18_eq]
                rw [hget_eq2] at hvm_q hem_q ⊢
                have hk_in : csrOff G (st.regs 18) + t < st.regs 16 := by
                  have hOff : csrOff G (st.regs 18) + t < csrOff G (st.regs 18 + 1) := by
                    rw [csrOff_succ]; omega
                  omega
                exact hscan_cur h14_pos t ht'' hk_in hvm_q hem_q
            · exact hscan_prev i (by omega) t ht' hvm_q hem_q
          · dsimp only
            intro _ t ht hlt
            rw [h16', h18'] at hlt
            omega
          · exact bfsShortestInv_pop
              (fun h => by
                rcases hcur_act with ⟨_, _, _, _⟩ | ⟨_, h18_eq, _, _, _, hkEnd_eq⟩
                · omega
                · exact ⟨h18_eq, hkEnd_eq⟩)
              hk_ge hmem' h14' h15' (by rw [h16', h18']) hshort
          · unfold bfsMeas
            rw [hmem', h14', h16', h17', h19', h19_eq1]
            have hdd_succ := bfsDoneDeg_succ G queueBase (st.regs 14) st.mem hpop_inj
            have hdd_le' : bfsDoneDeg G queueBase (st.regs 14 + 1) st.mem ≤ csrOff G n := by
              rw [← hn]
              exact bfsDoneDeg_le G queueBase (st.regs 14 + 1) st.mem fun i hi =>
                by simpa [hn] using (hq_lt i (by omega)).1
            have hcur_zero : st.regs 17 - st.regs 16 = 0 := by omega
            have hoff_sub : csrOff G (st.mem (queueBase + st.regs 14) + 1) -
                csrOff G (st.mem (queueBase + st.regs 14)) =
                (csrIncAux (st.mem (queueBase + st.regs 14)) 0 G.edges).length := by
              rw [csrOff_succ]; omega
            have hoff_mono := csrOff_mono G (Nat.le_succ (st.mem (queueBase + st.regs 14)))
            clear hfr hq_lt hq_inj hdist_q hdist_le hdu hdu_uniq hd_vm hpar_inv hcur_act hscan_prev
              hscan_cur hcsr_st heq_csr heq_vm heq_em hfr_init_st hfr_init hcsr hr0 hr1 hr2 hr3 hr4
              hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hr13 hInv_copy hpop_inj hoff0 hoff1
            omega
      · -- Branch C: qHead = qTail
        have h14_eq : st.regs 14 = st.regs 15 := by
          have := (by simpa using hcond : st.regs 15 ≤ st.regs 14); omega
        wram_run
        · refine ⟨⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
              Or.inl (by simp), h14_15, h15_n, h15_pos, hfr, hq_lt, hq_inj, hdist_q, hdist_le,
              hdu, hdu_uniq, hd_vm, hpar_inv, ?_, hscan_prev, hscan_cur,
              fun _ => ⟨h14_eq, hk_ge⟩,
              bfsShortestInv_congr rfl (by simp) (by simp) (by simp) (by simp) hshort⟩, ?_⟩
          · rcases hcur_act with ⟨_, _, _, _⟩ | ⟨h14_pos, h18_eq, h18_n, hcur_le, hk_le, hkEnd_eq⟩
            · omega
            · exact Or.inr ⟨h14_pos, h18_eq, h18_n, hcur_le, hk_le, hkEnd_eq⟩
          · unfold bfsMeas
            simp only [Function.update_of_ne (by decide : (14 : ℕ) ≠ 19),
              Function.update_of_ne (by decide : (16 : ℕ) ≠ 19),
              Function.update_of_ne (by decide : (17 : ℕ) ≠ 19),
              Function.update_self, h19_eq1]
            omega
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega

/-! ## 5. Loop 3: Backtrack Walk Emission -/

private lemma bfs_backtrack_step_triple {w : ℕ} {p : Program} (st0 : State)
    (n workAddr outAddr parVBase parEBase L x idx e_val pv_val : ℕ)
    (h8 : st0.regs 8 = outAddr) (h9 : st0.regs 9 = parVBase) (h10 : st0.regs 10 = parEBase)
    (h20 : st0.regs 20 = L) (h21 : st0.regs 21 = x) (h22 : st0.regs 22 = idx)
    (hpv : parVBase = workAddr + n) (hpe : parEBase = workAddr + 2 * n)
    (hdj_wo : workAddr + 4 * n ≤ outAddr ∨ outAddr + 2 * n + 2 ≤ workAddr)
    (hx_n : x < n) (hL_le : L ≤ n) (hidx_pos : 0 < idx) (hidx_lt : idx < L)
    (hparE_eq : st0.mem (parEBase + x) = e_val)
    (hparV_eq : st0.mem (parVBase + x) = pv_val)
    (hout_w : outAddr + 2 * n + 2 < 2 ^ w) (hwork_w : workAddr + 4 * n < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st0)
      (seqStmts [
        .store (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 22)) (.reg 21),
        .assign 23 (.load (.bin .add (.reg 10) (.reg 21))),
        .store (.bin .add (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 20))
          (.bin .sub (.reg 22) (.const 1))) (.reg 23),
        .assign 21 (.load (.bin .add (.reg 9) (.reg 21))),
        .assign 22 (.bin .sub (.reg 22) (.const 1))])
      (normalPost fun st' =>
        (∀ r ≤ 20, st'.regs r = st0.regs r) ∧
        st'.regs 21 = pv_val ∧ st'.regs 22 = idx - 1 ∧
        st'.mem = Function.update (Function.update st0.mem (outAddr + 1 + idx) x)
          (outAddr + 2 + L + (idx - 1)) e_val)
      (fun _ => 45) := by
  intro st ω hpre; subst hpre; refine runs_start_le ?_
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h8_1_w : outAddr + 1 < 2 ^ w := by omega
  have h8_1_idx_w : outAddr + 1 + idx < 2 ^ w := by omega
  have h8_2_w : outAddr + 2 < 2 ^ w := by omega
  have h8_2_L_w : outAddr + 2 + L < 2 ^ w := by omega
  have hidx1_w : idx - 1 < 2 ^ w := by omega
  have h8_e_w : outAddr + 2 + L + (idx - 1) < 2 ^ w := by omega
  have hpe_x_w : parEBase + x < 2 ^ w := by omega
  have hpv_x_w : parVBase + x < 2 ^ w := by omega
  have hne_E : parEBase + x ≠ outAddr + 1 + idx := by
    rcases hdj_wo with h | h <;> omega
  have hne_V1 : parVBase + x ≠ outAddr + 1 + idx := by
    rcases hdj_wo with h | h <;> omega
  have hne_V2 : parVBase + x ≠ outAddr + 2 + L + (idx - 1) := by
    rcases hdj_wo with h | h <;> omega
  have ha1 : (Expr.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 22)).eval w st =
      some (outAddr + 1 + idx) := by
    simp [Expr.eval, BinOp.eval, h8, h22, h1_w, h8_1_w, h8_1_idx_w]
  have hv1 : (Expr.reg 21).eval w st = some x := by simp [Expr.eval, h21]
  refine runs_seq_store_le ha1 hv1 ?_
  have he2 : (Expr.load (.bin .add (.reg 10) (.reg 21))).eval w
      ({ mem := Function.update st.mem (outAddr + 1 + idx) x,
         regs := st.regs, pos := st.pos } : State) = some e_val := by
    simp [Expr.eval, BinOp.eval, h10, h21, hpe_x_w, Function.update_of_ne hne_E, hparE_eq]
  refine runs_seq_assign_le he2 ?_
  have ha3 : (Expr.bin .add (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 20))
      (.bin .sub (.reg 22) (.const 1))).eval w
      ({ mem := Function.update st.mem (outAddr + 1 + idx) x,
         regs := Function.update st.regs 23 e_val, pos := st.pos } : State) =
      some (outAddr + 2 + L + (idx - 1)) := by
    simp [Expr.eval, BinOp.eval, h8, h20, h22, h2_w, h1_w, h8_2_w, h8_2_L_w, hidx1_w, h8_e_w]
  have hv3 : (Expr.reg 23).eval w
      ({ mem := Function.update st.mem (outAddr + 1 + idx) x,
         regs := Function.update st.regs 23 e_val, pos := st.pos } : State) = some e_val := by
    simp [Expr.eval, Function.update_self]
  refine runs_seq_store_le ha3 hv3 ?_
  have he4 : (Expr.load (.bin .add (.reg 9) (.reg 21))).eval w
      ({ mem := Function.update (Function.update st.mem (outAddr + 1 + idx) x)
          (outAddr + 2 + L + (idx - 1)) e_val,
         regs := Function.update st.regs 23 e_val, pos := st.pos } : State) = some pv_val := by
    simp [Expr.eval, BinOp.eval, h9, h21, hpv_x_w,
      Function.update_of_ne hne_V2, Function.update_of_ne hne_V1, hparV_eq]
  refine runs_seq_assign_le he4 ?_
  have he5 : (Expr.bin .sub (.reg 22) (.const 1)).eval w
      ({ mem := Function.update (Function.update st.mem (outAddr + 1 + idx) x)
          (outAddr + 2 + L + (idx - 1)) e_val,
         regs := Function.update (Function.update st.regs 23 e_val) 21 pv_val,
         pos := st.pos } : State) = some (idx - 1) := by
    simp [Expr.eval, BinOp.eval, h22, h1_w, hidx1_w]
  refine runs_assign_le he5 ?_ ?_
  · dsimp only [normalPost]
    refine ⟨fun r hr => by
      simp [Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 21),
        Function.update_of_ne (by omega : r ≠ 23)],
      by simp, by simp, rfl⟩
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma bfs_backtrack_loop {w : ℕ} {p : Program}
    (n workAddr outAddr parVBase parEBase u v L : ℕ)
    (memMain : ℕ → ℕ)
    (hpv : parVBase = workAddr + n) (hpe : parEBase = workAddr + 2 * n)
    (hdj_wo : workAddr + 4 * n ≤ outAddr ∨ outAddr + 2 * n + 2 ≤ workAddr)
    (hout_w : outAddr + 2 * n + 2 < 2 ^ w) (hwork_w : workAddr + 4 * n < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hL_ge : 2 ≤ L) (hL_le : L ≤ n)
    (hpar_bounds : ∀ y < n, 2 ≤ memMain (workAddr + y) →
      memMain (workAddr + memMain (parVBase + y)) + 1 = memMain (workAddr + y) ∧
      memMain (parVBase + y) < n) :
    let parV : ℕ → ℕ := fun y => memMain (parVBase + y)
    let parE : ℕ → ℕ := fun y => memMain (parEBase + y)
    let InvBack : State → Prop := fun st =>
      st.regs 8 = outAddr ∧ st.regs 9 = parVBase ∧ st.regs 10 = parEBase ∧
      st.regs 20 = L ∧ st.regs 22 ≤ L - 1 ∧
      MemFrame memMain st.mem outAddr (outAddr + 2 * n + 2) ∧
      st.mem outAddr = L ∧
      st.mem (outAddr + 1 + L) = L - 1 ∧
      st.mem (outAddr + 1) = u ∧
      (bfsWalkVerts parV (L - 1) v)[st.regs 22]? = some (st.regs 21) ∧
      st.regs 21 < n ∧ memMain (workAddr + st.regs 21) = st.regs 22 + 1 ∧
      (∀ j, st.regs 22 < j → ∀ (hj : j < L),
        st.mem (outAddr + 1 + j) = (bfsWalkVerts parV (L - 1) v)[j]'(by rw [bfsWalkVerts_length]; omega)) ∧
      (∀ j, st.regs 22 ≤ j → ∀ (hj : j < L - 1),
        st.mem (outAddr + 2 + L + j) = (bfsWalkEdges parV parE (L - 1) v)[j]'(by rw [bfsWalkEdges_length]; omega))
    Triple w p InvBack
      (.loop (.bin .lt (.const 0) (.reg 22))
        (seqStmts [
          .store (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 22)) (.reg 21),
          .assign 23 (.load (.bin .add (.reg 10) (.reg 21))),
          .store (.bin .add (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 20))
            (.bin .sub (.reg 22) (.const 1))) (.reg 23),
          .assign 21 (.load (.bin .add (.reg 9) (.reg 21))),
          .assign 22 (.bin .sub (.reg 22) (.const 1))]))
      (normalPost fun st' => InvBack st' ∧ st'.regs 22 = 0)
      (fun st => (3 + 45 + 1) * st.regs 22 + 3 + 1) := by
  intro parV parE InvBack
  refine Triple.loop_const_normal (fun st => st.regs 22)
    (fun st => if 0 < st.regs 22 then 1 else 0) 45
    (fun st hInv => by rcases hInv with ⟨_, _, _, _, h22, _⟩; eval_expr)
    (fun st hInv h0 => by
      simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0
      exact ⟨hInv, by omega⟩)
    (fun st hInv hne => ?_)
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
  rcases hInv with ⟨hr8, hr9, hr10, hr20, h22_le, hfr, ho0, hoL, hou, hwalk_at?, hx_n, hx_d, hv_suff, he_suff⟩
  have hwalk_len : st.regs 22 < (bfsWalkVerts parV (L - 1) v).length := by
    rw [bfsWalkVerts_length]; omega
  have hwalk_at : (bfsWalkVerts parV (L - 1) v)[st.regs 22]'hwalk_len = st.regs 21 := by
    have := hwalk_at?
    rw [List.getElem?_eq_getElem hwalk_len] at this
    exact Option.some.inj this
  have hx_ge2 : 2 ≤ memMain (workAddr + st.regs 21) := by omega
  have heq_work : ∀ addr, workAddr ≤ addr → addr < workAddr + 4 * n → st.mem addr = memMain addr :=
    fun addr ha hb => hfr addr (by rcases hdj_wo with h | h <;> [left; right] <;> omega)
  have hpv_eq : st.mem (parVBase + st.regs 21) = parV (st.regs 21) :=
    heq_work (parVBase + st.regs 21) (by omega) (by omega)
  have hpe_eq : st.mem (parEBase + st.regs 21) = parE (st.regs 21) :=
    heq_work (parEBase + st.regs 21) (by omega) (by omega)
  have hpb := hpar_bounds _ hx_n hx_ge2
  have hpv_lt_n : parV (st.regs 21) < n := hpb.2
  have hstep_walk := bfsWalk_step_eq parV parE (L - 1) v (st.regs 22 - 1) (by omega) (st.regs 21)
    (by
      have hidx1 : st.regs 22 - 1 + 1 = st.regs 22 := by omega
      have htmp := hwalk_at
      simpa [hidx1] using htmp)
  refine (bfs_backtrack_step_triple (w := w) (p := p) st n workAddr outAddr parVBase parEBase L
      (st.regs 21) (st.regs 22) (parE (st.regs 21)) (parV (st.regs 21))
      hr8 hr9 hr10 hr20 rfl rfl hpv hpe hdj_wo hx_n hL_le hne (by omega)
      hpe_eq hpv_eq hout_w hwork_w hw4).conseq
    (fun _ h => h) ?_ (fun _ _ => Nat.le_refl _)
  intro o st' hpost
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hr_le20', h21', h22', hmem'⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [hr_le20' 8 (by omega)] using hr8
    · simpa [hr_le20' 9 (by omega)] using hr9
    · simpa [hr_le20' 10 (by omega)] using hr10
    · simpa [hr_le20' 20 (by omega)] using hr20
    · omega
    · rw [hmem']
      refine memFrame_trans (memFrame_trans hfr (memFrame_update (by omega) (by omega)))
        (memFrame_update (by omega) (by omega))
    · rw [hmem', Function.update_of_ne (by omega), Function.update_of_ne (by omega), ho0]
    · rw [hmem', Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoL]
    · rw [hmem', Function.update_of_ne (by omega), Function.update_of_ne (by omega), hou]
    · rw [h22', h21', List.getElem?_eq_getElem (by rw [bfsWalkVerts_length]; omega)]
      exact congrArg some hstep_walk.1
    · rw [h21']; exact hpv_lt_n
    · rw [h21', h22']; dsimp only [parV]; have := hpb.1; omega
    · intro j hj1 hj2
      rw [h22'] at hj1
      rw [hmem', Function.update_of_ne (by omega)]
      by_cases hjj : j = st.regs 22
      · subst hjj; rw [Function.update_self]; exact hwalk_at.symm
      · rw [Function.update_of_ne (by omega)]; exact hv_suff j (by omega) hj2
    · intro j hj1 hj2
      rw [h22'] at hj1
      rw [hmem']
      by_cases hjj : j = st.regs 22 - 1
      · subst hjj; rw [Function.update_self]; exact hstep_walk.2.symm
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact he_suff j (by omega) hj2
    · rw [h22']; omega

/-! ## 6. CSR Congruence Helpers and `bfsPath_spec` -/

private lemma mem_csrIncAux_edgeMatches {x r idx : ℕ} {dir : Bool} {y : ℕ} {L : List (ℕ × ℕ)}
    (hmem : (idx, dir, y) ∈ csrIncAux x r L) :
    r ≤ idx ∧ idx - r < L.length ∧ x ≠ y ∧ Walk.EdgeMatches (L.getD (idx - r) (0, 0)) x y := by
  induction L generalizing r with
  | nil => simp [csrIncAux] at hmem
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    simp only [csrIncAux] at hmem
    split_ifs at hmem with hab hau hbu
    · obtain ⟨hr, hlen, hne, hm⟩ := ih hmem
      refine ⟨by omega, by simp; omega, hne, ?_⟩
      have hpos : 0 < idx - r := by omega
      have hsub : idx - r = (idx - (r + 1)) + 1 := by omega
      rw [hsub]
      simpa using hm
    · simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, -, rfl⟩ | htail
      · subst hau
        refine ⟨le_rfl, by simp, hab, ?_⟩
        simp [Walk.EdgeMatches]
      · obtain ⟨hr, hlen, hne, hm⟩ := ih htail
        refine ⟨by omega, by simp; omega, hne, ?_⟩
        have hpos : 0 < idx - r := by omega
        have hsub : idx - r = (idx - (r + 1)) + 1 := by omega
        rw [hsub]
        simpa using hm
    · simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, -, rfl⟩ | htail
      · subst hbu
        refine ⟨le_rfl, by simp, fun h => hab h.symm, ?_⟩
        simp [Walk.EdgeMatches]
      · obtain ⟨hr, hlen, hne, hm⟩ := ih htail
        refine ⟨by omega, by simp; omega, hne, ?_⟩
        have hpos : 0 < idx - r := by omega
        have hsub : idx - r = (idx - (r + 1)) + 1 := by omega
        rw [hsub]
        simpa using hm
    · obtain ⟨hr, hlen, hne, hm⟩ := ih hmem
      refine ⟨by omega, by simp; omega, hne, ?_⟩
      have hpos : 0 < idx - r := by omega
      have hsub : idx - r = (idx - (r + 1)) + 1 := by omega
      rw [hsub]
      simpa using hm

private lemma csrIncAux_eq_of_hasCsrAt {mem : ℕ → ℕ} {csrAddr : ℕ} {G1 G2 : Cited.Graph}
    (h1 : HasCsrAt mem csrAddr G1) (h2 : HasCsrAt mem csrAddr G2)
    (hn : G1.n = G2.n) (hm : G1.m = G2.m) {u : ℕ} (hu : u < G1.n) :
    csrIncAux u 0 G1.edges = csrIncAux u 0 G2.edges := by
  have hu2 : u < G2.n := hn ▸ hu
  have hoff12 : csrOff G1 u = csrOff G2 u := by
    rw [← h1.1 u (Nat.le_of_lt hu), h2.1 u (Nat.le_of_lt hu2)]
  have hoff12_s : csrOff G1 (u + 1) = csrOff G2 (u + 1) := by
    rw [← h1.1 (u + 1) hu, h2.1 (u + 1) hu2]
  have hlen : (csrIncAux u 0 G1.edges).length = (csrIncAux u 0 G2.edges).length := by
    have hs1 := csrOff_succ G1 u
    have hs2 := csrOff_succ G2 u
    omega
  refine List.ext_getElem hlen fun j hj1 hj2 => ?_
  have hc1 := h1.2 u hu j hj1
  have hc2 := h2.2 u hu2 j hj2
  rcases q1 : (csrIncAux u 0 G1.edges)[j]'hj1 with ⟨e1, d1, v1⟩
  rcases q2 : (csrIncAux u 0 G2.edges)[j]'hj2 with ⟨e2, d2, v2⟩
  rw [q1] at hc1
  rw [q2] at hc2
  dsimp only at hc1 hc2
  have hv_eq : v1 = v2 := by
    rw [← hc1.1, hn, hoff12, hc2.1]
  have he_eq : 2 * e1 + (if d1 then 1 else 0) = 2 * e2 + (if d2 then 1 else 0) := by
    rw [← hc1.2, hn, hm, hoff12, hc2.2]
  have he12 : e1 = e2 := by
    cases d1 <;> cases d2 <;> simp at he_eq <;> omega
  have hd12 : d1 = d2 := by
    cases d1 <;> cases d2 <;> simp at he_eq <;> first | rfl | omega
  simp [he12, hd12, hv_eq]

private lemma bfsPath_preserves_frame {n workAddr outAddr : ℕ} {mem mem1 mem2 : ℕ → ℕ}
    (h1 : MemFrame mem mem1 workAddr (workAddr + 4 * n))
    (h2 : MemFrame mem1 mem2 outAddr (outAddr + 2 * n + 2)) :
    PreservedOutside2 mem mem2 workAddr (workAddr + 4 * n) outAddr (outAddr + 2 * n + 2) :=
  memFrame_to_preservedOutside2 h1 h2

/-- Specification proof for `bfsPathProc`: meets `bfsShortestPathContract w`, so the returned
walk has the fewest edges among the kept walks from `u` to `v`. -/
theorem bfsShortestPath_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [bfsPathProc]) :
    MeetsContract w p b (bfsShortestPathContract w) := by
  intro args mem pos ω hwords hpre
  dsimp only [bfsShortestPathContract, bfsPathContract] at hpre
  rcases hpre with ⟨n, m, csrAddr, vMaskAddr, eMaskAddr, u, v, workAddr, outAddr, G0,
    rfl, hG0n, hG0m, hG0val, hG0csr, hu_n, hv_n, hvm_u, hvm_v,
    hdj_wo, hdj_cw, hdj_co, hdj_vw, hdj_vo, hdj_ew, hdj_eo,
    hcsr_w, hvm_w, hem_w, hwork_w, hout_w, hw4⟩
  have hproc : p.procs[b]? = some bfsPathProc := hp 0 (by simp)
  have hlt_n : n < 2 ^ w := hwords n (by simp)
  have hlt_m : m < 2 ^ w := hwords m (by simp)
  have hlt_c : csrAddr < 2 ^ w := hwords csrAddr (by simp)
  have hlt_vm : vMaskAddr < 2 ^ w := hwords vMaskAddr (by simp)
  have hlt_em : eMaskAddr < 2 ^ w := hwords eMaskAddr (by simp)
  have hlt_u : u < 2 ^ w := hwords u (by simp)
  have hlt_v : v < 2 ^ w := hwords v (by simp)
  have hlt_work : workAddr < 2 ^ w := hwords workAddr (by simp)
  have hlt_out : outAddr < 2 ^ w := hwords outAddr (by simp)
  have htriple :
      Triple w p
        (fun st => st = startState [n, m, csrAddr, vMaskAddr, eMaskAddr, u, v, workAddr, outAddr] mem pos)
        bfsPathProc
        (fun o st' => ∃ res : ℕ, o = .returned res ∧
          (bfsShortestPathContract w).post [n, m, csrAddr, vMaskAddr, eMaskAddr, u, v, workAddr, outAddr]
            mem res st'.mem)
        (fun _ => 350 * (n + m + 1)) := by
    wram_enter
    · subst hpre
      dsimp only [bfsPathProc]
      wram_step
      · -- Case u = v
        have huv : u = v := by simpa using hcond
        have hout0_w : outAddr < 2 ^ w := by omega
        have hout1_w : outAddr + 1 < 2 ^ w := by omega
        wram_run
        · refine ⟨1, rfl, ⟨Or.inr rfl, ?_, fun G hGn hGm hGval hGcsr => ⟨fun _ => ?_, fun h0 => by omega⟩⟩,
            fun G hGn hGm hGval hGcsr _ => ?_⟩
          · simp only [List.getD_cons_zero, List.getD_cons_succ, startState]
            intro a _ ha2
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          · simp only [List.getD_cons_zero, List.getD_cons_succ, startState] at hGn ⊢
            refine ⟨Walk.empty, walkAt_empty_of_cells ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [Function.update_of_ne (by omega), Function.update_self]
            · rw [Function.update_self]
            · subst huv; simp [Walk.IsWalk, Walk.empty, hGn ▸ hu_n]
            · simp [Walk.empty]
            · intro e he; simp [Walk.empty] at he
            · intro x hx; simp [Walk.empty] at hx
            · simp [Walk.empty]; omega
          · simp only [List.getD_cons_zero, List.getD_cons_succ, startState] at hGn ⊢
            refine ⟨Walk.empty, walkAt_empty_of_cells ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [Function.update_of_ne (by omega), Function.update_self]
            · rw [Function.update_self]
            · subst huv; simp [Walk.IsWalk, Walk.empty, hGn ▸ hu_n]
            · simp [Walk.empty]
            · intro e he; simp [Walk.empty] at he
            · intro x hx; simp [Walk.empty] at hx
            · simp [Walk.empty]; omega
            · intro W _ _ _; simp [Walk.empty]
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega
      · -- Case u ≠ v
        have huv : u ≠ v := by simpa using hcond
        have h1_w : 1 < 2 ^ w := by omega
        have h2_w : 2 < 2 ^ w := by omega
        obtain ⟨parVBase, hpv⟩ : ∃ x, x = workAddr + n := ⟨_, rfl⟩
        obtain ⟨parEBase, hpe⟩ : ∃ x, x = workAddr + 2 * n := ⟨_, rfl⟩
        obtain ⟨queueBase, hqb⟩ : ∃ x, x = workAddr + 3 * n := ⟨_, rfl⟩
        obtain ⟨adjVBase, hav⟩ : ∃ x, x = csrAddr + 2 * n + 1 := ⟨_, rfl⟩
        obtain ⟨adjHBase, hah⟩ : ∃ x, x = adjVBase + 2 * m := ⟨_, rfl⟩
        have hparV_w : parVBase < 2 ^ w := by omega
        have hparE_w : parEBase < 2 ^ w := by omega
        have hqb_w : queueBase < 2 ^ w := by omega
        have hadjV_w : adjVBase < 2 ^ w := by omega
        have hadjH_w : adjHBase < 2 ^ w := by omega
        have h2n_w : 2 * n < 2 ^ w := by omega
        have h2m_w : 2 * m < 2 ^ w := by omega
        have hc2n_w : csrAddr + 2 * n < 2 ^ w := by omega
        wram_step
        wram_step
        wram_step
        wram_step
        wram_step
        wram_step
        have hl1 := bfs_zero_loop (p := p) n m csrAddr vMaskAddr eMaskAddr u v
          workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase mem hwork_w hw4
        refine runs_seq_triple_le hl1 ?_ (fun st1 hst1 => ?_)
        · simp only [startState, Function.update_apply,
            Nat.reduceEqDiff, ite_false, ite_true]
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hpv.symm, ?_, ?_, hav.symm, ?_,
            Nat.zero_le _, memFrame_refl _ _ _, fun _ hi => by simp at hi⟩
          · rw [hpe]; omega
          · rw [hqb]; omega
          · rw [hah, hav]
        · rcases hst1 with ⟨⟨hs1_0, hs1_1, hs1_2, hs1_3, hs1_4, hs1_5, hs1_6, hs1_7, hs1_8,
              hs1_9, hs1_10, hs1_11, hs1_12, hs1_13, _, hfr1, hz1⟩, hs1_14⟩
          clear hl1
          have hz1_all : ∀ i < n, st1.mem (workAddr + i) = 0 := fun i hi => hz1 i (hs1_14 ▸ hi)
          have hwu_w : workAddr + u < 2 ^ w := by linarith only [hu_n, hwork_w]
          wram_step
          wram_step
          wram_step
          wram_step
          wram_step
          wram_step
          wram_step
          wram_step
          obtain ⟨memBase, hmBase⟩ : ∃ f : ℕ → ℕ,
              f = Function.update (Function.update st1.mem (workAddr + u) 1) queueBase u := ⟨_, rfl⟩
          have hfr_base : MemFrame mem memBase workAddr (workAddr + 4 * n) := by
            rw [hmBase]
            have h1_4n : MemFrame mem st1.mem workAddr (workAddr + 4 * n) :=
              memFrame_mono hfr1 le_rfl (by omega)
            exact memFrame_trans (memFrame_trans h1_4n (memFrame_update (by omega) (by omega)))
              (memFrame_update (by omega) (by omega))
          have hq0_eq : memBase (queueBase + 0) = u := by
            simp [hmBase, Function.update_self]
          have hwu_eq : memBase (workAddr + u) = 1 := by
            have hne_uq : workAddr + u ≠ queueBase := by linarith only [hqb, hu_n]
            simp [hmBase, Function.update_of_ne hne_uq, Function.update_self]
          have hwx_eq : ∀ x < n, x ≠ u → memBase (workAddr + x) = 0 := by
            intro x hx hxu
            have hne1 : workAddr + x ≠ queueBase := by linarith only [hqb, hx]
            have hne2 : workAddr + x ≠ workAddr + u := by omega
            simp only [hmBase, Function.update_of_ne hne1, Function.update_of_ne hne2]
            exact hz1_all x hx
          have hdd0 : ∀ f, bfsDoneDeg G0 queueBase 0 f = 0 := fun f => by
            simp [bfsDoneDeg, bfsPoppedSet]
          have hcsr_le : csrOff G0 n ≤ 2 * m := by
            simpa [hG0n, hG0m] using csrOff_le_two_mul_m G0 G0.n
          have hl2 := bfs_main_loop (p := p) n m csrAddr vMaskAddr eMaskAddr u v
            workAddr outAddr parVBase parEBase queueBase adjVBase adjHBase G0 mem memBase
            hG0n hG0m hG0val hu_n hG0csr hfr_base hdj_cw hdj_vw hdj_ew
            hcsr_w hvm_w hem_w hwork_w hw4 hpv hpe hqb hav hah
          refine runs_seq_triple_le hl2 ?_ (fun st2 hst2 => ?_)
          · dsimp only [BfsMainInv]
            simp only [← hmBase]
            refine ⟨by simp [hs1_0], by simp [hs1_1], by simp [hs1_2], by simp [hs1_3],
              by simp [hs1_4], by simp [hs1_5], by simp [hs1_6], by simp [hs1_7],
              by simp [hs1_8], by simp [hs1_9], by simp [hs1_10], by simp [hs1_11],
              by simp [hs1_12], by simp [hs1_13], Or.inr (by simp), by simp,
              by simp; omega, by simp, memFrame_refl memBase workAddr (workAddr + 4 * n),
              ?_, ?_, ?_, ?_, hwu_eq, ?_, ?_, ?_,
              Or.inl ⟨by simp, by simp, by simp, by simp⟩,
              fun i hi => by simp at hi, fun h14 => by simp at h14, fun h19 => by simp at h19, ?_⟩
            · intro i hi
              have hi0 : i = 0 := by simp at hi; omega
              subst hi0
              rw [hq0_eq, hwu_eq]
              exact ⟨hu_n, Nat.one_ne_zero⟩
            · intro i hi j hj _
              simp at hi hj; omega
            · intro x hx hnz
              by_cases hxu : x = u
              · subst hxu; exact ⟨0, by simp, hq0_eq⟩
              · exfalso; exact hnz (hwx_eq x hx hxu)
            · intro x hx
              by_cases hxu : x = u
              · subst hxu; rw [hwu_eq]; simp
              · rw [hwx_eq x hx hxu]; exact Nat.zero_le _
            · intro x hx hx1
              by_contra hxu
              have h0 := hwx_eq x hx hxu
              omega
            · intro x hx hnz
              by_cases hxu : x = u
              · subst hxu; exact hvm_u
              · exfalso; exact hnz (hwx_eq x hx hxu)
            · intro x hx hx2
              by_cases hxu : x = u
              · subst hxu; omega
              · have := hwx_eq x hx hxu; omega
            · refine bfsShortestInv_init (u := u) (by simp) (by simp) (fun x hx => ?_)
              by_cases hxu : x = u
              · subst hxu; simp [hwu_eq]
              · simp [hxu, hwx_eq x hx hxu]
          · rcases hst2 with ⟨⟨hs2_0, hs2_1, hs2_2, hs2_3, hs2_4, hs2_5, hs2_6, hs2_7, hs2_8,
                hs2_9, hs2_10, hs2_11, hs2_12, hs2_13, _, h14_15, h15_n, h15_pos, hfr2,
                hq_lt, hq_inj, hdist_q, hdist_le, hdu, hdu_uniq, hd_vm, hpar_inv,
                hcur_act, hscan_prev, hscan_cur, hdone, hshort⟩, h19_0⟩
            clear hl2
            have hfr_mem2 : MemFrame mem st2.mem workAddr (workAddr + 4 * n) :=
              memFrame_trans hfr_base hfr2
            have hwv_w : workAddr + v < 2 ^ w := by linarith only [hv_n, hwork_w]
            wram_step
            wram_step
            · -- L = 0 -> res = 0
              have hL0 : st2.mem (workAddr + v) = 0 := by
                simpa [hs2_7, hs2_6] using hcond
              wram_run
              · refine ⟨0, rfl, ⟨Or.inl rfl, ?_, fun G hGn hGm hGval hGcsr => ⟨fun h1 => by omega, fun _ => ?_⟩⟩,
                  fun _ _ _ _ _ h1 => absurd h1 (by decide)⟩
                · simp only [List.getD_cons_zero, List.getD_cons_succ]
                  intro a ha _
                  exact hfr_mem2 a ha
                · simp only [List.getD_cons_zero, List.getD_cons_succ] at hGn hGm hGcsr
                  let S : Finset ℕ := (Finset.range (st2.regs 15)).image fun i => st2.mem (queueBase + i)
                  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
                  · obtain ⟨i, hi, hiq⟩ := hdist_q u hu_n (by omega)
                    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hiq⟩
                  · intro hvS
                    rcases Finset.mem_image.mp hvS with ⟨i, hi, hiq⟩
                    have := (hq_lt i (Finset.mem_range.mp hi)).2
                    rw [hiq] at this
                    exact this hL0
                  · intro x hxS
                    rcases Finset.mem_image.mp hxS with ⟨i, hi, rfl⟩
                    exact Finset.mem_range.mpr (hq_lt i (Finset.mem_range.mp hi)).1
                  · intro x hxS
                    rcases Finset.mem_image.mp hxS with ⟨i, hi, rfl⟩
                    have hqi := hq_lt i (Finset.mem_range.mp hi)
                    exact hd_vm _ hqi.1 hqi.2
                  · intro j hj hem x hxS y hed hy_n hym
                    by_cases hyx : y = x
                    · subst hyx; exact hxS
                    · rcases Finset.mem_image.mp hxS with ⟨i, hi, rfl⟩
                      have hi_lt : i < st2.regs 15 := Finset.mem_range.mp hi
                      have hqi := hq_lt i hi_lt
                      have hdone' := hdone h19_0
                      have hinc_mem :
                          (j, false, y) ∈ csrIncAux (st2.mem (queueBase + i)) 0 G0.edges ∨
                          (j, true, y) ∈ csrIncAux (st2.mem (queueBase + i)) 0 G0.edges := by
                        have hxG : st2.mem (queueBase + i) < G.n := by linarith only [hqi.1, hGn]
                        have hcsr_eq := csrIncAux_eq_of_hasCsrAt hGcsr hG0csr
                          (by linarith only [hGn, hG0n]) (by linarith only [hGm, hG0m]) hxG
                        have hInG := edge_mem_csrIncAux_of_ne (L := G.edges)
                          (k := j) (r := 0) (by rw [← Cited.Graph.m, hGm]; exact hj)
                          (Ne.symm hyx) hed
                        simpa [hcsr_eq] using hInG
                      obtain ⟨dir, hdir⟩ : ∃ dir : Bool,
                          (j, dir, y) ∈ csrIncAux (st2.mem (queueBase + i)) 0 G0.edges := by
                        rcases hinc_mem with h | h <;> exact ⟨_, h⟩
                      rcases List.mem_iff_getElem.mp hdir with ⟨t, ht, hqt⟩
                      have hy_nz : st2.mem (workAddr + y) ≠ 0 := by
                        by_cases hi_last : i + 1 < st2.regs 14
                        · have hs := hscan_prev i hi_last t ht
                          rw [hqt] at hs
                          exact hs hym hem
                        · have hi_succ : i + 1 = st2.regs 14 := by linarith only [hi_last, hi_lt, hdone'.1]
                          have hi_eq : i = st2.regs 14 - 1 := Nat.eq_sub_of_add_eq hi_succ
                          have h14_pos : 0 < st2.regs 14 := by linarith only [hi_lt, hdone'.1]
                          rcases hcur_act with ⟨_, _, h14_0, _⟩ | ⟨_, h18_eq, _, _, _, hkEnd⟩
                          · linarith only [h14_pos, h14_0]
                          · have hx18 : st2.mem (queueBase + i) = st2.regs 18 := by
                              rw [hi_eq, h18_eq]
                            have ht' : t < (csrIncAux (st2.regs 18) 0 G0.edges).length := by
                              rw [hx18] at ht; exact ht
                            have hget_eq : (csrIncAux (st2.mem (queueBase + i)) 0 G0.edges)[t]'ht =
                                (csrIncAux (st2.regs 18) 0 G0.edges)[t]'ht' := by simp only [hx18]
                            rw [hget_eq] at hqt
                            have hk_t : csrOff G0 (st2.regs 18) + t < st2.regs 16 := by
                              have h1 : csrOff G0 (st2.regs 18) + t < csrOff G0 (st2.regs 18 + 1) := by
                                rw [csrOff_succ]; exact Nat.add_lt_add_left ht' _
                              linarith only [h1, hkEnd, hdone'.2]
                            have hs := hscan_cur h14_pos t ht' hk_t
                            rw [hqt] at hs
                            exact hs hym hem
                      obtain ⟨i', hi', hiq'⟩ := hdist_q y hy_n hy_nz
                      exact Finset.mem_image.mpr ⟨i', Finset.mem_range.mpr hi', hiq'⟩
              · clear hfr_base hfr2 hq_lt hq_inj hdist_q hdist_le hdu hdu_uniq hd_vm hpar_inv
                  hcur_act hscan_prev hscan_cur hdone hfr1 hmBase hq0_eq hwu_eq hwx_eq
                simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin,
                  bfsMeas, Function.update_apply, Nat.reduceEqDiff, ite_false, ite_true, Nat.sub_zero]
                rw [hdd0]
                simp only [Nat.sub_zero]
                linarith only [hcsr_le]
            · -- L ≠ 0 -> backtrack & res = 1
              obtain ⟨L, hL_def⟩ : ∃ vL, vL = st2.mem (workAddr + v) := ⟨_, rfl⟩
              have hL_nz : L ≠ 0 := by
                simpa [hs2_7, hs2_6, hL_def] using hcond
              have hL_le : L ≤ n := by
                have := hdist_le v hv_n
                linarith only [this, h15_n, hL_def]
              have hL_ge : 2 ≤ L := by
                by_contra hlt
                have hLpos := Nat.pos_of_ne_zero hL_nz
                have hL1 : L = 1 := by linarith only [hlt, hLpos]
                exact huv (hdu_uniq v hv_n (by linarith only [hL1, hL_def])).symm
              have hLm1_add : L - 1 + 1 = L := Nat.sub_add_cancel (by linarith only [hL_ge])
              have hL_w : L < 2 ^ w := by linarith only [hL_le, hout_w]
              have hLm1_w : L - 1 < 2 ^ w := lt_of_le_of_lt (Nat.sub_le L 1) hL_w
              have houtL_w : outAddr + 1 + L < 2 ^ w := by linarith only [hL_le, hout_w]
              have hout0_w : outAddr < 2 ^ w := by linarith only [hout_w]
              have hout1_w : outAddr + 1 < 2 ^ w := by linarith only [hout_w]
              wram_step
              wram_step
              wram_step
              wram_step
              wram_step
              obtain ⟨parV, hparV_def⟩ : ∃ f : ℕ → ℕ, f = fun y => st2.mem (parVBase + y) := ⟨_, rfl⟩
              obtain ⟨parE, hparE_def⟩ : ∃ f : ℕ → ℕ, f = fun y => st2.mem (parEBase + y) := ⟨_, rfl⟩
              have hpar_bounds : ∀ y < n, 2 ≤ st2.mem (workAddr + y) →
                  st2.mem (workAddr + st2.mem (parVBase + y)) + 1 = st2.mem (workAddr + y) ∧
                  st2.mem (parVBase + y) < n := by
                intro y hy hy2
                have hp_ := hpar_inv y hy hy2
                exact ⟨hp_.1, hp_.2.1⟩
              have hmf_init : MemFrame st2.mem
                  (Function.update (Function.update (Function.update st2.mem outAddr L)
                    (outAddr + 1 + L) (L - 1)) (outAddr + 1) u)
                  outAddr (outAddr + 2 * n + 2) :=
                memFrame_trans
                  (memFrame_trans
                    (memFrame_update le_rfl (by linarith only [hL_le, hL_ge]))
                    (memFrame_update (by linarith only []) (by linarith only [hL_le])))
                  (memFrame_update (by linarith only []) (by linarith only [hL_le, hL_ge]))
              have hl3 := bfs_backtrack_loop (p := p) n workAddr outAddr parVBase parEBase u v L
                st2.mem hpv hpe hdj_wo hout_w hwork_w hw4 hL_ge hL_le hpar_bounds
              refine runs_seq_triple_le hl3 ?_ (fun st3 hst3 => ?_)
              · dsimp only
                simp only [hs2_8, hs2_6, hs2_5, ← hL_def]
                refine ⟨by simp [hs2_8], by simp [hs2_9], by simp [hs2_10],
                  by simp, by simp,
                  hmf_init, ?_, ?_, ?_, ?_, by simp; exact hv_n, ?_, ?_, ?_⟩
                · rw [Function.update_of_ne (by linarith only []),
                    Function.update_of_ne (by linarith only [hL_ge]), Function.update_self]
                · rw [Function.update_of_ne (by linarith only [hL_ge]), Function.update_self]
                · rw [Function.update_self]
                · simp only [Function.update_self]
                  rw [List.getElem?_eq_getElem (by rw [bfsWalkVerts_length]; linarith only [hLm1_add])]
                  simpa [hparV_def] using congrArg some (bfsWalkVerts_last parV (L - 1) v)
                · simp [← hL_def, hLm1_add]
                · intro j hj1 hj2
                  simp only [Function.update_apply, ite_true] at hj1
                  linarith only [hj1, hj2, hLm1_add]
                · intro j hj1 hj2
                  simp only [Function.update_apply, ite_true] at hj1
                  linarith only [hj1, hj2]
              · rcases hst3 with ⟨⟨hs3_8, hs3_9, hs3_10, hs3_20, _, hfr3, ho0, hoL, hou,
                    hwalk_at?, _, _, hv_suff, he_suff⟩, h22_0⟩
                clear hl3
                wram_run
                · have key : ∀ G : Cited.Graph, G.n = n → G.m = m → G.IsValid →
                      HasCsrAt mem csrAddr G →
                      ∃ P : Walk, WalkAt st3.mem outAddr P ∧ P.IsWalk G u v ∧ P.verts.Nodup ∧
                        (∀ e ∈ P.edges, mem (eMaskAddr + e) ≠ 0) ∧
                        (∀ x ∈ P.verts, mem (vMaskAddr + x) ≠ 0) ∧
                        P.edges.length < n ∧
                        (∀ W : Walk, W.IsWalk G u v →
                          (∀ e ∈ W.edges, mem (eMaskAddr + e) ≠ 0) →
                          (∀ x ∈ W.verts, mem (vMaskAddr + x) ≠ 0) →
                          P.edges.length ≤ W.edges.length) := by
                    intro G hGn hGm hGval hGcsr
                    let P : Walk := ⟨bfsWalkVerts parV (L - 1) v, bfsWalkEdges parV parE (L - 1) v⟩
                    let dist' : ℕ → ℕ := fun y => if y < n then st2.mem (workAddr + y) else 0
                    have hstep_d : ∀ y, 2 ≤ dist' y → dist' (parV y) + 1 = dist' y := by
                      intro y hy
                      by_cases hyn : y < n
                      · simp only [dist', hyn, ↓reduceIte] at hy ⊢
                        have hyi := hpar_inv y hyn hy
                        simp only [hparV_def, hyi.2.1, ↓reduceIte]
                        exact hyi.1
                      · simp [dist', hyn] at hy
                    have hu_uniq_d : ∀ y, dist' y = 1 → y = u := by
                      intro y hy
                      by_cases hyn : y < n
                      · simp only [dist', hyn, ↓reduceIte] at hy
                        exact hdu_uniq y hyn hy
                      · simp [dist', hyn] at hy
                    have hdv_d : dist' v = L := by
                      simp [dist', hv_n, hL_def]
                    have hinv_d : ∀ y, 2 ≤ dist' y →
                        dist' (parV y) + 1 = dist' y ∧ y < G.n ∧ parV y < G.n ∧
                        mem (vMaskAddr + y) ≠ 0 ∧ parE y < G.m ∧ mem (eMaskAddr + parE y) ≠ 0 ∧
                        Walk.EdgeMatches (G.edges.getD (parE y) (0, 0)) (parV y) y := by
                      intro y hy
                      have hyn : y < n := by by_contra h; simp [dist', h] at hy
                      have hy2 : 2 ≤ st2.mem (workAddr + y) := by simpa [dist', hyn] using hy
                      have hyi := hpar_inv y hyn hy2
                      have hpv_n : parV y < n := by simpa [hparV_def] using hyi.2.1
                      have hne_py : parV y ≠ y := by
                        intro heq
                        rw [hparV_def] at heq
                        dsimp only at heq
                        rw [heq] at hyi
                        linarith only [hyi.1]
                      have hinc0 : (parE y, false, y) ∈ csrIncAux (parV y) 0 G0.edges ∨
                          (parE y, true, y) ∈ csrIncAux (parV y) 0 G0.edges := by
                        simpa using edge_mem_csrIncAux_of_ne (L := G0.edges) (k := parE y) (r := 0)
                          (by rw [← Cited.Graph.m, hG0m, hparE_def]; exact hyi.2.2.1)
                          hne_py (by simpa [hparV_def, hparE_def] using hyi.2.2.2.2)
                      have hcsr_eq := csrIncAux_eq_of_hasCsrAt hG0csr hGcsr
                        (by linarith only [hGn, hG0n]) (by linarith only [hGm, hG0m])
                        (u := parV y) (by linarith only [hpv_n, hG0n])
                      have hincG : (parE y, false, y) ∈ csrIncAux (parV y) 0 G.edges ∨
                          (parE y, true, y) ∈ csrIncAux (parV y) 0 G.edges := by
                        simpa [hcsr_eq] using hinc0
                      have hEdgeG : parE y < G.m ∧ Walk.EdgeMatches (G.edges.getD (parE y) (0, 0)) (parV y) y := by
                        rcases hincG with h | h <;>
                        · obtain ⟨_, hlen, _, hm⟩ := mem_csrIncAux_edgeMatches h
                          exact ⟨by simpa [Cited.Graph.m] using hlen, by simpa using hm⟩
                      refine ⟨hstep_d y hy, by linarith only [hyn, hGn], by linarith only [hpv_n, hGn],
                        hd_vm y hyn (by linarith only [hy2]),
                        hEdgeG.1, by simpa [hparE_def] using hyi.2.2.2.1, hEdgeG.2⟩
                    obtain ⟨hwalk, hnodup, hemask, hvmask⟩ := bfsWalk_isWalk
                      (vMask := fun z => mem (vMaskAddr + z)) (eMask := fun e => mem (eMaskAddr + e))
                      hL_ge hdv_d
                      (by linarith only [hu_n, hGn]) (by linarith only [hv_n, hGn]) hu_uniq_d hinv_d hvm_u
                    have hv0_eq : P.verts[0]'(by simp [P, bfsWalkVerts_length]) = u :=
                      (bfsWalkVerts_getElem hstep_d (hdv_d.trans hLm1_add.symm) hu_uniq_d 0
                        (by simp [bfsWalkVerts_length])).2.1 rfl
                    have hwat : WalkAt st3.mem outAddr P := by
                      refine walkAt_of_cells ?_ ?_ ?_ ?_
                      · simpa [P, bfsWalkVerts_length, hLm1_add] using ho0
                      · simpa [P, bfsWalkVerts_length, bfsWalkEdges_length, hLm1_add] using hoL
                      · intro j hj
                        have hjL : j < L := by simpa [P, bfsWalkVerts_length, hLm1_add] using hj
                        by_cases hj0 : j = 0
                        · subst hj0
                          simpa [P, hv0_eq] using hou
                        · simpa [P, ← hparV_def] using hv_suff j (by linarith only [Nat.pos_of_ne_zero hj0, h22_0]) hjL
                      · intro j hj
                        have hjL : j < L - 1 := by simpa [P, bfsWalkEdges_length] using hj
                        simpa [P, bfsWalkVerts_length, hLm1_add, ← hparV_def, ← hparE_def] using
                          he_suff j (by linarith only [h22_0]) hjL
                    refine ⟨P, hwat, hwalk, hnodup, hemask,
                      fun z hz => (hvmask z hz).2, ?_, ?_⟩
                    · simp only [P, bfsWalkEdges_length]
                      have hLm1_lt : L - 1 < L := by linarith only [hLm1_add]
                      linarith only [hLm1_lt, hL_le]
                    · intro W hW heW hvW
                      have hrelax := bfsShortestInv_step_relax hG0n hdist_q hscan_prev hscan_cur
                        (fun h => by
                          rcases hcur_act with ⟨_, _, h14_0, _⟩ | ⟨_, h18_eq, _, _, _, hkEnd_eq⟩
                          · omega
                          · exact ⟨h18_eq, hkEnd_eq⟩)
                        (hdone h19_0) hshort
                      have hd := dist_le_walk_edges_length_add_one (G := G) hGval
                        (dist := fun y => st2.mem (workAddr + y))
                        (vMask := fun z => mem (vMaskAddr + z)) (eMask := fun e => mem (eMaskAddr + e))
                        hdu (fun x hx hdx j hj hej y hy hvy hmatch => by
                          by_cases hxy : x = y
                          · subst hxy; exact ⟨hdx, Nat.le_succ _⟩
                          · have hInG := edge_mem_csrIncAux_of_ne (L := G.edges) (k := j) (r := 0)
                              (by rw [← Cited.Graph.m]; exact hj) hxy hmatch
                            have hcsr_eq := csrIncAux_eq_of_hasCsrAt hGcsr hG0csr
                              (by rw [hGn, hG0n]) (by rw [hGm, hG0m]) (u := x) hx
                            have hinc0 : (j, false, y) ∈ csrIncAux x 0 G0.edges ∨
                                (j, true, y) ∈ csrIncAux x 0 G0.edges := by
                              simpa [hcsr_eq] using hInG
                            obtain ⟨dir, hdir⟩ : ∃ dir : Bool, (j, dir, y) ∈ csrIncAux x 0 G0.edges := by
                              rcases hinc0 with h | h <;> exact ⟨_, h⟩
                            obtain ⟨_, hlen, _, hm0⟩ := mem_csrIncAux_edgeMatches hdir
                            exact hrelax x (by rw [hG0n, ← hGn]; exact hx) hdx j
                              (by simpa [Cited.Graph.m] using hlen) hej y
                              (by rw [hG0n, ← hGn]; exact hy) hvy (by simpa using hm0))
                        hW heW hvW
                      simp only [P, bfsWalkEdges_length]
                      have hdv : st2.mem (workAddr + v) = L := hL_def.symm
                      simp only [hdv] at hd
                      omega
                  refine ⟨1, rfl, ⟨Or.inr rfl, ?_, fun G hGn hGm hGval hGcsr => ⟨fun _ => ?_, fun h0 => by omega⟩⟩,
                    fun G hGn hGm hGval hGcsr _ => key G hGn hGm hGval hGcsr⟩
                  · simp only [List.getD_cons_zero, List.getD_cons_succ]
                    exact bfsPath_preserves_frame hfr_mem2 hfr3
                  · obtain ⟨P, h1, h2, h3, h4, h5, h6, _⟩ := key G hGn hGm hGval hGcsr
                    exact ⟨P, h1, h2, h3, h4, h5, h6⟩
                · have hLm1 : L - 1 ≤ n := le_trans (Nat.sub_le L 1) hL_le
                  clear hfr_base hfr2 hq_lt hq_inj hdist_q hdist_le hdu hdu_uniq hd_vm hpar_inv
                    hcur_act hscan_prev hscan_cur hdone hfr1 hmBase hq0_eq hwu_eq hwx_eq
                    hpar_bounds hfr3 ho0 hoL hou hwalk_at? hv_suff he_suff hparV_def hparE_def
                  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin,
                    bfsMeas, Function.update_apply, Nat.reduceEqDiff, ite_false, ite_true, Nat.sub_zero]
                  rw [hdd0, ← hL_def]
                  simp only [Nat.sub_zero]
                  linarith only [hcsr_le, hLm1]
  obtain ⟨o, st', c, hrun, ⟨res, rfl, hpost⟩, hcost⟩ :=
    htriple (startState [n, m, csrAddr, vMaskAddr, eMaskAddr, u, v, workAddr, outAddr] mem pos) ω rfl
  refine ⟨bfsPathProc, hproc, .returned res, st', c, hrun, hpost, ?_⟩
  simpa [bfsShortestPathContract, bfsPathContract] using hcost

/-- Specification proof for `bfsPathProc`: meets `bfsPathContract w`. It follows from
`bfsShortestPath_spec`. -/
theorem bfsPath_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [bfsPathProc]) :
    MeetsContract w p b (bfsPathContract w) :=
  meets_bfsPathContract_of_shortest (bfsShortestPath_spec hp)

/-- Bundled CSR builder and BFS shortest-path procedure table (`[buildCsrProc, bfsPathProc]`). -/
def csrBfsProcs : List Stmt := [buildCsrProc, bfsPathProc]

lemma csrBfsProcs_length : csrBfsProcs.length = 2 := rfl

lemma csrBfsProcs_noRand : ∀ s ∈ csrBfsProcs, s.NoRand := by
  intro s hs
  simp only [csrBfsProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact buildCsrProc_noRand
  · exact bfsPathProc_noRand

theorem buildCsr_meets {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b csrBfsProcs) :
    MeetsContract w p b (buildCsrContract w) :=
  buildCsr_spec fun i hi => by simp at hi; subst hi; exact hp 0 (by simp [csrBfsProcs])

theorem bfsPath_meets {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b csrBfsProcs) :
    MeetsContract w p (b + 1) (bfsPathContract w) :=
  bfsPath_spec fun i hi => by simp at hi; subst hi; exact hp 1 (by simp [csrBfsProcs])

end MinCostFlow.Expander
