module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBPrim
public import MinCostFlow.ExpanderDecomp.ProgStepBSpec

import Mathlib.Tactic.Linarith

/-!
# Step B Single-Pass Scatter of `matchings.flatten` (`ProgStepBScatter`)

Implements and verifies `sbScatterStmt`, which scatters all edges of `matchings.flatten`
returned by `bRoute` directly into each active cut block's witness graph `W_i` in a single
`O(t * (b / 2) + |matchings.flatten|)` pass with zero scan of `range G.n`, restoring `locAddr`
to all zeros.

Main results:
- `sbScatterStmt`, `sbScatterStmt_noRand`
- `sbScatter_triple`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Characterization of `GraphAt mem a (Graph.mk n E)` in terms of header words and `EdgesAt`. -/
lemma graphAt_mk_iff {mem : ℕ → ℕ} {a n : ℕ} {E : List (ℕ × ℕ)} :
    GraphAt mem a (Graph.mk n E) ↔ mem a = n ∧ mem (a + 1) = E.length ∧ EdgesAt mem (a + 2) E := by
  constructor
  · intro h
    refine ⟨graphAt_n h, graphAt_m h, fun q hq => ?_⟩
    exact ⟨graphAt_edge_fst h hq, by
      have h2 := graphAt_edge_snd h hq
      have heq : a + 2 + 2 * q + 1 = a + 3 + 2 * q := by omega
      rwa [heq]⟩
  · rintro ⟨hn, hm, hE⟩
    refine graphAt_of_cells (G := Graph.mk n E) hn hm (fun q hq => ⟨(hE q hq).1, ?_⟩)
    have heq : a + 3 + 2 * q = a + 2 + 2 * q + 1 := by omega
    rw [heq]; exact (hE q hq).2

private lemma flatMap_pair_getElem_even (pairs : List (Finset ℕ × Finset ℕ)) :
    ∀ k (hk : k < pairs.length),
      (pairs.flatMap fun p => [p.1, p.2])[2 * k]'(by
        have hfl : (pairs.flatMap fun p => [p.1, p.2]).length = 2 * pairs.length := by
          induction pairs with | nil => simp | cons _ _ _ => simp; omega
        omega) = (pairs[k]'hk).1 := by
  induction pairs with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    intro k hk
    cases k with
    | zero => simp
    | succ k' =>
      have hk' : k' < xs.length := by simpa using hk
      have heq : 2 * (k' + 1) = (2 * k') + 2 := by omega
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, heq, List.getElem_cons_succ]
      exact ih k' hk'

/-- Mark `locAddr[u] := idx + 1` for `u ∈ C'_idx` (`idx < t`), scatter all edges of
`matchings.flatten` at `rtOutA + 2` (len `mem[rtOutA + 1]`) directly into the owning witness graph
`W_i` recorded at `cutRecsA + 3 * idx`, and unmark `locAddr` back to all zeros.
Inputs: `r4 = b`, `r8 = locA`, `r22 = cutRecsA`, `r25 = t`, `r27 = rtOutA`.
Modifies only `r30..r37`. -/
def sbScatterStmt : Stmt :=
  seqStmts [
    .assign 30 (.bin .div (.reg 4) (.const 2)),
    forRange 31 (.const 0) (.reg 25) (seqStmts [
      .assign 32 (.load (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31))) (.const 1))),
      .assign 33 (.bin .add (.reg 31) (.const 1)),
      sbMarkListStmt 32 30 8 33 34 35
    ]),
    .assign 36 (.load (.bin .add (.reg 27) (.const 1))),
    forRange 31 (.const 0) (.reg 36) (seqStmts [
      .assign 32 (.load (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 31)))),
      .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 31))) (.const 1))),
      .assign 34 (.bin .sub (.load (.bin .add (.reg 8) (.reg 32))) (.const 1)),
      .assign 35 (.load (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 34)))),
      .assign 37 (.load (.bin .add (.reg 35) (.const 1))),
      .store (.bin .add (.bin .add (.reg 35) (.const 2)) (.bin .mul (.const 2) (.reg 37))) (.reg 32),
      .store (.bin .add (.bin .add (.bin .add (.reg 35) (.const 2)) (.bin .mul (.const 2) (.reg 37))) (.const 1)) (.reg 33),
      .store (.bin .add (.reg 35) (.const 1)) (.bin .add (.reg 37) (.const 1))
    ]),
    .assign 33 (.const 0),
    forRange 31 (.const 0) (.reg 25) (seqStmts [
      .assign 32 (.load (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31))) (.const 1))),
      sbMarkListStmt 32 30 8 33 34 35
    ])
  ]

theorem sbScatterStmt_noRand : sbScatterStmt.NoRand := by
  simp [sbScatterStmt, sbMarkListStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Triple for `sbScatterStmt`: appends `matchings.getD idx []` to each `W_{cutIds[idx]}` (`idx < t`),
restores `locAddr` to all zeros, preserves `r < 30`, and runs in
`≤ 48 * t * (b / 2) + 80 * t + 70 * matchings.flatten.length + 100` steps. -/
theorem sbScatter_triple {w n b t locA cutRecsA rtOutA wBaseA wStride nBlocks maxR : ℕ}
    {p : Program} {mem : ℕ → ℕ} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {matchings : List (List (ℕ × ℕ))}
    {cutIds : List ℕ} {cPrimeAddrs : List ℕ} {cPrimeLists : List (List ℕ)}
    {prevEdges : ℕ → List (ℕ × ℕ)} {st₀ : State}
    (ht_len : pairs.length = t) (hcut_len : cutIds.length = t)
    (hcpa_len : cPrimeAddrs.length = t) (hcpl_len : cPrimeLists.length = t)
    (hcut_nd : cutIds.Nodup) (hcut_lt : ∀ i ∈ cutIds, i < nBlocks)
    (hX_sub : X ⊆ Finset.range n) (hvtp : ValidTerminalPairs X pairs)
    (hmlen : matchings.length = t)
    (hpm : ∀ idx (hidx : idx < t),
      IsPartialMatching (pairs[idx]'(ht_len.symm ▸ hidx)).1
        (pairs[idx]'(ht_len.symm ▸ hidx)).2 (matchings.getD idx []))
    (hrec_w : ∀ idx (hidx : idx < t),
      mem (cutRecsA + 3 * idx) = wBaseA + (cutIds[idx]'(hcut_len.symm ▸ hidx)) * wStride)
    (hrec_c : ∀ idx (hidx : idx < t),
      mem (cutRecsA + 3 * idx + 1) = cPrimeAddrs[idx]'(hcpa_len.symm ▸ hidx))
    (hcpl_spec : ∀ idx (hidx : idx < t),
      (cPrimeLists[idx]'(hcpl_len.symm ▸ hidx)).length = b / 2 ∧
      (cPrimeLists[idx]'(hcpl_len.symm ▸ hidx)).toFinset = (pairs[idx]'(ht_len.symm ▸ hidx)).1 ∧
      ListAt mem (cPrimeAddrs[idx]'(hcpa_len.symm ▸ hidx)) (cPrimeLists[idx]'(hcpl_len.symm ▸ hidx)) ∧
      DisjointRange locA n (cPrimeAddrs[idx]'(hcpa_len.symm ▸ hidx)) (b / 2) ∧
      DisjointRange wBaseA (nBlocks * wStride) (cPrimeAddrs[idx]'(hcpa_len.symm ▸ hidx)) (b / 2) ∧
      cPrimeAddrs[idx]'(hcpa_len.symm ▸ hidx) + b / 2 < 2 ^ w)
    (hwStride_eq : wStride = 2 + 2 * maxR * (b / 2))
    (hprev_W : ∀ i < nBlocks, GraphAt mem (wBaseA + i * wStride) (Graph.mk n (prevEdges i)))
    (hprev_len_all : ∀ i < nBlocks, (prevEdges i).length ≤ maxR * (b / 2))
    (hprev_cap : ∀ idx (hidx : idx < t),
      (prevEdges (cutIds[idx]'(hcut_len.symm ▸ hidx))).length + (matchings.getD idx []).length ≤ maxR * (b / 2))
    (hmLen : mem (rtOutA + 1) = matchings.flatten.length)
    (hmAt : EdgesAt mem (rtOutA + 2) matchings.flatten)
    (hloc0 : ∀ u < n, mem (locA + u) = 0)
    (hd_loc_rec : DisjointRange locA n cutRecsA (3 * t))
    (hd_loc_rt : DisjointRange locA n rtOutA (2 + 2 * matchings.flatten.length))
    (hd_loc_w : DisjointRange locA n wBaseA (nBlocks * wStride))
    (hd_w_rec : DisjointRange wBaseA (nBlocks * wStride) cutRecsA (3 * t))
    (hd_w_rt : DisjointRange wBaseA (nBlocks * wStride) rtOutA (2 + 2 * matchings.flatten.length))
    (hloc_w : locA + n < 2 ^ w) (hrec_w_bnd : cutRecsA + 3 * t < 2 ^ w)
    (hrt_w : rtOutA + 2 + 2 * matchings.flatten.length < 2 ^ w)
    (hw_w : wBaseA + nBlocks * wStride < 2 ^ w) (ht_w : t + 1 < 2 ^ w)
    (hb_w : b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st₀.regs 4 = b) (hr8 : st₀.regs 8 = locA)
    (hr22 : st₀.regs 22 = cutRecsA) (hr25 : st₀.regs 25 = t) (hr27 : st₀.regs 27 = rtOutA)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) sbScatterStmt
      (normalPost fun st' =>
        (∀ r < 30, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + n ≤ a) → (a < wBaseA ∨ wBaseA + nBlocks * wStride ≤ a) →
          st'.mem a = mem a) ∧
        (∀ idx (hidx : idx < t),
          let i := cutIds[idx]'(hcut_len.symm ▸ hidx)
          GraphAt st'.mem (wBaseA + i * wStride) (Graph.mk n (prevEdges i ++ matchings.getD idx []))) ∧
        (∀ i < nBlocks, i ∉ cutIds →
          GraphAt st'.mem (wBaseA + i * wStride) (Graph.mk n (prevEdges i))))
      (fun _ => 48 * t * (b / 2) + 110 * t + 100 * matchings.flatten.length + 100) := by
  have hpairs_disj : ∀ j₁ j₂ (hj₁ : j₁ < t) (hj₂ : j₂ < t), j₁ ≠ j₂ →
      Disjoint (pairs[j₁]'(ht_len.symm ▸ hj₁)).1 (pairs[j₂]'(ht_len.symm ▸ hj₂)).1 := by
    intro j₁ j₂ hj₁ hj₂ hne
    have hpw := hvtp.2
    have h1 : ∀ a b (ha : a < t) (hb : b < t), a < b →
        Disjoint (pairs[a]'(ht_len.symm ▸ ha)).1 (pairs[b]'(ht_len.symm ▸ hb)).1 := by
      intro a b ha hb hab
      have hfl : (pairs.flatMap fun p => [p.1, p.2]).length = 2 * pairs.length := by
        clear hpw; induction pairs with | nil => simp | cons _ _ _ => simp; omega
      have hpw_get := List.pairwise_iff_getElem.mp hpw (2 * a) (2 * b) (by omega) (by omega) (by omega)
      rwa [flatMap_pair_getElem_even pairs a (ht_len.symm ▸ ha),
        flatMap_pair_getElem_even pairs b (ht_len.symm ▸ hb)] at hpw_get
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact h1 j₁ j₂ hj₁ hj₂ hlt
    · exact (h1 j₂ j₁ hj₂ hj₁ hgt).symm
  have hpairs_sub_n : ∀ idx (hidx : idx < t), ∀ u ∈ (pairs[idx]'(ht_len.symm ▸ hidx)).1, u < n := by
    intro idx hidx u hu
    exact Finset.mem_range.mp (hX_sub ((hvtp.1 _ (List.getElem_mem (ht_len.symm ▸ hidx))).1 hu))
  have hwS2 : wStride = 2 + 2 * (maxR * (b / 2)) := by rw [hwStride_eq]; ring
  have hslot_lt : ∀ i < nBlocks, ∀ off < wStride, wBaseA + i * wStride + off < wBaseA + nBlocks * wStride := by
    intro i hi off hoff
    have h1 : (i + 1) * wStride ≤ nBlocks * wStride := Nat.mul_le_mul_right wStride hi
    have h2 : (i + 1) * wStride = i * wStride + wStride := by ring
    omega
  have hslot_disj : ∀ i₁ i₂, i₁ ≠ i₂ → ∀ off₁ < wStride, ∀ off₂ < wStride,
      wBaseA + i₁ * wStride + off₁ ≠ wBaseA + i₂ * wStride + off₂ := by
    intro i₁ i₂ hne off₁ h1 off₂ h2
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have : (i₁ + 1) * wStride ≤ i₂ * wStride := Nat.mul_le_mul_right wStride hlt
      have : (i₁ + 1) * wStride = i₁ * wStride + wStride := by ring
      omega
    · have : (i₂ + 1) * wStride ≤ i₁ * wStride := Nat.mul_le_mul_right wStride hgt
      have : (i₂ + 1) * wStride = i₂ * wStride + wStride := by ring
      omega
  have hflat_owner : ∀ e ∈ matchings.flatten,
      ∃ idx, ∃ hidx : idx < t, e.1 ∈ (pairs[idx]'(ht_len.symm ▸ hidx)).1 := by
    intro e he
    obtain ⟨m, hm, hem⟩ := List.mem_flatten.mp he
    obtain ⟨idx, hidx_m, rfl⟩ := List.mem_iff_getElem.mp hm
    have hidx : idx < t := hmlen ▸ hidx_m
    refine ⟨idx, hidx, ?_⟩
    have h1 := (hpm idx hidx).1 e
    rw [List.getD_eq_getElem _ _ hidx_m] at h1
    exact (h1 hem).1
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbScatterStmt, seqStmts]
  refine runs_seq_assign_le (v := b / 2)
    (Expr.eval_div (Expr.eval_reg_of_eq hr4) (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 30 (b / 2), pos := st₀.pos }
  -- Loop 1: mark `locA[u] := idx + 1` for `idx < t` and `u ∈ (pairs[idx]).1`
  let Inv1 : ℕ → State → Prop := fun j st =>
    st.regs 31 = j ∧
    st.regs 30 = b / 2 ∧
    (∀ r < 30, st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem locA (locA + n) ∧
    (∀ u < n,
      (∀ idx (hidx : idx < j) (hidx_p : idx < pairs.length), u ∈ (pairs[idx]'hidx_p).1 → st.mem (locA + u) = idx + 1) ∧
      ((∀ idx (hidx : idx < j) (hidx_p : idx < pairs.length), u ∉ (pairs[idx]'hidx_p).1) → st.mem (locA + u) = 0))
  have hloop1 := Triple.forRange_const (w := w) (p := p) (r := 31) (lo := .const 0) (hi := .reg 25)
    (body := seqStmts [
      .assign 32 (.load (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31))) (.const 1))),
      .assign 33 (.bin .add (.reg 31) (.const 1)),
      sbMarkListStmt 32 30 8 33 34 35])
    (P := fun st => st = st1) (Inv := Inv1) (24 * (b / 2) + 45) 0 t (Nat.zero_le t) (by omega)
    (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (w := w) (by omega), by simp,
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self],
        fun r hr => by dsimp only [st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
        rfl, fun a _ => congrFun hmem a, fun u hu => ⟨fun _ h _ => by omega, fun _ => hmem ▸ hloc0 u hu⟩⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq ((hInv.2.2.1 25 (by decide)).trans hr25))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hr30, hoth, hpos, hfr, hloc⟩
      have hspec_j := hcpl_spec j hjlt
      have hrec_j : st.mem (cutRecsA + 3 * j + 1) = cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt) := by
        rw [hfr _ (by rcases hd_loc_rec with h | h <;> [right; left] <;> omega)]; exact hrec_c j hjlt
      have hcpl_at : ListAt st.mem (cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt)) (cPrimeLists[j]'(hcpl_len.symm ▸ hjlt)) :=
        fun q hq => by
          rw [hfr _ (by rcases hspec_j.2.2.2.1 with h | h <;> [right; left] <;> omega)]
          exact hspec_j.2.2.1 q hq
      have hcpl_lt : ∀ u ∈ cPrimeLists[j]'(hcpl_len.symm ▸ hjlt), u < n := fun u hu =>
        hpairs_sub_n j hjlt u (hspec_j.2.1 ▸ List.mem_toFinset.mpr hu)
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq ((hoth 22 (by decide)).trans hr22))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq hj) (by omega)) (by omega))
          (Expr.eval_const (w := w) (by omega)) (by omega)) hrec_j) ?_
      refine runs_seq_assign_le (v := j + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hj]))
          (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
      let stB : State :=
        { mem := st.mem,
          regs := Function.update (Function.update st.regs 32 (cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt))) 33 (j + 1),
          pos := st.pos }
      refine runs_triple_le
        (sbMarkList_triple (w := w) (n := n) (len := b / 2) (sa := cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt))
          (la := locA) (val := j + 1) (rSrc := 32) (rLen := 30) (rLoc := 8) (rVal := 33) (rI := 34) (rU := 35)
          (by decide) p st.mem (cPrimeLists[j]'(hcpl_len.symm ▸ hjlt)) stB hspec_j.1 hcpl_at hcpl_lt
          hspec_j.2.2.2.1 hspec_j.2.2.2.2.2 hloc_w hw16
          (by dsimp only [stB]; rw [Function.update_of_ne (by decide), Function.update_self])
          (by dsimp only [stB]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30])
          (by dsimp only [stB]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth 8 (by decide), hr8])
          (by dsimp only [stB]; rw [Function.update_self]) rfl) rfl ?_
        (by simp only [Expr.size]; omega)
      rintro (_ | _) stC hC
      · rcases hC with ⟨hothC, hposC, hfrC, hlocC⟩
        have hr31_C : stC.regs 31 = j := by
          rw [hothC 31 (by decide) (by decide)]; dsimp only [stB]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne (by decide), hothC 30 (by decide) (by decide)]; dsimp only [stB]
             rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30],
          fun r hr => by dsimp only; rw [Function.update_of_ne (by omega), hothC r (by omega) (by omega)]; dsimp only [stB]
                         rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoth r hr],
          hposC.trans hpos, fun a ha => (hfrC a ha).trans (hfr a ha), fun u hu => ?_⟩, hr31_C⟩
        refine ⟨fun idx hidx hidx_p hu_in => ?_, fun hnone => ?_⟩
        · rw [hlocC u hu, hspec_j.2.1]
          by_cases hjeq : idx = j
          · subst hjeq; simp [hu_in]
          · have hnotj : u ∉ (pairs[j]'(ht_len.symm ▸ hjlt)).1 :=
              Finset.disjoint_left.mp (hpairs_disj idx j (by omega) hjlt hjeq) hu_in
            simp only [hnotj, ↓reduceIte]
            exact (hloc u hu).1 idx (by omega) hidx_p hu_in
        · rw [hlocC u hu, hspec_j.2.1]
          have hnotj : u ∉ (pairs[j]'(ht_len.symm ▸ hjlt)).1 := hnone j (Nat.lt_succ_self j) (ht_len.symm ▸ hjlt)
          simp only [hnotj, ↓reduceIte]
          exact (hloc u hu).2 fun idx hidx hidx_p => hnone idx (Nat.lt_succ_of_lt hidx) hidx_p
      · exact False.elim hC)
  refine runs_seq_triple_le hloop1 rfl ?_
  intro st2 ⟨_, hr30_2, hoth2, hpos2, hfr2, hloc2⟩
  -- Loop 2: scatter `matchings.flatten`
  have hmLen2 : st2.mem (rtOutA + 1) = matchings.flatten.length := by
    rw [hfr2 _ (by rcases hd_loc_rt with h | h <;> [right; left] <;> omega)]; exact hmLen
  refine runs_seq_assign_le (v := matchings.flatten.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ((hoth2 27 (by decide)).trans hr27))
      (Expr.eval_const (w := w) (by omega)) (by omega)) hmLen2) ?_
  let st3 : State := { mem := st2.mem, regs := Function.update st2.regs 36 matchings.flatten.length, pos := st2.pos }
  let Inv2 : ℕ → State → Prop := fun j st =>
    st.regs 31 = j ∧
    st.regs 30 = b / 2 ∧
    st.regs 36 = matchings.flatten.length ∧
    (∀ r < 30, st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame st2.mem st.mem wBaseA (wBaseA + nBlocks * wStride) ∧
    (∀ idx (hidx : idx < t),
      let i := cutIds[idx]'(hcut_len.symm ▸ hidx)
      let added := (matchings.flatten.take j).filter (fun e => decide (e.1 ∈ (pairs[idx]'(ht_len.symm ▸ hidx)).1))
      GraphAt st.mem (wBaseA + i * wStride) (Graph.mk n (prevEdges i ++ added))) ∧
    (∀ i < nBlocks, i ∉ cutIds → GraphAt st.mem (wBaseA + i * wStride) (Graph.mk n (prevEdges i)))
  have hloop2 := Triple.forRange_const (w := w) (p := p) (r := 31) (lo := .const 0) (hi := .reg 36)
    (body := seqStmts [
      .assign 32 (.load (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 31)))),
      .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 31))) (.const 1))),
      .assign 34 (.bin .sub (.load (.bin .add (.reg 8) (.reg 32))) (.const 1)),
      .assign 35 (.load (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 34)))),
      .assign 37 (.load (.bin .add (.reg 35) (.const 1))),
      .store (.bin .add (.bin .add (.reg 35) (.const 2)) (.bin .mul (.const 2) (.reg 37))) (.reg 32),
      .store (.bin .add (.bin .add (.bin .add (.reg 35) (.const 2)) (.bin .mul (.const 2) (.reg 37))) (.const 1)) (.reg 33),
      .store (.bin .add (.reg 35) (.const 1)) (.bin .add (.reg 37) (.const 1))])
    (P := fun st => st = st3) (Inv := Inv2) 85 0 matchings.flatten.length (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (w := w) (by omega), by simp,
        by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30_2],
        by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_self],
        fun r hr => by dsimp only [st3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoth2 r hr],
        hpos2, fun a _ => rfl, fun idx hidx => ?_, fun i hi _ => ?_⟩
      · simp only [List.take_zero, List.filter_nil, List.append_nil]
        have hi := hcut_lt _ (List.getElem_mem (hcut_len.symm ▸ hidx))
        have hlen_i := hprev_len_all _ hi
        have hprev := graphAt_mk_iff.mp (hprev_W _ hi)
        refine graphAt_mk_iff.mpr ⟨by rw [hfr2 _ (by have := hslot_lt _ hi 0 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hprev.1,
          by rw [hfr2 _ (by have := hslot_lt _ hi 1 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hprev.2.1,
          fun q hq => by
            have h1 := hslot_lt _ hi (2 + 2 * q) (by omega)
            have h2 := hslot_lt _ hi (2 + 2 * q + 1) (by omega)
            rw [hfr2 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega),
              hfr2 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega)]
            exact hprev.2.2 q hq⟩
      · have hlen_i := hprev_len_all i hi
        have hprev := graphAt_mk_iff.mp (hprev_W i hi)
        refine graphAt_mk_iff.mpr ⟨by rw [hfr2 _ (by have := hslot_lt i hi 0 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hprev.1,
          by rw [hfr2 _ (by have := hslot_lt i hi 1 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hprev.2.1,
          fun q hq => by
            have h1 := hslot_lt i hi (2 + 2 * q) (by omega)
            have h2 := hslot_lt i hi (2 + 2 * q + 1) (by omega)
            rw [hfr2 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega),
              hfr2 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega)]
            exact hprev.2.2 q hq⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.1)
    (fun j _ hjlt => by
      intro st ω ⟨hj, hr30, hr36, hoth, hpos, hfr, hWcut, hWnon⟩
      set e := matchings.flatten[j]'hjlt
      obtain ⟨idx0, hidx0, he1_in⟩ := hflat_owner e (List.getElem_mem hjlt)
      have hu_lt : e.1 < n := hpairs_sub_n idx0 hidx0 e.1 he1_in
      set i0 := cutIds[idx0]'(hcut_len.symm ▸ hidx0)
      have hi0_lt : i0 < nBlocks := hcut_lt i0 (List.getElem_mem (hcut_len.symm ▸ hidx0))
      set wA0 := wBaseA + i0 * wStride
      set added0 := (matchings.flatten.take j).filter (fun ed => decide (ed.1 ∈ (pairs[idx0]'(ht_len.symm ▸ hidx0)).1))
      set wm0 := (prevEdges i0 ++ added0).length
      have hadded0_lt : added0.length < (matchings.getD idx0 []).length := by
        have hfull := filter_flatten_by_fst_eq_getD hvtp (hmlen.trans ht_len.symm)
          (fun k hk => hpm k (ht_len ▸ hk)) (ht_len.symm ▸ hidx0)
        have htake_s : matchings.flatten.take (j + 1) = matchings.flatten.take j ++ [e] :=
          List.take_succ_eq_append_getElem hjlt
        have hsub : List.Sublist (matchings.flatten.take (j + 1)) matchings.flatten := List.take_sublist _ _
        have hfl_le : ((matchings.flatten.take (j + 1)).filter (fun ed => decide (ed.1 ∈ (pairs[idx0]'(ht_len.symm ▸ hidx0)).1))).length ≤
            (matchings.getD idx0 []).length := by
          rw [← hfull]; exact (hsub.filter _).length_le
        rw [htake_s, List.filter_append] at hfl_le
        simp only [List.filter_cons, he1_in, decide_true, ↓reduceIte, List.filter_nil, List.length_append, List.length_singleton] at hfl_le
        change added0.length + 1 ≤ (matchings.getD idx0 []).length at hfl_le
        omega
      have hwm0_lt : wm0 < maxR * (b / 2) := by
        have hcap := hprev_cap idx0 hidx0
        have hlen_wm : wm0 = (prevEdges i0).length + added0.length := List.length_append
        change (prevEdges i0).length + (matchings.getD idx0 []).length ≤ maxR * (b / 2) at hcap
        omega
      have hslot0_w : wA0 + 2 + 2 * wm0 + 1 < wBaseA + nBlocks * wStride := by
        have := hslot_lt i0 hi0_lt (2 + 2 * wm0 + 1) (by omega); omega
      have hrt_e := hmAt j hjlt
      have he_mem1 : st.mem (rtOutA + 2 + 2 * j) = e.1 := by
        rw [hfr _ (by rcases hd_w_rt with h | h <;> [right; left] <;> omega),
          hfr2 _ (by rcases hd_loc_rt with h | h <;> [right; left] <;> omega)]
        exact hrt_e.1
      have he_mem2 : st.mem (rtOutA + 2 + 2 * j + 1) = e.2 := by
        rw [hfr _ (by rcases hd_w_rt with h | h <;> [right; left] <;> omega),
          hfr2 _ (by rcases hd_loc_rt with h | h <;> [right; left] <;> omega)]
        exact hrt_e.2
      have hloc_e1 : st.mem (locA + e.1) = idx0 + 1 := by
        rw [hfr _ (by rcases hd_loc_w with h | h <;> [left; right] <;> omega)]
        exact (hloc2 e.1 hu_lt).1 idx0 hidx0 (ht_len.symm ▸ hidx0) he1_in
      have hrec_w0 : st.mem (cutRecsA + 3 * idx0) = wA0 := by
        rw [hfr _ (by rcases hd_w_rec with h | h <;> [right; left] <;> omega),
          hfr2 _ (by rcases hd_loc_rec with h | h <;> [right; left] <;> omega)]
        exact hrec_w idx0 hidx0
      have hwm0_mem : st.mem (wA0 + 1) = wm0 := (graphAt_mk_iff.mp (hWcut idx0 hidx0)).2.1
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := e.1)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ((hoth 27 (by decide)).trans hr27))
          (Expr.eval_const (w := w) (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq hj) (by omega)) (by omega)) he_mem1) ?_
      refine runs_seq_assign_le (v := e.2)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hoth 27 (by decide), hr27]))
          (Expr.eval_const (w := w) (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hj])) (by omega)) (by omega))
          (Expr.eval_const (w := w) (by omega)) (by omega)) he_mem2) ?_
      refine runs_seq_assign_le (v := idx0)
        (by have hsub : idx0 + 1 - 1 = idx0 := Nat.add_sub_cancel idx0 1
            exact hsub ▸ Expr.eval_sub (Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth 8 (by decide), hr8]))
              (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega)) hloc_e1)
              (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (v := wA0)
        (Expr.eval_load_of_eq (Expr.eval_add
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth 22 (by decide), hr22]))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega)) hrec_w0) ?_
      refine runs_seq_assign_le (v := wm0)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (w := w) (by omega)) (by omega)) hwm0_mem) ?_
      refine runs_seq_store_le (x := wA0 + 2 + 2 * wm0) (v := e.1)
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
          (Expr.eval_const (w := w) (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])) ?_
      refine runs_seq_store_le (x := wA0 + 2 + 2 * wm0 + 1) (v := e.2)
        (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
          (Expr.eval_const (w := w) (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega))
          (Expr.eval_const (w := w) (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self])) ?_
      refine runs_store_le (x := wA0 + 1) (v := wm0 + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
          (Expr.eval_const (w := w) (by omega)) (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (w := w) (by omega)) (by omega))
        ?_ (by simp [Expr.size])
      have htake_s : matchings.flatten.take (j + 1) = matchings.flatten.take j ++ [e] :=
        List.take_succ_eq_append_getElem hjlt
      refine ⟨⟨by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr36],
        fun r hr => by
          dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoth r hr],
        hpos, fun a ha => by
          have ha1 : a ≠ wA0 + 1 := by have := hslot_lt i0 hi0_lt 1 (by omega); omega
          have ha2 : a ≠ wA0 + 2 + 2 * wm0 + 1 := by omega
          have ha3 : a ≠ wA0 + 2 + 2 * wm0 := by omega
          dsimp only; rw [Function.update_of_ne ha1, Function.update_of_ne ha2, Function.update_of_ne ha3]
          exact hfr a ha, ?_, ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]⟩
      · intro idx hidx
        rw [htake_s, List.filter_append]
        by_cases heq : idx = idx0
        · subst heq
          simp only [List.filter_cons, he1_in, decide_true, ↓reduceIte, List.filter_nil, ← List.append_assoc]
          have hprev_g := graphAt_mk_iff.mp (hWcut idx hidx)
          have hwm_def : wm0 = (prevEdges cutIds[idx] ++
              (matchings.flatten.take j).filter (fun ed => decide (ed.1 ∈ (pairs[idx]'(ht_len.symm ▸ hidx)).1))).length := rfl
          refine graphAt_mk_iff.mpr ⟨by dsimp only [wA0, i0]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hprev_g.1,
            by dsimp only [wA0, i0]; rw [Function.update_self]; simp [wm0, added0, i0, Nat.add_assoc], fun q hq => ?_⟩
          simp only [List.length_append, List.length_singleton] at hq
          have hq_lt : q < wm0 + 1 := by simp only [List.length_append] at hwm_def; omega
          dsimp only [wA0, i0]
          by_cases hqq : q = wm0
          · subst hqq
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self,
              Function.update_of_ne (by omega), Function.update_self, List.getElem_append_right (by omega)]
            simp [wm0, added0, i0]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              List.getElem_append_left (by omega)]
            exact hprev_g.2.2 q (by omega)
        · have hnot : e.1 ∉ (pairs[idx]'(ht_len.symm ▸ hidx)).1 :=
            Finset.disjoint_left.mp (hpairs_disj idx0 idx hidx0 hidx (Ne.symm heq)) he1_in
          simp only [List.filter_cons, hnot, decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
          have hne_id : cutIds[idx]'(hcut_len.symm ▸ hidx) ≠ i0 := fun h =>
            heq ((List.Nodup.getElem_inj_iff hcut_nd).mp h)
          have hprev_g := graphAt_mk_iff.mp (hWcut idx hidx)
          have hlen_idx : (prevEdges (cutIds[idx]'(hcut_len.symm ▸ hidx)) ++
              (matchings.flatten.take j).filter (fun ed => decide (ed.1 ∈ (pairs[idx]'(ht_len.symm ▸ hidx)).1))).length ≤
              maxR * (b / 2) := by
            have hfull := filter_flatten_by_fst_eq_getD hvtp (hmlen.trans ht_len.symm)
              (fun k hk => hpm k (ht_len ▸ hk)) (ht_len.symm ▸ hidx)
            have hsub := ((List.take_sublist j matchings.flatten).filter (fun ed => decide (ed.1 ∈ (pairs[idx]'(ht_len.symm ▸ hidx)).1))).length_le
            rw [hfull] at hsub
            have hcap := hprev_cap idx hidx
            rw [List.length_append]; omega
          have hne_base : ∀ off < wStride, wBaseA + cutIds[idx] * wStride ≠ wA0 + off := fun off hoff => by
            simpa only [Nat.add_zero] using hslot_disj _ _ hne_id 0 (by omega) off hoff
          refine graphAt_mk_iff.mpr ⟨by
              rw [Function.update_of_ne (hne_base 1 (by omega)),
                Function.update_of_ne (by have := hne_base (2 + 2 * wm0 + 1) (by omega); omega),
                Function.update_of_ne (by have := hne_base (2 + 2 * wm0) (by omega); omega)]
              exact hprev_g.1,
            by
              rw [Function.update_of_ne (hslot_disj _ _ hne_id 1 (by omega) 1 (by omega)),
                Function.update_of_ne (by have := hslot_disj _ _ hne_id 1 (by omega) (2 + 2 * wm0 + 1) (by omega); omega),
                Function.update_of_ne (by have := hslot_disj _ _ hne_id 1 (by omega) (2 + 2 * wm0) (by omega); omega)]
              exact hprev_g.2.1,
            fun q hq => by
              rw [Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q) (by omega) 1 (by omega); omega),
                Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q) (by omega) (2 + 2 * wm0 + 1) (by omega); omega),
                Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q) (by omega) (2 + 2 * wm0) (by omega); omega),
                Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q + 1) (by omega) 1 (by omega); omega),
                Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q + 1) (by omega) (2 + 2 * wm0 + 1) (by omega); omega),
                Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q + 1) (by omega) (2 + 2 * wm0) (by omega); omega)]
              exact hprev_g.2.2 q hq⟩
      · intro i hi hnotin
        have hne_id : i ≠ i0 := fun h => hnotin (h ▸ List.getElem_mem (hcut_len.symm ▸ hidx0))
        have hprev_g := graphAt_mk_iff.mp (hWnon i hi hnotin)
        have hlen_i := hprev_len_all i hi
        have hne_base : ∀ off < wStride, wBaseA + i * wStride ≠ wA0 + off := fun off hoff => by
          simpa only [Nat.add_zero] using hslot_disj _ _ hne_id 0 (by omega) off hoff
        refine graphAt_mk_iff.mpr ⟨by
            dsimp only
            rw [Function.update_of_ne (hne_base 1 (by omega)),
              Function.update_of_ne (by have := hne_base (2 + 2 * wm0 + 1) (by omega); omega),
              Function.update_of_ne (by have := hne_base (2 + 2 * wm0) (by omega); omega)]
            exact hprev_g.1,
          by
            dsimp only
            rw [Function.update_of_ne (hslot_disj _ _ hne_id 1 (by omega) 1 (by omega)),
              Function.update_of_ne (by have := hslot_disj _ _ hne_id 1 (by omega) (2 + 2 * wm0 + 1) (by omega); omega),
              Function.update_of_ne (by have := hslot_disj _ _ hne_id 1 (by omega) (2 + 2 * wm0) (by omega); omega)]
            exact hprev_g.2.1,
          fun q hq => by
            dsimp only
            rw [Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q) (by omega) 1 (by omega); omega),
              Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q) (by omega) (2 + 2 * wm0 + 1) (by omega); omega),
              Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q) (by omega) (2 + 2 * wm0) (by omega); omega),
              Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q + 1) (by omega) 1 (by omega); omega),
              Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q + 1) (by omega) (2 + 2 * wm0 + 1) (by omega); omega),
              Function.update_of_ne (by have := hslot_disj _ _ hne_id (2 + 2 * q + 1) (by omega) (2 + 2 * wm0) (by omega); omega)]
            exact hprev_g.2.2 q hq⟩)
  refine runs_seq_triple_le hloop2 rfl ?_
  intro st4 ⟨_, hr30_4, _, hoth4, hpos4, hfr4, hWcut4, hWnon4⟩
  -- Loop 3: unmark `locA[u] := 0` for `idx < t` and `u ∈ (pairs[idx]).1`
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (w := w) (by omega)) ?_
  let st5 : State := { mem := st4.mem, regs := Function.update st4.regs 33 0, pos := st4.pos }
  let Inv3 : ℕ → State → Prop := fun j st =>
    st.regs 31 = j ∧
    st.regs 30 = b / 2 ∧
    st.regs 33 = 0 ∧
    (∀ r < 30, st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame st4.mem st.mem locA (locA + n) ∧
    (∀ u < n, (∀ idx (hidx : idx < t), j ≤ idx → u ∉ (pairs[idx]'(ht_len.symm ▸ hidx)).1) → st.mem (locA + u) = 0)
  have hloop3 := Triple.forRange_const (w := w) (p := p) (r := 31) (lo := .const 0) (hi := .reg 25)
    (body := seqStmts [
      .assign 32 (.load (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31))) (.const 1))),
      sbMarkListStmt 32 30 8 33 34 35])
    (P := fun st => st = st5) (Inv := Inv3) (24 * (b / 2) + 38) 0 t (Nat.zero_le t) (by omega)
    (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (w := w) (by omega), by simp,
        by dsimp only [st5]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30_4],
        by dsimp only [st5]; rw [Function.update_of_ne (by decide), Function.update_self],
        fun r hr => by dsimp only [st5]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoth4 r hr],
        hpos4, fun a _ => rfl, fun u hu hnone => by
          rw [hfr4 _ (by rcases hd_loc_w with h | h <;> [left; right] <;> omega)]
          exact (hloc2 u hu).2 fun idx hidx _ => hnone idx hidx (Nat.zero_le idx)⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq ((hInv.2.2.2.1 25 (by decide)).trans hr25))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hr30, hr33, hoth, hpos, hfr, hloc⟩
      have hspec_j := hcpl_spec j hjlt
      have hrec_j : st.mem (cutRecsA + 3 * j + 1) = cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt) := by
        rw [hfr _ (by rcases hd_loc_rec with h | h <;> [right; left] <;> omega),
          hfr4 _ (by rcases hd_w_rec with h | h <;> [right; left] <;> omega),
          hfr2 _ (by rcases hd_loc_rec with h | h <;> [right; left] <;> omega)]
        exact hrec_c j hjlt
      have hcpl_at : ListAt st.mem (cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt)) (cPrimeLists[j]'(hcpl_len.symm ▸ hjlt)) :=
        fun q hq => by
          rw [hfr _ (by rcases hspec_j.2.2.2.1 with h | h <;> [right; left] <;> omega),
            hfr4 _ (by rcases hspec_j.2.2.2.2.1 with h | h <;> [right; left] <;> omega),
            hfr2 _ (by rcases hspec_j.2.2.2.1 with h | h <;> [right; left] <;> omega)]
          exact hspec_j.2.2.1 q hq
      have hcpl_lt : ∀ u ∈ cPrimeLists[j]'(hcpl_len.symm ▸ hjlt), u < n := fun u hu =>
        hpairs_sub_n j hjlt u (hspec_j.2.1 ▸ List.mem_toFinset.mpr hu)
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq ((hoth 22 (by decide)).trans hr22))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq hj) (by omega)) (by omega))
          (Expr.eval_const (w := w) (by omega)) (by omega)) hrec_j) ?_
      let stB : State := { mem := st.mem, regs := Function.update st.regs 32 (cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt)), pos := st.pos }
      refine runs_triple_le
        (sbMarkList_triple (w := w) (n := n) (len := b / 2) (sa := cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt))
          (la := locA) (val := 0) (rSrc := 32) (rLen := 30) (rLoc := 8) (rVal := 33) (rI := 34) (rU := 35)
          (by decide) p st.mem (cPrimeLists[j]'(hcpl_len.symm ▸ hjlt)) stB hspec_j.1 hcpl_at hcpl_lt
          hspec_j.2.2.2.1 hspec_j.2.2.2.2.2 hloc_w hw16
          (by dsimp only [stB]; rw [Function.update_self])
          (by dsimp only [stB]; rw [Function.update_of_ne (by decide), hr30])
          (by dsimp only [stB]; rw [Function.update_of_ne (by decide), hoth 8 (by decide), hr8])
          (by dsimp only [stB]; rw [Function.update_of_ne (by decide), hr33]) rfl) rfl ?_
        (by simp only [Expr.size]; omega)
      rintro (_ | _) stC hC
      · rcases hC with ⟨hothC, hposC, hfrC, hlocC⟩
        have hr31_C : stC.regs 31 = j := by
          rw [hothC 31 (by decide) (by decide)]; dsimp only [stB]; rw [Function.update_of_ne (by decide), hj]
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne (by decide), hothC 30 (by decide) (by decide)]; dsimp only [stB]; rw [Function.update_of_ne (by decide), hr30],
          by dsimp only; rw [Function.update_of_ne (by decide), hothC 33 (by decide) (by decide)]; dsimp only [stB]; rw [Function.update_of_ne (by decide), hr33],
          fun r hr => by dsimp only; rw [Function.update_of_ne (by omega), hothC r (by omega) (by omega)]; dsimp only [stB]; rw [Function.update_of_ne (by omega), hoth r hr],
          hposC.trans hpos, fun a ha => (hfrC a ha).trans (hfr a ha), fun u hu hnone => ?_⟩, hr31_C⟩
        rw [hlocC u hu, hspec_j.2.1]
        by_cases huj : u ∈ (pairs[j]'(ht_len.symm ▸ hjlt)).1
        · simp [huj]
        · simp only [huj, ↓reduceIte]
          exact hloc u hu fun idx hidx hge => by
            by_cases heq : idx = j
            · subst heq; exact huj
            · exact hnone idx hidx (by omega)
      · exact False.elim hC)
  refine runs_triple_le hloop3 rfl ?_
    (by simp only [Expr.size, Nat.sub_zero]
        have h1 : t * (24 * (b / 2) + 45 + 1 + 8) = 24 * t * (b / 2) + 54 * t := by ring
        have h2 : t * (24 * (b / 2) + 38 + 1 + 8) = 24 * t * (b / 2) + 47 * t := by ring
        have h3 : matchings.flatten.length * (85 + 1 + 8) = 94 * matchings.flatten.length := by ring
        have h4 : 24 * t * (b / 2) + 24 * t * (b / 2) = 48 * t * (b / 2) := by ring
        rw [h1, h2, h3]; omega)
  rintro (_ | _) st6 h6
  · rcases h6 with ⟨_, _, _, hoth6, hpos6, hfr6, hloc6⟩
    refine ⟨hoth6, hpos6, fun u hu => hloc6 u hu (fun _ h1 h2 => by omega),
      fun a ha_loc ha_w => (hfr6 a ha_loc).trans ((hfr4 a ha_w).trans (hfr2 a ha_loc)),
      fun idx hidx => ?_, fun i hi hnotin => ?_⟩
    · have hW := hWcut4 idx hidx
      rw [List.take_length, filter_flatten_by_fst_eq_getD hvtp (hmlen.trans ht_len.symm)
        (fun k hk => hpm k (ht_len ▸ hk)) (ht_len.symm ▸ hidx)] at hW
      have hWg := graphAt_mk_iff.mp hW
      have hi := hcut_lt _ (List.getElem_mem (hcut_len.symm ▸ hidx))
      have hcap := hprev_cap idx hidx
      refine graphAt_mk_iff.mpr ⟨by rw [hfr6 _ (by have := hslot_lt _ hi 0 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.1,
        by rw [hfr6 _ (by have := hslot_lt _ hi 1 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.2.1,
        fun q hq => by
          rw [List.length_append] at hq
          have h1 := hslot_lt _ hi (2 + 2 * q) (by omega)
          have h2 := hslot_lt _ hi (2 + 2 * q + 1) (by omega)
          rw [hfr6 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega),
            hfr6 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega)]
          exact hWg.2.2 q (by rw [List.length_append]; exact hq)⟩
    · have hWg := graphAt_mk_iff.mp (hWnon4 i hi hnotin)
      have hlen_i := hprev_len_all i hi
      refine graphAt_mk_iff.mpr ⟨by rw [hfr6 _ (by have := hslot_lt i hi 0 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.1,
        by rw [hfr6 _ (by have := hslot_lt i hi 1 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.2.1,
        fun q hq => by
          have h1 := hslot_lt i hi (2 + 2 * q) (by omega)
          have h2 := hslot_lt i hi (2 + 2 * q + 1) (by omega)
          rw [hfr6 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega),
            hfr6 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega)]
          exact hWg.2.2 q hq⟩
  · exact False.elim h6

end MinCostFlow.ExpanderDecomp
