module

public import MinCostFlow.Expander.DecomposeLevelBase
public import MinCostFlow.Expander.DecomposeTwinProg
public import MinCostFlow.Expander.DecomposeLevelSplit
public import MinCostFlow.Expander.DecomposeGroupVertsProg
public import MinCostFlow.Expander.DecomposeGroupEdgesSpec
public import MinCostFlow.Expander.DecomposePartSpec
public import MinCostFlow.Expander.DecomposeMath

import Mathlib.Tactic.Linarith

/-!
# Single-Level Word-RAM Procedure for Expander Decomposition

Implements `levelProc` and proves `level_runs` (Theorem 8.5 / Algorithm 5, single recursive
level `lvl ∈ {ℓ, ..., 1}`):
1. Loads `curN, curM` and computes `csrAddr, qAddr, lblAddr`.
2. Builds the twin graph (`buildTwinStmt`) and runs `[B1]` on it (`twinDecompStmt`).
3. Clears `keptVert[0..curN)` (`zeroKeptStmt`), groups vertices (`b_gv`), normalizes
   `grpSameTwin` to `{0, 1}` (`normSameTwinStmt`), and groups edges (`b_ge`).
4. Loops `q = 0..k-1` calling `b_part`, emitting non-empty kept expanders `R_q` (`2 ≤ |R_q|`)
   into the arena (`statePtr`), and marks kept vertices in `keptVert`.
5. Partitions edges into `(nextGAddr, nextIdxAddr)` and updates `lvlArr` (`splitEdgesStmt`).
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Pure Helpers for Level Cost, Arena Size, and Edge Filtering -/

/-- Variable-cost `forRange` execution lemma (tracks exact summed loop body cost). -/
lemma forRange_varCost {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (r : ℕ) (lo hi : Expr) (body : Stmt) (Inv : ℕ → State → Prop)
    (stepBound : ℕ → ℕ) (loVal hiVal : ℕ)
    (hlo_hi : loVal ≤ hiVal) (hw1 : 1 < 2 ^ w) (hhi_w : hiVal < 2 ^ w)
    (hr_get : ∀ i st, loVal ≤ i → i ≤ hiVal → Inv i st → st.regs r = i)
    (hhi_eval : ∀ i st, loVal ≤ i → i ≤ hiVal → Inv i st → hi.eval w st = some hiVal)
    (hstep : ∀ i st, loVal ≤ i → i < hiVal → Inv i st →
      ∃ st₁ c₁, Runs w p ω body st .normal st₁ c₁ ∧ c₁ ≤ stepBound i ∧ st₁.regs r = i ∧
        Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) })
    (st₀ : State) (hlo_eval : lo.eval w st₀ = some loVal)
    (hstart : Inv loVal { st₀ with regs := Function.update st₀.regs r loVal }) :
    ∃ st' c, Runs w p ω (forRange r lo hi body) st₀ .normal st' c ∧ Inv hiVal st' ∧
      c ≤ lo.size + 1 + hi.size + 5 + ∑ q ∈ Finset.Ico loVal hiVal, (stepBound q + hi.size + 8) := by
  let st_init : State := { st₀ with regs := Function.update st₀.regs r loVal }
  have hassign_lo : Runs w p ω (.assign r lo) st₀ .normal st_init (lo.size + 1) :=
    runs_assign_iff.mpr ⟨loVal, hlo_eval, rfl, rfl, rfl⟩
  have hloop : ∀ (d i : ℕ) (st : State), hiVal - i = d → loVal ≤ i → i ≤ hiVal → Inv i st →
      ∃ st' c, Runs w p ω (forUp r hi body) st .normal st' c ∧ Inv hiVal st' ∧
        c ≤ hi.size + 3 + ∑ q ∈ Finset.Ico i hiVal, (stepBound q + hi.size + 8) := by
    intro d
    induction d with
    | zero =>
      intro i st hd hli hih hinv
      have hieq : i = hiVal := by omega
      subst i
      have hr : st.regs r = hiVal := hr_get hiVal st hli le_rfl hinv
      have hehi := hhi_eval hiVal st hli le_rfl hinv
      have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 0 := by
        simp [Expr.eval, BinOp.eval, hr, hehi]
      refine ⟨st, (Expr.bin .lt (.reg r) hi).size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), hinv, ?_⟩
      simp [Expr.size]; omega
    | succ d ih =>
      intro i st hd hli hih hinv
      have hilt : i < hiVal := by omega
      have hr : st.regs r = i := hr_get i st hli hih hinv
      have hehi := hhi_eval i st hli hih hinv
      have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, hr, hehi, hilt, hw1]
      obtain ⟨st₁, c₁, hrun₁, hc₁, hst₁_r, hinv₁⟩ := hstep i st hli hilt hinv
      let st₂ : State := { st₁ with regs := Function.update st₁.regs r (i + 1) }
      have hinc : Runs w p ω (.assign r (.bin .add (.reg r) (.const 1))) st₁ .normal st₂ 4 := by
        refine runs_assign_iff.mpr ⟨i + 1, ?_, rfl, rfl, rfl⟩
        simp [Expr.eval, BinOp.eval, hst₁_r, hw1, show i + 1 < 2 ^ w by omega]
      have hbody_seq : Runs w p ω (.seq body (.assign r (.bin .add (.reg r) (.const 1))))
          st .normal st₂ (c₁ + 4 + 1) := runs_seq hrun₁ hinc
      obtain ⟨st', c₂, hrest, hinv', hc₂⟩ :=
        ih (i + 1) st₂ (by omega) (by omega) hilt hinv₁
      have hloop_step : Runs w p ω (forUp r hi body) st .normal st'
          ((Expr.bin .lt (.reg r) hi).size + (c₁ + 4 + 1) + c₂ + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st₂, c₁ + 4 + 1, c₂, hcond, by omega, hbody_seq, hrest, rfl⟩))
      refine ⟨st', (Expr.bin .lt (.reg r) hi).size + (c₁ + 4 + 1) + c₂ + 1, hloop_step, hinv', ?_⟩
      have hsplit : Finset.Ico i hiVal = insert i (Finset.Ico (i + 1) hiVal) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      simp only [Expr.size] at hc₂ ⊢
      omega
  obtain ⟨st', c_up, hup, hinv', hc_up⟩ :=
    hloop (hiVal - loVal) loVal st_init rfl le_rfl hlo_hi (by dsimp only [st_init]; exact hstart)
  refine ⟨st', lo.size + 1 + c_up + 1, runs_seq hassign_lo hup, hinv', ?_⟩
  omega

/-- Pointwise congruence for `tab`. -/
lemma tab_eq_of_eq {n : ℕ} {f g : ℕ → ℕ} (h : ∀ t < n, f t = g t) :
    tab n f = tab n g := by
  simp only [tab, List.map_inj_left, List.mem_range]
  exact h

/-- Telescoping sum over `Finset.Ico 0 k` when `off (q + 1) = off q + cnt q` and `off 0 = 0`. -/
lemma sum_Ico_eq_of_off {off cnt : ℕ → ℕ} (k : ℕ)
    (h0 : off 0 = 0) (hstep : ∀ q < k, off (q + 1) = off q + cnt q) :
    ∑ q ∈ Finset.Ico 0 k, cnt q = off k := by
  induction k with
  | zero => simpa using h0.symm
  | succ k ih =>
    rw [Finset.sum_Ico_succ_top (Nat.zero_le k), ih (fun q hq => hstep q (by omega)), hstep k (by omega)]

/-- Crossing edges of a labeled graph are at most `1 / 200 * G.m` when `IsExpanderDecomposition` holds. -/
lemma crossing_edges_le_of_expDecomp {G : Cited.Graph} (hV : G.IsValid) {φ : ℝ} {label : List ℕ}
    (hdec : IsExpanderDecomposition G (1 / 200) φ label) :
    ((G.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
      1 / 200 * (G.m : ℝ) := by
  have hsum : (∑ X ∈ partsOf G label, (G.cut X : ℝ)) =
      2 * ((G.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) := by
    exact_mod_cast sum_cut_partsOf hV label
  have hvol : (G.vol G.verts : ℝ) = 2 * (G.m : ℝ) := by
    exact_mod_cast vol_verts_of_isValid hV
  have hcut := hdec.2.2
  rw [hsum, hvol] at hcut
  linarith

/-- Disjoint subsets `Rs` satisfy `∑_{R ∈ Rs} |G.inside R| ≤ E.length` for any edge list `E`. -/
lemma sum_filter_inside_disjoint_le (Rs : List (Finset ℕ)) (hRs : Rs.Pairwise Disjoint)
    (E : List (ℕ × ℕ)) :
    (Rs.map fun R => (E.filter fun e => decide (e.1 ∈ R ∧ e.2 ∈ R)).length).sum ≤ E.length := by
  induction E with
  | nil => simp
  | cons e es ih =>
    simp only [List.filter_cons, List.length_cons]
    have hstep : ∀ (L : List (Finset ℕ)), L.Pairwise Disjoint →
        (L.map fun R => (if decide (e.1 ∈ R ∧ e.2 ∈ R) then
          (es.filter fun e' => decide (e'.1 ∈ R ∧ e'.2 ∈ R)).length + 1
          else (es.filter fun e' => decide (e'.1 ∈ R ∧ e'.2 ∈ R)).length)).sum ≤
        (L.map fun R => (es.filter fun e' => decide (e'.1 ∈ R ∧ e'.2 ∈ R)).length).sum + 1 := by
      intro L hL
      induction L with
      | nil => simp
      | cons R ts ihL =>
        rw [List.pairwise_cons] at hL
        simp only [List.map_cons, List.sum_cons]
        by_cases hmem : decide (e.1 ∈ R ∧ e.2 ∈ R) = true
        · have he1 : e.1 ∈ R := (decide_eq_true_eq.mp hmem).1
          have hzero : ∀ T ∈ ts, decide (e.1 ∈ T ∧ e.2 ∈ T) = false := by
            intro T hT
            simp only [decide_eq_false_iff_not, not_and]
            intro heT
            exact False.elim (Finset.disjoint_left.mp (hL.1 T hT) he1 heT)
          have heq : (ts.map fun T => if decide (e.1 ∈ T ∧ e.2 ∈ T) then
              (es.filter fun e' => decide (e'.1 ∈ T ∧ e'.2 ∈ T)).length + 1
              else (es.filter fun e' => decide (e'.1 ∈ T ∧ e'.2 ∈ T)).length) =
              (ts.map fun T => (es.filter fun e' => decide (e'.1 ∈ T ∧ e'.2 ∈ T)).length) :=
            List.map_congr_left fun T hT => by simp [hzero T hT]
          rw [heq]; simp only [hmem, ↓reduceIte]
          omega
        · have ih' := ihL hL.2
          simp only [hmem, Bool.false_eq_true, ↓reduceIte]
          omega
    simp only [apply_ite List.length, List.length_cons]
    exact le_trans (hstep Rs hRs) (Nat.add_le_add_right ih 1)

/-- Each non-empty emitted expander `R_q` uses at most `4 * (curG.inside R_q).length` arena words. -/
lemma arena_record_le_four_inside {curG : Cited.Graph} {D D_phi : ℕ}
    (hD : 1 ≤ D) (hD_phi : 1 ≤ D_phi) {R : Finset ℕ} (hcard : 2 ≤ R.card)
    (hdeg : ∀ v ∈ R, (1 : ℝ) / (3 * (D_phi : ℝ)) * (D : ℝ) ≤ (curG.degIn R v : ℝ)) :
    2 + R.card ≤ 4 * (curG.inside R).length := by
  have h1deg : ∀ v ∈ R, 1 ≤ curG.degIn R v := by
    intro v hv
    have hpos : (0 : ℝ) < (curG.degIn R v : ℝ) := by
      have hp : (0 : ℝ) < 1 / (3 * (D_phi : ℝ)) * (D : ℝ) := by positivity
      linarith [hdeg v hv]
    exact_mod_cast (by exact_mod_cast hpos : (0 : ℕ) < curG.degIn R v)
  have hsum_ge : R.card ≤ ∑ v ∈ R, curG.degIn R v := by
    calc R.card = ∑ _v ∈ R, 1 := by simp
      _ ≤ ∑ v ∈ R, curG.degIn R v := Finset.sum_le_sum fun v hv => h1deg v hv
  have hvol_eq : ∑ v ∈ R, curG.degIn R v = 2 * (curG.inside R).length := by
    change curG.volIn R R = 2 * (curG.inside R).length
    exact volIn_self curG R
  omega

/-- Equates `edgeKeptBool` on edge index `j` with membership of `(u, v)` in some emitted `R ∈ validRs`. -/
lemma edgeKeptBool_iff_any_valid {curG : Cited.Graph} {k : ℕ} (partId kept : ℕ → ℕ)
    (R_of : ℕ → Finset ℕ) (validRs : List (Finset ℕ))
    (hvalid : validRs = (List.range k).filterMap (fun q => if 2 ≤ (R_of q).card then some (R_of q) else none))
    (hsub : ∀ q < k, R_of q ⊆ {u ∈ Finset.range curG.n | partId u = q})
    (hempty : ∀ q < k, R_of q = ∅ ∨ 2 ≤ (R_of q).card)
    (hkept_iff : ∀ u < curG.n, kept u ≠ 0 ↔ ∃ q < k, u ∈ R_of q)
    (hV : curG.IsValid) {j : ℕ} (hj : j < curG.m) :
    edgeKeptBool curG partId kept j =
      validRs.any (fun R => decide ((curG.edges.getD j (0, 0)).1 ∈ R ∧ (curG.edges.getD j (0, 0)).2 ∈ R)) := by
  set u := (curG.edges.getD j (0, 0)).1
  set v := (curG.edges.getD j (0, 0)).2
  have huv : u < curG.n ∧ v < curG.n := by
    have hmem : curG.edges.getD j (0, 0) ∈ curG.edges := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    exact hV _ hmem
  have hu := huv.1
  have hv := huv.2
  rw [Bool.eq_iff_iff]
  simp only [edgeKeptBool, decide_eq_true_eq, List.any_eq_true, decide_eq_true_eq]
  rw [hvalid]
  constructor
  · rintro ⟨hp, hku, hkv⟩
    obtain ⟨q, hqk, huR⟩ := (hkept_iff u hu).mp hku
    have huq : partId u = q := (Finset.mem_filter.mp (hsub q hqk huR)).2
    obtain ⟨q', hq'k, hvR⟩ := (hkept_iff v hv).mp hkv
    have hvq' : partId v = q' := (Finset.mem_filter.mp (hsub q' hq'k hvR)).2
    have hqq' : q' = q := hvq'.symm.trans (hp.symm.trans huq)
    rw [hqq'] at hvR
    refine ⟨R_of q, ?_, huR, hvR⟩
    rw [List.mem_filterMap]
    refine ⟨q, List.mem_range.mpr hqk, ?_⟩
    rcases hempty q hqk with h0 | hc
    · rw [h0] at huR; exact absurd huR (Finset.notMem_empty _)
    · simp [hc]
  · rintro ⟨R, hRmem, huR, hvR⟩
    rw [List.mem_filterMap] at hRmem
    rcases hRmem with ⟨q, hqk, hqsome⟩
    rw [List.mem_range] at hqk
    split_ifs at hqsome with hcard
    cases hqsome
    have huq : partId u = q := (Finset.mem_filter.mp (hsub q hqk huR)).2
    have hvq : partId v = q := (Finset.mem_filter.mp (hsub q hqk hvR)).2
    exact ⟨huq.trans hvq.symm, (hkept_iff u hu).mpr ⟨q, hqk, huR⟩, (hkept_iff v hv).mpr ⟨q, hqk, hvR⟩⟩

/-- Subsequence characterization of `remEdgesPrefix`. -/
lemma remEdgesPrefix_eq_filter_map (curG : Cited.Graph) (partId kept : ℕ → ℕ) :
    ∀ j ≤ curG.m,
      remEdgesPrefix curG partId kept j =
        ((List.range j).filter fun t => !edgeKeptBool curG partId kept t).map
          (fun t => curG.edges.getD t (0, 0))
  | 0, _ => by simp [remEdgesPrefix]
  | j + 1, hj => by
    rw [remEdgesPrefix_succ, remEdgesPrefix_eq_filter_map curG partId kept j (by omega),
      List.range_succ, List.filter_append, List.map_append]
    simp only [List.filter_cons, List.filter_nil]
    by_cases h : edgeKeptBool curG partId kept j = true <;> simp [h]

/-- Subsequence characterization of `remIdxPrefix`. -/
lemma remIdxPrefix_eq_filter_map (curG : Cited.Graph) (curIdx : List ℕ) (partId kept : ℕ → ℕ) :
    ∀ j ≤ curG.m,
      remIdxPrefix curG curIdx partId kept j =
        ((List.range j).filter fun t => !edgeKeptBool curG partId kept t).map
          (fun t => curIdx.getD t 0)
  | 0, _ => by simp [remIdxPrefix]
  | j + 1, hj => by
    rw [remIdxPrefix_succ, remIdxPrefix_eq_filter_map curG curIdx partId kept j (by omega),
      List.range_succ, List.filter_append, List.map_append]
    simp only [List.filter_cons, List.filter_nil]
    by_cases h : edgeKeptBool curG partId kept j = true <;> simp [h]

/-- Filtering `l` by index predicate preserves strict increasing order. -/
lemma pairwise_lt_map_filter (l : List ℕ) (hnd : l.Pairwise (· < ·)) (p : ℕ → Bool) :
    (((List.range l.length).filter p).map fun t => l.getD t 0).Pairwise (· < ·) := by
  have hr : (List.range l.length).Pairwise (fun a b => a < b ∧ a < l.length ∧ b < l.length) := by
    refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
    simp only [List.length_range] at hi hj
    simp only [List.getElem_range]
    exact ⟨hij, hi, hj⟩
  have hsub := hr.filter p
  rw [List.pairwise_map]
  exact hsub.imp fun {a b} ⟨hab, ha, hb⟩ => by
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
    exact (List.pairwise_iff_getElem.mp hnd) _ _ ha hb hab

/-- Helper: `partPruneCost cnt ecnt D_phi` bounded cleanly in `cnt`, `ecnt`, `H_max`. -/
lemma partPruneCost_le_bound {cnt ecnt m D_phi : ℕ} (hec : ecnt ≤ m) :
    let H_max := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * m + 1) + 1) + 2
    partPruneCost cnt ecnt D_phi ≤
      620 * cnt +
      (590 + 720 * (4 * H_max + 14) ^ 2) * ecnt +
      (900 + 400 * (4 * H_max + 14) ^ 2) := by
  dsimp only [partPruneCost, pruneTimeBound]
  set H := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * ecnt + 1) + 1) + 2
  set H_max := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * m + 1) + 1) + 2
  have hlog_le : Nat.log 2 (2 * ecnt + 1) + 1 ≤ Nat.log 2 (2 * m + 1) + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
  have hH_le : H ≤ H_max := by
    dsimp only [H, H_max]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog_le) 2
  have hlog_le_H : Nat.log 2 (2 * ecnt + 1) + 1 ≤ H_max := by
    have : Nat.log 2 (2 * m + 1) + 1 ≤ 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * m + 1) + 1) + 2 := by
      nlinarith
    exact le_trans hlog_le this
  have h4H4 : 4 * H + 4 ≤ 4 * H_max + 14 := by omega
  have h4H14 : 4 * H + 14 ≤ 4 * H_max + 14 := by omega
  have hsq : (4 * H + 14) * (4 * H + 4) ≤ (4 * H_max + 14) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul h4H14 h4H4
  have hmul_edge : (4 * H + 14) * (4 * H + 4) * (2 * ecnt + 1) ≤
      (4 * H_max + 14) ^ 2 * (2 * ecnt + 1) :=
    Nat.mul_le_mul_right _ hsq
  have hec_part : 360 * ((4 * H + 14) * (4 * H + 4) * (2 * ecnt + 1)) ≤
      720 * (4 * H_max + 14) ^ 2 * ecnt + 360 * (4 * H_max + 14) ^ 2 := by
    nlinarith
  have hlin_H : 30 * (H + 1) + 13 * (Nat.log 2 (2 * ecnt + 1) + 1) ≤
      40 * (4 * H_max + 14) ^ 2 := by
    have hH1 : H + 1 ≤ H_max + 1 := by omega
    nlinarith [show H_max + 1 ≤ (4 * H_max + 14) ^ 2 by nlinarith]
  rw [Nat.add_mul]
  linarith [hec_part, hlin_H]

/-- Every word in `(twinGraph D curG).encode ++ [1, 200, rOf m_tw]` fits in `2 ^ w`. -/
lemma twinGraph_encode_lt_pow {w : ℕ} (curG : Cited.Graph) (D : ℕ)
    (hV : curG.IsValid) (hn_w : 2 * curG.n < 2 ^ w) (hm_w : (twinGraph D curG).m < 2 ^ w)
    (hr_w : rOf (twinGraph D curG).m < 2 ^ w) (h201_w : 201 ≤ 2 ^ w) :
    ∀ v ∈ (twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m], v < 2 ^ w := by
  intro v hv
  rw [List.mem_append] at hv
  rcases hv with hv_enc | hv_suf
  · dsimp only [Cited.Graph.encode] at hv_enc
    simp only [List.mem_cons] at hv_enc
    rcases hv_enc with rfl | rfl | hv_flat
    · exact hn_w
    · exact hm_w
    · rw [List.mem_flatMap] at hv_flat
      rcases hv_flat with ⟨e, he, hve⟩
      have hev := twinGraph_isValid (D := D) hV e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hve
      rcases hve with rfl | rfl
      · exact lt_of_lt_of_le hev.1 (le_of_eq (rfl : (twinGraph D curG).n = 2 * curG.n) |>.trans hn_w.le)
      · exact lt_of_lt_of_le hev.2 (le_of_eq (rfl : (twinGraph D curG).n = 2 * curG.n) |>.trans hn_w.le)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_suf
    rcases hv_suf with rfl | rfl | rfl <;> omega

/-- For a strictly increasing list `L`, `List.idxOf (L[q]) L = q`. -/
lemma idxOf_getElem_of_pairwise_lt {l : List ℕ} (h : l.Pairwise (· < ·)) {q : ℕ} (hq : q < l.length) :
    l.idxOf l[q] = q := by
  have hnd : l.Nodup := h.imp fun hab => Nat.ne_of_lt hab
  exact List.Nodup.idxOf_getElem hnd q hq

/-- Equivalence between `List.filter (2 ≤ ·.card) (map R_of (range k))` and `filterMap`. -/
lemma filter_ge2_map_eq_filterMap {k : ℕ} (R_of : ℕ → Finset ℕ) :
    List.filter (fun R => decide (2 ≤ R.card)) ((List.range k).map R_of) =
      (List.range k).filterMap (fun q => if 2 ≤ (R_of q).card then some (R_of q) else none) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.filterMap_append, ih]
    simp only [List.map_singleton, List.filter_cons, List.filter_nil, List.filterMap_cons,
      List.filterMap_nil]
    by_cases h : 2 ≤ (R_of k).card <;> simp [h]

/-! ## 2. Normalize `grpSameTwin`, `levelProc`, and Cost Bound -/

/-- Normalizes `mem[bufAddr + u]` to `0` or `1` for `u < curN` in `O(curN)` steps. -/
def normSameTwinStmt : Stmt :=
  forRange 21 (.const 0) (.reg 14)
    (.cond (.load (.bin .add (.reg 6) (.reg 21)))
      (.store (.bin .add (.reg 6) (.reg 21)) (.const 1)) .nop)

lemma normSameTwinStmt_noRand : normSameTwinStmt.NoRand := by
  simp [normSameTwinStmt, forRange, forUp, Stmt.NoRand]

lemma normSameTwin_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (curN bufAddr : ℕ) (st₀ : State)
    (hr14 : st₀.regs 14 = curN) (hr6 : st₀.regs 6 = bufAddr)
    (hcurN_w : curN < 2 ^ w) (hbuf_w : bufAddr + curN < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ st' c, Runs w p ω normSameTwinStmt st₀ .normal st' c ∧
      c ≤ 19 * curN + 8 ∧
      (∀ r, r ≠ 21 → st'.regs r = st₀.regs r) ∧
      (∀ u < curN, st'.mem (bufAddr + u) = if st₀.mem (bufAddr + u) = 0 then 0 else 1) ∧
      MemFrame st₀.mem st'.mem bufAddr (bufAddr + curN) := by
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 14 = curN ∧ st.regs 6 = bufAddr ∧ st.regs 21 = i ∧
    (∀ r, r ≠ 21 → st.regs r = st₀.regs r) ∧
    (∀ u < i, st.mem (bufAddr + u) = if st₀.mem (bufAddr + u) = 0 then 0 else 1) ∧
    (∀ u, i ≤ u → u < curN → st.mem (bufAddr + u) = st₀.mem (bufAddr + u)) ∧
    MemFrame st₀.mem st.mem bufAddr (bufAddr + curN)
  have hres := forRange_varCost (w := w) (p := p) (ω := ω)
    21 (.const 0) (.reg 14)
    (.cond (.load (.bin .add (.reg 6) (.reg 21)))
      (.store (.bin .add (.reg 6) (.reg 21)) (.const 1)) .nop)
    Inv (fun _ => 10) 0 curN (Nat.zero_le curN) hw1 hcurN_w
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ _ _ _ h => by simp [Expr.eval, h.1])
    (fun i st _ hi h => by
      rcases h with ⟨hr14', hr6', hr21', hregs_other, hdone, hrest, hfr⟩
      have haddr_eval : (Expr.bin .add (.reg 6) (.reg 21)).eval w st = some (bufAddr + i) := by
        simp [Expr.eval, BinOp.eval, hr6', hr21', show bufAddr + i < 2 ^ w by omega]
      have hload_eval : (Expr.load (.bin .add (.reg 6) (.reg 21))).eval w st = some (st.mem (bufAddr + i)) := by
        simp [Expr.eval, BinOp.eval, hr6', hr21', show bufAddr + i < 2 ^ w by omega]
      have hval_orig : st.mem (bufAddr + i) = st₀.mem (bufAddr + i) := hrest i le_rfl hi
      by_cases h0 : st₀.mem (bufAddr + i) = 0
      · have hload0 : (Expr.load (.bin .add (.reg 6) (.reg 21))).eval w st = some 0 := by
          rw [hload_eval, hval_orig, h0]
        have hcond : Runs w p ω
            (.cond (.load (.bin .add (.reg 6) (.reg 21)))
              (.store (.bin .add (.reg 6) (.reg 21)) (.const 1)) .nop)
            st .normal st 6 :=
          runs_cond_iff.mpr ⟨0, 1, hload0, by simp [runs_nop_iff], rfl⟩
        refine ⟨st, 6, hcond, by omega, hr21', hr14', hr6', by simp,
          fun r hr => by simp only; rw [Function.update_of_ne hr]; exact hregs_other r hr, ?_, ?_, hfr⟩
        · intro u hu
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | rfl
          · exact hdone u hlt
          · rw [hval_orig, h0]; simp
        · intro u hu1 hu2; exact hrest u (by omega) hu2
      · let st1 : State := { st with mem := Function.update st.mem (bufAddr + i) 1 }
        have hst_mem_ne : st.mem (bufAddr + i) ≠ 0 := by rwa [hval_orig]
        have hstore : Runs w p ω (.store (.bin .add (.reg 6) (.reg 21)) (.const 1)) st .normal st1 5 :=
          runs_store_iff.mpr ⟨bufAddr + i, 1, haddr_eval, by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
        have hcond : Runs w p ω
            (.cond (.load (.bin .add (.reg 6) (.reg 21)))
              (.store (.bin .add (.reg 6) (.reg 21)) (.const 1)) .nop)
            st .normal st1 10 :=
          runs_cond_iff.mpr ⟨st.mem (bufAddr + i), 5, hload_eval, by simp [hst_mem_ne, hstore], rfl⟩
        refine ⟨st1, 10, hcond, le_rfl, hr21', hr14', hr6', by simp,
          fun r hr => by simp only; rw [Function.update_of_ne hr]; exact hregs_other r hr, ?_, ?_, ?_⟩
        · intro u hu
          dsimp only [st1]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | rfl
          · rw [Function.update_of_ne (by omega)]; exact hdone u hlt
          · rw [Function.update_self]; simp [h0]
        · intro u hu1 hu2
          dsimp only [st1]; rw [Function.update_of_ne (by omega)]; exact hrest u (by omega) hu2
        · intro a ha
          dsimp only [st1]; rw [Function.update_of_ne (by omega)]; exact hfr a ha)
    st₀ (by simp [Expr.eval])
    ⟨hr14, hr6, by simp, fun r hr => by simp [Function.update, hr],
      fun _ h => by omega, fun u _ _ => rfl, fun _ _ => rfl⟩
  rcases hres with ⟨st', c, hrun, ⟨_, _, hr21', hregs_other, hdone, _, hfr⟩, hc⟩
  refine ⟨st', c, hrun, ?_, hregs_other, hdone, hfr⟩
  simp only [Expr.size, Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hc
  omega

/-- Body of the `q = 0..k-1` part loop inside `levelProc`. -/
def partLoopBody (b_part : ℕ) : Stmt :=
  seqStmts
    [ .assign 21 (.load (.reg 9))
    , .call 22 b_part
        [.reg 0, .reg 6, .reg 19, .reg 10, .reg 11, .reg 12, .reg 7, .reg 8, .reg 21]
    , .cond (.bin .lt (.reg 21) (.reg 22))
        (seqStmts
          [ .store (.reg 9) (.reg 22)
          , .store (.bin .add (.reg 9) (.const 2))
              (.bin .add (.load (.bin .add (.reg 9) (.const 2))) (.const 1)) ])
        .nop ]

lemma partLoopBody_eq (b_part : ℕ) :
    partLoopBody b_part =
      .seq (.assign 21 (.load (.reg 9)))
        (.seq (.call 22 b_part [.reg 0, .reg 6, .reg 19, .reg 10, .reg 11, .reg 12, .reg 7, .reg 8, .reg 21])
          (.cond (.bin .lt (.reg 21) (.reg 22))
            (.seq (.store (.reg 9) (.reg 22))
              (.store (.bin .add (.reg 9) (.const 2))
                (.bin .add (.load (.bin .add (.reg 9) (.const 2))) (.const 1))))
            .nop)) := rfl

lemma partLoopBody_noRand (b_part : ℕ) : (partLoopBody b_part).NoRand := by
  simp [partLoopBody, seqStmts, Stmt.NoRand]

/-- First half of `levelProc`: computes `LvlRegs`, runs `buildTwinStmt`, `twinDecompStmt`,
clears `keptVert`, runs `b_gv`, `normSameTwinStmt`, `b_ge`, and copies `k` into `reg 20`. -/
def levelSetupPrefix (b_run b_csr b_bfs b_gv b_ge thr : ℕ) : Stmt :=
  seqStmts
    [ .assign 14 (.load (.reg 0))
    , .assign 15 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 19 (.bin .add (.reg 15) (.bin .mul (.reg 11) (.reg 14)))
    , .assign 16 (.bin .add (.reg 5) (.bin .add (.const 5) (.bin .mul (.const 2) (.reg 19))))
    , .assign 17 (.bin .add (.reg 16)
        (.bin .add (.bin .mul (.const 4) (.reg 14))
          (.bin .add (.const 1) (.bin .mul (.const 4) (.reg 19)))))
    , .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 14)))
    , buildTwinStmt
    , twinDecompStmt b_run b_csr b_bfs thr
    , zeroKeptStmt
    , .call 19 b_gv [.reg 14, .reg 18, .reg 6]
    , normSameTwinStmt
    , .call 20 b_ge [.reg 0, .reg 19, .reg 6]
    , .assign 20 (.reg 19) ]

lemma levelSetupPrefix_eq (b_run b_csr b_bfs b_gv b_ge thr : ℕ) :
    levelSetupPrefix b_run b_csr b_bfs b_gv b_ge thr =
      .seq (.assign 14 (.load (.reg 0)))
        (.seq (.assign 15 (.load (.bin .add (.reg 0) (.const 1))))
          (.seq (.assign 19 (.bin .add (.reg 15) (.bin .mul (.reg 11) (.reg 14))))
            (.seq (.assign 16 (.bin .add (.reg 5) (.bin .add (.const 5) (.bin .mul (.const 2) (.reg 19)))))
              (.seq (.assign 17 (.bin .add (.reg 16)
                  (.bin .add (.bin .mul (.const 4) (.reg 14))
                    (.bin .add (.const 1) (.bin .mul (.const 4) (.reg 19))))))
                (.seq (.assign 18 (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 14))))
                  (.seq buildTwinStmt
                    (.seq (twinDecompStmt b_run b_csr b_bfs thr)
                      (.seq zeroKeptStmt
                        (.seq (.call 19 b_gv [.reg 14, .reg 18, .reg 6])
                          (.seq normSameTwinStmt
                            (.seq (.call 20 b_ge [.reg 0, .reg 19, .reg 6])
                              (.assign 20 (.reg 19))))))))))))) := rfl

lemma levelSetupPrefix_noRand (b_run b_csr b_bfs b_gv b_ge thr : ℕ) :
    (levelSetupPrefix b_run b_csr b_bfs b_gv b_ge thr).NoRand := by
  simp [levelSetupPrefix, seqStmts, Stmt.NoRand, buildTwinStmt_noRand, twinDecompStmt_noRand,
    zeroKeptStmt_noRand, normSameTwinStmt_noRand]

/-- Word-RAM procedure for one recursive level of `Decompose` (Algorithm 5).
Expects `args = [curGAddr, curIdxAddr, nextGAddr, nextIdxAddr, lvlArrAddr, twAddr, bufAddr,
workAddr, keptVertAddr, statePtr, lvl, D, D_phi, mCap]`. -/
def levelProc (b_run b_csr b_bfs b_gv b_ge b_part thr : ℕ) : Stmt :=
  seqStmts
    [ levelSetupPrefix b_run b_csr b_bfs b_gv b_ge thr
    , forRange 19 (.const 0) (.reg 20) (partLoopBody b_part)
    , splitEdgesStmt
    , .ret (.const 0) ]

lemma levelProc_noRand (b_run b_csr b_bfs b_gv b_ge b_part thr : ℕ) :
    (levelProc b_run b_csr b_bfs b_gv b_ge b_part thr).NoRand := by
  simp [levelProc, seqStmts, Stmt.NoRand, levelSetupPrefix_noRand, forRange_noRand,
    partLoopBody_noRand, splitEdgesStmt_noRand]

/-- Cost bound for `levelProc`. -/
def levelCost (curN curM D D_phi c_cited_ub scaleP c_ws : ℕ) : ℕ :=
  120 * (curM + D * curN + 1) + 45 * (Nat.log 2 (curM + D * curN + 1) + 2) +
  400 * (2 * curN + (curM + D * curN) + 2) +
  scaleP * (2 * c_cited_ub + (5 + 2 * (curM + D * curN)) + c_ws + 1) +
  1000 * (curN * (2 * Nat.log 2 (curN + 2) + 1) + 1) +
  42 * curN + 200 * (curN + curM + 1) +
  (620 * curN +
    (590 + 720 * (4 * (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curM + 1) + 1) + 2) + 14) ^ 2) * curM +
    curN * (1100 + 400 * (4 * (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curM + 1) + 1) + 2) + 14) ^ 2)) +
  125 * curM + 260


end MinCostFlow.Expander
