module

public import MinCostFlow.Expander.PruningState
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Push-relabel expander pruning transitions

Implements the single-vertex removal step (`removeOneFromR`), push-relabel micro-steps
(`absorbStep`, `pushStep`, `relabelOrFreezeStep`), `pruneStep`, and proves preservation of
the invariants (`SweepInv` / `PruningInv`), strict decrease of the global potential `pot`,
step-count accounting, and the `vol(P \ B) + 2 C_cap cut(P, R)` monotone bound.
-/

public section

namespace MinCostFlow.Expander

open MinCostFlow.Cited

/-! ### Helper sum lemmas for edge removal and updates -/

lemma list_sum_map_eq_add_at {α β : Type*} [AddCommMonoid β] (L : List α)
    (hnd : L.Nodup) (f g : α → β) (q : α) (hq : q ∈ L)
    (hother : ∀ x ∈ L, x ≠ q → f x = g x) :
    (L.map f).sum + g q = (L.map g).sum + f q := by
  induction L with
  | nil => simp at hq
  | cons a t ih =>
    rcases List.nodup_cons.mp hnd with ⟨ha_not, hnd_t⟩
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hqt
    · have htail : t.map f = t.map g :=
        List.map_congr_left fun x hx => hother x (List.mem_cons_of_mem _ hx) (fun heq => ha_not (heq ▸ hx))
      rw [htail]; abel
    · have hne : a ≠ q := fun heq => ha_not (heq ▸ hqt)
      have ha_eq : f a = g a := hother a (by simp) hne
      have ih' := ih hnd_t hqt fun x hx hxne => hother x (List.mem_cons_of_mem _ hx) hxne
      rw [ha_eq, add_assoc, ih', ← add_assoc]

lemma sum_filter_edges_between (a w : ℕ) (haw : a ≠ w) (k : ℕ) (L : List (ℕ × ℕ))
    (g : ℕ → Bool → ℤ) :
    ((incEdgesAux w k L).filter (fun q => decide (q.2.2 = a)) |>.map
      (fun q => g q.1 (!q.2.1))).sum =
    ((incEdgesAux a k L).filter (fun p => decide (p.2.2 = w)) |>.map
      (fun p => g p.1 p.2.1)).sum := by
  induction L generalizing k with
  | nil => simp [incEdgesAux]
  | cons e rest ih =>
    rcases e with ⟨x, y⟩
    have ih' := ih (k + 1)
    by_cases hxy : x = y
    · subst hxy; simp [incEdgesAux, ih']
    · by_cases h1 : x = w ∧ y = a
      · rcases h1 with ⟨rfl, rfl⟩
        rw [incEdgesAux, incEdgesAux]
        simp [hxy, ih']
      · by_cases h2 : y = w ∧ x = a
        · rcases h2 with ⟨rfl, rfl⟩
          rw [incEdgesAux, incEdgesAux]
          simp [hxy, ih']
        · have hincW : ((incEdgesAux w k ((x, y) :: rest)).filter (fun q => decide (q.2.2 = a))) =
              ((incEdgesAux w (k + 1) rest).filter (fun q => decide (q.2.2 = a))) := by
            by_cases hxw : x = w
            · subst hxw
              have hya : y ≠ a := fun h => h1 ⟨rfl, h⟩
              rw [incEdgesAux]
              simp [hxy, hya]
            · by_cases hyw : y = w
              · have hxa : x ≠ a := fun h => h2 ⟨hyw, h⟩
                rw [incEdgesAux]
                simp [hxw, hyw, hxa]
              · rw [incEdgesAux]
                simp [hxw, hyw]
          have hincA : ((incEdgesAux a k ((x, y) :: rest)).filter (fun p => decide (p.2.2 = w))) =
              ((incEdgesAux a (k + 1) rest).filter (fun p => decide (p.2.2 = w))) := by
            by_cases hxa : x = a
            · subst hxa
              have hyw : y ≠ w := fun h => h2 ⟨h, rfl⟩
              rw [incEdgesAux]
              simp [hxy, hyw]
            · by_cases hya : y = a
              · have hxw : x ≠ w := fun h => h1 ⟨h, hya⟩
                rw [incEdgesAux]
                simp [hxa, hya, hxw]
              · rw [incEdgesAux]
                simp [hxa, hya]
          rw [hincW, hincA, ih']

lemma degIn_sdiff_singleton_eq_filter {G : Graph} {X R : Finset ℕ} (hRX : R ⊆ X)
    {a w : ℕ} (haw : a ≠ w) (hwR : w ∈ R) (haR : a ∈ R) :
    G.degIn R w - G.degIn (R \ {a}) w =
      ((incEdgesAux a 0 (G.inside X)).filter fun p => decide (p.2.2 = w)).length ∧
    G.degIn (R \ {a}) w ≤ G.degIn R w := by
  have hwRs : w ∈ R \ {a} := Finset.mem_sdiff.mpr ⟨hwR, fun h => haw (Finset.mem_singleton.mp h).symm⟩
  have h1 := (filter_incEdgesAux_degIn_eq (G := G) hRX hwR).1
  have h2 := (filter_incEdgesAux_degIn_eq (G := G) hRX hwR).2
  have hRsX : R \ {a} ⊆ X := Finset.sdiff_subset.trans hRX
  have h3 := (filter_incEdgesAux_degIn_eq (G := G) hRsX hwRs).1
  have h4 := (filter_incEdgesAux_degIn_eq (G := G) hRsX hwRs).2
  have hlen_split : ((incEdgesAux w 0 (G.inside X)).filter fun p => decide (p.2.2 ∉ R \ {a})).length =
      ((incEdgesAux w 0 (G.inside X)).filter fun p => decide (p.2.2 ∉ R)).length +
      ((incEdgesAux w 0 (G.inside X)).filter fun p => decide (p.2.2 = a)).length := by
    induction (incEdgesAux w 0 (G.inside X)) with
    | nil => simp
    | cons p t ih =>
      by_cases hpR : p.2.2 ∈ R
      · by_cases hpa : p.2.2 = a
        · have h1 : decide (p.2.2 ∉ R \ {a}) = true := by simp [hpa]
          have h2 : decide (p.2.2 ∉ R) = false := by simp [hpR]
          have h3 : decide (p.2.2 = a) = true := by simp [hpa]
          rw [List.filter_cons, List.filter_cons, List.filter_cons, h1, h2, h3]
          dsimp
          omega
        · have h1 : decide (p.2.2 ∉ R \ {a}) = false := by
            simp [hpR, hpa]
          have h2 : decide (p.2.2 ∉ R) = false := by simp [hpR]
          have h3 : decide (p.2.2 = a) = false := by simp [hpa]
          rw [List.filter_cons, List.filter_cons, List.filter_cons, h1, h2, h3]
          dsimp
          exact ih
      · have hpa : p.2.2 ≠ a := fun h => hpR (h ▸ haR)
        have h1 : decide (p.2.2 ∉ R \ {a}) = true := by
          simp [Finset.mem_sdiff, hpR]
        have h2 : decide (p.2.2 ∉ R) = true := by simp [hpR]
        have h3 : decide (p.2.2 = a) = false := by simp [hpa]
        rw [List.filter_cons, List.filter_cons, List.filter_cons, h1, h2, h3]
        dsimp
        omega
  have hsymm_len : ((incEdgesAux w 0 (G.inside X)).filter fun p => decide (p.2.2 = a)).length =
      ((incEdgesAux a 0 (G.inside X)).filter fun p => decide (p.2.2 = w)).length := by
    have hz := sum_filter_edges_between a w haw 0 (G.inside X) (fun _ _ => (1 : ℤ))
    have hl : ∀ (M : List (ℕ × Bool × ℕ)),
        ((M.map fun (_ : ℕ × Bool × ℕ) => (1 : ℤ)).sum) = (M.length : ℤ) := by
      intro M
      induction M with
      | nil => simp
      | cons _ t _ => simp [add_comm]
    rw [hl, hl] at hz
    exact_mod_cast hz
  rw [← hsymm_len]
  omega

/-! ### Relaxed invariant for level-sweep freezing -/

/-- Extended pruning invariant permitting a subset `A ⊆ R` to reach height `H` momentarily
right before `A` is removed from `R`. When `A = ∅`, this is equivalent to `PruningInv`. -/
structure SweepInv (cfg : PruneCfg) (A : Finset ℕ) (s : PruneState) : Prop where
  inR_sub : ∀ u, s.inR u = true → u ∈ cfg.X
  not_inR_B : ∀ b ∈ cfg.B, s.inR b = false
  h_le_H : ∀ u, s.inR u = true → s.h u ≤ cfg.H
  h_lt_H_notA : ∀ u, s.inR u = true → u ∉ A → s.h u < cfg.H
  cur_le : ∀ u, s.inR u = true → s.cur u ≤ (cfg.incEdges u).length
  abs_le : ∀ u, s.inR u = true → s.abs u ≤ cfg.degX u
  h_pos_abs : ∀ u, s.inR u = true → 0 < s.h u → s.abs u = cfg.degX u
  flow_cap : ∀ idx, idx < cfg.edges.length →
    -(cfg.C_cap : ℤ) ≤ s.flow idx ∧ s.flow idx ≤ (cfg.C_cap : ℤ)
  h_edge : ∀ u, s.inR u = true → ∀ p ∈ cfg.incEdges u, s.inR p.2.2 = true →
    flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ) → s.h u ≤ s.h p.2.2 + 1
  cur_no_adm : ∀ u, s.inR u = true → s.abs u = cfg.degX u →
    ∀ j < s.cur u,
      let p := (cfg.incEdges u).getD j (0, false, 0)
      s.inR p.2.2 = false ∨ flowDir s.flow p.1 p.2.1 = (cfg.C_cap : ℤ) ∨ s.h u ≤ s.h p.2.2
  cur_zero_of_abs_lt : ∀ u, s.inR u = true → s.abs u < cfg.degX u → s.cur u = 0
  flow_balance : ∀ u, s.inR u = true →
    (s.ex u : ℤ) + (s.abs u : ℤ) = ((cfg.incEdges u).map (edgeContrib s.inR s.flow cfg.C_cap)).sum
  degR_eq : ∀ u, s.inR u = true → s.degR u = cfg.G.degIn (s.Rset cfg) u
  degR_peel : ∀ u, s.inR u = true → s.degR u < cfg.θ_out_nat → u ∈ s.peelQ
  active_cov : ∀ u, s.inR u = true → 0 < s.ex u → u ∈ s.active
  active_mem_inActive : ∀ u, s.inActive u = true ↔ u ∈ s.active
  active_nodup : s.active.Nodup
  active_sub : ∀ u ∈ s.active, u ∈ cfg.X
  no_ex_isolated : ∀ u, (cfg.incEdges u).length = 0 →
    s.ex u = 0 ∧ s.h u = 0 ∧ u ∉ s.active ∧ u ∉ s.peelQ

lemma pruningInv_iff_sweepInv_empty (cfg : PruneCfg) (s : PruneState) :
    PruningInv cfg s ↔ SweepInv cfg ∅ s := by
  constructor
  · intro h
    exact
      { inR_sub := h.inR_sub
        not_inR_B := h.not_inR_B
        h_le_H := fun u hu => le_of_lt (h.h_lt_H u hu)
        h_lt_H_notA := fun u hu _ => h.h_lt_H u hu
        cur_le := h.cur_le
        abs_le := h.abs_le
        h_pos_abs := h.h_pos_abs
        flow_cap := h.flow_cap
        h_edge := h.h_edge
        cur_no_adm := h.cur_no_adm
        cur_zero_of_abs_lt := h.cur_zero_of_abs_lt
        flow_balance := h.flow_balance
        degR_eq := h.degR_eq
        degR_peel := h.degR_peel
        active_cov := h.active_cov
        active_mem_inActive := h.active_mem_inActive
        active_nodup := h.active_nodup
        active_sub := h.active_sub
        no_ex_isolated := h.no_ex_isolated }
  · intro h
    exact
      { inR_sub := h.inR_sub
        not_inR_B := h.not_inR_B
        h_lt_H := fun u hu => h.h_lt_H_notA u hu (Finset.notMem_empty u)
        cur_le := h.cur_le
        abs_le := h.abs_le
        h_pos_abs := h.h_pos_abs
        flow_cap := h.flow_cap
        h_edge := h.h_edge
        cur_no_adm := h.cur_no_adm
        cur_zero_of_abs_lt := h.cur_zero_of_abs_lt
        flow_balance := h.flow_balance
        degR_eq := h.degR_eq
        degR_peel := h.degR_peel
        active_cov := h.active_cov
        active_mem_inActive := h.active_mem_inActive
        active_nodup := h.active_nodup
        active_sub := h.active_sub
        no_ex_isolated := h.no_ex_isolated }

/-! ### Single-vertex removal from `R` (used by both Peel and Freeze) -/

/-- Updates neighbor `w = p.2.2` when removing `a` across half-edge `p = (idx, dir, w)`. -/
@[expose] def removeEdgeStep (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool)
    (s : PruneState) (p : ℕ × Bool × ℕ) : PruneState :=
  let idx := p.1
  let dir := p.2.1
  let w := p.2.2
  if inR' w then
    let rc := ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat
    let newEx := s.ex w + rc
    let pushAct := (0 < rc) && !(s.inActive w)
    let act' := if pushAct then w :: s.active else s.active
    let inAct' := if pushAct then (fun x => if x = w then true else s.inActive x) else s.inActive
    let oldDeg := s.degR w
    let pushPeel := decide (oldDeg = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat)
    let pQ' := if pushPeel then w :: s.peelQ else s.peelQ
    { s with
      ex := fun x => if x = w then newEx else s.ex x
      degR := fun x => if x = w then oldDeg - 1 else s.degR x
      active := act'
      inActive := inAct'
      peelQ := pQ' }
  else s

/-- Removes vertex `a` from `R` and pushes compensating residual excess and degree updates
to all neighbors of `a` still in `R \ {a}`. Does not alter `steps`. -/
@[expose] def removeOneFromR (cfg : PruneCfg) (a : ℕ) (s : PruneState) : PruneState :=
  let inR' : ℕ → Bool := fun x => if x = a then false else s.inR x
  let s0 := { s with inR := inR' }
  (cfg.incEdges a).foldl (removeEdgeStep cfg s.flow inR') s0

lemma removeEdgeStep_const (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool)
    (s : PruneState) (p : ℕ × Bool × ℕ) :
    let s' := removeEdgeStep cfg flow inR' s p
    s'.inR = s.inR ∧ s'.h = s.h ∧ s'.cur = s.cur ∧ s'.abs = s.abs ∧
    s'.flow = s.flow ∧ s'.steps = s.steps := by
  unfold removeEdgeStep
  dsimp only
  by_cases hw : inR' p.2.2 = true
  · simp [hw]
  · simp [hw]

lemma foldl_removeEdgeStep_const (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool)
    (L : List (ℕ × Bool × ℕ)) (s : PruneState) :
    let s' := L.foldl (removeEdgeStep cfg flow inR') s
    s'.inR = s.inR ∧ s'.h = s.h ∧ s'.cur = s.cur ∧ s'.abs = s.abs ∧
    s'.flow = s.flow ∧ s'.steps = s.steps := by
  induction L generalizing s with
  | nil => simp
  | cons p t ih =>
    simp only [List.foldl_cons]
    have hc := removeEdgeStep_const cfg flow inR' s p
    have iht := ih (removeEdgeStep cfg flow inR' s p)
    exact ⟨iht.1.trans hc.1, iht.2.1.trans hc.2.1, iht.2.2.1.trans hc.2.2.1,
      iht.2.2.2.1.trans hc.2.2.2.1, iht.2.2.2.2.1.trans hc.2.2.2.2.1,
      iht.2.2.2.2.2.trans hc.2.2.2.2.2⟩

lemma foldl_removeEdgeStep_mem_props (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool)
    (L : List (ℕ × Bool × ℕ))
    (hLinR' : ∀ p ∈ L, inR' p.2.2 = true → p.2.2 ∈ cfg.X)
    (hLdeg : ∀ p ∈ L, inR' p.2.2 = true → 0 < (cfg.incEdges p.2.2).length)
    (s : PruneState) (hs_inR : s.inR = inR')
    (hmem_act : ∀ x, s.inActive x = true ↔ x ∈ s.active)
    (hnodup : s.active.Nodup) (hsub : ∀ x ∈ s.active, x ∈ cfg.X)
    (hiso : ∀ x, (cfg.incEdges x).length = 0 →
      s.ex x = 0 ∧ s.h x = 0 ∧ x ∉ s.active ∧ x ∉ s.peelQ) :
    let s' := L.foldl (removeEdgeStep cfg flow inR') s
    (∀ x, s'.ex x = s.ex x + ((L.filter fun p => decide (p.2.2 = x && inR' x)).map
      fun p => ((cfg.C_cap : ℤ) - flowDir flow p.1 p.2.1).toNat).sum) ∧
    (∀ x, s'.degR x = s.degR x - (L.filter fun p => decide (p.2.2 = x && inR' x)).length) ∧
    (∀ x, s'.inActive x = true ↔ x ∈ s'.active) ∧
    s'.active.Nodup ∧
    (∀ x ∈ s'.active, x ∈ cfg.X) ∧
    (∀ x, x ∈ s.active → x ∈ s'.active) ∧
    (∀ x, s.ex x < s'.ex x → x ∈ s'.active) ∧
    (∀ x, x ∈ s.peelQ → x ∈ s'.peelQ) ∧
    (∀ x, s'.degR x < cfg.θ_out_nat → cfg.θ_out_nat ≤ s.degR x → x ∈ s'.peelQ) ∧
    s'.peelQ.length ≤ s.peelQ.length + L.length ∧
    phiActive s' ≤ phiActive s +
      (L.map fun p => if inR' p.2.2 then s.h p.2.2 + 2 else 0).sum ∧
    (∀ x, (cfg.incEdges x).length = 0 →
      s'.ex x = 0 ∧ s'.h x = 0 ∧ x ∉ s'.active ∧ x ∉ s'.peelQ) := by
  induction L generalizing s with
  | nil =>
    simp only [List.foldl_nil, List.filter_nil, List.map_nil, List.sum_nil, add_zero,
      List.length_nil, Nat.sub_zero]
    refine ⟨fun _ => by simp, fun _ => by simp, hmem_act, hnodup, hsub, fun _ h => h,
      fun _ h => absurd h (lt_irrefl _), fun _ h => h,
      fun _ h1 h2 => absurd h1 (not_lt.mpr h2), le_rfl, le_rfl, hiso⟩
  | cons p t ih =>
    rcases p with ⟨idx, dir, w⟩
    have hL1 : ∀ q ∈ t, inR' q.2.2 = true → q.2.2 ∈ cfg.X :=
      fun q hq => hLinR' q (by simp [hq])
    have hL2 : ∀ q ∈ t, inR' q.2.2 = true → 0 < (cfg.incEdges q.2.2).length :=
      fun q hq => hLdeg q (by simp [hq])
    let s1 := removeEdgeStep cfg flow inR' s (idx, dir, w)
    have h1_const := removeEdgeStep_const cfg flow inR' s (idx, dir, w)
    have h1_inR : s1.inR = inR' := h1_const.1.trans hs_inR
    have h1_h : s1.h = s.h := h1_const.2.1
    have h1_mem_act : ∀ x, s1.inActive x = true ↔ x ∈ s1.active := by
      intro x
      dsimp only [s1, removeEdgeStep]
      by_cases hw : inR' w = true
      · simp only [hw, ↓reduceIte]
        by_cases hpush : 0 < ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat ∧ s.inActive w = false
        · have hp : ((0 < ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat) && !(s.inActive w)) = true := by
            simp [hpush.1, hpush.2]
          simp only [hp, ↓reduceIte, List.mem_cons]
          by_cases hx : x = w <;> simp [hx, hmem_act x]
        · have hp : ((0 < ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat) && !(s.inActive w)) = false := by
            by_cases h1 : 0 < ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat <;>
              by_cases h2 : s.inActive w = true <;> simp_all
          simp only [hp, Bool.false_eq_true, ↓reduceIte, hmem_act x]
      · simp [hw, hmem_act x]
    have h1_nodup : s1.active.Nodup := by
      dsimp only [s1, removeEdgeStep]
      by_cases hw : inR' w = true
      · simp only [hw, ↓reduceIte]
        split_ifs with hp
        · have hnot : w ∉ s.active := by
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
            intro hm; exact absurd ((hmem_act w).mpr hm) (by simp [hp.2])
          exact List.nodup_cons.mpr ⟨hnot, hnodup⟩
        · exact hnodup
      · simp [hw, hnodup]
    have h1_sub : ∀ x ∈ s1.active, x ∈ cfg.X := by
      intro x hx
      dsimp only [s1, removeEdgeStep] at hx
      by_cases hw : inR' w = true
      · simp only [hw, ↓reduceIte] at hx
        split_ifs at hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hLinR' (idx, dir, x) (by simp) hw
          · exact hsub x hx
        · exact hsub x hx
      · simp [hw] at hx
        exact hsub x hx
    have h1_iso : ∀ x, (cfg.incEdges x).length = 0 →
        s1.ex x = 0 ∧ s1.h x = 0 ∧ x ∉ s1.active ∧ x ∉ s1.peelQ := by
      intro x hxlen
      obtain ⟨he0, hh0, hna, hnp⟩ := hiso x hxlen
      dsimp only [s1, removeEdgeStep]
      by_cases hw : inR' w = true
      · have hxw : x ≠ w := by
          intro heq
          subst heq
          have hpos := hLdeg (idx, dir, x) (by simp) hw
          change 0 < (cfg.incEdges x).length at hpos
          omega
        simp only [hw, ↓reduceIte]
        split_ifs <;> first | contradiction | simp [he0, hh0, hna, hnp, hxw]
      · simp [hw, he0, hh0, hna, hnp]
    obtain ⟨ih_ex, ih_deg, ih_mem, ih_nd, ih_sub, ih_asub, ih_ex_act, ih_psub,
        ih_deg_peel, ih_plen, ih_phi, ih_iso⟩ :=
      ih hL1 hL2 s1 h1_inR h1_mem_act h1_nodup h1_sub h1_iso
    simp only [List.foldl_cons]
    have hfold_eq : t.foldl (removeEdgeStep cfg flow inR') (removeEdgeStep cfg flow inR' s (idx, dir, w)) =
        t.foldl (removeEdgeStep cfg flow inR') s1 := rfl
    rw [hfold_eq]
    refine ⟨?_, ?_, ih_mem, ih_nd, ih_sub, ?_, ?_, ?_, ?_, ?_, ?_, ih_iso⟩
    · intro x
      rw [ih_ex x, List.filter_cons]
      dsimp only [s1, removeEdgeStep]
      by_cases hwx : w = x ∧ inR' x = true
      · obtain ⟨rfl, hx⟩ := hwx
        simp only [hx, ↓reduceIte, decide_true, Bool.and_self, List.map_cons, List.sum_cons]
        omega
      · have hdf : decide (w = x && inR' x) = false := by
          simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
          tauto
        simp only [hdf, Bool.false_eq_true, ↓reduceIte]
        by_cases hw : inR' w = true
        · have hne : x ≠ w := fun h => hwx ⟨h.symm, h ▸ hw⟩
          simp [hw, hne]
        · simp [hw]
    · intro x
      rw [ih_deg x, List.filter_cons]
      dsimp only [s1, removeEdgeStep]
      by_cases hwx : w = x ∧ inR' x = true
      · obtain ⟨rfl, hx⟩ := hwx
        simp only [hx, ↓reduceIte, decide_true, Bool.and_self, List.length_cons]
        omega
      · have hdf : decide (w = x && inR' x) = false := by
          simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
          tauto
        simp only [hdf, Bool.false_eq_true, ↓reduceIte]
        by_cases hw : inR' w = true
        · have hne : x ≠ w := fun h => hwx ⟨h.symm, h ▸ hw⟩
          simp [hw, hne]
        · simp [hw]
    · intro x hx
      apply ih_asub
      dsimp only [s1, removeEdgeStep]
      split_ifs <;> simp [hx]
    · intro x hx
      by_cases hlt1 : s1.ex x < (t.foldl (removeEdgeStep cfg flow inR') s1).ex x
      · exact ih_ex_act x hlt1
      · have hgt : s.ex x < s1.ex x := by omega
        apply ih_asub
        dsimp only [s1, removeEdgeStep] at hgt ⊢
        by_cases hw : inR' w = true
        · simp only [hw, ↓reduceIte] at hgt ⊢
          have hxw : x = w := by by_contra hne; simp [hne] at hgt
          subst hxw
          have hrc : 0 < ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat := by
            simp only [↓reduceIte] at hgt; omega
          by_cases hia : s.inActive x = true
          · simp only [hrc, hia, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact (hmem_act x).mp hia
          · have hp : ((0 < ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat) && !(s.inActive x)) = true := by
              simp [hrc, hia]
            simp only [hp, ↓reduceIte, List.mem_cons, true_or]
        · simp [hw] at hgt
    · intro x hx
      apply ih_psub
      dsimp only [s1, removeEdgeStep]
      split_ifs <;> simp [hx]
    · intro x hxlt hxge
      by_cases h1lt : s1.degR x < cfg.θ_out_nat
      · apply ih_psub
        dsimp only [s1, removeEdgeStep] at h1lt ⊢
        by_cases hw : inR' w = true
        · simp only [hw, ↓reduceIte] at h1lt ⊢
          have hxw : x = w := by by_contra hne; simp [hne] at h1lt; omega
          subst hxw
          simp only [↓reduceIte] at h1lt
          have heq : s.degR x = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat := by omega
          simp [heq]
        · simp [hw] at h1lt; omega
      · exact ih_deg_peel x hxlt (by omega)
    · have hp1 : s1.peelQ.length ≤ s.peelQ.length + 1 := by
        dsimp only [s1, removeEdgeStep]
        by_cases hw : inR' w = true
        · simp only [hw, ↓reduceIte]; split_ifs <;> simp
        · simp [hw]
      simp only [List.length_cons]
      have hlen_t : (t.foldl (removeEdgeStep cfg flow inR') s1).peelQ.length ≤ s1.peelQ.length + t.length :=
        ih_plen
      exact le_trans hlen_t (by omega)
    · have hphi1 : phiActive s1 ≤ phiActive s + (if inR' w then s.h w + 2 else 0) := by
        dsimp only [s1, removeEdgeStep]
        by_cases hw : inR' w = true
        · simp only [hw, ↓reduceIte]
          by_cases hp : ((0 < ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat) && !(s.inActive w)) = true
          · simp only [hp, ↓reduceIte]
            unfold phiActive
            simp only [List.map_cons, List.sum_cons]
            have hmap : (s.active.map fun u => if s.inR u = true then s.h u + 2 else 2).sum =
                phiActive s := rfl
            have hsw : (if s.inR w = true then s.h w + 2 else 2) ≤ s.h w + 2 := by
              split_ifs <;> omega
            rw [hmap]
            omega
          · have hpf : ((0 < ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat) && !(s.inActive w)) = false :=
              Bool.eq_false_iff.mpr hp
            simp only [hpf, Bool.false_eq_true, ↓reduceIte]
            have hpeq : phiActive
                { s with
                  ex := fun x => if x = w then s.ex w + ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat else s.ex x
                  degR := fun x => if x = w then s.degR w - 1 else s.degR x
                  peelQ := if decide (s.degR w = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat) then w :: s.peelQ else s.peelQ } =
                phiActive s := rfl
            change phiActive { s with
              ex := fun x => if x = w then s.ex w + ((cfg.C_cap : ℤ) - flowDir flow idx dir).toNat else s.ex x
              degR := fun x => if x = w then s.degR w - 1 else s.degR x
              peelQ := if decide (s.degR w = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat) then w :: s.peelQ else s.peelQ } ≤
              phiActive s + (s.h w + 2)
            rw [hpeq]
            omega
        · simp [hw]
      simp only [List.map_cons, List.sum_cons, h1_h] at ih_phi ⊢
      omega

/-- `removeOneFromR cfg a s` preserves `SweepInv` (removing `a` from `A` as well if desired). -/
lemma removeOneFromR_inv {cfg : PruneCfg} (_hcfg : cfg.Valid) {A : Finset ℕ} {s : PruneState}
    (hinv : SweepInv cfg A s) {a : ℕ} (haR : s.inR a = true) :
    let s' := removeOneFromR cfg a s
    SweepInv cfg (A \ {a}) s' ∧
    (∀ x, x ∈ s.active → x ∈ s'.active) ∧
    (∀ x, x ∈ s.peelQ → x ∈ s'.peelQ) ∧
    s'.peelQ.length ≤ s.peelQ.length + (cfg.incEdges a).length ∧
    phiActive s' ≤ phiActive s +
      ((cfg.incEdges a).map fun p => if p.2.2 ≠ a ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0).sum ∧
    s'.h = s.h ∧ s'.cur = s.cur ∧ s'.abs = s.abs ∧ s'.flow = s.flow ∧ s'.steps = s.steps := by
  dsimp only [removeOneFromR]
  set inR' : ℕ → Bool := fun x => if x = a then false else s.inR x
  set s0 : PruneState := { s with inR := inR' }
  have hLinR' : ∀ p ∈ cfg.incEdges a, inR' p.2.2 = true → p.2.2 ∈ cfg.X := by
    intro p hp _
    exact (incEdges_mem_sub hp).2
  have hLdeg : ∀ p ∈ cfg.incEdges a, inR' p.2.2 = true → 0 < (cfg.incEdges p.2.2).length := by
    intro p hp _
    have hs := incEdges_symm hp
    exact List.length_pos_of_mem hs
  have hiso0 : ∀ x, (cfg.incEdges x).length = 0 →
      s0.ex x = 0 ∧ s0.h x = 0 ∧ x ∉ s0.active ∧ x ∉ s0.peelQ := by
    intro x hx
    exact hinv.no_ex_isolated x hx
  obtain ⟨hex, hdeg, hmem_act, hnd_act, hsub_act, hasub_act, hex_act, hpsub, hdeg_peel,
      hplen, hphi, hiso⟩ :=
    foldl_removeEdgeStep_mem_props cfg s.flow inR' (cfg.incEdges a) hLinR' hLdeg
      s0 rfl hinv.active_mem_inActive hinv.active_nodup hinv.active_sub hiso0
  obtain ⟨hc_inR, hc_h, hc_cur, hc_abs, hc_flow, hc_steps⟩ :=
    foldl_removeEdgeStep_const cfg s.flow inR' (cfg.incEdges a) s0
  set s' := (cfg.incEdges a).foldl (removeEdgeStep cfg s.flow inR') s0
  have hc_inR0 : s'.inR = inR' := hc_inR
  have hc_h0 : s'.h = s.h := hc_h
  have hc_cur0 : s'.cur = s.cur := hc_cur
  have hc_abs0 : s'.abs = s.abs := hc_abs
  have hc_flow0 : s'.flow = s.flow := hc_flow
  have hc_steps0 : s'.steps = s.steps := hc_steps
  have hinR'_sub : ∀ u, s'.inR u = true → u ∈ cfg.X := by
    intro u hu
    rw [hc_inR0] at hu
    by_cases hua : u = a
    · simp only [inR', hua, ↓reduceIte, Bool.false_eq_true] at hu
    · simp only [inR', hua, ↓reduceIte] at hu
      exact hinv.inR_sub u hu
  have hinR'_imp : ∀ u, s'.inR u = true → s.inR u = true ∧ u ≠ a := by
    intro u hu
    rw [hc_inR0] at hu
    by_cases hua : u = a
    · simp only [inR', hua, ↓reduceIte, Bool.false_eq_true] at hu
    · simp only [inR', hua, ↓reduceIte] at hu
      exact ⟨hu, hua⟩
  have hRset' : s'.Rset cfg = s.Rset cfg \ {a} := by
    ext u
    simp only [PruneState.Rset, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton, hc_inR0]
    by_cases hua : u = a <;> simp [inR', hua]
  have hflow_bal : ∀ u, s'.inR u = true →
      (s'.ex u : ℤ) + (s'.abs u : ℤ) = ((cfg.incEdges u).map (edgeContrib s'.inR s'.flow cfg.C_cap)).sum := by
    intro u hu
    obtain ⟨huR, hua⟩ := hinR'_imp u hu
    have hbal := hinv.flow_balance u huR
    have hex_u := hex u
    have hu' : inR' u = true := by rw [← hc_inR0]; exact hu
    have hfilter_eq : (cfg.incEdges a |>.filter fun p => decide (p.2.2 = u && inR' u)) =
        (cfg.incEdges a |>.filter fun p => decide (p.2.2 = u)) := by
      congr 1; ext p; simp [hu']
    rw [hfilter_eq] at hex_u
    have hcontrib : ((cfg.incEdges u).map (edgeContrib s'.inR s'.flow cfg.C_cap)).sum =
        ((cfg.incEdges u).map (edgeContrib s.inR s.flow cfg.C_cap)).sum +
        ((cfg.incEdges u |>.filter fun q => decide (q.2.2 = a)).map
          fun q => (cfg.C_cap : ℤ) + flowDir s.flow q.1 q.2.1).sum := by
      rw [hc_flow0]
      clear hex_u hfilter_eq hbal
      induction (cfg.incEdges u) with
      | nil => simp
      | cons q t ihq =>
        rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.filter_cons, ihq]
        by_cases hqa : q.2.2 = a
        · have hin1 : edgeContrib s'.inR s.flow cfg.C_cap q = (cfg.C_cap : ℤ) := by
            simp [edgeContrib, hc_inR0, inR', hqa]
          have hin2 : edgeContrib s.inR s.flow cfg.C_cap q = -(flowDir s.flow q.1 q.2.1) := by
            simp [edgeContrib, hqa, haR]
          simp only [hqa, decide_true, ↓reduceIte, List.map_cons, List.sum_cons, hin1, hin2]
          ring
        · have hin12 : edgeContrib s'.inR s.flow cfg.C_cap q = edgeContrib s.inR s.flow cfg.C_cap q := by
            simp [edgeContrib, hc_inR0, inR', hqa]
          rw [hin12]
          simp only [hqa, decide_false, Bool.false_eq_true, ↓reduceIte]
          ring
    have hsymm : ((cfg.incEdges u |>.filter fun q => decide (q.2.2 = a)).map
        fun q => (cfg.C_cap : ℤ) + flowDir s.flow q.1 q.2.1).sum =
        ((cfg.incEdges a |>.filter fun p => decide (p.2.2 = u)).map
          fun p => (cfg.C_cap : ℤ) - flowDir s.flow p.1 p.2.1).sum := by
      have hz := sum_filter_edges_between a u hua.symm 0 cfg.edges
        (fun idx dir => (cfg.C_cap : ℤ) - flowDir s.flow idx dir)
      have hmap1 : ((cfg.incEdges u |>.filter fun q => decide (q.2.2 = a)).map
          fun q => (cfg.C_cap : ℤ) + flowDir s.flow q.1 q.2.1) =
          ((incEdgesAux u 0 cfg.edges |>.filter fun q => decide (q.2.2 = a)).map
            fun q => (cfg.C_cap : ℤ) - flowDir s.flow q.1 (!q.2.1)) := by
        apply List.map_congr_left
        intro q _
        rw [flowDir_not]
        ring
      rw [hmap1]
      exact hz
    have hnonneg : (((cfg.incEdges a |>.filter fun p => decide (p.2.2 = u)).map
        fun p => ((cfg.C_cap : ℤ) - flowDir s.flow p.1 p.2.1).toNat).sum : ℤ) =
        ((cfg.incEdges a |>.filter fun p => decide (p.2.2 = u)).map
          fun p => (cfg.C_cap : ℤ) - flowDir s.flow p.1 p.2.1).sum := by
      clear hcontrib hsymm hex_u
      have hcap : ∀ p ∈ cfg.incEdges a, 0 ≤ (cfg.C_cap : ℤ) - flowDir s.flow p.1 p.2.1 := by
        intro p hp
        have hidx := (incEdgesAux_idx_ge hp).2
        have hc := hinv.flow_cap p.1 (by simpa using hidx)
        cases p.2.1 <;> simp [flowDir] <;> linarith
      suffices hL : ∀ (L : List (ℕ × Bool × ℕ)),
          (∀ p ∈ L, 0 ≤ (cfg.C_cap : ℤ) - flowDir s.flow p.1 p.2.1) →
          ((L.map fun p => ((cfg.C_cap : ℤ) - flowDir s.flow p.1 p.2.1).toNat).sum : ℤ) =
            (L.map fun p => (cfg.C_cap : ℤ) - flowDir s.flow p.1 p.2.1).sum by
        exact hL _ fun p hp => hcap p (List.mem_filter.mp hp).1
      intro L hL
      induction L with
      | nil => simp
      | cons p t ihL =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        have hp0 := hL p (by simp)
        have ht0 := ihL fun q hq => hL q (by simp [hq])
        omega
    rw [hc_abs0]
    dsimp only [s0] at hex_u hnonneg ⊢
    rw [hcontrib, hsymm, ← hbal, hex_u, Nat.cast_add, hnonneg]
    ring
  have hdegR_eq : ∀ u, s'.inR u = true → s'.degR u = cfg.G.degIn (s'.Rset cfg) u := by
    intro u hu
    obtain ⟨huR, hua⟩ := hinR'_imp u hu
    have huRs : u ∈ s.Rset cfg := (PruneState.mem_Rset cfg s hinv.inR_sub).mpr huR
    have haRs : a ∈ s.Rset cfg := (PruneState.mem_Rset cfg s hinv.inR_sub).mpr haR
    have hRX : s.Rset cfg ⊆ cfg.X := Finset.filter_subset _ _
    have hdiff := (degIn_sdiff_singleton_eq_filter (G := cfg.G) hRX (Ne.symm hua) huRs haRs).1
    have hle := (degIn_sdiff_singleton_eq_filter (G := cfg.G) hRX (Ne.symm hua) huRs haRs).2
    have hdeg_s := hinv.degR_eq u huR
    have hdeg_s' := hdeg u
    have hu' : inR' u = true := by rw [← hc_inR0]; exact hu
    have hfilter_eq : (cfg.incEdges a |>.filter fun p => decide (p.2.2 = u && inR' u)) =
        (cfg.incEdges a |>.filter fun p => decide (p.2.2 = u)) := by
      congr 1; ext p; simp [hu']
    rw [hfilter_eq] at hdeg_s'
    dsimp only [s0] at hdeg_s'
    rw [hRset']
    change cfg.G.degIn (s.Rset cfg) u - cfg.G.degIn (s.Rset cfg \ {a}) u =
      ((cfg.incEdges a).filter fun p => decide (p.2.2 = u)).length at hdiff
    change s'.degR u = cfg.G.degIn (s.Rset cfg \ {a}) u
    rw [hdeg_s', hdeg_s]
    omega
  refine ⟨?_, hasub_act, hpsub, hplen, ?_, hc_h0, hc_cur0, hc_abs0, hc_flow0, hc_steps0⟩
  · exact
      { inR_sub := hinR'_sub
        not_inR_B := fun b hb => by
          rw [hc_inR0]
          by_cases hba : b = a <;> simp [inR', hba, hinv.not_inR_B b hb]
        h_le_H := fun u hu => by rw [hc_h0]; exact hinv.h_le_H u (hinR'_imp u hu).1
        h_lt_H_notA := fun u hu hnot => by
          rw [hc_h0]
          exact hinv.h_lt_H_notA u (hinR'_imp u hu).1
            (fun haA => hnot (Finset.mem_sdiff.mpr ⟨haA, by simpa using (hinR'_imp u hu).2⟩))
        cur_le := fun u hu => by rw [hc_cur0]; exact hinv.cur_le u (hinR'_imp u hu).1
        abs_le := fun u hu => by rw [hc_abs0]; exact hinv.abs_le u (hinR'_imp u hu).1
        h_pos_abs := fun u hu hpos => by
          rw [hc_abs0]
          rw [hc_h0] at hpos
          exact hinv.h_pos_abs u (hinR'_imp u hu).1 hpos
        flow_cap := fun idx hi => by rw [hc_flow0]; exact hinv.flow_cap idx hi
        h_edge := fun u hu p hp hw hlt => by
          rw [hc_h0]
          rw [hc_flow0] at hlt
          exact hinv.h_edge u (hinR'_imp u hu).1 p hp (hinR'_imp p.2.2 hw).1 hlt
        cur_no_adm := fun u hu habs j hj => by
          rw [hc_cur0] at hj
          rw [hc_abs0] at habs
          rcases hinv.cur_no_adm u (hinR'_imp u hu).1 habs j hj with h1 | h2 | h3
          · left; rw [hc_inR0]; dsimp only [inR']; split_ifs
            · rfl
            · exact h1
          · right; left; rw [hc_flow0]; exact h2
          · right; right; rw [hc_h0]; exact h3
        cur_zero_of_abs_lt := fun u hu hlt => by
          rw [hc_cur0]; rw [hc_abs0] at hlt
          exact hinv.cur_zero_of_abs_lt u (hinR'_imp u hu).1 hlt
        flow_balance := hflow_bal
        degR_eq := hdegR_eq
        degR_peel := fun u hu hlt => by
          by_cases hprev : s.degR u < cfg.θ_out_nat
          · exact hpsub u (hinv.degR_peel u (hinR'_imp u hu).1 hprev)
          · have hdp := hdeg_peel u hlt
            change cfg.θ_out_nat ≤ s.degR u → u ∈ s'.peelQ at hdp
            exact hdp (by omega)
        active_cov := fun u hu hpos => by
          obtain ⟨huR, _⟩ := hinR'_imp u hu
          by_cases h0 : s.ex u = 0
          · exact hex_act u (by dsimp only [s0]; omega)
          · exact hasub_act u (hinv.active_cov u huR (by omega))
        active_mem_inActive := hmem_act
        active_nodup := hnd_act
        active_sub := hsub_act
        no_ex_isolated := hiso }
  · have hphi' : phiActive s' ≤ phiActive s0 +
        ((cfg.incEdges a).map fun p => if inR' p.2.2 then s.h p.2.2 + 2 else 0).sum := hphi
    have hphi0 : phiActive s0 ≤ phiActive s := by
      unfold phiActive
      apply sum_map_le_sum_map
      intro u _
      dsimp only [s0, inR']
      by_cases h1 : u = a <;> by_cases h2 : s.inR u = true <;> simp [h1, h2]
      all_goals (split_ifs; omega)
    have hmap_eq : ((cfg.incEdges a).map fun p => if inR' p.2.2 then s.h p.2.2 + 2 else 0) =
        ((cfg.incEdges a).map fun p => if p.2.2 ≠ a ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0) := by
      apply List.map_congr_left
      intro p _
      by_cases ha : p.2.2 = a <;> by_cases hr : s.inR p.2.2 = true <;> simp [inR', ha, hr]
    rw [hmap_eq] at hphi'
    omega

lemma removeOneFromR_inR (cfg : PruneCfg) (a : ℕ) (s : PruneState) (x : ℕ) :
    (removeOneFromR cfg a s).inR x = if x = a then false else s.inR x := by
  unfold removeOneFromR
  rw [(foldl_removeEdgeStep_const cfg s.flow (fun x => if x = a then false else s.inR x)
    (cfg.incEdges a) { s with inR := fun x => if x = a then false else s.inR x }).1]

end MinCostFlow.Expander
