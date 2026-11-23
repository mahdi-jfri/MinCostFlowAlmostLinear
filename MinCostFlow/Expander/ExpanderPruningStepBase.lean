module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.Basic
public import MinCostFlow.Expander.GraphHelpers
public import MinCostFlow.Expander.PruningState
public import MinCostFlow.Expander.PruningStep

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Expander Pruning Push-Relabel Step and Level-Sweep Freeze

Implements the micro-steps of push-relabel + low-degree peeling expander pruning:
- `peelStep`: removes a low-degree vertex from `R`, preserving invariants and cut-volume charge;
- `absorbStep`, `pushFlowStep`, `advanceCurStep`, `relabelStep`: standard push-relabel steps;
- `freezeStep`: selects a good sweep level `lvl ∈ {1, ..., H - 1}` via `pickLevel` and removes
  `A = {x ∈ R | h'(x) ≥ lvl + 1}` from `R` using `removeOneFromR`;
- `pruneStep`: combines all micro-steps into a deterministic transition preserving `PruningInv`,
  strictly decreasing `pot`, keeping `steps + pot` non-increasing, and keeping
  `volPminusB + 2 * C_cap * cutPR` non-increasing.
-/

namespace MinCostFlow.Expander

open Classical

public section

/-! ### Helper lemmas for lists, cut counts, and incident degrees -/

lemma list_mem_exists_getD {α : Type*} (d : α) :
    ∀ (L : List α) {p : α}, p ∈ L → ∃ j, j < L.length ∧ L.getD j d = p
  | [], _, hp => by simp at hp
  | x :: xs, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨0, by simp, rfl⟩
    · rcases list_mem_exists_getD d xs hp' with ⟨j, hj, hget⟩
      exact ⟨j + 1, by simp; omega, by simpa using hget⟩

lemma list_getD_mem {α : Type*} (d : α) :
    ∀ (L : List α) {j : ℕ}, j < L.length → L.getD j d ∈ L
  | [], _, hj => by simp at hj
  | x :: _, 0, _ => by simp
  | _ :: xs, j + 1, hj => by
    simp only [List.length_cons] at hj
    exact List.mem_cons_of_mem _ (list_getD_mem d xs (by omega))

private lemma incEdgesAux_length_le_sum (u : ℕ) :
    ∀ (k : ℕ) (L : List (ℕ × ℕ)),
      (incEdgesAux u k L).length ≤
        (L.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum
  | _, [] => by simp [incEdgesAux]
  | k, (a, b) :: rest => by
    have ih := incEdgesAux_length_le_sum u (k + 1) rest
    simp only [incEdgesAux, List.map_cons, List.sum_cons]
    split_ifs <;> simp at * <;> omega

lemma incEdges_length_le_degX (cfg : PruneCfg) (u : ℕ) :
    (cfg.incEdges u).length ≤ cfg.degX u := by
  unfold PruneCfg.incEdges PruneCfg.degX PruneCfg.edges
  rw [degIn_eq_sum_map]
  exact incEdgesAux_length_le_sum u 0 (cfg.G.inside cfg.X)

private lemma incEdgesAux_mono_mem (u : ℕ) {p : ℕ × Bool × ℕ} :
    ∀ (k : ℕ) (L : List (ℕ × ℕ)) (e : ℕ × ℕ),
      p ∈ incEdgesAux u (k + 1) L → p ∈ incEdgesAux u k (e :: L)
  | k, L, (a, b), hp => by
    simp only [incEdgesAux]
    split_ifs <;> simp [hp]

private lemma list_getElem?_mem_incEdgesAux :
    ∀ (L : List (ℕ × ℕ)) (k j a b : ℕ),
      L[j]? = some (a, b) → a ≠ b →
      (k + j, false, b) ∈ incEdgesAux a k L ∧
        (k + j, true, a) ∈ incEdgesAux b k L ∧
        j < L.length
  | [], _, _, _, _, hj, _ => by simp at hj
  | (x, y) :: rest, k, 0, a, b, hj, hab => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj
    rcases hj with ⟨rfl, rfl⟩
    have hne : y ≠ x := Ne.symm hab
    refine ⟨?_, ?_, by simp⟩
    · simp [incEdgesAux, hab]
    · simp [incEdgesAux, hab]
  | (x, y) :: rest, k, j + 1, a, b, hj, hab => by
    simp only [List.getElem?_cons_succ] at hj
    obtain ⟨h1, h2, h3⟩ := list_getElem?_mem_incEdgesAux rest (k + 1) j a b hj hab
    have hk : k + (j + 1) = (k + 1) + j := by omega
    rw [hk]
    exact ⟨incEdgesAux_mono_mem a k rest (x, y) h1,
      incEdgesAux_mono_mem b k rest (x, y) h2, by simp; omega⟩

lemma edges_getElem?_mem_incEdges (cfg : PruneCfg) {j a b : ℕ}
    (hj : cfg.edges[j]? = some (a, b)) (hab : a ≠ b) :
    (j, false, b) ∈ cfg.incEdges a ∧ (j, true, a) ∈ cfg.incEdges b ∧ j < cfg.edges.length := by
  simpa [PruneCfg.incEdges] using list_getElem?_mem_incEdgesAux cfg.edges 0 j a b hj hab

/-! ### Cut and pruned-volume observables -/

/-- Number of edges in `cfg.edges = G.inside X` crossing between `R` and `X \ R`. -/
@[expose] def cutPR (cfg : PruneCfg) (s : PruneState) : ℕ :=
  (cfg.edges.filter fun e => decide (s.inR e.1 ≠ s.inR e.2)).length

/-- Volume in `G[X]` of pruned vertices outside `B`, i.e., `G.volIn X (P \ B)`. -/
@[expose] def volPminusB (cfg : PruneCfg) (s : PruneState) : ℕ :=
  ∑ u ∈ cfg.X, if !s.inR u && decide (u ∉ cfg.B) then cfg.degX u else 0

lemma filter_cons_length {α : Type*} (p : α → Bool) (x : α) (xs : List α) :
    (List.filter p (x :: xs)).length = (if p x then 1 else 0) + (xs.filter p).length := by
  cases hp : p x <;> simp [hp, Nat.add_comm]

private lemma cut_change_removeOne (inR : ℕ → Bool) (a : ℕ) (haR : inR a = true) :
    ∀ (k : ℕ) (L : List (ℕ × ℕ)),
      let inR' := fun x => if x = a then false else inR x
      ((L.filter fun e => decide (inR' e.1 ≠ inR' e.2)).length : ℤ) -
        ((L.filter fun e => decide (inR e.1 ≠ inR e.2)).length : ℤ) =
        (((incEdgesAux a k L).filter fun p => inR p.2.2).length : ℤ) -
          (((incEdgesAux a k L).filter fun p => !inR p.2.2).length : ℤ)
  | _, [] => by simp [incEdgesAux]
  | k, (u, v) :: rest => by
    have ih := cut_change_removeOne inR a haR (k + 1) rest
    dsimp only at ih ⊢
    by_cases huv : u = v
    · subst huv
      have hinc : incEdgesAux a k ((u, u) :: rest) = incEdgesAux a (k + 1) rest := by
        simp [incEdgesAux]
      rw [filter_cons_length, filter_cons_length, hinc]
      push_cast
      conv_lhs =>
        arg 1; arg 1; simp
      conv_lhs =>
        arg 2; arg 1; simp
      linarith
    · by_cases hua : u = a
      · subst hua
        have hva : v ≠ u := Ne.symm huv
        have hinc : incEdgesAux u k ((u, v) :: rest) = (k, false, v) :: incEdgesAux u (k + 1) rest := by
          simp [incEdgesAux, huv]
        rw [filter_cons_length, filter_cons_length, hinc, filter_cons_length, filter_cons_length]
        push_cast
        by_cases hvR : inR v = true
        · conv_lhs => arg 1; arg 1; simp [hva, hvR]
          conv_lhs => arg 2; arg 1; simp [haR, hvR]
          conv_rhs => arg 1; arg 1; simp [hvR]
          conv_rhs => arg 2; arg 1; simp [hvR]
          linarith
        · have hvF : inR v = false := Bool.eq_false_iff.mpr hvR
          conv_lhs => arg 1; arg 1; simp [hva, hvF]
          conv_lhs => arg 2; arg 1; simp [haR, hvF]
          conv_rhs => arg 1; arg 1; simp [hvF]
          conv_rhs => arg 2; arg 1; simp [hvF]
          linarith
      · by_cases hva : v = a
        · subst hva
          have hinc : incEdgesAux v k ((u, v) :: rest) = (k, true, u) :: incEdgesAux v (k + 1) rest := by
            simp [incEdgesAux, huv]
          rw [filter_cons_length, filter_cons_length, hinc, filter_cons_length, filter_cons_length]
          push_cast
          by_cases huR : inR u = true
          · conv_lhs => arg 1; arg 1; simp [hua, huR]
            conv_lhs => arg 2; arg 1; simp [haR, huR]
            conv_rhs => arg 1; arg 1; simp [huR]
            conv_rhs => arg 2; arg 1; simp [huR]
            linarith
          · have huF : inR u = false := Bool.eq_false_iff.mpr huR
            conv_lhs => arg 1; arg 1; simp [hua, huF]
            conv_lhs => arg 2; arg 1; simp [haR, huF]
            conv_rhs => arg 1; arg 1; simp [huF]
            conv_rhs => arg 2; arg 1; simp [huF]
            linarith
        · have hinc : incEdgesAux a k ((u, v) :: rest) = incEdgesAux a (k + 1) rest := by
            simp [incEdgesAux, huv, hua, hva]
          rw [filter_cons_length, filter_cons_length, hinc]
          push_cast
          conv_lhs => arg 1; arg 1; simp [hua, hva]
          conv_lhs => arg 2; arg 1; simp
          linarith

private lemma volPminusB_removeOne {cfg : PruneCfg} {s s' : PruneState} {a : ℕ}
    (haX : a ∈ cfg.X) (haB : a ∉ cfg.B) (haR : s.inR a = true)
    (hinR : ∀ x, s'.inR x = if x = a then false else s.inR x) :
    volPminusB cfg s' = volPminusB cfg s + cfg.degX a := by
  unfold volPminusB
  rw [← Finset.add_sum_erase _ _ haX, ← Finset.add_sum_erase cfg.X _ haX]
  have ha1 : (if !s'.inR a && decide (a ∉ cfg.B) then cfg.degX a else 0) = cfg.degX a := by
    simp [hinR a, haB]
  have ha2 : (if !s.inR a && decide (a ∉ cfg.B) then cfg.degX a else 0) = 0 := by
    simp [haR]
  have hrest : ∑ x ∈ cfg.X.erase a, (if !s'.inR x && decide (x ∉ cfg.B) then cfg.degX x else 0) =
      ∑ x ∈ cfg.X.erase a, (if !s.inR x && decide (x ∉ cfg.B) then cfg.degX x else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ a := (Finset.mem_erase.mp hx).1
    simp [hinR x, hne]
  rw [ha1, ha2, hrest]
  omega

private lemma volR_removeOne {cfg : PruneCfg} {s s' : PruneState} {a : ℕ}
    (haX : a ∈ cfg.X) (haR : s.inR a = true)
    (hinR : ∀ x, s'.inR x = if x = a then false else s.inR x) :
    volR cfg s' + (cfg.incEdges a).length = volR cfg s := by
  unfold volR
  rw [← Finset.add_sum_erase _ _ haX, ← Finset.add_sum_erase cfg.X _ haX]
  have ha1 : (if s'.inR a then (cfg.incEdges a).length else 0) = 0 := by simp [hinR a]
  have ha2 : (if s.inR a then (cfg.incEdges a).length else 0) = (cfg.incEdges a).length := by
    simp [haR]
  have hrest : ∑ x ∈ cfg.X.erase a, (if s'.inR x then (cfg.incEdges x).length else 0) =
      ∑ x ∈ cfg.X.erase a, (if s.inR x then (cfg.incEdges x).length else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ a := (Finset.mem_erase.mp hx).1
    simp [hinR x, hne]
  rw [ha1, ha2, hrest]
  omega

private lemma relabelCurRem_removeOne_le {cfg : PruneCfg} {s s' : PruneState} {a : ℕ}
    (hinR : ∀ x, s'.inR x = if x = a then false else s.inR x)
    (hh : s'.h = s.h) (hcur : s'.cur = s.cur) :
    relabelCurRem cfg s' ≤ relabelCurRem cfg s := by
  unfold relabelCurRem
  apply Finset.sum_le_sum
  intro x _
  rw [hh, hcur, hinR x]
  by_cases hxa : x = a
  · simp [hxa]
  · simp [hxa]

private lemma sumAbsRem_removeOne_le {cfg : PruneCfg} {s s' : PruneState} {a : ℕ}
    (hinR : ∀ x, s'.inR x = if x = a then false else s.inR x)
    (habs : s'.abs = s.abs) :
    sumAbsRem cfg s' ≤ sumAbsRem cfg s := by
  unfold sumAbsRem
  apply Finset.sum_le_sum
  intro x _
  rw [habs, hinR x]
  by_cases hxa : x = a
  · simp [hxa]
  · simp [hxa]

private lemma sum_map_le_const_mul {α : Type*} (L : List α) (f g : α → ℕ) (c : ℕ)
    (hfg : ∀ x ∈ L, f x ≤ g x * c) :
    (L.map f).sum ≤ (L.map g).sum * c := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := hfg x (by simp)
    have hxs := ih fun y hy => hfg y (by simp [hy])
    linarith [show ((List.map g xs).sum + g x) * c = g x * c + (List.map g xs).sum * c by ring,
      show (g x + (List.map g xs).sum) * c = g x * c + (List.map g xs).sum * c by ring]

lemma foldl_removeOneFromR_inv {cfg : PruneCfg} (hcfg : cfg.Valid) :
    ∀ (L : List ℕ) (A : Finset ℕ) (s : PruneState),
      L.Nodup →
      (∀ a ∈ L, s.inR a = true) →
      SweepInv cfg A s →
      (∀ x, s.inR x = true → s.h x < cfg.H ∨ L.head? = some x) →
      let s' := L.foldl (fun st a => removeOneFromR cfg a st) s
      SweepInv cfg (A \ L.toFinset) s' ∧
      (∀ x, s'.inR x = (s.inR x && !(x ∈ L))) ∧
      volR cfg s' + (L.map fun a => (cfg.incEdges a).length).sum = volR cfg s ∧
      relabelCurRem cfg s' ≤ relabelCurRem cfg s ∧
      sumAbsRem cfg s' ≤ sumAbsRem cfg s ∧
      (∀ x, x ∈ s.active → x ∈ s'.active) ∧
      (∀ x, x ∈ s.peelQ → x ∈ s'.peelQ) ∧
      s'.peelQ.length ≤ s.peelQ.length + (L.map fun a => (cfg.incEdges a).length).sum ∧
      phiActive s' ≤ phiActive s +
        (L.map fun a => (cfg.incEdges a).length).sum * (cfg.H + 1) ∧
      s'.h = s.h ∧ s'.cur = s.cur ∧ s'.abs = s.abs ∧ s'.flow = s.flow ∧ s'.steps = s.steps
  | [], A, s, _, _, hinv, _ => by
    dsimp only [List.foldl_nil]
    rw [List.toFinset_nil, Finset.sdiff_empty, List.map_nil, List.sum_nil]
    refine ⟨hinv, fun x => ?_, by simp, le_rfl, le_rfl, fun _ h => h, fun _ h => h,
      by simp, by simp, rfl, rfl, rfl, rfl, rfl⟩
    simp
  | a :: t, A, s, hnodup, hLinR, hinv, hheadH => by
    have haR : s.inR a = true := hLinR a (by simp)
    have haNotMem : a ∉ t := (List.nodup_cons.mp hnodup).1
    have htNodup : t.Nodup := (List.nodup_cons.mp hnodup).2
    let s0 := removeOneFromR cfg a s
    have h0 := removeOneFromR_inv hcfg hinv haR
    have h0_inv : SweepInv cfg (A \ {a}) s0 := h0.1
    have h0_act : ∀ x, x ∈ s.active → x ∈ s0.active := h0.2.1
    have h0_peel : ∀ x, x ∈ s.peelQ → x ∈ s0.peelQ := h0.2.2.1
    have h0_plen : s0.peelQ.length ≤ s.peelQ.length + (cfg.incEdges a).length := h0.2.2.2.1
    have h0_phi : phiActive s0 ≤ phiActive s +
        ((cfg.incEdges a).map fun p => if p.2.2 ≠ a ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0).sum :=
      h0.2.2.2.2.1
    have h0_h : s0.h = s.h := h0.2.2.2.2.2.1
    have h0_cur : s0.cur = s.cur := h0.2.2.2.2.2.2.1
    have h0_abs : s0.abs = s.abs := h0.2.2.2.2.2.2.2.1
    have h0_flow : s0.flow = s.flow := h0.2.2.2.2.2.2.2.2.1
    have h0_steps : s0.steps = s.steps := h0.2.2.2.2.2.2.2.2.2
    have h0_inR : ∀ x, s0.inR x = if x = a then false else s.inR x := removeOneFromR_inR cfg a s
    have ht_inR : ∀ b ∈ t, s0.inR b = true := by
      intro b hb
      have hne : b ≠ a := fun heq => haNotMem (heq ▸ hb)
      rw [h0_inR b, ite_eq_right hne]
      exact hLinR b (by simp [hb])
    have ht_headH : ∀ x, s0.inR x = true → s0.h x < cfg.H ∨ t.head? = some x := by
      intro x hxR
      have hne : x ≠ a := by
        intro heq
        rw [heq, h0_inR a] at hxR
        simp at hxR
      have hsR : s.inR x = true := by simpa [h0_inR x, hne] using hxR
      rcases hheadH x hsR with hlt | hsome
      · left; simpa [h0_h] using hlt
      · simp only [List.head?_cons, Option.some.injEq] at hsome
        exact False.elim (hne hsome.symm)
    have hrec := foldl_removeOneFromR_inv hcfg t (A \ {a}) s0 htNodup ht_inR h0_inv ht_headH
    dsimp only [List.foldl_cons] at hrec ⊢
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    have h_sdiff : (A \ {a}) \ t.toFinset = A \ (a :: t).toFinset := by
      ext x; simp [Finset.mem_sdiff, List.mem_toFinset]; tauto
    have h_inR_final : ∀ x, (t.foldl (fun st b => removeOneFromR cfg b st) s0).inR x =
        (s.inR x && !(x ∈ a :: t)) := by
      intro x
      rw [hrec.2.1 x, h0_inR x]
      by_cases hxa : x = a <;> by_cases hxt : x ∈ t <;> simp [hxa, hxt]
    have hphi0_le : phiActive s0 ≤ phiActive s + (cfg.incEdges a).length * (cfg.H + 1) := by
      have hp_bound : ∀ p ∈ cfg.incEdges a,
          (if p.2.2 ≠ a ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0) ≤ cfg.H + 1 := by
        intro p _
        split_ifs with hp
        · rcases hheadH p.2.2 hp.2 with hlt | hsome
          · omega
          · simp only [List.head?_cons, Option.some.injEq] at hsome
            exact False.elim (hp.1 hsome.symm)
        · omega
      have hsum : ((cfg.incEdges a).map fun p => if p.2.2 ≠ a ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0).sum ≤
          (cfg.incEdges a).length * (cfg.H + 1) := by
        clear hrec
        suffices hM : ∀ (M : List (ℕ × Bool × ℕ)),
            (∀ p ∈ M, (if p.2.2 ≠ a ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0) ≤ cfg.H + 1) →
            (M.map fun p => if p.2.2 ≠ a ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0).sum ≤
              M.length * (cfg.H + 1) from
          hM (cfg.incEdges a) hp_bound
        intro M hM
        induction M with
        | nil => simp
        | cons p ps ihp =>
          have hps : ∀ q ∈ ps, (if q.2.2 ≠ a ∧ s.inR q.2.2 then s.h q.2.2 + 2 else 0) ≤ cfg.H + 1 :=
            fun q hq => hM q (List.mem_cons_of_mem _ hq)
          have hpt := hM p List.mem_cons_self
          have ih' := ihp hps
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          linarith [show (ps.length + 1) * (cfg.H + 1) = (cfg.H + 1) + ps.length * (cfg.H + 1) by ring]
      omega
    have haX : a ∈ cfg.X := hinv.inR_sub a haR
    have hvol0 := volR_removeOne haX haR h0_inR
    have hrel0 := relabelCurRem_removeOne_le (cfg := cfg) h0_inR h0_h h0_cur
    have habs0 := sumAbsRem_removeOne_le (cfg := cfg) h0_inR h0_abs
    refine ⟨?_, h_inR_final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h_sdiff]; exact hrec.1
    · rw [List.map_cons, List.sum_cons]; linarith [hrec.2.2.1]
    · exact le_trans hrec.2.2.2.1 hrel0
    · exact le_trans hrec.2.2.2.2.1 habs0
    · intro x hx; exact hrec.2.2.2.2.2.1 x (h0_act x hx)
    · intro x hx; exact hrec.2.2.2.2.2.2.1 x (h0_peel x hx)
    · rw [List.map_cons, List.sum_cons]; linarith [hrec.2.2.2.2.2.2.2.1, h0_plen]
    · rw [List.map_cons, List.sum_cons, Nat.add_mul]; linarith [hrec.2.2.2.2.2.2.2.2.1, hphi0_le]
    · exact hrec.2.2.2.2.2.2.2.2.2.1.trans h0_h
    · exact hrec.2.2.2.2.2.2.2.2.2.2.1.trans h0_cur
    · exact hrec.2.2.2.2.2.2.2.2.2.2.2.1.trans h0_abs
    · exact hrec.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h0_flow
    · exact hrec.2.2.2.2.2.2.2.2.2.2.2.2.2.trans h0_steps

/-! ### Micro-step 1: Low-degree peeling (`peelStep`) -/

/-- Processes the head `v :: rest` of `s.peelQ`: removes `v` from `R` if it is still in `R` and
has `degR v < θ_out_nat`, or discards the stale queue entry otherwise. -/
@[expose] def peelStep (cfg : PruneCfg) (v : ℕ) (rest : List ℕ) (s : PruneState) : PruneState :=
  if s.inR v && decide (s.degR v < cfg.θ_out_nat) then
    let s1 := removeOneFromR cfg v s
    { s1 with
      peelQ := s1.peelQ.erase v
      steps := s.steps + 1 + (cfg.incEdges v).length }
  else
    { s with peelQ := rest, steps := s.steps + 1 }

lemma peelStep_inv_pot {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) {v : ℕ} {rest : List ℕ} (hq : s.peelQ = v :: rest)
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d, d < cfg.θ_out_nat → 3 * d ≤ cfg.degX x) :
    let s' := peelStep cfg v rest s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
      volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s := by
  have hH3 := cfg.valid_three_le_H hcfg
  have hC4 := hcfg.2.2.1
  by_cases hdo : s.inR v = true ∧ s.degR v < cfg.θ_out_nat
  · have hb : (s.inR v && decide (s.degR v < cfg.θ_out_nat)) = true := by simp [hdo.1, hdo.2]
    dsimp only [peelStep]
    simp only [hb, ↓reduceIte]
    set len := (cfg.incEdges v).length
    have hlen_pos : 1 ≤ len := by
      by_contra h0
      have h0' : len = 0 := by omega
      have hnv := (hinv.no_ex_isolated v h0').2.2.2
      rw [hq] at hnv
      exact hnv (by simp)
    set s1 := removeOneFromR cfg v s
    have hinv_sw : SweepInv cfg ∅ s := (pruningInv_iff_sweepInv_empty cfg s).mp hinv
    have h1 := removeOneFromR_inv hcfg hinv_sw hdo.1
    have h1_sw : SweepInv cfg ∅ s1 := by simpa using h1.1
    have h1_inv : PruningInv cfg s1 := (pruningInv_iff_sweepInv_empty cfg s1).mpr h1_sw
    have h1_inR : ∀ x, s1.inR x = if x = v then false else s.inR x := removeOneFromR_inR cfg v s
    have hv_mem_s : v ∈ s.peelQ := by rw [hq]; simp
    have hv_mem1 : v ∈ s1.peelQ := h1.2.2.1 v hv_mem_s
    set s' : PruneState :=
      { s1 with peelQ := s1.peelQ.erase v, steps := s.steps + 1 + len }
    have hs'_inv : PruningInv cfg s' :=
      { inR_sub := h1_inv.inR_sub
        not_inR_B := h1_inv.not_inR_B
        h_lt_H := h1_inv.h_lt_H
        cur_le := h1_inv.cur_le
        abs_le := h1_inv.abs_le
        h_pos_abs := h1_inv.h_pos_abs
        flow_cap := h1_inv.flow_cap
        h_edge := h1_inv.h_edge
        cur_no_adm := h1_inv.cur_no_adm
        cur_zero_of_abs_lt := h1_inv.cur_zero_of_abs_lt
        flow_balance := h1_inv.flow_balance
        degR_eq := h1_inv.degR_eq
        degR_peel := by
          intro x hxR hxdeg
          have hne : x ≠ v := by
            intro heq
            have hvf : s1.inR v = false := by rw [h1_inR]; simp
            rw [heq, hvf] at hxR
            exact Bool.false_ne_true hxR
          exact (List.mem_erase_of_ne hne).mpr (h1_inv.degR_peel x hxR hxdeg)
        active_cov := h1_inv.active_cov
        active_mem_inActive := h1_inv.active_mem_inActive
        active_nodup := h1_inv.active_nodup
        active_sub := h1_inv.active_sub
        no_ex_isolated := by
          intro x hx0
          have hne := h1_inv.no_ex_isolated x hx0
          exact ⟨hne.1, hne.2.1, hne.2.2.1, fun hmem => hne.2.2.2 (List.mem_of_mem_erase hmem)⟩ }
    have hvX : v ∈ cfg.X := hinv.inR_sub v hdo.1
    have hvB : v ∉ cfg.B := fun hb' => by have := hinv.not_inR_B v hb'; simp [hdo.1] at this
    have hvol_eq : volR cfg s' + len = volR cfg s := volR_removeOne hvX hdo.1 h1_inR
    have hrel_le : relabelCurRem cfg s' ≤ relabelCurRem cfg s :=
      relabelCurRem_removeOne_le h1_inR h1.2.2.2.2.2.1 h1.2.2.2.2.2.2.1
    have habs_le : sumAbsRem cfg s' ≤ sumAbsRem cfg s :=
      sumAbsRem_removeOne_le h1_inR h1.2.2.2.2.2.2.2.1
    have hpeel_len : s'.peelQ.length = s1.peelQ.length - 1 := List.length_erase_of_mem hv_mem1
    have h1_plen : s1.peelQ.length ≤ s.peelQ.length + len := h1.2.2.2.1
    have hsp_pos : 1 ≤ s.peelQ.length := by rw [hq]; simp
    have hplen' : s'.peelQ.length + 1 ≤ s.peelQ.length + len := by omega
    have hphi' : phiActive s' ≤ phiActive s + len * (cfg.H + 1) := by
      have hphi1 : phiActive s1 ≤ phiActive s +
          ((cfg.incEdges v).map fun p => if p.2.2 ≠ v ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0).sum :=
        h1.2.2.2.2.1
      have hp_le : ∀ p ∈ cfg.incEdges v,
          (if p.2.2 ≠ v ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0) ≤ cfg.H + 1 := by
        intro p _
        split_ifs with hp
        · have := hinv.h_lt_H p.2.2 hp.2; omega
        · omega
      have hsum : ((cfg.incEdges v).map fun p => if p.2.2 ≠ v ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0).sum ≤
          len * (cfg.H + 1) := by
        clear h1 hinv_sw h1_sw h1_inv hs'_inv hvol_eq hrel_le habs_le hphi1
        suffices hM : ∀ (M : List (ℕ × Bool × ℕ)),
            (∀ p ∈ M, (if p.2.2 ≠ v ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0) ≤ cfg.H + 1) →
            (M.map fun p => if p.2.2 ≠ v ∧ s.inR p.2.2 then s.h p.2.2 + 2 else 0).sum ≤
              M.length * (cfg.H + 1) from
          hM (cfg.incEdges v) hp_le
        intro M hM
        induction M with
        | nil => simp
        | cons p ps ihp =>
          have hps : ∀ q ∈ ps, (if q.2.2 ≠ v ∧ s.inR q.2.2 then s.h q.2.2 + 2 else 0) ≤ cfg.H + 1 :=
            fun q hq => hM q (List.mem_cons_of_mem _ hq)
          have hpt := hM p List.mem_cons_self
          have ih' := ihp hps
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          linarith [show (ps.length + 1) * (cfg.H + 1) = (cfg.H + 1) + ps.length * (cfg.H + 1) by ring]
      change phiActive s1 ≤ _
      omega
    have hpot_drop : pot cfg s' + (cfg.H + 4) * len + 2 ≤ pot cfg s := by
      unfold pot
      have hvol_drop : (3 * cfg.H + 8) * volR cfg s =
          (3 * cfg.H + 8) * volR cfg s' + (3 * cfg.H + 8) * len := by
        rw [← hvol_eq]; ring
      nlinarith
    have hpot_lt : pot cfg s' < pot cfg s := by nlinarith
    have hsteps_pot : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := by
      change s.steps + 1 + len + pot cfg s' ≤ s.steps + pot cfg s
      nlinarith
    have hvolP_eq : volPminusB cfg s' = volPminusB cfg s + cfg.degX v :=
      volPminusB_removeOne hvX hvB hdo.1 h1_inR
    have hcut_diff : (cutPR cfg s' : ℤ) - (cutPR cfg s : ℤ) =
        (((cfg.incEdges v).filter fun p => s.inR p.2.2).length : ℤ) -
          (((cfg.incEdges v).filter fun p => !s.inR p.2.2).length : ℤ) := by
      have hinR' : s'.inR = fun x => if x = v then false else s.inR x := funext h1_inR
      unfold cutPR PruneCfg.incEdges
      rw [hinR']
      exact cut_change_removeOne s.inR v hdo.1 0 cfg.edges
    have hRsubX : s.Rset cfg ⊆ cfg.X := Finset.filter_subset _ _
    have hvRset : v ∈ s.Rset cfg := (s.mem_Rset cfg hinv.inR_sub).mpr hdo.1
    have hfilt_in : ((cfg.incEdges v).filter fun p => s.inR p.2.2).length ≤ s.degR v := by
      rw [hinv.degR_eq v hdo.1]
      have heq : (cfg.incEdges v).filter (fun p => s.inR p.2.2) =
          (cfg.incEdges v).filter (fun p => decide (p.2.2 ∈ s.Rset cfg)) := by
        apply List.filter_congr
        intro p hp
        have hpX : p.2.2 ∈ cfg.X := (incEdges_mem_sub hp).2
        simp [PruneState.Rset, hpX]
      rw [heq]
      exact filter_incEdgesAux_mem_degIn hRsubX hvRset
    have hfilt_out : cfg.degX v - s.degR v =
        ((cfg.incEdges v).filter fun p => !s.inR p.2.2).length := by
      rw [hinv.degR_eq v hdo.1]
      have h1 := (filter_incEdgesAux_degIn_eq (G := cfg.G) hRsubX hvRset).1
      have heq : (cfg.incEdges v).filter (fun p => decide (p.2.2 ∉ s.Rset cfg)) =
          (cfg.incEdges v).filter (fun p => !s.inR p.2.2) := by
        apply List.filter_congr
        intro p hp
        have hpX : p.2.2 ∈ cfg.X := (incEdges_mem_sub hp).2
        simp [PruneState.Rset, hpX]
      rw [← heq]
      exact h1
    have hdeg_le_X : s.degR v ≤ cfg.degX v := by
      rw [hinv.degR_eq v hdo.1]
      exact (filter_incEdgesAux_degIn_eq hRsubX hvRset).2
    have h3deg : 3 * s.degR v ≤ cfg.degX v := hθ v hvX hvB (s.degR v) hdo.2
    have hcut_le_Z : (volPminusB cfg s' : ℤ) + 2 * (cfg.C_cap : ℤ) * (cutPR cfg s' : ℤ) ≤
        (volPminusB cfg s : ℤ) + 2 * (cfg.C_cap : ℤ) * (cutPR cfg s : ℤ) := by
      have hin_z : (((cfg.incEdges v).filter fun p => s.inR p.2.2).length : ℤ) ≤ (s.degR v : ℤ) := by
        exact_mod_cast hfilt_in
      have hout_z : (((cfg.incEdges v).filter fun p => !s.inR p.2.2).length : ℤ) =
          (cfg.degX v : ℤ) - (s.degR v : ℤ) := by
        omega
      have hC_z : (4 : ℤ) ≤ (cfg.C_cap : ℤ) := by exact_mod_cast hC4
      have h3_z : 3 * (s.degR v : ℤ) ≤ (cfg.degX v : ℤ) := by exact_mod_cast h3deg
      have hvol_z : (volPminusB cfg s' : ℤ) = (volPminusB cfg s : ℤ) + (cfg.degX v : ℤ) := by
        exact_mod_cast hvolP_eq
      nlinarith
    have hvc : volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
        volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s := by
      exact_mod_cast hcut_le_Z
    exact ⟨hs'_inv, hsteps_pot, hpot_lt, hvc⟩
  · have hb : (s.inR v && decide (s.degR v < cfg.θ_out_nat)) = false := by
      by_cases h1 : s.inR v = true <;> by_cases h2 : s.degR v < cfg.θ_out_nat <;> simp_all
    dsimp only [peelStep]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    set s' : PruneState := { s with peelQ := rest, steps := s.steps + 1 }
    have hs'_inv : PruningInv cfg s' :=
      { inR_sub := hinv.inR_sub
        not_inR_B := hinv.not_inR_B
        h_lt_H := hinv.h_lt_H
        cur_le := hinv.cur_le
        abs_le := hinv.abs_le
        h_pos_abs := hinv.h_pos_abs
        flow_cap := hinv.flow_cap
        h_edge := hinv.h_edge
        cur_no_adm := hinv.cur_no_adm
        cur_zero_of_abs_lt := hinv.cur_zero_of_abs_lt
        flow_balance := hinv.flow_balance
        degR_eq := hinv.degR_eq
        degR_peel := by
          intro x hxR hxdeg
          have hne : x ≠ v := fun heq => hdo ⟨heq ▸ hxR, heq ▸ hxdeg⟩
          have hmem := hinv.degR_peel x hxR hxdeg
          rw [hq] at hmem
          rcases List.mem_cons.mp hmem with rfl | hrest
          · exact False.elim (hne rfl)
          · exact hrest
        active_cov := hinv.active_cov
        active_mem_inActive := hinv.active_mem_inActive
        active_nodup := hinv.active_nodup
        active_sub := hinv.active_sub
        no_ex_isolated := by
          intro x hx0
          have hne := hinv.no_ex_isolated x hx0
          refine ⟨hne.1, hne.2.1, hne.2.2.1, fun hmem => hne.2.2.2 ?_⟩
          rw [hq]; exact List.mem_cons_of_mem _ hmem }
    have hpot_eq : pot cfg s' + 2 = pot cfg s := by
      unfold pot
      have hp : s'.peelQ = rest := rfl
      have hv : volR cfg s' = volR cfg s := rfl
      have hr : relabelCurRem cfg s' = relabelCurRem cfg s := rfl
      have ha : sumAbsRem cfg s' = sumAbsRem cfg s := rfl
      have hphi : phiActive s' = phiActive s := rfl
      rw [hp, hv, hr, ha, hphi, hq, List.length_cons]
      ring
    exact ⟨hs'_inv, by omega, by omega, le_rfl⟩

/-! ### Micro-step 2: Popping stale/zero-excess active vertices (`popInactiveStep`) -/

/-- Pops `u` from `s.active = u :: restAct` when `u` is no longer in `R` or has `s.ex u = 0`. -/
@[expose] def popInactiveStep (u : ℕ) (restAct : List ℕ) (s : PruneState) : PruneState :=
  { s with
    active := restAct
    inActive := fun x => if x = u then false else s.inActive x
    steps := s.steps + 1 }

lemma popInactiveStep_inv_pot {cfg : PruneCfg} {s : PruneState}
    (hinv : PruningInv cfg s) {u : ℕ} {restAct : List ℕ} (hact : s.active = u :: restAct)
    (hdead : s.inR u = false ∨ s.ex u = 0) :
    let s' := popInactiveStep u restAct s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' = volPminusB cfg s ∧
    cutPR cfg s' = cutPR cfg s := by
  dsimp only [popInactiveStep]
  set s' : PruneState :=
    { s with
      active := restAct
      inActive := fun x => if x = u then false else s.inActive x
      steps := s.steps + 1 }
  have hnodup' : restAct.Nodup := by
    have hn := hinv.active_nodup; rw [hact] at hn; exact (List.nodup_cons.mp hn).2
  have huNotRest : u ∉ restAct := by
    have hn := hinv.active_nodup; rw [hact] at hn; exact (List.nodup_cons.mp hn).1
  have hs'_inv : PruningInv cfg s' :=
    { inR_sub := hinv.inR_sub
      not_inR_B := hinv.not_inR_B
      h_lt_H := hinv.h_lt_H
      cur_le := hinv.cur_le
      abs_le := hinv.abs_le
      h_pos_abs := hinv.h_pos_abs
      flow_cap := hinv.flow_cap
      h_edge := hinv.h_edge
      cur_no_adm := hinv.cur_no_adm
      cur_zero_of_abs_lt := hinv.cur_zero_of_abs_lt
      flow_balance := hinv.flow_balance
      degR_eq := hinv.degR_eq
      degR_peel := hinv.degR_peel
      active_cov := by
        intro x hxR hxpos
        have hne : x ≠ u := by
          rintro rfl
          rcases hdead with hf | hz
          · exact absurd hf (by simpa [s'] using hxR)
          · change 0 < s.ex x at hxpos; omega
        have hmem := hinv.active_cov x hxR hxpos
        rw [hact] at hmem
        rcases List.mem_cons.mp hmem with rfl | hr
        · exact False.elim (hne rfl)
        · exact hr
      active_mem_inActive := by
        intro x
        by_cases hxu : x = u
        · subst hxu; simp [s', huNotRest]
        · have hmem := hinv.active_mem_inActive x
          rw [hact] at hmem
          simp [s', hxu, hmem]
      active_nodup := hnodup'
      active_sub := fun x hx => hinv.active_sub x (by rw [hact]; exact List.mem_cons_of_mem _ hx)
      no_ex_isolated := by
        intro x hx0
        have hne := hinv.no_ex_isolated x hx0
        exact ⟨hne.1, hne.2.1, fun hmem => hne.2.2.1 (by rw [hact]; exact List.mem_cons_of_mem _ hmem),
          hne.2.2.2⟩ }
  have hphi_eq : phiActive s = (if s.inR u then s.h u + 2 else 2) + phiActive s' := by
    unfold phiActive
    change (s.active.map _).sum = _ + (restAct.map _).sum
    rw [hact, List.map_cons, List.sum_cons]
  have hhead_ge : 2 ≤ if s.inR u then s.h u + 2 else 2 := by split_ifs <;> omega
  have hpot_le : pot cfg s' + 4 ≤ pot cfg s := by
    unfold pot
    have hv : volR cfg s' = volR cfg s := rfl
    have hr : relabelCurRem cfg s' = relabelCurRem cfg s := rfl
    have ha : sumAbsRem cfg s' = sumAbsRem cfg s := rfl
    have hp : s'.peelQ = s.peelQ := rfl
    rw [hv, hr, ha, hp, hphi_eq]
    omega
  exact ⟨hs'_inv, by omega, by omega, rfl, rfl⟩


end

end MinCostFlow.Expander
