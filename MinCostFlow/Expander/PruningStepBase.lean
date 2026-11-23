module

public import MinCostFlow.Expander.PruningBucketProg

import Mathlib.Tactic.Linarith

/-!
# Word-RAM Push-Relabel & Low-Degree Peeling Steps for Expander Pruning

Implements and formally verifies every step operation of `ExpanderPruningStep` / `PruningStep`
in deterministic Word RAM against `PruneMemInv` and `BucketMemPreserved`:
1. `removeOneFromRStmt` (`removeOneFromR`)
2. `peelStepStmt` (`peelStep`)
3. `popInactiveStepStmt` (`popInactiveStep`)
4. `absorbStepStmt` (`absorbStep`)
5. `advanceCurStepStmt` (`advanceCurStep`)
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

/-! ## 1. Shared Register Projection, Bounds, and Run/Eval Helpers -/

/-- The 27 read-only configuration and workspace/input base-pointer registers of `PruneMemInv`. -/
structure PruneStepRegs (cfg : PruneCfg) (gAddr csrAddr inBAddr outRAddr workAddr : ℕ)
    (st : State) : Prop where
  reg_g : st.regs prG = gAddr
  reg_csr : st.regs prCsr = csrAddr
  reg_inB : st.regs prInB = inBAddr
  reg_outR : st.regs prOutR = outRAddr
  reg_work : st.regs prWork = workAddr
  reg_ccap : st.regs prCcap = cfg.C_cap
  reg_H : st.regs prH = cfg.H
  reg_theta : st.regs prTheta = cfg.θ_out_nat
  reg_n : st.regs prN = cfg.G.n
  reg_m : st.regs prM = cfg.G.m
  reg_degX : st.regs prDegX = wDegX workAddr cfg.G.n cfg.G.m cfg.H
  reg_hArr : st.regs prHArr = wHArr workAddr cfg.G.n cfg.G.m cfg.H
  reg_cur : st.regs prCur = wCur workAddr cfg.G.n cfg.G.m cfg.H
  reg_abs : st.regs prAbs = wAbs workAddr cfg.G.n cfg.G.m cfg.H
  reg_ex : st.regs prEx = wEx workAddr cfg.G.n cfg.G.m cfg.H
  reg_degR : st.regs prDegR = wDegR workAddr cfg.G.n cfg.G.m cfg.H
  reg_inAct : st.regs prInAct = wInAct workAddr cfg.G.n cfg.G.m cfg.H
  reg_actStk : st.regs prActStk = wActStk workAddr cfg.G.n cfg.G.m cfg.H
  reg_peelStk : st.regs prPeelStk = wPeelStk workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlNext : st.regs prLvlNext = wLvlNext workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlPrev : st.regs prLvlPrev = wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H
  reg_remArr : st.regs prRemArr = wRemArr workAddr cfg.G.n cfg.G.m cfg.H
  reg_flowEnc : st.regs prFlowEnc = wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlVol : st.regs prLvlVol = wLvlVol workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlHead : st.regs prLvlHead = wLvlHead workAddr cfg.G.n cfg.G.m cfg.H
  reg_adjV : st.regs prCsrAdjV = csrAddr + 2 * cfg.G.n + 1
  reg_adjH : st.regs prCsrAdjH = csrAddr + 2 * cfg.G.n + 1 + 2 * cfg.G.m

lemma PruneMemInv.stepRegs {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) :
    PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st where
  reg_g := h.reg_g
  reg_csr := h.reg_csr
  reg_inB := h.reg_inB
  reg_outR := h.reg_outR
  reg_work := h.reg_work
  reg_ccap := h.reg_ccap
  reg_H := h.reg_H
  reg_theta := h.reg_theta
  reg_n := h.reg_n
  reg_m := h.reg_m
  reg_degX := h.reg_degX
  reg_hArr := h.reg_hArr
  reg_cur := h.reg_cur
  reg_abs := h.reg_abs
  reg_ex := h.reg_ex
  reg_degR := h.reg_degR
  reg_inAct := h.reg_inAct
  reg_actStk := h.reg_actStk
  reg_peelStk := h.reg_peelStk
  reg_lvlNext := h.reg_lvlNext
  reg_lvlPrev := h.reg_lvlPrev
  reg_remArr := h.reg_remArr
  reg_flowEnc := h.reg_flowEnc
  reg_lvlVol := h.reg_lvlVol
  reg_lvlHead := h.reg_lvlHead
  reg_adjV := h.reg_adjV
  reg_adjH := h.reg_adjH

lemma pruneStepRegs_of_agree {cfg : PruneCfg}
    {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} {st st' : State}
    (h : PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st)
    (hagree : ∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st.regs r) :
    PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st' where
  reg_g := (hagree prG (by decide) (by decide) (by decide)).trans h.reg_g
  reg_csr := (hagree prCsr (by decide) (by decide) (by decide)).trans h.reg_csr
  reg_inB := (hagree prInB (by decide) (by decide) (by decide)).trans h.reg_inB
  reg_outR := (hagree prOutR (by decide) (by decide) (by decide)).trans h.reg_outR
  reg_work := (hagree prWork (by decide) (by decide) (by decide)).trans h.reg_work
  reg_ccap := (hagree prCcap (by decide) (by decide) (by decide)).trans h.reg_ccap
  reg_H := (hagree prH (by decide) (by decide) (by decide)).trans h.reg_H
  reg_theta := (hagree prTheta (by decide) (by decide) (by decide)).trans h.reg_theta
  reg_n := (hagree prN (by decide) (by decide) (by decide)).trans h.reg_n
  reg_m := (hagree prM (by decide) (by decide) (by decide)).trans h.reg_m
  reg_degX := (hagree prDegX (by decide) (by decide) (by decide)).trans h.reg_degX
  reg_hArr := (hagree prHArr (by decide) (by decide) (by decide)).trans h.reg_hArr
  reg_cur := (hagree prCur (by decide) (by decide) (by decide)).trans h.reg_cur
  reg_abs := (hagree prAbs (by decide) (by decide) (by decide)).trans h.reg_abs
  reg_ex := (hagree prEx (by decide) (by decide) (by decide)).trans h.reg_ex
  reg_degR := (hagree prDegR (by decide) (by decide) (by decide)).trans h.reg_degR
  reg_inAct := (hagree prInAct (by decide) (by decide) (by decide)).trans h.reg_inAct
  reg_actStk := (hagree prActStk (by decide) (by decide) (by decide)).trans h.reg_actStk
  reg_peelStk := (hagree prPeelStk (by decide) (by decide) (by decide)).trans h.reg_peelStk
  reg_lvlNext := (hagree prLvlNext (by decide) (by decide) (by decide)).trans h.reg_lvlNext
  reg_lvlPrev := (hagree prLvlPrev (by decide) (by decide) (by decide)).trans h.reg_lvlPrev
  reg_remArr := (hagree prRemArr (by decide) (by decide) (by decide)).trans h.reg_remArr
  reg_flowEnc := (hagree prFlowEnc (by decide) (by decide) (by decide)).trans h.reg_flowEnc
  reg_lvlVol := (hagree prLvlVol (by decide) (by decide) (by decide)).trans h.reg_lvlVol
  reg_lvlHead := (hagree prLvlHead (by decide) (by decide) (by decide)).trans h.reg_lvlHead
  reg_adjV := (hagree prCsrAdjV (by decide) (by decide) (by decide)).trans h.reg_adjV
  reg_adjH := (hagree prCsrAdjH (by decide) (by decide) (by decide)).trans h.reg_adjH

lemma stepRegs_agree_update_ge29 {r : ℕ} (hr : 29 ≤ r) (v : ℕ) (st : State) :
    ∀ k, k ≤ prCsrAdjH → Function.update st.regs r v k = st.regs k := by
  intro k hk
  exact Function.update_of_ne (show k ≠ r by dsimp only [prCsrAdjH] at hk; omega) v st.regs

lemma eval_sub_regs {w : ℕ} {st : State} {r₁ r₂ v₁ v₂ : ℕ}
    (hr₁ : st.regs r₁ = v₁) (hr₂ : st.regs r₂ = v₂) (_hv₁ : v₁ < 2 ^ w) (_hv₂ : v₂ < 2 ^ w) :
    Expr.eval w st (.bin .sub (.reg r₁) (.reg r₂)) = some (v₁ - v₂) := by
  have hsub : v₁ - v₂ < 2 ^ w := by omega
  simp [Expr.eval, hr₁, hr₂, WordRAM.BinOp.eval, hsub]

lemma eval_load_reg {w : ℕ} {st : State} {r addr v : ℕ}
    (hr : st.regs r = addr) (_ha : addr < 2 ^ w)
    (hm : st.mem addr = v) (_hv : v < 2 ^ w) :
    Expr.eval w st (.load (.reg r)) = some v := by
  simp [Expr.eval, hr, hm]

lemma eval_load_add_regs_any {w : ℕ} {st : State} {r₁ r₂ v₁ v₂ v : ℕ}
    (hr₁ : st.regs r₁ = v₁) (hr₂ : st.regs r₂ = v₂)
    (hsum : v₁ + v₂ < 2 ^ w) (hm : st.mem (v₁ + v₂) = v) :
    Expr.eval w st (.load (.bin .add (.reg r₁) (.reg r₂))) = some v := by
  simp [Expr.eval, hr₁, hr₂, WordRAM.BinOp.eval, hsum, hm]

lemma eval_add_reg_const {w : ℕ} {st : State} {r v c : ℕ}
    (hr : st.regs r = v) (hc : c < 2 ^ w) (hsum : v + c < 2 ^ w) :
    Expr.eval w st (.bin .add (.reg r) (.const c)) = some (v + c) := by
  simp [Expr.eval, hr, hc, WordRAM.BinOp.eval, hsum]

lemma eval_sub_reg_const {w : ℕ} {st : State} {r v c : ℕ}
    (hr : st.regs r = v) (_hv : v < 2 ^ w) (hc : c < 2 ^ w) :
    Expr.eval w st (.bin .sub (.reg r) (.const c)) = some (v - c) := by
  have hsub : v - c < 2 ^ w := by omega
  simp [Expr.eval, hr, hc, WordRAM.BinOp.eval, hsub]

lemma memFrame_weaken {m1 m2 : ℕ → ℕ} {a1 b1 a2 b2 : ℕ}
    (h : MemFrame m1 m2 a1 b1) (ha : a2 ≤ a1) (hb : b1 ≤ b2) : MemFrame m1 m2 a2 b2 := by
  intro x hx
  rcases hx with hlt | hge
  · exact h x (Or.inl (by omega))
  · exact h x (Or.inr (by omega))

lemma preservedOutside2_refl (mem : ℕ → ℕ) (a1 b1 a2 b2 : ℕ) :
    PreservedOutside2 mem mem a1 b1 a2 b2 :=
  fun _ _ _ => rfl

lemma preservedOutside2_trans {m1 m2 m3 : ℕ → ℕ} {a1 b1 a2 b2 : ℕ}
    (h1 : PreservedOutside2 m1 m2 a1 b1 a2 b2)
    (h2 : PreservedOutside2 m2 m3 a1 b1 a2 b2) :
    PreservedOutside2 m1 m3 a1 b1 a2 b2 :=
  fun x hx1 hx2 => (h2 x hx1 hx2).trans (h1 x hx1 hx2)

lemma preservedOutside2_update_left {mem : ℕ → ℕ} {a1 b1 a2 b2 x v : ℕ}
    (hax : a1 ≤ x) (hxb : x < b1) :
    PreservedOutside2 mem (Function.update mem x v) a1 b1 a2 b2 := by
  intro y hy _
  rw [Function.update_of_ne]
  intro hyx; subst hyx
  rcases hy with hlt | hge <;> omega

lemma preservedOutside2_update_right {mem : ℕ → ℕ} {a1 b1 a2 b2 x v : ℕ}
    (hax : a2 ≤ x) (hxb : x < b2) :
    PreservedOutside2 mem (Function.update mem x v) a1 b1 a2 b2 := by
  intro y _ hy
  rw [Function.update_of_ne]
  intro hyx; subst hyx
  rcases hy with hlt | hge <;> omega

lemma preservedOutside2_of_memFrame2 {m1 m2 : ℕ → ℕ} {a1 b1 a2 b2 : ℕ}
    (h : MemFrame m1 m2 a2 b2) : PreservedOutside2 m1 m2 a1 b1 a2 b2 :=
  fun x _ hx2 => h x hx2

lemma preservedOutside2_sub_right {m1 m2 : ℕ → ℕ} {a1 b1 a2 b2 A2 B2 : ℕ}
    (h : PreservedOutside2 m1 m2 a1 b1 a2 b2) (ha : A2 ≤ a2) (hb : b2 ≤ B2) :
    PreservedOutside2 m1 m2 a1 b1 A2 B2 := by
  intro x hx1 hx2
  apply h x hx1
  rcases hx2 with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

lemma ex_le_bound_of_flow_balance {cfg : PruneCfg} {s : PruneState}
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hGv : cfg.G.IsValid)
    (hcap : ∀ idx < cfg.edges.length, -(cfg.C_cap : ℤ) ≤ s.flow idx ∧ s.flow idx ≤ (cfg.C_cap : ℤ))
    (hbal : ∀ u, s.inR u = true →
      (s.ex u : ℤ) + (s.abs u : ℤ) =
        ((cfg.incEdges u).map (edgeContrib s.inR s.flow cfg.C_cap)).sum)
    (hinR_sub : ∀ u, s.inR u = true → u ∈ cfg.X)
    {u : ℕ} (huR : s.inR u = true) :
    s.ex u ≤ 4 * cfg.C_cap * cfg.G.m := by
  have hsum_le : ((cfg.incEdges u).map (edgeContrib s.inR s.flow cfg.C_cap)).sum ≤
      ((cfg.incEdges u).length : ℤ) * (2 * (cfg.C_cap : ℤ)) := by
    have hmem : ∀ p ∈ cfg.incEdges u,
        edgeContrib s.inR s.flow cfg.C_cap p ≤ 2 * (cfg.C_cap : ℤ) := by
      intro p hp
      have hid := incEdgesAux_idx_ge (by simpa [PruneCfg.incEdges] using hp)
      have hc := hcap p.1 (by simpa using hid.2)
      have hc0 : (0 : ℤ) ≤ (cfg.C_cap : ℤ) := Int.natCast_nonneg _
      unfold edgeContrib flowDir
      split_ifs <;> linarith [hc.1, hc.2, hc0]
    clear hbal
    suffices hsum_gen : ∀ L : List (ℕ × Bool × ℕ),
        (∀ p ∈ L, edgeContrib s.inR s.flow cfg.C_cap p ≤ 2 * (cfg.C_cap : ℤ)) →
        (L.map (edgeContrib s.inR s.flow cfg.C_cap)).sum ≤ (L.length : ℤ) * (2 * (cfg.C_cap : ℤ)) from
      hsum_gen (cfg.incEdges u) hmem
    intro L hL
    induction L with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have h1 := hL p (by simp)
      have h2 := ih (fun q hq => hL q (by simp [hq]))
      linarith
  have hdeg_le : cfg.degX u ≤ 2 * cfg.G.m := by
    have huX : u ∈ cfg.G.verts := by
      have := hinR_sub u huR
      rw [hcfgX] at this
      exact this
    have hsum : ∑ v ∈ cfg.G.verts, cfg.G.deg v = 2 * cfg.G.m := sum_deg_eq_two_mul_m hGv
    have hsingle := Finset.single_le_sum (f := cfg.G.deg) (fun _ _ => Nat.zero_le _) huX
    have hdx : cfg.degX u = cfg.G.deg u := by
      unfold PruneCfg.degX Cited.Graph.deg
      rw [hcfgX]
      rfl
    omega
  have hlen : (cfg.incEdges u).length ≤ 2 * cfg.G.m :=
    le_trans (incEdges_length_le_degX cfg u) hdeg_le
  have hlenZ : ((cfg.incEdges u).length : ℤ) ≤ 2 * (cfg.G.m : ℤ) := by exact_mod_cast hlen
  have hbalu := hbal u huR
  have hZ : (s.ex u : ℤ) ≤ 4 * (cfg.C_cap : ℤ) * (cfg.G.m : ℤ) := by
    have hnonneg : (0 : ℤ) ≤ 2 * (cfg.C_cap : ℤ) := by omega
    have hmul : ((cfg.incEdges u).length : ℤ) * (2 * (cfg.C_cap : ℤ)) ≤
        (2 * (cfg.G.m : ℤ)) * (2 * (cfg.C_cap : ℤ)) :=
      mul_le_mul_of_nonneg_right hlenZ hnonneg
    linarith
  exact_mod_cast hZ

/-! ### Prefix & `peelQ` Shift Helpers for `foldl removeEdgeStep` -/

lemma removeEdgeStep_eq_peelShift (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool)
    (s : PruneState) (p : ℕ × Bool × ℕ) (q0 : List ℕ) :
    let step := removeEdgeStep cfg flow inR'
    let sp := step { s with peelQ := q0 } p
    let s1 := step s p
    sp.inR = s1.inR ∧ sp.h = s1.h ∧ sp.cur = s1.cur ∧ sp.abs = s1.abs ∧
    sp.ex = s1.ex ∧ sp.degR = s1.degR ∧ sp.active = s1.active ∧ sp.inActive = s1.inActive ∧
    sp.flow = s1.flow ∧ sp.steps = s1.steps := by
  dsimp only [removeEdgeStep]
  split_ifs <;> simp

lemma removeEdgeStep_peelQ_update (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool)
    (s : PruneState) (p : ℕ × Bool × ℕ) (q1 : List ℕ) :
    removeEdgeStep cfg flow inR' { s with peelQ := q1 } p =
    { removeEdgeStep cfg flow inR' s p with
      peelQ := if inR' p.2.2 = true ∧ s.degR p.2.2 = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat then
          p.2.2 :: q1 else q1 } := by
  rcases p with ⟨idx, dir, w⟩
  dsimp only [removeEdgeStep]
  by_cases hw : inR' w = true
  · simp only [hw, ↓reduceIte]
    by_cases hp : s.degR w = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat <;> simp [hp]
  · simp [hw]

lemma foldl_removeEdgeStep_peelShift (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool) :
    ∀ (L : List (ℕ × Bool × ℕ)) (s : PruneState),
      ∃ pref : List ℕ,
        (∀ x ∈ pref, inR' x = true) ∧
        ∀ q0 : List ℕ,
          let sq := L.foldl (removeEdgeStep cfg flow inR') { s with peelQ := q0 }
          let s1 := L.foldl (removeEdgeStep cfg flow inR') s
          sq.peelQ = pref ++ q0 ∧
          sq.inR = s1.inR ∧ sq.h = s1.h ∧ sq.cur = s1.cur ∧ sq.abs = s1.abs ∧
          sq.ex = s1.ex ∧ sq.degR = s1.degR ∧ sq.active = s1.active ∧
          sq.inActive = s1.inActive ∧ sq.flow = s1.flow ∧ sq.steps = s1.steps := by
  intro L
  induction L with
  | nil =>
    intro s
    refine ⟨[], fun _ h => by simp at h, fun q0 => by simp⟩
  | cons p t ih =>
    intro s
    rcases p with ⟨idx, dir, w⟩
    by_cases hw : inR' w = true
    · by_cases hpush : s.degR w = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat
      · let sNext := removeEdgeStep cfg flow inR' s (idx, dir, w)
        obtain ⟨pref, hpref, hspec⟩ := ih sNext
        refine ⟨pref ++ [w], fun x hx => ?_, fun q0 => ?_⟩
        · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | rfl
          · exact hpref x hx
          · exact hw
        · have hstep0 : removeEdgeStep cfg flow inR' { s with peelQ := q0 } (idx, dir, w) =
              { sNext with peelQ := w :: q0 } := by
            rw [removeEdgeStep_peelQ_update]; simp [hw, hpush, sNext]
          have hstep1 : removeEdgeStep cfg flow inR' s (idx, dir, w) = sNext := rfl
          have hq := hspec (w :: q0)
          simp only [List.foldl_cons, hstep0, hstep1]
          refine ⟨?_, hq.2⟩
          rw [hq.1, List.append_assoc]; rfl
      · let sNext := removeEdgeStep cfg flow inR' s (idx, dir, w)
        obtain ⟨pref, hpref, hspec⟩ := ih sNext
        refine ⟨pref, hpref, fun q0 => ?_⟩
        have hstep0 : removeEdgeStep cfg flow inR' { s with peelQ := q0 } (idx, dir, w) =
            { sNext with peelQ := q0 } := by
          rw [removeEdgeStep_peelQ_update]; simp [hw, hpush, sNext]
        have hstep1 : removeEdgeStep cfg flow inR' s (idx, dir, w) = sNext := rfl
        simp only [List.foldl_cons, hstep0, hstep1]
        exact hspec q0
    · obtain ⟨pref, hpref, hspec⟩ := ih s
      refine ⟨pref, hpref, fun q0 => ?_⟩
      have hstep0 : removeEdgeStep cfg flow inR' { s with peelQ := q0 } (idx, dir, w) =
          { s with peelQ := q0 } := by
        simp [removeEdgeStep, hw]
      have hstep1 : removeEdgeStep cfg flow inR' s (idx, dir, w) = s := by
        simp [removeEdgeStep, hw]
      simp only [List.foldl_cons, hstep0, hstep1]
      exact hspec q0

lemma foldl_removeEdgeStep_peelQ_erase {cfg : PruneCfg} {flow : ℕ → ℤ}
    {inR' : ℕ → Bool} {L : List (ℕ × Bool × ℕ)} {s : PruneState}
    {a : ℕ} {rest : List ℕ}
    (ha_false : inR' a = false) (hq : s.peelQ = a :: rest) :
    let sq := L.foldl (removeEdgeStep cfg flow inR') { s with peelQ := rest }
    let s1 := L.foldl (removeEdgeStep cfg flow inR') s
    sq.peelQ = s1.peelQ.erase a ∧
    sq.inR = s1.inR ∧ sq.h = s1.h ∧ sq.cur = s1.cur ∧ sq.abs = s1.abs ∧
    sq.ex = s1.ex ∧ sq.degR = s1.degR ∧ sq.active = s1.active ∧
    sq.inActive = s1.inActive ∧ sq.flow = s1.flow ∧ sq.steps = s1.steps := by
  obtain ⟨pref, hpref, hspec⟩ := foldl_removeEdgeStep_peelShift cfg flow inR' L s
  have hq_res := hspec rest
  have hnot : a ∉ pref := fun hm => by
    have := hpref a hm
    rw [ha_false] at this
    exact Bool.false_ne_true this
  refine ⟨?_, hq_res.2⟩
  rw [hq_res.1]
  have hs1_eq : (L.foldl (removeEdgeStep cfg flow inR') s).peelQ = pref ++ a :: rest := by
    have h' := hspec s.peelQ
    have hconst : { s with peelQ := s.peelQ } = s := rfl
    rw [hconst] at h'
    rw [h'.1, hq]
  rw [hs1_eq, List.erase_append_right _ hnot, List.erase_cons_head]

lemma foldl_removeEdgeStep_ex_mono {cfg : PruneCfg} {flow : ℕ → ℤ}
    {inR' : ℕ → Bool} :
    ∀ (L : List (ℕ × Bool × ℕ)) (s : PruneState) (w : ℕ),
      s.ex w ≤ (L.foldl (removeEdgeStep cfg flow inR') s).ex w := by
  intro L
  induction L with
  | nil => intro s w; simp
  | cons p t ih =>
    intro s w
    rcases p with ⟨idx, dir, u⟩
    have h1 : s.ex w ≤ (removeEdgeStep cfg flow inR' s (idx, dir, u)).ex w := by
      dsimp only [removeEdgeStep]
      by_cases hr : inR' u = true
      · by_cases hwu : w = u
        · subst hwu; simp [hr]
        · simp [hr, hwu]
      · simp [hr]
    exact le_trans h1 (ih _ w)

lemma foldl_removeEdgeStep_degR_antitone {cfg : PruneCfg} {flow : ℕ → ℤ}
    {inR' : ℕ → Bool} :
    ∀ (L : List (ℕ × Bool × ℕ)) (s : PruneState) (w : ℕ),
      (L.foldl (removeEdgeStep cfg flow inR') s).degR w ≤ s.degR w := by
  intro L
  induction L with
  | nil => intro s w; simp
  | cons p t ih =>
    intro s w
    rcases p with ⟨idx, dir, u⟩
    have h1 : (removeEdgeStep cfg flow inR' s (idx, dir, u)).degR w ≤ s.degR w := by
      dsimp only [removeEdgeStep]
      by_cases hr : inR' u = true
      · by_cases hwu : w = u
        · subst hwu; simp [hr]
        · simp [hr, hwu]
      · simp [hr]
    exact le_trans (ih _ w) h1

lemma foldl_removeEdgeStep_peelQ_props {cfg : PruneCfg} {flow : ℕ → ℤ}
    {inR' : ℕ → Bool} :
    ∀ (L : List (ℕ × Bool × ℕ)) (s : PruneState),
      (∀ p ∈ L, inR' p.2.2 = true → p.2.2 < cfg.G.n) →
      s.peelQ.Nodup →
      (∀ x ∈ s.peelQ, x < cfg.G.n ∧ (inR' x = true → s.degR x < cfg.θ_out_nat)) →
      let s' := L.foldl (removeEdgeStep cfg flow inR') s
      s'.peelQ.Nodup ∧
      (∀ x ∈ s'.peelQ, x < cfg.G.n ∧ (inR' x = true → s'.degR x < cfg.θ_out_nat)) := by
  intro L
  induction L with
  | nil => intro s _ hnd hinv; exact ⟨hnd, hinv⟩
  | cons p t ih =>
    intro s hLn hnd hinv
    rcases p with ⟨idx, dir, w⟩
    have htn : ∀ q ∈ t, inR' q.2.2 = true → q.2.2 < cfg.G.n := fun q hq => hLn q (by simp [hq])
    have hw_lt : inR' w = true → w < cfg.G.n := hLn (idx, dir, w) (by simp)
    apply ih _ htn
    · dsimp only [removeEdgeStep]
      by_cases hw : inR' w = true
      · simp only [hw, ↓reduceIte]
        by_cases hpush : s.degR w = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat
        · simp only [hpush]
          have hnot : w ∉ s.peelQ := by
            intro hm
            have := (hinv w hm).2 hw
            omega
          exact List.nodup_cons.mpr ⟨hnot, hnd⟩
        · simp only [hpush, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnd
      · simp [hw, hnd]
    · intro x hx
      dsimp only [removeEdgeStep] at hx ⊢
      by_cases hw : inR' w = true
      · simp only [hw, ↓reduceIte] at hx ⊢
        by_cases hpush : s.degR w = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat
        · simp only [hpush] at hx ⊢
          rcases List.mem_cons.mp hx with hxw | hx'
          · subst hxw
            refine ⟨hw_lt hw, fun _ => ?_⟩
            simp only [↓reduceIte]
            omega
          · refine ⟨(hinv x hx').1, fun hxR => ?_⟩
            have hlt := (hinv x hx').2 hxR
            by_cases hxw : x = w
            · subst hxw; simp; omega
            · simp [hxw]; omega
        · simp only [hpush, decide_false, Bool.false_eq_true, ↓reduceIte] at hx ⊢
          refine ⟨(hinv x hx).1, fun hxR => ?_⟩
          have hlt := (hinv x hx).2 hxR
          by_cases hxw : x = w
          · subst hxw; simp; omega
          · simp [hxw]; omega
      · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hx ⊢
        exact hinv x hx

lemma peelQInv_to_nodup_lt {cfg : PruneCfg} {s : PruneState}
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hpq : PeelQInv cfg s) :
    s.peelQ.Nodup ∧
    ∀ x ∈ s.peelQ, x < cfg.G.n ∧ (s.inR x = true → s.degR x < cfg.θ_out_nat) := by
  refine ⟨hpq.1, fun x hx => ?_⟩
  refine ⟨?_, fun _ => hpq.2.2 x hx⟩
  · have := hpq.2.1 x hx
    rw [hcfgX] at this
    exact Finset.mem_range.mp this


end MinCostFlow.Expander
