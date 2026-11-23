module

public import WordRAM.Logic
public import WordRAM.Link
public import WordRAM.Tactic
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.Expander.DecomposePhiProg
public import MinCostFlow.Expander.DecomposePartSpec
public import MinCostFlow.Expander.BfsCompProg
public import MinCostFlow.Expander.DecomposeMath

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Level Building Blocks for Word-RAM `Decompose`

Provides deterministic (`Stmt.NoRand`) Word-RAM utilities for Algorithm 5:
1. `runsTo_mem_lt_of_input_lt` and `isExpanderDecomposition_of_partsEq` (fallback decomposition);
2. `LvlRegs`, `rOfStmt` (`rOfStmt_runs`), and `buildTwinStmt` + `ListAt` encoding helpers.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Output-Word Bound and Connected-Component Fallback -/

private lemma exprEval_lt_of_bounded {w w' : ℕ} (hw' : w' ≤ w) {st : State}
    (hm : ∀ a, st.mem a < 2 ^ w) (hr : ∀ r, st.regs r < 2 ^ w) :
    ∀ {e : Expr} {v : ℕ}, Expr.eval w' st e = some v → v < 2 ^ w
  | .const k, v, h => by
    simp only [Expr.eval] at h
    split_ifs at h with hk
    cases h; exact lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) hw')
  | .reg r, v, h => by
    simp only [Expr.eval, Option.some.injEq] at h
    subst h; exact hr r
  | .load a, v, h => by
    simp only [Expr.eval, Option.map_eq_some_iff] at h
    rcases h with ⟨x, _, rfl⟩; exact hm x
  | .bin op a b, v, h => by
    simp only [Expr.eval] at h
    cases ha : a.eval w' st with
    | none => simp [ha] at h
    | some x =>
      cases hb : b.eval w' st with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        split_ifs at h with hlt
        cases h; exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hw')

private lemma evalArgs_lt_of_bounded {w w' : ℕ} (hw' : w' ≤ w) {st : State}
    (hm : ∀ a, st.mem a < 2 ^ w) (hr : ∀ r, st.regs r < 2 ^ w) :
    ∀ {es : List Expr} {vs : List ℕ}, evalArgs w' st es = some vs → ∀ v ∈ vs, v < 2 ^ w
  | [], vs, h => by simp [evalArgs] at h; subst h; simp
  | e :: es, vs, h => by
    simp only [evalArgs] at h
    cases he : e.eval w' st with
    | none => simp [he] at h
    | some v =>
      cases hes : evalArgs w' st es with
      | none => simp [he, hes] at h
      | some rest =>
        simp only [he, hes, Option.some.injEq] at h
        subst h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hrest
        · exact exprEval_lt_of_bounded hw' hm hr he
        · exact evalArgs_lt_of_bounded hw' hm hr hes x hrest

private lemma exec_preserves_bounded {w w' : ℕ} (hw' : w' ≤ w) (Q : Program) (ω : ℕ → Bool) :
    ∀ (fuel : ℕ) (s : Stmt) (st st' : State) (o : Outcome) (c : ℕ),
      (∀ a, st.mem a < 2 ^ w) → (∀ r, st.regs r < 2 ^ w) →
      exec w' Q ω fuel s st = some (o, st', c) →
      (∀ a, st'.mem a < 2 ^ w) ∧ (∀ r, st'.regs r < 2 ^ w) ∧ (∀ u, o = .returned u → u < 2 ^ w)
  | 0, _, _, _, _, _, _, _, h => by simp [exec] at h
  | fuel + 1, s, st, st', o, c, hm, hr, h => by
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, _⟩; exact ⟨hm, hr, fun _ hc => by cases hc⟩
    | assign r e =>
      simp only [exec] at h
      cases he : e.eval w' st with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, _⟩
        have hv := exprEval_lt_of_bounded hw' hm hr he
        refine ⟨hm, fun r' => ?_, fun _ hc => by cases hc⟩
        by_cases hrr : r' = r
        · subst hrr; simp [hv]
        · simp [Function.update_of_ne hrr, hr r']
    | store a e =>
      simp only [exec] at h
      cases ha : a.eval w' st with
      | none => simp [ha] at h
      | some x =>
        cases he : e.eval w' st with
        | none => simp [ha, he] at h
        | some v =>
          simp only [ha, he, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, _⟩
          have hv := exprEval_lt_of_bounded hw' hm hr he
          refine ⟨fun a' => ?_, hr, fun _ hc => by cases hc⟩
          by_cases haa : a' = x
          · subst haa; simp [hv]
          · simp [Function.update_of_ne haa, hm a']
    | rand r =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, _⟩
      have hread_lt : ∀ p' n, readWord ω p' n < 2 ^ n := by
        intro p' n
        induction n generalizing p' with
        | zero => simp [readWord]
        | succ k ih =>
          have := ih (p' + 1)
          simp only [readWord]
          rw [Nat.pow_succ']
          split_ifs <;> omega
      have hw_lt : readWord ω st.pos w' < 2 ^ w :=
        lt_of_lt_of_le (hread_lt st.pos w') (Nat.pow_le_pow_right (by norm_num) hw')
      refine ⟨hm, fun r' => ?_, fun _ hc => by cases hc⟩
      by_cases hrr : r' = r
      · subst hrr; simp [hw_lt]
      · simp [Function.update_of_ne hrr, hr r']
    | seq s₁ s₂ =>
      simp only [exec] at h
      cases h1 : exec w' Q ω fuel s₁ st with
      | none => simp [h1] at h
      | some res1 =>
        rcases res1 with ⟨o1, st1, c1⟩
        rcases exec_preserves_bounded hw' Q ω fuel s₁ st st1 o1 c1 hm hr h1 with ⟨hm1, hr1, ho1⟩
        cases o1 with
        | returned u =>
          simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, _⟩; exact ⟨hm1, hr1, fun u' hu => by cases hu; exact ho1 u rfl⟩
        | normal =>
          simp only [h1] at h
          cases h2 : exec w' Q ω fuel s₂ st1 with
          | none => simp [h2] at h
          | some res2 =>
            rcases res2 with ⟨o2, st2, c2⟩
            simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨h_o, h_st, _⟩
            subst h_o; subst h_st
            exact exec_preserves_bounded hw' Q ω fuel s₂ st1 st2 o2 c2 hm1 hr1 h2
    | cond e s₁ s₂ =>
      simp only [exec] at h
      cases he : e.eval w' st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        cases hmatch : exec w' Q ω fuel (if v = 0 then s₂ else s₁) st with
        | none => rw [hmatch] at h; cases h
        | some resm =>
          rcases resm with ⟨om, stm, cm⟩
          rw [hmatch] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, _⟩
          exact exec_preserves_bounded hw' Q ω fuel (if v = 0 then s₂ else s₁) st stm om cm hm hr hmatch
    | loop e body =>
      simp only [exec] at h
      cases he : e.eval w' st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        split_ifs at h with hv0
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, _⟩; exact ⟨hm, hr, fun _ hc => by cases hc⟩
        · cases hb : exec w' Q ω fuel body st with
          | none => simp [hb] at h
          | some resb =>
            rcases resb with ⟨ob, stb, cb⟩
            rcases exec_preserves_bounded hw' Q ω fuel body st stb ob cb hm hr hb with ⟨hmb, hrb, hob⟩
            cases ob with
            | returned u =>
              simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl, _⟩; exact ⟨hmb, hrb, fun u' hu => by cases hu; exact hob u rfl⟩
            | normal =>
              simp only [hb] at h
              cases hl : exec w' Q ω fuel (.loop e body) stb with
              | none => simp [hl] at h
              | some resl =>
                rcases resl with ⟨ol, stl, cl⟩
                simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨h_o, h_st, _⟩
                subst h_o; subst h_st
                exact exec_preserves_bounded hw' Q ω fuel (.loop e body) stb stl ol cl hmb hrb hl
    | call r f args =>
      simp only [exec] at h
      cases hev : evalArgs w' st args with
      | none => simp [hev] at h
      | some vs =>
        cases hp : Q.procs[f]? with
        | none => simp [hev, hp] at h
        | some body =>
          simp only [hev, hp] at h
          have hvs := evalArgs_lt_of_bounded hw' hm hr hev
          have hzero_lt : 0 < 2 ^ w := Nat.two_pow_pos w
          have hr_init : ∀ i, vs.getD i 0 < 2 ^ w := fun i => by
            rw [List.getD_eq_getElem?_getD]
            cases hge : vs[i]? with
            | none => exact hzero_lt
            | some v => exact hvs v (List.mem_of_getElem? hge)
          cases hb : exec w' Q ω fuel body { st with regs := fun i => vs.getD i 0 } with
          | none => rw [hb] at h; simp at h
          | some resb =>
            rcases resb with ⟨ob, stb, cb⟩
            rw [hb] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, _⟩
            rcases exec_preserves_bounded hw' Q ω fuel body { st with regs := fun i => vs.getD i 0 }
                stb ob cb hm hr_init hb with ⟨hmb, hrb, hob⟩
            have hu_lt : (match ob with | .returned u => u | .normal => 0) < 2 ^ w := by
              cases ob with
              | normal => exact hzero_lt
              | returned u => exact hob u rfl
            refine ⟨hmb, fun r' => ?_, fun _ hc => by cases hc⟩
            by_cases hrr : r' = r
            · subst hrr; simp only [Function.update_self]; exact hu_lt
            · simp only [Function.update_of_ne hrr]; exact hr r'
    | ret e =>
      simp only [exec] at h
      cases he : e.eval w' st with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, _⟩
        exact ⟨hm, hr, fun u' hu => by cases hu; exact exprEval_lt_of_bounded hw' hm hr he⟩

lemma runsTo_mem_lt_of_input_lt {w w' : ℕ} (hw' : w' ≤ w) {Q : Program}
    {x : List ℕ} {ω : ℕ → Bool} {out : List ℕ} {cost : ℕ}
    (hx : ∀ v ∈ x, v < 2 ^ w) (hrun : RunsTo w' Q x ω out cost) :
    ∀ v ∈ out, v < 2 ^ w := by
  rcases hrun with ⟨fuel, hf⟩
  simp only [run] at hf
  cases hex : exec w' Q ω fuel (.call 0 0 [.const x.length])
      { mem := initMem x, regs := fun _ => 0, pos := 0 } with
  | none => simp [hex] at hf
  | some res =>
    rcases res with ⟨o, st', c⟩
    simp only [hex, Option.some.injEq, Prod.mk.injEq] at hf
    rcases hf with ⟨rfl, _⟩
    have h0 : 0 < 2 ^ w := Nat.two_pow_pos w
    have hm0 : ∀ a, initMem x a < 2 ^ w := fun a => by
      dsimp only [initMem]
      rw [List.getD_eq_getElem?_getD]
      cases hget : x[a]? with
      | none => exact h0
      | some v => exact hx v (List.mem_of_getElem? hget)
    have hm' := (exec_preserves_bounded hw' Q ω fuel _ _ st' o c hm0 (fun _ => h0) hex).1
    intro v hv
    rcases List.mem_map.mp hv with ⟨a, _, rfl⟩
    exact hm' a

lemma isExpanderDecomposition_of_partsEq {G : Cited.Graph} {D_phi thr : ℕ}
    (hV : G.IsValid) (hm_lt : G.m < thr) (hthr : thr + 1 ≤ D_phi)
    {label : List ℕ} (hlen : label.length = G.n)
    (hparts : Cited.partsOf G label = Cited.partsOf G (compLabels G)) :
    IsExpanderDecomposition G (1 / 200) (1 / (D_phi : ℝ)) label := by
  have hDphi_pos : (0 : ℝ) < D_phi := by
    have : 1 ≤ D_phi := by omega
    exact_mod_cast this
  refine ⟨hlen, ?_, ?_⟩
  · intro X hX S hSX hSne hSXne
    rw [hparts] at hX
    have hcut1 : (1 : ℝ) ≤ G.cutIn X S := by
      exact_mod_cast cutIn_ge_one_of_part_compLabels hV hX hSX hSne hSXne
    have hsum_v : G.volIn X S + G.volIn X (X \ S) = 2 * (G.inside X).length :=
      volIn_add_volIn_sdiff G X S hSX
    have hmin_le : min (G.volIn X S) (G.volIn X (X \ S)) ≤ G.m := by
      have hlen_m := inside_length_le_m G X
      omega
    have hmin_r : min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) ≤ (D_phi : ℝ) := by
      exact_mod_cast (by omega : min (G.volIn X S) (G.volIn X (X \ S)) ≤ D_phi)
    calc (1 / (D_phi : ℝ)) * min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ)
        ≤ (1 / (D_phi : ℝ)) * (D_phi : ℝ) := mul_le_mul_of_nonneg_left hmin_r (by positivity)
      _ = 1 := by field_simp
      _ ≤ G.cutIn X S := hcut1
  · rw [hparts]
    have hzero : ∑ X ∈ Cited.partsOf G (compLabels G), (G.cut X : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro X hX
      simp [cut_part_compLabels_eq_zero hV hX]
    rw [hzero]
    positivity

/-! ## 2. Shared Level Register Invariant, `rOfStmt`, and `buildTwinStmt` -/

/-- Persistent register assignment of `levelProc` (`regs 0..18`). -/
def LvlRegs (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
    keptVertAddr statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr : ℕ) (st : State) : Prop :=
  st.regs 0 = curGAddr ∧ st.regs 1 = curIdxAddr ∧ st.regs 2 = nextGAddr ∧
  st.regs 3 = nextIdxAddr ∧ st.regs 4 = lvlArrAddr ∧ st.regs 5 = twAddr ∧
  st.regs 6 = bufAddr ∧ st.regs 7 = workAddr ∧ st.regs 8 = keptVertAddr ∧
  st.regs 9 = statePtr ∧ st.regs 10 = lvl ∧ st.regs 11 = D ∧
  st.regs 12 = D_phi ∧ st.regs 13 = mCap ∧ st.regs 14 = curN ∧
  st.regs 15 = curM ∧ st.regs 16 = csrAddr ∧ st.regs 17 = qAddr ∧
  st.regs 18 = lblAddr

lemma lvlRegs_of_eq {curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
    keptVertAddr statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr : ℕ}
    {st st' : State} (h : ∀ r < 19, st'.regs r = st.regs r)
    (hs : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr st) :
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curN curM csrAddr qAddr lblAddr st' := by
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h 0 (by decide), h0]
  · rw [h 1 (by decide), h1]
  · rw [h 2 (by decide), h2]
  · rw [h 3 (by decide), h3]
  · rw [h 4 (by decide), h4]
  · rw [h 5 (by decide), h5]
  · rw [h 6 (by decide), h6]
  · rw [h 7 (by decide), h7]
  · rw [h 8 (by decide), h8]
  · rw [h 9 (by decide), h9]
  · rw [h 10 (by decide), h10]
  · rw [h 11 (by decide), h11]
  · rw [h 12 (by decide), h12]
  · rw [h 13 (by decide), h13]
  · rw [h 14 (by decide), h14]
  · rw [h 15 (by decide), h15]
  · rw [h 16 (by decide), h16]
  · rw [h 17 (by decide), h17]
  · rw [h 18 (by decide), h18]

def rOfStmt (rIn rOut rTmp1 rTmp2 : ℕ) : Stmt :=
  seqStmts
    [ .assign rTmp1 (.reg rIn)
    , .assign rOut (.const 0)
    , .loop (.bin .lt (.const 1) (.reg rTmp1))
        (seqStmts
          [ .assign rTmp1 (.bin .div (.reg rTmp1) (.const 2))
          , .assign rOut (.bin .add (.reg rOut) (.const 1)) ])
    , .assign rTmp2 (.reg rOut)
    , .assign rOut (.const 0)
    , .assign rTmp1 (.const 1)
    , .loop (.bin .lt (.bin .mul (.bin .mul (.reg rTmp1) (.reg rTmp1)) (.reg rTmp1))
          (.bin .add (.reg rTmp2) (.const 1)))
        (seqStmts
          [ .assign rOut (.bin .add (.reg rOut) (.const 1))
          , .assign rTmp1 (.bin .add (.reg rOut) (.const 1)) ]) ]

lemma rOfStmt_noRand (rIn rOut rTmp1 rTmp2 : ℕ) :
    (rOfStmt rIn rOut rTmp1 rTmp2).NoRand := by
  simp [rOfStmt, seqStmts, Stmt.NoRand]

/-- Direct execution lemma for `rOfStmt`, preserving memory, `pos`, and all registers outside
`{rOut, rTmp1, rTmp2}`. -/
lemma rOfStmt_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (rIn rOut rTmp1 rTmp2 : ℕ) (hd : [rIn, rOut, rTmp1, rTmp2].Nodup)
    (t : ℕ) (ht : t < 2 ^ w) (htp : Nat.log 2 t + 1 < 2 ^ w)
    (hcube : (rOf t + 1) ^ 3 < 2 ^ w) (h4 : 4 ≤ 2 ^ w)
    (st₀ : State) (hr_in : st₀.regs rIn = t) :
    ∃ st' c,
      Runs w p ω (rOfStmt rIn rOut rTmp1 rTmp2) st₀ .normal st' c ∧
      st'.regs rOut = rOf t ∧
      st'.mem = st₀.mem ∧
      st'.pos = st₀.pos ∧
      (∀ r, r ≠ rOut → r ≠ rTmp1 → r ≠ rTmp2 → st'.regs r = st₀.regs r) ∧
      c ≤ 40 * (Nat.log 2 (t + 1) + 2) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd
  rcases hd with ⟨⟨hin_out, hin_t1, hin_t2⟩, ⟨hout_t1, hout_t2⟩, ht1_t2, _⟩
  have hlog_le : Nat.log 2 t < 2 ^ w := by omega
  have hcb_eq : cubeRoot (Nat.log 2 t) = rOf t := by
    have h1 := cubeRoot_pow_le (Nat.log 2 t)
    have h2 := lt_cubeRoot_succ_pow (Nat.log 2 t)
    have h3 := rOf_pow_le t
    have h4 := lt_rOf_succ_pow t
    apply le_antisymm
    · by_contra hgt
      have hge : rOf t + 1 ≤ cubeRoot (Nat.log 2 t) := by omega
      have hpow := Nat.pow_le_pow_left hge 3
      omega
    · by_contra hgt
      have hge : cubeRoot (Nat.log 2 t) + 1 ≤ rOf t := by omega
      have hpow := Nat.pow_le_pow_left hge 3
      omega
  have hr_le_log : rOf t ≤ Nat.log 2 t := by
    have hpow := rOf_pow_le t
    rcases hreq : rOf t with _ | k
    · exact Nat.zero_le _
    · rw [hreq] at hpow
      have h1 : k + 1 ≤ (k + 1) ^ 3 := Nat.le_self_pow (by decide) _
      omega
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  let st1 : State := { st₀ with regs := Function.update st₀.regs rTmp1 t }
  let st2 : State := { st1 with regs := Function.update st1.regs rOut 0 }
  have h1 : Runs w p ω (.assign rTmp1 (.reg rIn)) st₀ .normal st1 2 :=
    runs_assign_iff.mpr ⟨t, by simp [Expr.eval, hr_in], rfl, rfl, by simp [Expr.size]⟩
  have h2 : Runs w p ω (.assign rOut (.const 0)) st1 .normal st2 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0w], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st3, c3, hr3, hr3_out, hm3, hp3, hreg3, hc3⟩ :=
    log2_loop_runs rTmp1 rOut (Ne.symm hout_t1) t ht h4 st2
      (by dsimp [st2, st1]; rw [Function.update_of_ne (Ne.symm hout_t1), Function.update_self])
      (by simp [st2]) hlog_le
  let st4 : State := { st3 with regs := Function.update st3.regs rTmp2 (Nat.log 2 t) }
  let st5 : State := { st4 with regs := Function.update st4.regs rOut 0 }
  let st6 : State := { st5 with regs := Function.update st5.regs rTmp1 1 }
  have h4' : Runs w p ω (.assign rTmp2 (.reg rOut)) st3 .normal st4 2 :=
    runs_assign_iff.mpr ⟨Nat.log 2 t, by simp [Expr.eval, hr3_out], rfl, rfl, by simp [Expr.size]⟩
  have h5' : Runs w p ω (.assign rOut (.const 0)) st4 .normal st5 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0w], rfl, rfl, by simp [Expr.size]⟩
  have h6' : Runs w p ω (.assign rTmp1 (.const 1)) st5 .normal st6 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h1w], rfl, rfl, by simp [Expr.size]⟩
  have hr6_t2 : st6.regs rTmp2 = Nat.log 2 t := by
    dsimp [st6, st5, st4]
    rw [Function.update_of_ne (Ne.symm ht1_t2), Function.update_of_ne (Ne.symm hout_t2),
      Function.update_self]
  obtain ⟨st7, c7, hr7, hr7_out, hm7, hp7, hreg7, hc7⟩ :=
    cubeRoot_loop_runs rOut rTmp2 rTmp1
      (by simp [List.nodup_cons, hout_t2, hout_t1, Ne.symm ht1_t2])
      (Nat.log 2 t) (by rwa [hcb_eq]) htp h4 st6 hr6_t2
      (by dsimp [st6, st5]; rw [Function.update_of_ne hout_t1, Function.update_self])
      (by simp [st6])
  have runs_seq' : ∀ {s₁ s₂ : Stmt} {a b c : State} {k₁ k₂ : ℕ},
      Runs w p ω s₁ a .normal b k₁ → Runs w p ω s₂ b .normal c k₂ →
      Runs w p ω (.seq s₁ s₂) a .normal c (k₁ + k₂ + 1) :=
    fun h1 h2 => runs_seq_iff.mpr (Or.inr ⟨_, _, _, h1, h2, rfl⟩)
  have hfull :=
    runs_seq' h1 <| runs_seq' h2 <| runs_seq' hr3 <| runs_seq' h4' <| runs_seq' h5' <| runs_seq' h6' hr7
  have hlog_mono : Nat.log 2 t ≤ Nat.log 2 (t + 1) := Nat.log_mono_right (Nat.le_succ t)
  refine ⟨st7, _, hfull, by rw [hr7_out, hcb_eq], hm7.trans hm3, hp7.trans hp3,
    fun r hro hrt1 hrt2 => ?_, by omega⟩
  rw [hreg7 r hro hrt2 hrt1]
  dsimp [st6, st5, st4]
  rw [Function.update_of_ne hrt1, Function.update_of_ne hro, Function.update_of_ne hrt2,
    hreg3 r hrt1 hro]
  dsimp [st2, st1]
  rw [Function.update_of_ne hro, Function.update_of_ne hrt1]

/-- Builds `(twinGraph D curG).encode ++ [1, 200, rOf m_twin]` at `twAddr` (`reg 5`).
Writes `m_twin` to `reg 19`, `twLen = 5 + 2 * m_twin` to `reg 20`, `r_twin` to `reg 21`. -/
def buildTwinStmt : Stmt :=
  seqStmts
    [ .assign 19 (.bin .add (.reg 15) (.bin .mul (.reg 11) (.reg 14)))
    , .assign 20 (.bin .mul (.const 2) (.reg 14))
    , .store (.reg 5) (.reg 20)
    , .store (.bin .add (.reg 5) (.const 1)) (.reg 19)
    , forRange 22 (.const 0) (.reg 15)
        (seqStmts
          [ .assign 23 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22)))))
          , .assign 24 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22)))))
          , .store (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22))))
              (.bin .mul (.const 2) (.reg 23))
          , .store (.bin .add (.reg 5) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22))))
              (.bin .mul (.const 2) (.reg 24)) ])
    , .assign 25 (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 15))))
    , forRange 22 (.const 0) (.reg 14)
        (seqStmts
          [ .assign 23 (.bin .mul (.const 2) (.reg 22))
          , .assign 24 (.bin .add (.reg 23) (.const 1))
          , forRange 26 (.const 0) (.reg 11)
              (seqStmts
                [ .store (.reg 25) (.reg 23)
                , .store (.bin .add (.reg 25) (.const 1)) (.reg 24)
                , .assign 25 (.bin .add (.reg 25) (.const 2)) ]) ])
    , rOfStmt 19 21 22 23
    , .store (.reg 25) (.const 1)
    , .store (.bin .add (.reg 25) (.const 1)) (.const 200)
    , .store (.bin .add (.reg 25) (.const 2)) (.reg 21)
    , .assign 20 (.bin .add (.bin .mul (.const 2) (.reg 19)) (.const 5)) ]

lemma buildTwinStmt_noRand : buildTwinStmt.NoRand := by
  simp [buildTwinStmt, rOfStmt_noRand, forRange, WordRAM.forUp, seqStmts, Stmt.NoRand]

private lemma twinEdges_flatMap_eq (n D : ℕ) :
    ((List.range n).flatMap fun u => List.replicate D (2 * u, 2 * u + 1)).flatMap
        (fun e => [e.1, e.2]) =
      ((List.range n).flatMap fun u => (List.replicate D (2 * u, 2 * u + 1)).flatMap
        fun e => [e.1, e.2]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_append, ih]
    simp

lemma listAt_replicate_pairs (mem : ℕ → ℕ) (base u D : ℕ)
    (h : ∀ d < D, mem (base + 2 * d) = 2 * u ∧ mem (base + 2 * d + 1) = 2 * u + 1) :
    ListAt mem base ((List.replicate D (2 * u, 2 * u + 1)).flatMap fun e => [e.1, e.2]) := by
  induction D generalizing base with
  | zero => simp [ListAt]
  | succ d ih =>
    simp only [List.replicate_succ, List.flatMap_cons]
    refine listAt_cons.mpr ⟨(h 0 (Nat.zero_lt_succ d)).1, listAt_cons.mpr ⟨(h 0 (Nat.zero_lt_succ d)).2, ?_⟩⟩
    simpa [Nat.add_assoc, show 2 * (d + 1) = 2 + 2 * d by omega] using
      ih (base + 2) (fun j hj => by
        have := h (j + 1) (by omega)
        simpa [Nat.add_assoc, show base + 2 + 2 * j = base + 2 * (j + 1) by omega] using this)

lemma listAt_twinEdges_block (mem : ℕ → ℕ) (base n D : ℕ)
    (h : ∀ u < n, ∀ d < D,
      mem (base + 2 * (u * D + d)) = 2 * u ∧ mem (base + 2 * (u * D + d) + 1) = 2 * u + 1) :
    ListAt mem base
      (((List.range n).flatMap fun u => List.replicate D (2 * u, 2 * u + 1)).flatMap
        fun e => [e.1, e.2]) := by
  rw [twinEdges_flatMap_eq]
  induction n generalizing base with
  | zero => simp [ListAt]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine listAt_append.mpr ⟨ih base fun u hu d hd => h u (by omega) d hd, ?_⟩
    have hlen : ((List.range n).flatMap fun u =>
        (List.replicate D (2 * u, 2 * u + 1)).flatMap fun e => [e.1, e.2]).length = 2 * (n * D) := by
      clear h ih
      induction n with
      | zero => simp
      | succ k ihk =>
        rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton, ihk]
        have hrep : ∀ D' (p : ℕ × ℕ), ((List.replicate D' p).flatMap fun e => [e.1, e.2]).length = 2 * D' := by
          intro D' p; induction D' with | zero => simp | succ a iha => simp [List.replicate_succ, iha]; omega
        rw [hrep]
        ring
    rw [hlen]
    exact listAt_replicate_pairs mem (base + 2 * (n * D)) n D fun d hd => by
      have := h n (Nat.lt_succ_self n) d hd
      simpa [Nat.add_assoc, show base + 2 * (n * D) + 2 * d = base + 2 * (n * D + d) by omega] using this

lemma listAt_scaledEdges (mem : ℕ → ℕ) (base : ℕ) (E : List (ℕ × ℕ))
    (h : ∀ j (hj : j < E.length),
      mem (base + 2 * j) = 2 * E[j].1 ∧ mem (base + 2 * j + 1) = 2 * E[j].2) :
    ListAt mem base ((E.map fun e => (2 * e.1, 2 * e.2)).flatMap fun e => [e.1, e.2]) := by
  induction E generalizing base with
  | nil => simp [ListAt]
  | cons e rest ih =>
    simp only [List.map_cons, List.flatMap_cons, List.cons_append]
    have h0 := h 0 (by simp)
    refine listAt_cons.mpr ⟨h0.1, listAt_cons.mpr ⟨h0.2, ?_⟩⟩
    have ih' := ih (base + 2) fun j hj => by
      have := h (j + 1) (by simpa using Nat.succ_lt_succ hj)
      simpa [Nat.add_assoc, show base + 2 + 2 * j = base + 2 * (j + 1) by omega] using this
    simpa [Nat.add_assoc] using ih'

end MinCostFlow.Expander
