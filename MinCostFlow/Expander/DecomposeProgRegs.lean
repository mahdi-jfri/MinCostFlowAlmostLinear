module

public import MinCostFlow.Expander.DecomposeProgBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Helper Word RAM Subroutines for `DecomposeProg`

Reusable helper `Stmt`s and their `Runs` / `Triple` specifications:
* `copyMemLoop` — disjoint memory range copy (`forRange`),
* `zeroRangeLoop` — zero-fill `[dst, dst + len)` (used by the `m ≤ n` fast path),
* `iotaRangeLoop` — fill `dst[j] = j` (`0 ≤ j < m`, initial edge indices),
* `sparseFastPathStmt` — exact `O(m + 1)` fast path when `m ≤ n`,
* `computeEllStmt` — `ℓ = Nat.log 2 (m / n) + 1`,
* `computeLayoutStmt` — computes all `DecompLayout` addresses and initial `ℓ, 2^ℓ` registers,
* `initMemoryStmt` — initializes `statePtr[0..2]`, `g0`, `idx0`,
* `packOutputStmt` — writes header, copies `lvlArr`, and appends ascending arena slices into `[h, ...)`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

public section

lemma ev_eq_of {w : ℕ} {st : State} {e : Expr} {x y : ℕ}
    (h1 : Expr.eval w st e = some x) (h2 : x = y) : Expr.eval w st e = some y :=
  h2 ▸ h1

lemma ev_const {w : ℕ} {st : State} {k : ℕ} (hk : k < 2 ^ w) :
    Expr.eval w st (.const k) = some k := by simp [Expr.eval, hk]

lemma ev_reg {w : ℕ} {st : State} {r v : ℕ} (hv : st.regs r = v) :
    Expr.eval w st (.reg r) = some v := by simp [Expr.eval, hv]

lemma ev_add {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (hxy : x + y < 2 ^ w) :
    Expr.eval w st (.bin .add a b) = some (x + y) := by
  simp [Expr.eval, BinOp.eval, ha, hb, hxy]

lemma ev_sub {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (hxy : x - y < 2 ^ w) :
    Expr.eval w st (.bin .sub a b) = some (x - y) := by
  simp [Expr.eval, BinOp.eval, ha, hb, hxy]

lemma ev_mul {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (hxy : x * y < 2 ^ w) :
    Expr.eval w st (.bin .mul a b) = some (x * y) := by
  simp [Expr.eval, BinOp.eval, ha, hb, hxy]

lemma ev_load {w : ℕ} {st : State} {a : Expr} {x v : ℕ}
    (ha : Expr.eval w st a = some x) (hv : st.mem x = v) :
    Expr.eval w st a.load = some v := by
  simp [Expr.eval, ha, hv]

lemma ev_shl {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : Expr.eval w st a = some x) (hb : Expr.eval w st b = some y) (hxy : x <<< y < 2 ^ w) :
    Expr.eval w st (.bin .shiftLeft a b) = some (x <<< y) := by
  simp [Expr.eval, BinOp.eval, ha, hb, hxy]

/-! ## 1. Register Map & Invariant -/

abbrev rGAddr : ℕ := 0
abbrev rOutH : ℕ := 1
abbrev rN : ℕ := 2
abbrev rM : ℕ := 3
abbrev rEll : ℕ := 4
abbrev rDphi : ℕ := 5
abbrev rStatePtr : ℕ := 6
abbrev rBounds : ℕ := 7
abbrev rLvlArr : ℕ := 8
abbrev rCurG : ℕ := 9
abbrev rCurIdx : ℕ := 10
abbrev rNextG : ℕ := 11
abbrev rNextIdx : ℕ := 12
abbrev rTw : ℕ := 13
abbrev rBuf : ℕ := 14
abbrev rWork : ℕ := 15
abbrev rKept : ℕ := 16
abbrev rArena : ℕ := 17
abbrev rZC : ℕ := 18
abbrev rLvl : ℕ := 19
abbrev rD : ℕ := 20
abbrev rTmp1 : ℕ := 21
abbrev rTmp2 : ℕ := 22
abbrev rTmp3 : ℕ := 23
abbrev rTmp4 : ℕ := 24
abbrev rTmp5 : ℕ := 25
abbrev rRet : ℕ := 26

@[expose] def DecompRegs (gAddr h n m ℓ D_phi lvl D curGAddr curIdxAddr nextGAddr nextIdxAddr : ℕ)
    (L : DecompLayout) (st : State) : Prop :=
  st.regs rGAddr = gAddr ∧ st.regs rOutH = h ∧ st.regs rN = n ∧ st.regs rM = m ∧
  st.regs rEll = ℓ ∧ st.regs rDphi = D_phi ∧
  st.regs rStatePtr = L.statePtr ∧ st.regs rBounds = L.boundsAddr ∧
  st.regs rLvlArr = L.lvlArrAddr ∧
  st.regs rCurG = curGAddr ∧ st.regs rCurIdx = curIdxAddr ∧
  st.regs rNextG = nextGAddr ∧ st.regs rNextIdx = nextIdxAddr ∧
  st.regs rTw = L.twAddr ∧ st.regs rBuf = L.bufAddr ∧
  st.regs rWork = L.workAddr ∧ st.regs rKept = L.keptVertAddr ∧
  st.regs rArena = L.arena₀ ∧ st.regs rZC = L.zeroCursor₀ ∧
  st.regs rLvl = lvl ∧ st.regs rD = D

lemma decompRegs_of_eq {gAddr h n m ℓ D_phi lvl D curGAddr curIdxAddr nextGAddr nextIdxAddr : ℕ}
    {L : DecompLayout} {st₁ st₂ : State}
    (heq : ∀ r ≤ 20, st₂.regs r = st₁.regs r)
    (hr : DecompRegs gAddr h n m ℓ D_phi lvl D curGAddr curIdxAddr nextGAddr nextIdxAddr L st₁) :
    DecompRegs gAddr h n m ℓ D_phi lvl D curGAddr curIdxAddr nextGAddr nextIdxAddr L st₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq 0 (by omega)]; exact hr.1
  · rw [heq 1 (by omega)]; exact hr.2.1
  · rw [heq 2 (by omega)]; exact hr.2.2.1
  · rw [heq 3 (by omega)]; exact hr.2.2.2.1
  · rw [heq 4 (by omega)]; exact hr.2.2.2.2.1
  · rw [heq 5 (by omega)]; exact hr.2.2.2.2.2.1
  · rw [heq 6 (by omega)]; exact hr.2.2.2.2.2.2.1
  · rw [heq 7 (by omega)]; exact hr.2.2.2.2.2.2.2.1
  · rw [heq 8 (by omega)]; exact hr.2.2.2.2.2.2.2.2.1
  · rw [heq 9 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.1
  · rw [heq 10 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 11 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 12 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 13 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 14 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 15 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 16 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 17 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 18 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 19 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [heq 20 (by omega)]; exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## 2. Reusable Loop Helpers (`copyMemLoop`, `zeroRangeLoop`, `iotaRangeLoop`) -/

@[expose] def copyMemLoop (rSrc rDst rLen rIdx : ℕ) : Stmt :=
  forRange rIdx (.const 0) (.reg rLen)
    (.store (.bin .add (.reg rDst) (.reg rIdx)) (.load (.bin .add (.reg rSrc) (.reg rIdx))))

lemma copyMemLoop_noRand (rSrc rDst rLen rIdx : ℕ) :
    (copyMemLoop rSrc rDst rLen rIdx).NoRand := by
  exact forRange_noRand _ _ _ _ (by simp [Stmt.NoRand])

lemma copyMemLoop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (rSrc rDst rLen rIdx : ℕ) (hnd : [rSrc, rDst, rLen, rIdx].Nodup)
    (src dst len : ℕ) (st₀ : State)
    (hsrc : st₀.regs rSrc = src) (hdst : st₀.regs rDst = dst) (hlen : st₀.regs rLen = len)
    (hw1 : 1 < 2 ^ w) (hlen_w : len < 2 ^ w)
    (hsrc_w : src + len ≤ 2 ^ w) (hdst_w : dst + len ≤ 2 ^ w)
    (hdisj : src + len ≤ dst ∨ dst + len ≤ src) :
    ∃ st' c,
      Runs w p ω (copyMemLoop rSrc rDst rLen rIdx) st₀ .normal st' c ∧
      (∀ t < len, st'.mem (dst + t) = st₀.mem (src + t)) ∧
      (∀ a, a < dst ∨ dst + len ≤ a → st'.mem a = st₀.mem a) ∧
      st'.pos = st₀.pos ∧
      (∀ r, r ≠ rIdx → st'.regs r = st₀.regs r) ∧
      c ≤ 20 * len + 12 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs rIdx = i ∧ st.regs rSrc = src ∧ st.regs rDst = dst ∧ st.regs rLen = len ∧
    st.pos = st₀.pos ∧ (∀ r, r ≠ rIdx → st.regs r = st₀.regs r) ∧
    (∀ t < i, st.mem (dst + t) = st₀.mem (src + t)) ∧
    (∀ a, a < dst ∨ dst + i ≤ a → st.mem a = st₀.mem a)
  have hrun := forRange_varCost (w := w) (p := p) (ω := ω) rIdx (.const 0) (.reg rLen)
    (.store (.bin .add (.reg rDst) (.reg rIdx)) (.load (.bin .add (.reg rSrc) (.reg rIdx))))
    Inv (fun _ => 11) 0 len (Nat.zero_le len) hw1 hlen_w
    (fun i st _ _ hi => hi.1)
    (fun i st _ _ hi => by simp [Expr.eval, hi.2.2.2.1])
    (fun i st _ hi_lt hi => by
      have hsrc_lt : src + i < 2 ^ w := by omega
      have hdst_lt : dst + i < 2 ^ w := by omega
      let st₁ : State := { st with mem := Function.update st.mem (dst + i) (st.mem (src + i)) }
      have hstep : Runs w p ω
          (.store (.bin .add (.reg rDst) (.reg rIdx)) (.load (.bin .add (.reg rSrc) (.reg rIdx))))
          st .normal st₁ 8 := by
        apply runs_store_iff.mpr
        refine ⟨dst + i, st.mem (src + i), ?_, ?_, rfl, rfl, ?_⟩
        · simp [Expr.eval, BinOp.eval, hi.1, hi.2.2.1, hdst_lt]
        · simp [Expr.eval, BinOp.eval, hi.1, hi.2.1, hsrc_lt]
        · simp [Expr.size]
      refine ⟨st₁, 8, hstep, by omega, hi.1, ?_⟩
      have hi_not_src : src + i < dst ∨ dst + i ≤ src + i := by omega
      have hsrc_mem : st.mem (src + i) = st₀.mem (src + i) := hi.2.2.2.2.2.2.2 _ hi_not_src
      refine ⟨Function.update_self _ _ _,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact hi.2.1,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact hi.2.2.1,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact hi.2.2.2.1,
        hi.2.2.2.2.1,
        by intro r hr; dsimp only; rw [Function.update_of_ne hr]; exact hi.2.2.2.2.2.1 r hr, ?_, ?_⟩
      · intro t ht
        dsimp [st₁]
        by_cases hti : t = i
        · subst t; rw [Function.update_self, hsrc_mem]
        · rw [Function.update_of_ne (by omega)]; exact hi.2.2.2.2.2.2.1 t (by omega)
      · intro a ha
        dsimp [st₁]
        rw [Function.update_of_ne (by omega)]
        exact hi.2.2.2.2.2.2.2 a (by omega))
    st₀ (by simp [Expr.eval])
    ⟨Function.update_self _ _ _,
      by dsimp only; rw [Function.update_of_ne (by omega)]; exact hsrc,
      by dsimp only; rw [Function.update_of_ne (by omega)]; exact hdst,
      by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlen,
      rfl, fun r hr => Function.update_of_ne hr _ _,
      fun _ ht => by omega, fun _ _ => rfl⟩
  rcases hrun with ⟨st', c, hrun_st, hinv, hc⟩
  refine ⟨st', c, hrun_st, hinv.2.2.2.2.2.2.1, hinv.2.2.2.2.2.2.2, hinv.2.2.2.2.1,
    hinv.2.2.2.2.2.1, ?_⟩
  simp only [Expr.size, Finset.sum_const, Nat.card_Ico, Nat.sub_zero, smul_eq_mul] at hc
  omega

@[expose] def zeroRangeLoop (rDstOff rLen rIdx : ℕ) : Stmt :=
  forRange rIdx (.const 0) (.reg rLen)
    (.store (.bin .add (.reg rDstOff) (.reg rIdx)) (.const 0))

lemma zeroRangeLoop_noRand (rDstOff rLen rIdx : ℕ) :
    (zeroRangeLoop rDstOff rLen rIdx).NoRand :=
  forRange_noRand _ _ _ _ (by simp [Stmt.NoRand])

lemma zeroRangeLoop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (rDstOff rLen rIdx : ℕ) (hnd : [rDstOff, rLen, rIdx].Nodup)
    (dst len : ℕ) (st₀ : State)
    (hdst : st₀.regs rDstOff = dst) (hlen : st₀.regs rLen = len)
    (hw1 : 1 < 2 ^ w) (hlen_w : len < 2 ^ w) (hdst_w : dst + len ≤ 2 ^ w) :
    ∃ st' c,
      Runs w p ω (zeroRangeLoop rDstOff rLen rIdx) st₀ .normal st' c ∧
      (∀ t < len, st'.mem (dst + t) = 0) ∧
      (∀ a, a < dst ∨ dst + len ≤ a → st'.mem a = st₀.mem a) ∧
      st'.pos = st₀.pos ∧
      (∀ r, r ≠ rIdx → st'.regs r = st₀.regs r) ∧
      c ≤ 18 * len + 12 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs rIdx = i ∧ st.regs rDstOff = dst ∧ st.regs rLen = len ∧
    st.pos = st₀.pos ∧ (∀ r, r ≠ rIdx → st.regs r = st₀.regs r) ∧
    (∀ t < i, st.mem (dst + t) = 0) ∧
    (∀ a, a < dst ∨ dst + i ≤ a → st.mem a = st₀.mem a)
  have hrun := forRange_varCost (w := w) (p := p) (ω := ω) rIdx (.const 0) (.reg rLen)
    (.store (.bin .add (.reg rDstOff) (.reg rIdx)) (.const 0))
    Inv (fun _ => 9) 0 len (Nat.zero_le len) hw1 hlen_w
    (fun i st _ _ hi => hi.1)
    (fun i st _ _ hi => by simp [Expr.eval, hi.2.2.1])
    (fun i st _ hi_lt hi => by
      have hdst_lt : dst + i < 2 ^ w := by omega
      let st₁ : State := { st with mem := Function.update st.mem (dst + i) 0 }
      have hstep : Runs w p ω (.store (.bin .add (.reg rDstOff) (.reg rIdx)) (.const 0))
          st .normal st₁ 5 := by
        apply runs_store_iff.mpr
        refine ⟨dst + i, 0, by simp [Expr.eval, BinOp.eval, hi.1, hi.2.1, hdst_lt],
          by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      refine ⟨st₁, 5, hstep, by omega, hi.1, ?_⟩
      refine ⟨Function.update_self _ _ _,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact hi.2.1,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact hi.2.2.1,
        hi.2.2.2.1, fun r hr => by dsimp only; rw [Function.update_of_ne hr]; exact hi.2.2.2.2.1 r hr, ?_, ?_⟩
      · intro t ht
        dsimp [st₁]
        by_cases hti : t = i
        · subst t; exact Function.update_self _ _ _
        · rw [Function.update_of_ne (by omega)]; exact hi.2.2.2.2.2.1 t (by omega)
      · intro a ha
        dsimp [st₁]; rw [Function.update_of_ne (by omega)]; exact hi.2.2.2.2.2.2 a (by omega))
    st₀ (by simp [Expr.eval])
    ⟨Function.update_self _ _ _,
      by dsimp only; rw [Function.update_of_ne (by omega)]; exact hdst,
      by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlen,
      rfl, fun r hr => Function.update_of_ne hr _ _,
      fun _ ht => by omega, fun _ _ => rfl⟩
  rcases hrun with ⟨st', c, hrun_st, hinv, hc⟩
  refine ⟨st', c, hrun_st, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2, hinv.2.2.2.1, hinv.2.2.2.2.1, ?_⟩
  simp only [Expr.size, Finset.sum_const, Nat.card_Ico, Nat.sub_zero, smul_eq_mul] at hc
  omega

@[expose] def iotaRangeLoop (rDst rLen rIdx : ℕ) : Stmt :=
  forRange rIdx (.const 0) (.reg rLen)
    (.store (.bin .add (.reg rDst) (.reg rIdx)) (.reg rIdx))

lemma iotaRangeLoop_noRand (rDst rLen rIdx : ℕ) :
    (iotaRangeLoop rDst rLen rIdx).NoRand :=
  forRange_noRand _ _ _ _ (by simp [Stmt.NoRand])

lemma iotaRangeLoop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (rDst rLen rIdx : ℕ) (hnd : [rDst, rLen, rIdx].Nodup)
    (dst len : ℕ) (st₀ : State)
    (hdst : st₀.regs rDst = dst) (hlen : st₀.regs rLen = len)
    (hw1 : 1 < 2 ^ w) (hlen_w : len < 2 ^ w) (hdst_w : dst + len ≤ 2 ^ w) :
    ∃ st' c,
      Runs w p ω (iotaRangeLoop rDst rLen rIdx) st₀ .normal st' c ∧
      (∀ t < len, st'.mem (dst + t) = t) ∧
      (∀ a, a < dst ∨ dst + len ≤ a → st'.mem a = st₀.mem a) ∧
      st'.pos = st₀.pos ∧
      (∀ r, r ≠ rIdx → st'.regs r = st₀.regs r) ∧
      c ≤ 18 * len + 12 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs rIdx = i ∧ st.regs rDst = dst ∧ st.regs rLen = len ∧
    st.pos = st₀.pos ∧ (∀ r, r ≠ rIdx → st.regs r = st₀.regs r) ∧
    (∀ t < i, st.mem (dst + t) = t) ∧
    (∀ a, a < dst ∨ dst + i ≤ a → st.mem a = st₀.mem a)
  have hrun := forRange_varCost (w := w) (p := p) (ω := ω) rIdx (.const 0) (.reg rLen)
    (.store (.bin .add (.reg rDst) (.reg rIdx)) (.reg rIdx))
    Inv (fun _ => 9) 0 len (Nat.zero_le len) hw1 hlen_w
    (fun i st _ _ hi => hi.1)
    (fun i st _ _ hi => by simp [Expr.eval, hi.2.2.1])
    (fun i st _ hi_lt hi => by
      have hdst_lt : dst + i < 2 ^ w := by omega
      let st₁ : State := { st with mem := Function.update st.mem (dst + i) i }
      have hstep : Runs w p ω (.store (.bin .add (.reg rDst) (.reg rIdx)) (.reg rIdx))
          st .normal st₁ 5 := by
        apply runs_store_iff.mpr
        refine ⟨dst + i, i, by simp [Expr.eval, BinOp.eval, hi.1, hi.2.1, hdst_lt],
          by simp [Expr.eval, hi.1], rfl, rfl, by simp [Expr.size]⟩
      refine ⟨st₁, 5, hstep, by omega, hi.1, ?_⟩
      refine ⟨Function.update_self _ _ _,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact hi.2.1,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact hi.2.2.1,
        hi.2.2.2.1, fun r hr => by dsimp only; rw [Function.update_of_ne hr]; exact hi.2.2.2.2.1 r hr, ?_, ?_⟩
      · intro t ht
        dsimp [st₁]
        by_cases hti : t = i
        · subst t; exact Function.update_self _ _ _
        · rw [Function.update_of_ne (by omega)]; exact hi.2.2.2.2.2.1 t (by omega)
      · intro a ha
        dsimp [st₁]; rw [Function.update_of_ne (by omega)]; exact hi.2.2.2.2.2.2 a (by omega))
    st₀ (by simp [Expr.eval])
    ⟨Function.update_self _ _ _,
      by dsimp only; rw [Function.update_of_ne (by omega)]; exact hdst,
      by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlen,
      rfl, fun r hr => Function.update_of_ne hr _ _,
      fun _ ht => by omega, fun _ _ => rfl⟩
  rcases hrun with ⟨st', c, hrun_st, hinv, hc⟩
  refine ⟨st', c, hrun_st, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2, hinv.2.2.2.1, hinv.2.2.2.2.1, ?_⟩
  simp only [Expr.size, Finset.sum_const, Nat.card_Ico, Nat.sub_zero, smul_eq_mul] at hc
  omega

/-! ## 3. Sparse Fast Path (`m ≤ n`) -/

@[expose] def sparseFastPathStmt : Stmt :=
  seqStmts
    [ .store (.reg rOutH) (.const 0)
    , .store (.bin .add (.reg rOutH) (.const 1)) (.const 1)
    , .store (.bin .add (.reg rOutH) (.const 2)) (.const 1)
    , .assign rTmp1 (.bin .add (.reg rOutH) (.const 3))
    , zeroRangeLoop rTmp1 rM rTmp2
    , .store (.bin .add (.reg rOutH) (.bin .add (.const 3) (.reg rM))) (.const 0)
    , .ret (.bin .add (.reg rOutH) (.bin .add (.const 4) (.reg rM))) ]

lemma sparseFastPathStmt_noRand : sparseFastPathStmt.NoRand := by
  simp [sparseFastPathStmt, seqStmts, Stmt.NoRand, zeroRangeLoop_noRand]

lemma sparseFastPath_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (h m : ℕ) (st₀ : State)
    (hh : st₀.regs rOutH = h) (hm : st₀.regs rM = m)
    (hw4 : 4 < 2 ^ w) (hm4 : h + m + 4 < 2 ^ w) :
    ∃ st' c,
      Runs w p ω sparseFastPathStmt st₀ (.returned (h + m + 4)) st' c ∧
      DecomposeOutAt st'.mem h 0 1 1 (List.replicate m 0) [] ∧
      (∀ a, a < h ∨ h + m + 4 ≤ a → st'.mem a = st₀.mem a) ∧
      c ≤ 18 * m + 55 := by
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw4
  have hh_w : h < 2 ^ w := by omega
  have hh1_w : h + 1 < 2 ^ w := by omega
  have hh2_w : h + 2 < 2 ^ w := by omega
  have hh3_w : h + 3 < 2 ^ w := by omega
  have hh3m_w : h + (3 + m) < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  let st1 : State := { st₀ with mem := Function.update st₀.mem h 0 }
  have h1 : Runs w p ω (.store (.reg rOutH) (.const 0)) st₀ .normal st1 3 := by
    apply runs_store_iff.mpr
    refine ⟨h, 0, by simp [Expr.eval, hh], by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with mem := Function.update st1.mem (h + 1) 1 }
  have h2 : Runs w p ω (.store (.bin .add (.reg rOutH) (.const 1)) (.const 1)) st1 .normal st2 5 := by
    apply runs_store_iff.mpr
    refine ⟨h + 1, 1, by simp [Expr.eval, BinOp.eval, st1, hh, hh1_w, hw0],
      by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  let st3 : State := { st2 with mem := Function.update st2.mem (h + 2) 1 }
  have h3 : Runs w p ω (.store (.bin .add (.reg rOutH) (.const 2)) (.const 1)) st2 .normal st3 5 := by
    apply runs_store_iff.mpr
    refine ⟨h + 2, 1, by simp [Expr.eval, BinOp.eval, st2, st1, hh, hh2_w, show 2 < 2 ^ w by omega],
      by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  let st4 : State := { st3 with regs := Function.update st3.regs rTmp1 (h + 3) }
  have h4 : Runs w p ω (.assign rTmp1 (.bin .add (.reg rOutH) (.const 3))) st3 .normal st4 4 := by
    apply runs_assign_iff.mpr
    refine ⟨h + 3, by simp [Expr.eval, BinOp.eval, st3, st2, st1, hh, hh3_w, show 3 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hnd : [rTmp1, rM, rTmp2].Nodup := by decide
  obtain ⟨st5, c5, h5, h5_zero, h5_fr, _, h5_regs, hc5⟩ :=
    zeroRangeLoop_runs (w := w) (p := p) (ω := ω) rTmp1 rM rTmp2 hnd (h + 3) m st4
      (by simp [st4, Function.update_self])
      (by simp [st4, st3, st2, st1, Function.update_of_ne, hm])
      (by omega) hm_w (by omega)
  let st6 : State := { st5 with mem := Function.update st5.mem (h + (3 + m)) 0 }
  have h5_h : st5.regs rOutH = h := by rw [h5_regs _ (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hh]
  have h5_m : st5.regs rM = m := by rw [h5_regs _ (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hm]
  have h6 : Runs w p ω (.store (.bin .add (.reg rOutH) (.bin .add (.const 3) (.reg rM))) (.const 0))
      st5 .normal st6 7 := by
    apply runs_store_iff.mpr
    refine ⟨h + (3 + m), 0, by
      simp [Expr.eval, BinOp.eval, h5_h, h5_m, show 3 < 2 ^ w by omega, show 3 + m < 2 ^ w by omega, hh3m_w],
      by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have h7 : Runs w p ω (.ret (.bin .add (.reg rOutH) (.bin .add (.const 4) (.reg rM))))
      st6 (.returned (h + m + 4)) st6 6 := by
    apply runs_ret_iff.mpr
    refine ⟨h + m + 4, by
      simp [Expr.eval, BinOp.eval, st6, h5_h, h5_m, hw4, show 4 + m < 2 ^ w by omega,
        show h + (4 + m) = h + m + 4 by omega, hm4],
      rfl, rfl, by simp [Expr.size]⟩
  have hfull := runs_seq h1 (runs_seq h2 (runs_seq h3 (runs_seq h4 (runs_seq h5 (runs_seq h6 h7)))))
  change Runs w p ω sparseFastPathStmt st₀ (.returned (h + m + 4)) st6 _ at hfull
  refine ⟨st6, _, hfull, ?_, ?_, ?_⟩
  · intro i hi
    have henc : Decompose.encode 0 1 1 (List.replicate m 0) [] =
        [0, 1, 1] ++ List.replicate m 0 ++ [0] := by
      simp [Decompose.encode]
    simp only [henc] at hi ⊢
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ (3 ≤ i ∧ i < 3 + m) ∨ i = 3 + m by
      simp [List.length_replicate] at hi; omega) with rfl | rfl | rfl | ⟨hi3, him⟩ | rfl
    · dsimp [st6]
      rw [Function.update_of_ne (by omega : h ≠ h + (3 + m)), h5_fr _ (by omega)]
      dsimp [st4, st3, st2, st1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · dsimp [st6]
      rw [Function.update_of_ne (by omega : h + 1 ≠ h + (3 + m)), h5_fr _ (by omega)]
      dsimp [st4, st3, st2]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · dsimp [st6]
      rw [Function.update_of_ne (by omega : h + 2 ≠ h + (3 + m)), h5_fr _ (by omega)]
      dsimp [st4, st3]
      rw [Function.update_self]
    · have hi_idx : i - 3 < m := by omega
      have hi_len : i < ([0, 1, 1] ++ List.replicate m 0).length := by
        simp [List.length_replicate]; omega
      have hrep : (List.replicate m 0).length = m := List.length_replicate
      rw [show ([0, 1, 1] ++ List.replicate m 0 ++ [0])[i] = 0 from by
        rw [List.getElem_append_left hi_len]
        have h3 : (0 :: 1 :: 1 :: List.replicate m 0)[i]'hi_len = (List.replicate m 0)[i - 3]'(by rw [hrep]; omega) := by
          rcases i with _ | _ | _ | k
          · omega
          · omega
          · omega
          · rfl
        exact h3.trans (by simp [List.getElem_replicate])]
      dsimp [st6]
      rw [Function.update_of_ne (by omega : h + i ≠ h + (3 + m)),
        show h + i = h + 3 + (i - 3) by omega, h5_zero (i - 3) hi_idx]
    · have h3m_idx : ([0, 1, 1] ++ List.replicate m 0 ++ [0])[3 + m] = 0 := by
        have hpre : ([0, 1, 1] ++ List.replicate m 0).length = 3 + m := by
          simp [List.length_replicate]; omega
        simp only [List.getElem_append, hpre, lt_irrefl, ↓reduceDIte, Nat.sub_self, List.getElem_singleton]
      rw [h3m_idx]
      dsimp [st6]
      rw [Function.update_self]
  · intro a ha
    dsimp [st6]
    rw [Function.update_of_ne (by omega)]
    rw [h5_fr a (by omega)]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · omega


end

end MinCostFlow.Expander
