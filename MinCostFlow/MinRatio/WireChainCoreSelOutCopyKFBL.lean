module

public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import WordRAM.Tactic

/-!
# Copies for the select outputs of the chain-update core (`WireChainCoreSelOutCopyKFBL`)

At a non-rebuilt level, the select part of `Update` reads lists and tables that the sparse core
wrote (`UpdateCoreSelectOutAt`). The sparse core says nothing on where its change records, its
re-embedding lists and the descriptor of its stretch tables lie with respect to its footprint, so
the chain core copies them into its own heap right after the call. This file gives the two copy
steps:
* `wireRawCopyBody`: copy `n` words, one load and one store per word. It makes no word check on
  the copied values, so it needs no bound on them (the re-embedding lists have none).
* `wireStretchDescCopyStmt`: copy the two base words of a stretch descriptor, and store `0` in place
  of a base above the heap pointer `cur` of the op (`guardWord`). Each row of a table ends at or
  below `cur`, so a base above `cur` can occur only when the edge set is empty, and then
  `StretchValuesAt` holds for any base. So the copy keeps the readout
  (`stretchValuesAt_of_moved`), and each stored base is at most `cur` (`guardWord_le`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Copy the `n = reg 0` words at `src = reg 1` to `dst = reg 2`, and return `0`. -/
@[expose] def wireRawCopyBody : Stmt :=
  forRange 3 (.const 0) (.reg 0)
    (.store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 1) (.reg 3)))) ;;
  .ret (.const 0)

theorem wireRawCopyBody_noRand : wireRawCopyBody.NoRand := by
  simp [wireRawCopyBody, forRange, forUp, Stmt.NoRand]

set_option maxHeartbeats 400000 in
/-- `wireRawCopyBody` copies the `n` words at `src` to `dst` in at most `20 n + 12` steps and
changes no other cell. The two ranges must not overlap, so that each load sees the old word. -/
theorem wireRawCopyBody_runs {w n src dst pos : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} (hw : 1 < 2 ^ w) (hSrc : src + n < 2 ^ w) (hDst : dst + n < 2 ^ w)
    (hDisj : src + n ≤ dst ∨ dst + n ≤ src) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω wireRawCopyBody (startState [n, src, dst] mem pos) (.returned 0) out cost ∧
      cost ≤ 20 * n + 12 ∧
      (∀ t < n, out.mem (dst + t) = mem (src + t)) ∧
      (∀ a, a < dst ∨ dst + n ≤ a → out.mem a = mem a) := by
  let s0 := startState [n, src, dst] mem pos
  let Inv : ℕ → State → Prop := fun i s =>
    s.regs 0 = n ∧ s.regs 1 = src ∧ s.regs 2 = dst ∧ s.regs 3 = i ∧
      (∀ t < i, s.mem (dst + t) = mem (src + t)) ∧
      (∀ a, a < dst ∨ dst + i ≤ a → s.mem a = mem a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 0)
    (P := fun s => s = s0) (Inv := Inv) (fun _ => 8) 0 n (Nat.zero_le _) hw
    (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [s0, startState])
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.1])
    (fun i _ hi s ω' ⟨h0, h1, h2, h3, hCp, hFr⟩ => by
      have hSrcOut : s.mem (src + i) = mem (src + i) := hFr _ (by omega)
      let t1 := { s with mem := Function.update s.mem (dst + i) (s.mem (src + i)) }
      have rt : Runs w p ω'
          (.store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 1) (.reg 3))))
          s .normal t1 8 :=
        runs_store_iff.mpr ⟨dst + i, s.mem (src + i),
          by simp [Expr.eval, BinOp.eval, h2, h3, show dst + i < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, h1, h3, show src + i < 2 ^ w by omega], rfl, rfl, rfl⟩
      refine ⟨.normal, t1, 8, rt, ⟨⟨by simp [t1, h0], by simp [t1, h1], by simp [t1, h2],
        by simp, fun t ht => ?_, fun a ha => ?_⟩, by simp [t1, h3]⟩, le_rfl⟩
      · by_cases hti : t = i
        · subst hti; simp [t1, hSrcOut]
        · have hne : dst + t ≠ dst + i := by omega
          simp only [t1, Function.update_of_ne hne]
          exact hCp t (by omega)
      · have hne : a ≠ dst + i := by omega
        simp only [t1, Function.update_of_ne hne]
        exact hFr a (by omega))
  obtain ⟨o, s1, cLoop, rLoop, hInv1, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv1
  | normal =>
    obtain ⟨_, _, _, _, hCp1, hFr1⟩ := hInv1
    have rRet : Runs w p ω (.ret (.const 0)) s1 (.returned 0) s1 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
    refine ⟨s1, _, runs_seq_iff.mpr (Or.inr ⟨s1, cLoop, 2, rLoop, rRet, rfl⟩), ?_, hCp1,
      hFr1⟩
    have hcBound : rangeCost (fun _ => 8) 0 n = 8 * n := by
      unfold rangeCost; simp [Nat.mul_comm]
    simp only [Expr.size, hcBound, Nat.sub_zero] at hcLoop
    omega

/-- Store at `reg rDst + off` the word at `reg rSrc + off`, or `0` when that word is above
`reg rCur`. The register `rT` is scratch. -/
@[expose] def wireGuardCopyWordStmt (rT rSrc rDst rCur off : ℕ) : Stmt :=
  .assign rT (.load (.bin .add (.reg rSrc) (.const off))) ;;
  .cond (.bin .lt (.reg rCur) (.reg rT))
    (.store (.bin .add (.reg rDst) (.const off)) (.const 0))
    (.store (.bin .add (.reg rDst) (.const off)) (.reg rT))

/-- Copy the two base words of a stretch descriptor at `reg rSrc` to `reg rDst`, each one guarded
by `reg rCur` as in `wireGuardCopyWordStmt`. -/
@[expose] def wireStretchDescCopyStmt (rT rSrc rDst rCur : ℕ) : Stmt :=
  wireGuardCopyWordStmt rT rSrc rDst rCur 0 ;; wireGuardCopyWordStmt rT rSrc rDst rCur 1

theorem wireStretchDescCopyStmt_noRand (rT rSrc rDst rCur : ℕ) :
    (wireStretchDescCopyStmt rT rSrc rDst rCur).NoRand := by
  simp [wireStretchDescCopyStmt, wireGuardCopyWordStmt, Stmt.NoRand]

/-- The guarded word: the word itself when it is at most `cur`, and `0` otherwise. -/
@[expose] def guardWord (cur x : ℕ) : ℕ := if cur < x then 0 else x

theorem guardWord_le (cur x : ℕ) : guardWord cur x ≤ cur := by
  unfold guardWord; split_ifs with h <;> omega

theorem guardWord_of_le {cur x : ℕ} (h : x ≤ cur) : guardWord cur x = x := by
  unfold guardWord; simp only [show ¬ cur < x by omega, ↓reduceIte]

/-- One run of `wireGuardCopyWordStmt`. -/
theorem wireGuardCopyWordStmt_runs {w rT rSrc rDst rCur off a b cur : ℕ} {p : Program}
    {ω : ℕ → Bool} {s : State} (hw : 1 < 2 ^ w)
    (hTDst : rT ≠ rDst) (hTCur : rT ≠ rCur)
    (hSrc : s.regs rSrc = a) (hDst : s.regs rDst = b) (hCur : s.regs rCur = cur)
    (hOff : off < 2 ^ w) (ha : a + off < 2 ^ w) (hb : b + off < 2 ^ w) :
    Runs w p ω (wireGuardCopyWordStmt rT rSrc rDst rCur off) s .normal
      { regs := Function.update s.regs rT (s.mem (a + off))
        mem := Function.update s.mem (b + off) (guardWord cur (s.mem (a + off)))
        pos := s.pos } 15 := by
  let x := s.mem (a + off)
  let t1 : State := { s with regs := Function.update s.regs rT x }
  have r1 : Runs w p ω (.assign rT (.load (.bin .add (.reg rSrc) (.const off)))) s .normal t1 5 :=
    runs_assign_iff.mpr ⟨x, by simp [Expr.eval, BinOp.eval, hSrc, hOff, ha, x], rfl, rfl,
      by simp [Expr.size]⟩
  have hT1Dst : t1.regs rDst = b := by simp [t1, Function.update_of_ne (Ne.symm hTDst), hDst]
  have hT1Cur : t1.regs rCur = cur := by simp [t1, Function.update_of_ne (Ne.symm hTCur), hCur]
  have hT1T : t1.regs rT = x := by simp [t1]
  by_cases hlt : cur < x
  · have r2 : Runs w p ω
        (.cond (.bin .lt (.reg rCur) (.reg rT))
          (.store (.bin .add (.reg rDst) (.const off)) (.const 0))
          (.store (.bin .add (.reg rDst) (.const off)) (.reg rT))) t1 .normal
        { t1 with mem := Function.update t1.mem (b + off) 0 } 9 :=
      runs_cond_iff.mpr ⟨1, 5, by simp [Expr.eval, BinOp.eval, hT1Cur, hT1T, hlt, hw],
        by
          simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
          exact runs_store_iff.mpr ⟨b + off, 0, by
            simp [Expr.eval, BinOp.eval, hT1Dst, hOff, hb], by
            simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, by simp [Expr.size]⟩,
        by simp [Expr.size]⟩
    have := runs_seq_iff.mpr (Or.inr ⟨t1, 5, 9, r1, r2, rfl⟩)
    simpa [wireGuardCopyWordStmt, t1, guardWord, hlt, x] using this
  · have hle : x ≤ cur := by omega
    have r2 : Runs w p ω
        (.cond (.bin .lt (.reg rCur) (.reg rT))
          (.store (.bin .add (.reg rDst) (.const off)) (.const 0))
          (.store (.bin .add (.reg rDst) (.const off)) (.reg rT))) t1 .normal
        { t1 with mem := Function.update t1.mem (b + off) x } 9 :=
      runs_cond_iff.mpr ⟨0, 5, by simp [Expr.eval, BinOp.eval, hT1Cur, hT1T, hlt],
        by
          simp only [↓reduceIte]
          exact runs_store_iff.mpr ⟨b + off, x, by
            simp [Expr.eval, BinOp.eval, hT1Dst, hOff, hb], by
            simp [Expr.eval, hT1T], rfl, rfl, by simp [Expr.size]⟩,
        by simp [Expr.size]⟩
    have := runs_seq_iff.mpr (Or.inr ⟨t1, 5, 9, r1, r2, rfl⟩)
    simpa [wireGuardCopyWordStmt, t1, guardWord, hlt, x] using this

/-- One run of `wireStretchDescCopyStmt`: the two words at `b` become the guarded words at `a`,
and only the register `rT` changes. -/
theorem wireStretchDescCopyStmt_runs {w rT rSrc rDst rCur a b cur : ℕ} {p : Program}
    {ω : ℕ → Bool} {s : State} (hw : 2 < 2 ^ w)
    (hTSrc : rT ≠ rSrc) (hTDst : rT ≠ rDst) (hTCur : rT ≠ rCur)
    (hSrc : s.regs rSrc = a) (hDst : s.regs rDst = b) (hCur : s.regs rCur = cur)
    (ha : a + 1 < 2 ^ w) (hb : b + 1 < 2 ^ w) (hDisj : b + 2 ≤ a ∨ a + 2 ≤ b) :
    Runs w p ω (wireStretchDescCopyStmt rT rSrc rDst rCur) s .normal
      { regs := Function.update s.regs rT (s.mem (a + 1))
        mem := Function.update (Function.update s.mem b (guardWord cur (s.mem a))) (b + 1)
          (guardWord cur (s.mem (a + 1)))
        pos := s.pos } 31 := by
  have r1 := wireGuardCopyWordStmt_runs (w := w) (p := p) (ω := ω) (s := s) (off := 0)
    (by omega) hTDst hTCur hSrc hDst hCur (by omega) (by omega) (by omega)
  set s1 : State :=
    { regs := Function.update s.regs rT (s.mem (a + 0))
      mem := Function.update s.mem (b + 0) (guardWord cur (s.mem (a + 0)))
      pos := s.pos } with hs1
  have h1Src : s1.regs rSrc = a := by simp [s1, Function.update_of_ne (Ne.symm hTSrc), hSrc]
  have h1Dst : s1.regs rDst = b := by simp [s1, Function.update_of_ne (Ne.symm hTDst), hDst]
  have h1Cur : s1.regs rCur = cur := by simp [s1, Function.update_of_ne (Ne.symm hTCur), hCur]
  have r2 := wireGuardCopyWordStmt_runs (w := w) (p := p) (ω := ω) (s := s1) (off := 1)
    (by omega) hTDst hTCur h1Src h1Dst h1Cur (by omega) ha hb
  have hne2 : a + 1 ≠ b := by omega
  have hm : s1.mem (a + 1) = s.mem (a + 1) := by simp [s1, Function.update_of_ne hne2]
  have := runs_seq_iff.mpr (Or.inr ⟨s1, 15, 15, r1, r2, rfl⟩)
  rw [hm] at this
  simpa [wireStretchDescCopyStmt, s1] using this

/-- A stretch readout moves with its descriptor: if the new descriptor at `b` holds the two old base
words whenever the edge set is not empty, and the rows of both tables are unchanged, the readout
holds at `b`. -/
theorem stretchValuesAt_of_moved {mem₁ mem₂ : ℕ → ℕ} {a b h L P : ℕ} {E : Finset ℕ}
    {values : ℕ → ℝ}
    (hv : StretchValuesAt mem₁ a h L P E values)
    (hb : E.Nonempty → mem₂ b = mem₁ a ∧ mem₂ (b + 1) = mem₁ (a + 1))
    (hnum : ∀ e ∈ E, ∀ t < L, mem₂ (mem₁ a + e * L + t) = mem₁ (mem₁ a + e * L + t))
    (hden : ∀ e ∈ E, ∀ t < L, mem₂ (mem₁ (a + 1) + e * L + t) = mem₁ (mem₁ (a + 1) + e * L + t)) :
    StretchValuesAt mem₂ b h L P E values := by
  intro e he
  obtain ⟨hb0, hb1⟩ := hb ⟨e, he⟩
  obtain ⟨hvn, hvd, hpos, hdiv⟩ := hv e he
  rw [hb0, hb1]
  have hvn2 : Num.Valid mem₂ (mem₁ a + e * L) h L := fun i hi => by
    rw [hnum e he i hi]; exact hvn i hi
  have hvd2 : Num.Valid mem₂ (mem₁ (a + 1) + e * L) h L := fun i hi => by
    rw [hden e he i hi]; exact hvd i hi
  have hfn : Num.fixVal mem₂ (mem₁ a + e * L) h L P = Num.fixVal mem₁ (mem₁ a + e * L) h L P := by
    unfold Num.fixVal Num.intVal
    rw [Num.unsignedVal_congr (hnum e he)]
  have hfd : Num.fixVal mem₂ (mem₁ (a + 1) + e * L) h L P =
      Num.fixVal mem₁ (mem₁ (a + 1) + e * L) h L P := by
    unfold Num.fixVal Num.intVal
    rw [Num.unsignedVal_congr (hden e he)]
  exact ⟨hvn2, hvd2, hfd ▸ hpos, by rw [hfn, hfd]; exact hdiv⟩

end MinCostFlow.MinRatio

end
