module

public import MinCostFlow.LSF.Program.BlockRep
public import MinCostFlow.LSF.Program.Utils
public import WordRAM.Tactic

/-!
# Moving the stretch arrays

`wstrProc` needs every array it reads below its numerator array. In the initialization the
endpoint arrays and the depths in `T_H` sit in scratch above the static blocks, so the stretch
pass writes its arrays in scratch, and two active-edge copy loops (`wstrCopyEdgesStmt`) move the
`L_w`-limb entries of the `m₀` edges in the edge list to the static place of `WstrAt`.
`WstrAt.of_copy_edges` says that copying only the edges of `G` keeps `WstrAt`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- Copying both stretch arrays to new places keeps `WstrAt`. -/
lemma WstrAt.of_copy {mem mem' : ℕ → ℕ} {num den num' den' eCap h L_w : ℕ} {G : MGraph}
    {wstr : ℕ → ℝ} (hw : WstrAt mem num den eCap h L_w G wstr)
    (hN : ∀ i < eCap * L_w, mem' (num' + i) = mem (num + i))
    (hD : ∀ i < eCap * L_w, mem' (den' + i) = mem (den + i)) :
    WstrAt mem' num' den' eCap h L_w G wstr := by
  rcases hw with ⟨hhL, hL, hE⟩
  refine ⟨hhL, hL, fun e he => ?_⟩
  rcases hE e he with ⟨hlt, hVN, hVD, hIN, hID, hval⟩
  have hin : ∀ i < L_w, e * L_w + i < eCap * L_w := fun i hi =>
    calc e * L_w + i < (e + 1) * L_w := by nlinarith
      _ ≤ eCap * L_w := Nat.mul_le_mul_right _ hlt
  have heN : ∀ i < L_w, mem (num + e * L_w + i) = mem' (num' + e * L_w + i) := fun i hi => by
    rw [Nat.add_assoc, Nat.add_assoc, hN _ (hin i hi)]
  have heD : ∀ i < L_w, mem (den + e * L_w + i) = mem' (den' + e * L_w + i) := fun i hi => by
    rw [Nat.add_assoc, Nat.add_assoc, hD _ (hin i hi)]
  have hVN' : Num.Valid mem' (num' + e * L_w) h L_w := fun i hi => by
    rw [← heN i hi]; exact hVN i hi
  have hVD' : Num.Valid mem' (den' + e * L_w) h L_w := fun i hi => by
    rw [← heD i hi]; exact hVD i hi
  rw [← Num.intVal_congr heN, ← Num.intVal_congr heD]
  exact ⟨hlt, hVN', hVD', hIN, hID, hval⟩

/-- Copying only the edges of `G` in both stretch arrays keeps `WstrAt`. -/
lemma WstrAt.of_copy_edges {mem mem' : ℕ → ℕ} {num den num' den' eCap h L_w : ℕ} {G : MGraph}
    {wstr : ℕ → ℝ} (hw : WstrAt mem num den eCap h L_w G wstr)
    (hN : ∀ e ∈ G.E, ∀ i < L_w, mem' (num' + e * L_w + i) = mem (num + e * L_w + i))
    (hD : ∀ e ∈ G.E, ∀ i < L_w, mem' (den' + e * L_w + i) = mem (den + e * L_w + i)) :
    WstrAt mem' num' den' eCap h L_w G wstr := by
  rcases hw with ⟨hhL, hL, hE⟩
  refine ⟨hhL, hL, fun e he => ?_⟩
  rcases hE e he with ⟨hlt, hVN, hVD, hIN, hID, hval⟩
  have heN : ∀ i < L_w, mem (num + e * L_w + i) = mem' (num' + e * L_w + i) :=
    fun i hi => (hN e he i hi).symm
  have heD : ∀ i < L_w, mem (den + e * L_w + i) = mem' (den' + e * L_w + i) :=
    fun i hi => (hD e he i hi).symm
  have hVN' : Num.Valid mem' (num' + e * L_w) h L_w := fun i hi => by
    rw [← heN i hi]; exact hVN i hi
  have hVD' : Num.Valid mem' (den' + e * L_w) h L_w := fun i hi => by
    rw [← heD i hi]; exact hVD i hi
  rw [← Num.intVal_congr heN, ← Num.intVal_congr heD]
  exact ⟨hlt, hVN', hVD', hIN, hID, hval⟩

/-- Copy `L_w` words for each of the `m0` edge IDs listed at `rEList` from `rSrc + e * L_w` to
`rDst + e * L_w`, calling `bCopy` (`memCopyContract`) and using scratch registers `46, 47, 48`. -/
def wstrCopyEdgesStmt (bCopy rDst rSrc rEList rM0 rLw : ℕ) : Stmt :=
  forRange 46 (.const 0) (.reg rM0)
    (.assign 47 (.bin .mul (.load (.bin .add (.reg rEList) (.reg 46))) (.reg rLw)) ;;
     .call 48 bCopy [.bin .add (.reg rDst) (.reg 47), .bin .add (.reg rSrc) (.reg 47), .reg rLw])

lemma wstrCopyEdgesStmt_noRand (bCopy rDst rSrc rEList rM0 rLw : ℕ) :
    (wstrCopyEdgesStmt bCopy rDst rSrc rEList rM0 rLw).NoRand := by
  simp [wstrCopyEdgesStmt, forRange, forUp, Stmt.NoRand]

/-- Step bound for `wstrCopyEdgesStmt`. -/
def wstrCopyEdgesCost (m0 Lw : ℕ) : ℕ := m0 * (20 * Lw + 40) + 15

/-- Precondition for `wstrCopyEdgesStmt`. -/
def wstrCopyEdgesPre (w dst src eListPtr m0 Lw totalLen : ℕ) (mem : ℕ → ℕ) : Prop :=
  16 ≤ 2 ^ w ∧
  1 ≤ Lw ∧ Lw < 2 ^ w ∧
  eListPtr + m0 ≤ dst ∧
  dst + totalLen ≤ src ∧
  src + totalLen < 2 ^ w ∧
  ∀ t < m0, (mem (eListPtr + t) + 1) * Lw ≤ totalLen

/-- Postcondition for `wstrCopyEdgesStmt`. -/
def wstrCopyEdgesPost (dst src eListPtr m0 Lw totalLen : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  (∀ t < m0, ∀ i < Lw,
    mem' (dst + mem (eListPtr + t) * Lw + i) = mem (src + mem (eListPtr + t) * Lw + i)) ∧
  (∀ a, a < dst ∨ dst + totalLen ≤ a → mem' a = mem a)

/-- Running `wstrCopyEdgesStmt` copies the `m0` edge blocks of length `Lw` in `O(m0 * Lw)` steps
and preserves registers below `46` as well as memory outside `[dst, dst + totalLen)`. -/
theorem wstrCopyEdges_runs {w bCopy rDst rSrc rEList rM0 rLw : ℕ} {p : Program} {ω : ℕ → Bool}
    {dst src eListPtr m0 Lw totalLen : ℕ} {st : State}
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hrDst : rDst < 46) (hrSrc : rSrc < 46) (hrEList : rEList < 46) (hrM0 : rM0 < 46)
    (hrLw : rLw < 46)
    (hR_dst : st.regs rDst = dst) (hR_src : st.regs rSrc = src)
    (hR_eL : st.regs rEList = eListPtr) (hR_m0 : st.regs rM0 = m0) (hR_Lw : st.regs rLw = Lw)
    (hpre : wstrCopyEdgesPre w dst src eListPtr m0 Lw totalLen st.mem) :
    ∃ st' c, Runs w p ω (wstrCopyEdgesStmt bCopy rDst rSrc rEList rM0 rLw) st .normal st' c ∧
      (∀ r < 46, st'.regs r = st.regs r) ∧
      wstrCopyEdgesPost dst src eListPtr m0 Lw totalLen st.mem st'.mem ∧
      c ≤ wstrCopyEdgesCost m0 Lw := by
  obtain ⟨hw16, hLw1, hLwW, hEL, hDS, hSW, hEt⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  let mem₀ := st.mem
  let regs₀ := st.regs
  let Inv : ℕ → State → Prop := fun t s =>
    (∀ r < 46, s.regs r = regs₀ r) ∧
    s.regs 46 = t ∧
    (∀ j < t, ∀ i < Lw,
      s.mem (dst + mem₀ (eListPtr + j) * Lw + i) = mem₀ (src + mem₀ (eListPtr + j) * Lw + i)) ∧
    (∀ a, a < dst ∨ dst + totalLen ≤ a → s.mem a = mem₀ a)
  have htrip : Triple w p (fun s => s = st)
      (wstrCopyEdgesStmt bCopy rDst rSrc rEList rM0 rLw)
      (normalPost (Inv m0))
      (fun _ => (m0 - 0) * ((20 * Lw + 31) + (Expr.reg rM0).size + 8) +
        ((Expr.const 0).size + (Expr.reg rM0).size + 5)) := by
    unfold wstrCopyEdgesStmt
    refine Triple.forRange_const (20 * Lw + 31) 0 m0 (Nat.zero_le _) hw1 (fun _ => by omega)
      ?_ ?_ ?_ ?_
    · rintro s rfl
      refine ⟨by eval_expr, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 46), regs₀],
        by simp, fun j hj => absurd hj (by omega), fun _ _ => rfl⟩
    · intro t s _ _ hI; exact hI.2.1
    · intro t s _ _ hI
      have hm0 : s.regs rM0 = m0 := (hI.1 rM0 hrM0).trans hR_m0
      eval_expr
    · intro t _ ht s ω' hI
      obtain ⟨hregs, hr46, hdone, hfr⟩ := hI
      have hrDst_s : s.regs rDst = dst := (hregs rDst hrDst).trans hR_dst
      have hrSrc_s : s.regs rSrc = src := (hregs rSrc hrSrc).trans hR_src
      have hrEL_s : s.regs rEList = eListPtr := (hregs rEList hrEList).trans hR_eL
      have hrLw_s : s.regs rLw = Lw := (hregs rLw hrLw).trans hR_Lw
      set e := mem₀ (eListPtr + t) with he_def
      have he_mem : s.mem (eListPtr + t) = e := hfr _ (Or.inl (by omega))
      have he_bd : (e + 1) * Lw ≤ totalLen := hEt t ht
      have he_mul_add : e * Lw + Lw = (e + 1) * Lw := by ring
      have he_ltw : e < 2 ^ w := by
        have : e + 1 ≤ (e + 1) * Lw := Nat.le_mul_of_pos_right _ hLw1
        omega
      have heLw_ltw : e * Lw < 2 ^ w := by omega
      have hdstE_ltw : dst + e * Lw < 2 ^ w := by omega
      have hsrcE_ltw : src + e * Lw < 2 ^ w := by omega
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := e * Lw)
        (by
          simp only [Expr.eval, BinOp.eval, hrEL_s, hr46, hrLw_s,
            show eListPtr + t < 2 ^ w by omega, ↓reduceIte, Option.map_some, he_mem, heLw_ltw])
        ?_
      let s1 : State := { mem := s.mem, regs := Function.update s.regs 47 (e * Lw), pos := s.pos }
      have hcall_pre : (memCopyContract w).pre [dst + e * Lw, src + e * Lw, Lw] s1.mem :=
        ⟨dst + e * Lw, src + e * Lw, Lw, rfl, by omega, by omega, Or.inl (by omega)⟩
      have hcall_words : ∀ x ∈ [dst + e * Lw, src + e * Lw, Lw], x < 2 ^ w := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> omega
      obtain ⟨body, hbody, o, st_f, c_f, hrun_f, hpost_f, hcost_f⟩ :=
        hCopy [dst + e * Lw, src + e * Lw, Lw] s1.mem s1.pos ω' hcall_words hcall_pre
      obtain ⟨d', s', l', heq_c, -, hcp_c, hfr_c⟩ := hpost_f
      simp only [List.cons.injEq, and_true] at heq_c
      obtain ⟨rfl, rfl, rfl⟩ := heq_c
      have hcost_f' : c_f ≤ 20 * Lw + 12 := by simpa [memCopyContract] using hcost_f
      have heval_args : evalArgs w s1
          [.bin .add (.reg rDst) (.reg 47), .bin .add (.reg rSrc) (.reg 47), .reg rLw] =
          some [dst + e * Lw, src + e * Lw, Lw] := by
        have hrDst1 : s1.regs rDst = dst := by
          dsimp only [s1]; rw [Function.update_of_ne (by omega)]; exact hrDst_s
        have hrSrc1 : s1.regs rSrc = src := by
          dsimp only [s1]; rw [Function.update_of_ne (by omega)]; exact hrSrc_s
        have hrLw1 : s1.regs rLw = Lw := by
          dsimp only [s1]; rw [Function.update_of_ne (by omega)]; exact hrLw_s
        have hr47_1 : s1.regs 47 = e * Lw := by dsimp only [s1]; exact Function.update_self _ _ _
        exact evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
      let s2 : State :=
        { mem := st_f.mem, regs := Function.update s1.regs 48 o.value, pos := st_f.pos }
      have hrun_call : Runs w p ω'
          (.call 48 bCopy [.bin .add (.reg rDst) (.reg 47), .bin .add (.reg rSrc) (.reg 47),
            .reg rLw])
          s1 .normal s2
          (argsSize [.bin .add (.reg rDst) (.reg 47), .bin .add (.reg rSrc) (.reg 47), .reg rLw] +
            c_f + 1) :=
        runs_call_iff.mpr ⟨_, body, o, st_f, c_f, heval_args, hbody, hrun_f, rfl, rfl, rfl⟩
      refine ⟨.normal, s2, _, hrun_call, ?_, ?_⟩
      · refine ⟨⟨fun r hr => ?_, ?_, fun j hj i hi => ?_, fun a ha => ?_⟩, ?_⟩
        · dsimp only [s2, s1]
          rw [Function.update_of_ne (by omega : r ≠ 46), Function.update_of_ne (by omega : r ≠ 48),
            Function.update_of_ne (by omega : r ≠ 47)]
          exact hregs r hr
        · dsimp only [s2, s1]
          exact Function.update_self _ _ _
        · dsimp only [s2, s1] at hcp_c hfr_c ⊢
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · set e' := mem₀ (eListPtr + j)
            rcases eq_or_ne e' e with hee | hee
            · rw [hee, hcp_c i hi, hfr _ (Or.inr (by omega))]
            · have hdisj : dst + e' * Lw + i < dst + e * Lw ∨
                  dst + e * Lw + Lw ≤ dst + e' * Lw + i := by
                rcases Nat.lt_or_gt_of_ne hee with hlt | hgt
                · left
                  have : (e' + 1) * Lw ≤ e * Lw := Nat.mul_le_mul_right Lw hlt
                  have : e' * Lw + Lw = (e' + 1) * Lw := by ring
                  omega
                · right
                  have : (e + 1) * Lw ≤ e' * Lw := Nat.mul_le_mul_right Lw hgt
                  omega
              rw [hfr_c _ hdisj]
              exact hdone j hj' i hi
          · rw [← he_def, hcp_c i hi, hfr _ (Or.inr (by omega))]
        · dsimp only [s2, s1] at hfr_c ⊢
          rw [hfr_c a (by omega)]
          exact hfr a ha
        · dsimp only [s2, s1]
          rw [Function.update_of_ne (by decide : (46 : ℕ) ≠ 48),
            Function.update_of_ne (by decide : (46 : ℕ) ≠ 47)]
          exact hr46
      · simp only [argsSize, Expr.size]
        omega
  obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htrip st ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨hregs', -, hdone', hfr'⟩ := hpost
    refine ⟨st', c, hrun, hregs', ⟨hdone', hfr'⟩, ?_⟩
    simp only [wstrCopyEdgesCost, Expr.size, Nat.sub_zero] at hcost ⊢
    rw [show 20 * Lw + 31 + 1 + 8 = 20 * Lw + 40 by omega] at hcost
    omega

end

end MinCostFlow.LSF.Program
