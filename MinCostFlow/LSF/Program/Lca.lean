module

public import MinCostFlow.LSF.Program.TreeArrays
import Mathlib.Tactic.Linarith

/-!
# Lowest common ancestors by binary lifting

`lcaProc` finds the lowest common ancestor of two vertex indices `x`, `y` with the ancestor
table of `BinaryLift.lean`, in time `O(logCap)`:

1. Let `x` be the deeper of the two. Lift `x` to the depth of `y`: for `j` from `logCap - 1`
   down to `0`, jump `2^j` steps up when the depth stays at least that of `y`. Before level `j`
   the depth difference is below `2^(j+1)`, so after all levels it is `0`.
2. If now `x = y`, this is the answer. Otherwise, for `j` from `logCap - 1` down to `0`, jump
   both `2^j` steps up when they land on different vertices. Before level `j` the two vertices
   differ but their ancestors `2^(j+1)` steps up agree, so at the end `x ≠ y` have the same
   parent, which is the answer.

`lca_meetsContract` proves that the result is the lowest common ancestor (`IsLcaOf`). The
contract states the result for every choice of arrays that matches the memory, since the
memory pins `par` and `dep` on the indices below `n` (`isLcaOf_congr`). The
key fact for the last step: a common ancestor `c` at least as deep as `x` would be an ancestor
of both `x` and `y` at their common depth, so `x = y` (`AncOf.eq_of_dep_eq`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-! ## The procedure -/

/-- Phase 1 step at level `j` (register `8`): try the jump of `x` (register `6`). -/
def lcaLiftBody : Stmt :=
  .assign 8 (.bin .sub (.reg 8) (.const 1)) ;;
  .assign 9 (.load (.bin .add (.reg 3) (.bin .add (.bin .mul (.reg 6) (.reg 2)) (.reg 8)))) ;;
  .cond (.bin .lt (.load (.bin .add (.reg 4) (.reg 9))) (.load (.bin .add (.reg 4) (.reg 7))))
    .nop (.assign 6 (.reg 9))

/-- Phase 2 step at level `j` (register `8`): jump both when they land apart. -/
def lcaBothBody : Stmt :=
  .assign 8 (.bin .sub (.reg 8) (.const 1)) ;;
  .assign 9 (.load (.bin .add (.reg 3) (.bin .add (.bin .mul (.reg 6) (.reg 2)) (.reg 8)))) ;;
  .assign 10 (.load (.bin .add (.reg 3) (.bin .add (.bin .mul (.reg 7) (.reg 2)) (.reg 8)))) ;;
  .cond (.bin .eq (.reg 9) (.reg 10)) .nop (.assign 6 (.reg 9) ;; .assign 7 (.reg 10))

/-- Args: `[x, y, logCap, upPtr, depPtr, parPtr]`. Returns the lowest common ancestor. -/
def lcaProc : Stmt :=
  .assign 6 (.reg 0) ;;
  .assign 7 (.reg 1) ;;
  .cond (.bin .lt (.load (.bin .add (.reg 4) (.reg 6))) (.load (.bin .add (.reg 4) (.reg 7))))
    (.assign 6 (.reg 1) ;; .assign 7 (.reg 0)) .nop ;;
  .assign 8 (.reg 2) ;;
  .loop (.reg 8) lcaLiftBody ;;
  .cond (.bin .eq (.reg 6) (.reg 7)) (.ret (.reg 6)) .nop ;;
  .assign 8 (.reg 2) ;;
  .loop (.reg 8) lcaBothBody ;;
  .ret (.load (.bin .add (.reg 5) (.reg 6)))

lemma lcaProc_noRand : lcaProc.NoRand := by
  simp [lcaProc, lcaLiftBody, lcaBothBody, Stmt.NoRand]

/-- The tables `lcaProc` reads: the ancestor table at `upPtr`, depths at `depPtr` and parents at
`parPtr`, for rooted arrays with `n` vertices. -/
structure LcaTables (w n logCap upPtr depPtr parPtr : ℕ) (par dep : ℕ → ℕ) (mem : ℕ → ℕ) :
    Prop where
  hL : 1 ≤ logCap
  hdep : ∀ x < n, dep x < 2 ^ logCap
  hup : ∀ i < n, ∀ j < logCap, mem (upPtr + (i * logCap + j)) = liftF par i j
  hd : ∀ i < n, mem (depPtr + i) = dep i
  hp : ∀ i < n, mem (parPtr + i) = par i
  hupW : upPtr + n * logCap < 2 ^ w
  hdW : depPtr + n < 2 ^ w
  hpW : parPtr + n < 2 ^ w

/-- The tables only depend on the parents and depths at the indices below `n`. -/
lemma LcaTables.congr {w n logCap upPtr depPtr parPtr tM r : ℕ} {tl hd pe : ℕ → ℕ}
    {par dep par' dep' mem : ℕ → ℕ} (hT : LcaTables w n logCap upPtr depPtr parPtr par dep mem)
    (hR : RootedArrays n tM r tl hd par pe dep) (hpar : ∀ x < n, par x = par' x)
    (hdep : ∀ x < n, dep x = dep' x) :
    LcaTables w n logCap upPtr depPtr parPtr par' dep' mem := by
  refine ⟨hT.hL, fun x hx => by rw [← hdep x hx]; exact hT.hdep x hx, fun i hi j hj => ?_,
    fun i hi => by rw [← hdep i hi]; exact hT.hd i hi,
    fun i hi => by rw [← hpar i hi]; exact hT.hp i hi, hT.hupW, hT.hdW, hT.hpW⟩
  rw [hT.hup i hi j hj, liftF_eq_iterate, liftF_eq_iterate]
  exact iterate_congr_of_lt hpar hR.par_lt hi _

/-- The contract of `lcaProc`. -/
def lcaContract (w : ℕ) : Contract where
  pre args mem := ∃ (x y logCap upPtr depPtr parPtr n tM r : ℕ) (tl hd par pe dep : ℕ → ℕ),
    args = [x, y, logCap, upPtr, depPtr, parPtr] ∧ 16 ≤ 2 ^ w ∧
    RootedArrays n tM r tl hd par pe dep ∧ x < n ∧ y < n ∧
    LcaTables w n logCap upPtr depPtr parPtr par dep mem
  post args mem ret mem' := mem' = mem ∧
    ∀ (x y logCap upPtr depPtr parPtr n tM r : ℕ) (tl hd par pe dep : ℕ → ℕ),
      args = [x, y, logCap, upPtr, depPtr, parPtr] → RootedArrays n tM r tl hd par pe dep →
      x < n → y < n → LcaTables w n logCap upPtr depPtr parPtr par dep mem →
      ret < n ∧ IsLcaOf par dep ret x y
  cost args _ := 100 * args.getD 2 0 + 100

/-! ## Proof -/

private lemma idx_lt' {i j n L : ℕ} (hi : i < n) (hj : j < L) : i * L + j < n * L := by
  have : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right _ hi
  nlinarith

/-- The registers `0, …, 5` hold the arguments. -/
def LcaRegs (st : State) (args : List ℕ) : Prop := ∀ i < 6, st.regs i = args.getD i 0

lemma LcaRegs.upd {st : State} {args : List ℕ} (h : LcaRegs st args) (q v : ℕ) (hq : 6 ≤ q) :
    LcaRegs { st with regs := Function.update st.regs q v } args := fun i hi => by
  simp only [Function.update_of_ne (show i ≠ q by omega)]; exact h i hi

/-- The result for the arrays of the precondition gives the result for any arrays that
match the memory: both agree on the indices below the smaller of the two sizes, and the
ancestors of `x` and `y` stay below it. -/
lemma lcaPost_of {w x y L upPtr depPtr parPtr n tM r : ℕ} {tl hd par pe dep : ℕ → ℕ}
    {mem mem' : ℕ → ℕ} {ret : ℕ} (hR : RootedArrays n tM r tl hd par pe dep)
    (hT : LcaTables w n L upPtr depPtr parPtr par dep mem) (hx : x < n) (hy : y < n)
    (hlca : IsLcaOf par dep ret x y) (hm : mem' = mem) :
    (lcaContract w).post [x, y, L, upPtr, depPtr, parPtr] mem ret mem' := by
  refine ⟨hm, fun x' y' L' upPtr' depPtr' parPtr' n' tM' r' tl' hd' par' pe' dep' heq hR' hx'
    hy' hT' => ?_⟩
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  have hpar : ∀ z < min n n', par z = par' z := fun z hz => by
    rw [← hT.hp z (by omega), hT'.hp z (by omega)]
  have hdep : ∀ z < min n n', dep z = dep' z := fun z hz => by
    rw [← hT.hd z (by omega), hT'.hd z (by omega)]
  have hlt : ∀ z < min n n', par z < min n n' := fun z hz => by
    have h1 := hR.par_lt z (by omega)
    have h2 := hR'.par_lt z (by omega)
    rw [← hpar z hz] at h2
    omega
  have hxm : x < min n n' := by omega
  have hym : y < min n n' := by omega
  obtain ⟨k, -, hk⟩ := hlca.1
  have hrm : ret < min n n' := by
    rw [← hk]
    clear hk
    induction k with
    | zero => exact hxm
    | succ k ih => rw [Function.iterate_succ_apply']; exact hlt _ ih
  exact ⟨by omega, (isLcaOf_congr hpar hdep hlt hxm hym hrm).mp hlca⟩

theorem lca_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some lcaProc) :
    MeetsContract w p b (lcaContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨x, y, L, upPtr, depPtr, parPtr, n, tM, r, tl, hd, par, pe, dep, rfl, hw, hR, hx, hy,
    hT⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hLw : L < 2 ^ w := hwords L (by simp)
  set args := [x, y, L, upPtr, depPtr, parPtr] with hargs
  have hL := hT.hL
  -- reading the tables
  have hupR : ∀ i < n, ∀ j < L, mem (upPtr + (i * L + j)) = par^[2 ^ j] i := fun i hi j hj => by
    rw [hT.hup i hi j hj, liftF_eq_iterate]
  have hupA : ∀ i < n, ∀ j < L, upPtr + (i * L + j) < 2 ^ w := fun i hi j hj => by
    have := idx_lt' hi hj; have := hT.hupW; omega
  -- `a` is the deeper one, `c` the other
  set a := if dep x < dep y then y else x with ha_def
  set c := if dep x < dep y then x else y with hc_def
  have han : a < n := by simp only [ha_def]; split_ifs <;> assumption
  have hcn : c < n := by simp only [hc_def]; split_ifs <;> assumption
  have hac : dep c ≤ dep a := by simp only [ha_def, hc_def]; split_ifs <;> omega
  have hsymm : ∀ z, IsLcaOf par dep z a c → IsLcaOf par dep z x y := by
    intro z hz
    simp only [ha_def, hc_def] at hz
    split_ifs at hz
    · exact ⟨hz.2.1, hz.1, fun c h1 h2 => hz.2.2 c h2 h1⟩
    · exact hz
  -- phase 1: lift `a` to the depth of `c`
  let Inv1 : ℕ → State → Prop := fun j st =>
    LcaRegs st args ∧ st.mem = mem ∧ st.regs 7 = c ∧ st.regs 8 = j ∧ j ≤ L ∧
    AncOf par dep (st.regs 6) a ∧ dep c ≤ dep (st.regs 6) ∧ dep (st.regs 6) - dep c < 2 ^ j
  have hloop1 : ∀ j₀, Triple w p (Inv1 j₀) (.loop (.reg 8) lcaLiftBody)
      (normalPost fun st => LcaRegs st args ∧ st.mem = mem ∧ st.regs 7 = c ∧
        AncOf par dep (st.regs 6) a ∧ dep (st.regs 6) = dep c)
      (fun _ => 40 * j₀ + 2) := by
    intro j₀
    refine Triple.loop_inv (Inv := Inv1) (condVal := fun st => st.regs 8) (fun j => j)
      (fun j => 40 * j + 2) ?_ ?_ ?_ j₀
    · intro j st _; eval_expr
    · rintro j st ⟨hR', hm, h7, h8, -, hanc, hle, hlt⟩ h0
      rw [h8] at h0; subst h0
      exact ⟨⟨hR', hm, h7, hanc, by simp at hlt; omega⟩, by simp⟩
    · rintro j st ⟨hR', hm, h7, h8, hjL, hanc, hle, hlt⟩ hne
      rw [h8] at hne
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      refine ⟨36, ?_⟩
      intro s ω' hs; subst s
      have r2 : st.regs 2 = L := hR' 2 (by omega)
      have r3 : st.regs 3 = upPtr := hR' 3 (by omega)
      have r4 : st.regs 4 = depPtr := hR' 4 (by omega)
      set u := st.regs 6 with hu
      have hun := hanc.lt hR han
      have hj'L : j' < L := by omega
      have hA := hupA u hun j' hj'L
      have hv : st.mem (upPtr + (u * L + j')) = par^[2 ^ j'] u := by rw [hm]; exact hupR u hun j' hj'L
      set v := par^[2 ^ j'] u with hv_def
      have hvn : v < n := hR.iterate_lt hun _
      have hdv : dep v = dep u - 2 ^ j' := hR.dep_iterate hun _
      have hdvm : st.mem (depPtr + v) = dep v := by rw [hm]; exact hT.hd v hvn
      have hdcm : st.mem (depPtr + c) = dep c := by rw [hm]; exact hT.hd c hcn
      have hdW := hT.hdW
      have hpow : 2 ^ (j' + 1) = 2 * 2 ^ j' := by ring
      have hb1 : st.regs 6 * L + j' < n * L := idx_lt' hun hj'L
      have hb2 := hT.hupW
      refine runs_start_le ?_
      unfold lcaLiftBody
      refine runs_seq_assign_le (v := j') (by show _ = some (j' + 1 - 1); eval_expr) ?_
      refine runs_seq_assign_le (v := v) (by rw [← hv]; eval_expr) ?_
      refine runs_cond_le (v := if dep v < dep c then 1 else 0) (by
        rw [← hdvm, ← hdcm]; eval_expr) ?_ ?_
      · intro hne'
        have hlt' : dep v < dep c := by by_contra h; simp [h] at hne'
        refine runs_nop_le ⟨j', ⟨((hR'.upd 8 j' (by omega)).upd 9 v (by omega)), hm,
          by simpa using h7, by simp, by omega, by simpa using hanc, by simpa using hle,
          by simp; (try rw [← hu]); omega⟩, by omega, ?_⟩ ?_
        · simp only [Expr.size_reg]; omega
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
      · intro hz
        have hge : dep c ≤ dep v := by by_contra h; simp [not_le.mp h] at hz
        refine runs_assign_le (v := v) (by eval_expr) ⟨j', ⟨(((hR'.upd 8 j' (by omega)).upd 9 v
          (by omega)).upd 6 v (by omega)), hm, by simpa using h7, by simp, by omega, ?_,
          by simpa using hge, by simp; omega⟩, by omega, ?_⟩ ?_
        · simp only [Function.update_self]
          exact (ancOf_iterate hR hun _).trans hR han hanc
        · simp only [Expr.size_reg]; omega
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- phase 2: lift both while they land apart
  let Inv2 : ℕ → State → Prop := fun j st =>
    LcaRegs st args ∧ st.mem = mem ∧ st.regs 8 = j ∧ j ≤ L ∧
    AncOf par dep (st.regs 6) a ∧ AncOf par dep (st.regs 7) c ∧
    dep (st.regs 6) = dep (st.regs 7) ∧ st.regs 6 ≠ st.regs 7 ∧
    par^[2 ^ j] (st.regs 6) = par^[2 ^ j] (st.regs 7)
  have hloop2 : ∀ j₀, Triple w p (Inv2 j₀) (.loop (.reg 8) lcaBothBody)
      (normalPost fun st => LcaRegs st args ∧ st.mem = mem ∧
        AncOf par dep (st.regs 6) a ∧ AncOf par dep (st.regs 7) c ∧
        dep (st.regs 6) = dep (st.regs 7) ∧ st.regs 6 ≠ st.regs 7 ∧
        par (st.regs 6) = par (st.regs 7))
      (fun _ => 40 * j₀ + 2) := by
    intro j₀
    refine Triple.loop_inv (Inv := Inv2) (condVal := fun st => st.regs 8) (fun j => j)
      (fun j => 40 * j + 2) ?_ ?_ ?_ j₀
    · intro j st _; eval_expr
    · rintro j st ⟨hR', hm, h8, -, h6, h7, hd, hne, hit⟩ h0
      rw [h8] at h0; subst h0
      exact ⟨⟨hR', hm, h6, h7, hd, hne, by simpa using hit⟩, by simp⟩
    · rintro j st ⟨hR', hm, h8, hjL, h6, h7, hd, hne, hit⟩ hne8
      rw [h8] at hne8
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      refine ⟨36, ?_⟩
      intro s ω' hs; subst s
      have r2 : st.regs 2 = L := hR' 2 (by omega)
      have r3 : st.regs 3 = upPtr := hR' 3 (by omega)
      set u := st.regs 6 with hu
      set u' := st.regs 7 with hu'
      have hun := h6.lt hR han
      have hun' := h7.lt hR hcn
      have hj'L : j' < L := by omega
      have hA := hupA u hun j' hj'L
      have hA' := hupA u' hun' j' hj'L
      have hv : st.mem (upPtr + (u * L + j')) = par^[2 ^ j'] u := by
        rw [hm]; exact hupR u hun j' hj'L
      have hv' : st.mem (upPtr + (u' * L + j')) = par^[2 ^ j'] u' := by
        rw [hm]; exact hupR u' hun' j' hj'L
      have hsplit : ∀ z, par^[2 ^ (j' + 1)] z = par^[2 ^ j'] (par^[2 ^ j'] z) := by
        intro z; rw [← Function.iterate_add_apply]; congr 1; ring
      have hb1 : st.regs 6 * L + j' < n * L := idx_lt' hun hj'L
      have hb1' : st.regs 7 * L + j' < n * L := idx_lt' hun' hj'L
      have hb2 := hT.hupW
      refine runs_start_le ?_
      unfold lcaBothBody
      refine runs_seq_assign_le (v := j') (by show _ = some (j' + 1 - 1); eval_expr) ?_
      refine runs_seq_assign_le (v := par^[2 ^ j'] u) (by rw [← hv]; eval_expr) ?_
      refine runs_seq_assign_le (v := par^[2 ^ j'] u') (by rw [← hv']; eval_expr) ?_
      refine runs_cond_le (v := if par^[2 ^ j'] u = par^[2 ^ j'] u' then 1 else 0)
        (by eval_expr) ?_ ?_
      · intro hne'
        have heq : par^[2 ^ j'] u = par^[2 ^ j'] u' := by by_contra h; simp [h] at hne'
        refine runs_nop_le ⟨j', ⟨(((hR'.upd 8 j' (by omega)).upd 9 _ (by omega)).upd 10 _
          (by omega)), hm, by simp, by omega, by simpa using h6, by simpa using h7,
          by simpa using hd, by simpa using hne, by simpa using heq⟩, by omega, ?_⟩ ?_
        · simp only [Expr.size_reg]; omega
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
      · intro hz
        have hne' : par^[2 ^ j'] u ≠ par^[2 ^ j'] u' := by intro h; simp [h] at hz
        refine runs_seq_assign_le (v := par^[2 ^ j'] u) (by eval_expr) ?_
        refine runs_assign_le (v := par^[2 ^ j'] u') (by eval_expr) ⟨j', ⟨((((hR'.upd 8 j'
          (by omega)).upd 9 _ (by omega)).upd 10 _ (by omega)).upd 6 _ (by omega)).upd 7 _
          (by omega), hm, by simp, by omega, ?_, ?_, ?_, ?_, ?_⟩, by omega, ?_⟩ ?_
        · simp only [Function.update_self, Function.update_of_ne (show (6 : ℕ) ≠ 7 by omega)]
          exact (ancOf_iterate hR hun _).trans hR han h6
        · simp only [Function.update_self]
          exact (ancOf_iterate hR hun' _).trans hR hcn h7
        · simp only [Function.update_self, Function.update_of_ne (show (6 : ℕ) ≠ 7 by omega)]
          rw [hR.dep_iterate hun, hR.dep_iterate hun', hd]
        · simpa [Function.update_of_ne (show (6 : ℕ) ≠ 7 by omega)] using hne'
        · simp only [Function.update_self, Function.update_of_ne (show (6 : ℕ) ≠ 7 by omega)]
          rw [← hsplit, ← hsplit]; exact hit
        · simp only [Expr.size_reg]; omega
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- after the swap: register 6 is `a`, register 7 is `c`
  have hfinish : ∀ (st : State) (k : ℕ), LcaRegs st args → st.mem = mem → st.regs 6 = a →
      st.regs 7 = c →
      ∃ o st' cst, Runs w p ω
        (.assign 8 (.reg 2) ;;
         .loop (.reg 8) lcaLiftBody ;;
         .cond (.bin .eq (.reg 6) (.reg 7)) (.ret (.reg 6)) .nop ;;
         .assign 8 (.reg 2) ;;
         .loop (.reg 8) lcaBothBody ;;
         .ret (.load (.bin .add (.reg 5) (.reg 6)))) st o st' cst ∧
        (lcaContract w).post args mem o.value st'.mem ∧ k + cst ≤ k + (90 * L + 30) := by
    intro st k hRs hms h6 h7
    have r2 : st.regs 2 = L := hRs 2 (by omega)
    have hda : dep a < 2 ^ L := hT.hdep a han
    refine runs_seq_assign_le (v := L) (by eval_expr) ?_
    refine runs_seq_triple_le (hloop1 L) ⟨hRs.upd 8 L (by omega), hms, by simpa using h7,
      by simp, le_rfl, by simpa [h6] using AncOf.refl par dep a, by simpa [h6] using hac,
      by simp [h6]; omega⟩ ?_
    rintro st₁ ⟨hR1, hm1, h71, ha1, hd1⟩
    have r2' : st₁.regs 2 = L := hR1 2 (by omega)
    refine runs_seq_cond_le (v := if st₁.regs 6 = st₁.regs 7 then 1 else 0) (by eval_expr)
      ?_ ?_
    · intro hne
      have heq : st₁.regs 6 = st₁.regs 7 := by by_contra h; simp [h] at hne
      refine ⟨.returned (st₁.regs 6), st₁, Expr.size (.reg 6) + 1 + 1,
        runs_seq_iff.mpr (Or.inl ⟨_, _, runs_ret_iff.mpr ⟨_, by eval_expr, rfl, rfl, rfl⟩,
          rfl, rfl⟩), ?_, ?_⟩
      · refine lcaPost_of hR hT hx hy (hsymm _ ⟨ha1, by rw [heq, h71]; exact AncOf.refl _ _ _,
          ?_⟩) hm1
        intro z _ hz2; rw [heq, h71]; exact hz2
      · simp only [Expr.size_reg, Expr.size_bin]; omega
    · intro hz
      have hne : st₁.regs 6 ≠ st₁.regs 7 := by intro h; simp [h] at hz
      refine runs_seq_nop_le ?_
      refine runs_seq_assign_le (v := L) (by eval_expr) ?_
      have hu6 := ha1.lt hR han
      have hitR : ∀ z < n, dep z < 2 ^ L → par^[2 ^ L] z = r := fun z hz hdz =>
        hR.iterate_dep hz (by omega)
      refine runs_seq_triple_le (hloop2 L) ⟨hR1.upd 8 L (by omega), hm1, by simp, le_rfl,
        by simpa using ha1, by simpa [h71] using AncOf.refl par dep c, by simpa [h71] using hd1,
        by simpa [h71] using hne, ?_⟩ ?_
      · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 8 by omega),
          Function.update_of_ne (show (7 : ℕ) ≠ 8 by omega)]
        rw [hitR _ hu6 (lt_of_le_of_lt (ha1.dep_le hR han) hda), h71,
          hitR _ hcn (lt_of_le_of_lt hac hda)]
      · rintro st₂ ⟨hR2, hm2, ha2, hc2, hd2, hne2, hpar2⟩
        have r5 : st₂.regs 5 = parPtr := hR2 5 (by omega)
        have hu := ha2.lt hR han
        have hu' := hc2.lt hR hcn
        have hp : st₂.mem (parPtr + st₂.regs 6) = par (st₂.regs 6) := by
          rw [hm2]; exact hT.hp _ hu
        have hpW := hT.hpW
        refine runs_ret_le (v := par (st₂.regs 6)) (by rw [← hp]; eval_expr) ?_ ?_
        · refine lcaPost_of hR hT hx hy (hsymm _ ⟨?_, ?_, ?_⟩) hm2
          · exact (ancOf_iterate hR hu 1).trans hR han ha2
          · rw [hpar2]; exact (ancOf_iterate hR hu' 1).trans hR hcn hc2
          · -- a common ancestor is above the two distinct vertices at equal depth
            intro z hza hzc
            have hlt : dep z < dep (st₂.regs 6) := by
              by_contra hge
              have h1 : AncOf par dep (st₂.regs 6) z :=
                ha2.of_dep_le hR han hza (by omega)
              have h2 : AncOf par dep (st₂.regs 7) z :=
                hc2.of_dep_le hR hcn hzc (by omega)
              exact hne2 (h1.eq_of_dep_eq hR (hza.lt hR han) h2 hd2)
            have hz1 : AncOf par dep (par^[1] (st₂.regs 6)) a :=
              (ancOf_iterate hR hu 1).trans hR han ha2
            have hdp : dep (par^[1] (st₂.regs 6)) = dep (st₂.regs 6) - 1 :=
              hR.dep_iterate hu 1
            show AncOf par dep z (par^[1] (st₂.regs 6))
            exact hza.of_dep_le hR han hz1 (by omega)
        · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- the whole procedure
  have hR0 : LcaRegs (startState args mem pos) args := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have r0 : (startState args mem pos).regs 0 = x := hR0 0 (by omega)
  have r1 : (startState args mem pos).regs 1 = y := hR0 1 (by omega)
  have r4 : (startState args mem pos).regs 4 = depPtr := hR0 4 (by omega)
  have hdx : mem (depPtr + x) = dep x := hT.hd x hx
  have hdy : mem (depPtr + y) = dep y := hT.hd y hy
  have hdW := hT.hdW
  refine runs_start_le ?_
  unfold lcaProc
  refine runs_seq_assign_le (v := x) (by eval_expr) ?_
  refine runs_seq_assign_le (v := y) (by eval_expr) ?_
  refine runs_seq_cond_le (v := if dep x < dep y then 1 else 0) (by
    show Expr.eval w _ _ = _
    rw [show (startState args mem pos).mem = mem from rfl] at *
    have : mem (depPtr + x) = dep x := hdx
    eval_expr) ?_ ?_
  · intro hne
    have hlt : dep x < dep y := by by_contra h; simp [h] at hne
    have ha : a = y := by simp [ha_def, hlt]
    have hc : c = x := by simp [hc_def, hlt]
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := y) (by eval_expr) ?_
    refine runs_seq_assign_le (v := x) (by eval_expr) ?_
    obtain ⟨o, st', cst, hrun, hq, hc'⟩ := hfinish _ 0 ((((hR0.upd 6 x (by omega)).upd 7 y
      (by omega)).upd 6 y (by omega)).upd 7 x (by omega)) rfl (by simp [ha]) (by simp [hc])
    refine ⟨o, st', cst, hrun, hq, ?_⟩
    simp only [lcaContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg,
      Expr.size_load, Expr.size_bin]
    omega
  · intro hz
    have hge : ¬ dep x < dep y := by intro h; simp [h] at hz
    have ha : a = x := by simp [ha_def, hge]
    have hc : c = y := by simp [hc_def, hge]
    refine runs_seq_nop_le ?_
    obtain ⟨o, st', cst, hrun, hq, hc'⟩ := hfinish _ 0 (((hR0.upd 6 x (by omega)).upd 7 y
      (by omega))) rfl (by simp [ha]) (by simp [hc])
    refine ⟨o, st', cst, hrun, hq, ?_⟩
    simp only [lcaContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg,
      Expr.size_load, Expr.size_bin]
    omega

end

end MinCostFlow.LSF.Program
