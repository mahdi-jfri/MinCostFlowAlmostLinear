module

public import MinCostFlow.LowStretch.ProgChildStepRaw2
public import MinCostFlow.LowStretch.ProgChildProg

/-!
# One child: the loads

The first part of `oneP` loads the words that child `k` needs into the registers `11` to `44`
(`onePro`). This file proves a general rule for a list of assignments to registers in increasing
order (`runs_assigns_le`). It then names the words that `oneP` loads (`OneV`) and proves that the
loads put them in the registers (`onePro_runs`), from the memory facts in `OneFacts`.

The general rule avoids long chains of register updates. It tracks the registers by one function
`f`: a register that is assigned later still holds its start value `g`, and every other register
already holds its value under `f`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- **Assignments in increasing order.** Let `f` give the final value of every register and `g`
the current value of every register that is still to be assigned. If each expression evaluates to
the `f` value of its register once the smaller registers hold their `f` values, then the
assignments end with the registers equal to `f`. -/
theorem runs_assigns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {M : ℕ → ℕ} (f g : ℕ → ℕ)
    {s : Stmt} {Q : Outcome → State → Prop} {T : ℕ} :
    ∀ (l : List (ℕ × Expr)) (st : State) (k : ℕ),
      l.Pairwise (fun a b => a.1 < b.1) → st.mem = M →
      (∀ r, st.regs r = if r ∈ l.map Prod.fst then g r else f r) →
      (∀ q ∈ l, ∀ st' : State, st'.mem = M → (∀ r < q.1, st'.regs r = f r) →
        q.2.eval w st' = some (f q.1)) →
      (∀ st' : State, st'.mem = M → st'.regs = f →
        ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧
          k + (l.map fun q => q.2.size + 2).sum + c ≤ T) →
      ∃ o st' c, Runs w p ω (assigns l s) st o st' c ∧ Q o st' ∧ k + c ≤ T
  | [], st, k, _, hM, hr, _, hrest => by
      obtain ⟨o, st', c, h1, h2, h3⟩ := hrest st hM (funext fun r => by simpa using hr r)
      exact ⟨o, st', c, h1, h2, by simpa using h3⟩
  | (r, e) :: l, st, k, hp, hM, hr, hev, hrest => by
      rw [List.pairwise_cons] at hp
      have he : e.eval w st = some (f r) := hev (r, e) (by simp) st hM fun r' hr' => by
        rw [hr r']
        have : r' ∉ ((r, e) :: l).map Prod.fst := by
          simp only [List.map_cons, List.mem_cons, List.mem_map, not_or]
          refine ⟨by omega, ?_⟩
          rintro ⟨q, hq, rfl⟩
          have := hp.1 q hq
          omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h this)]
      refine runs_seq_assign_le he ?_
      refine runs_assigns_le f g l _ _ hp.2 hM (fun r' => ?_)
        (fun q hq => hev q (by simp [hq])) (fun st' h1 h2 => ?_)
      · simp only [Function.update_apply]
        by_cases h : r' = r
        · subst h
          have : r' ∉ l.map Prod.fst := by
            simp only [List.mem_map, not_exists, not_and]
            intro q hq h
            have := hp.1 q hq
            omega
          simp [this]
        · rw [hr r']
          simp only [List.map_cons, List.mem_cons, h, false_or, ↓reduceIte]
      · obtain ⟨o, st'', c, a1, a2, a3⟩ := hrest st' h1 h2
        exact ⟨o, st'', c, a1, a2, by simp only [List.map_cons, List.sum_cons] at a3; omega⟩

/-- The words in the registers `0` to `38` and `44` of `oneP` after the loads. -/
structure OneV where
  GB : ℕ
  RB : ℕ
  XB : ℕ
  BK : ℕ
  k : ℕ
  H : ℕ
  OFFN : ℕ
  ORDN : ℕ
  OFFK : ℕ
  ORDK : ℕ
  HM : ℕ
  IN : ℕ
  PW : ℕ
  EXP : ℕ
  LAB : ℕ
  LOC : ℕ
  HEAD : ℕ
  KMW : ℕ
  KSZ : ℕ
  J : ℕ
  INF : ℕ
  PAR : ℕ
  PP : ℕ
  PF : ℕ
  PA : ℕ
  PB : ℕ
  ACT : ℕ
  Dc : ℕ
  lθ : ℕ
  NAp : ℕ
  ct : ℕ
  cc : ℕ
  u0 : ℕ
  v0 : ℕ
  rg : ℕ
  SRCK : ℕ
  cnt : ℕ
  SRCN : ℕ
  sN : ℕ
  B : ℕ

namespace OneV

variable (V : OneV)

/-- The words in the registers `0` to `38`. -/
def vals : List ℕ :=
  [V.GB, V.RB, V.XB, V.BK, V.k, V.H, V.OFFN, V.ORDN, V.OFFK, V.ORDK, V.HM, V.IN, V.PW, V.EXP,
    V.LAB, V.LOC, V.HEAD, V.KMW, V.KSZ, V.J, V.INF, V.PAR, V.PP, V.PF, V.PA, V.PB, V.ACT, V.Dc,
    V.lθ, V.NAp, V.ct, V.cc, V.u0, V.v0, V.rg, V.SRCK, V.cnt, V.SRCN, V.sN]

/-- The arguments of `oneP`. -/
def args : List ℕ := [V.GB, V.RB, V.XB, V.BK, V.k, V.H, V.OFFN, V.ORDN, V.OFFK, V.ORDK, V.HM]

/-- All registers after the loads. -/
def f (r : ℕ) : ℕ :=
  if r < 39 then V.vals.getD r 0 else if r = 42 then 1 else if r = 43 then 0 else
    if r = 44 then V.B else 0

/-- The registers after the loads, as later steps use them. -/
def Regs (st : State) : Prop :=
  (∀ r < 39, st.regs r = V.vals.getD r 0) ∧ st.regs 42 = 1 ∧ st.regs 43 = 0 ∧ st.regs 44 = V.B

theorem Regs.upd {V : OneV} {st : State} (h : V.Regs st) {r : ℕ} (hr : 39 ≤ r) (hr2 : r ≠ 42)
    (hr3 : r ≠ 43) (hr4 : r ≠ 44) (v : ℕ) (M : ℕ → ℕ) (q : ℕ) :
    V.Regs { mem := M, regs := Function.update st.regs r v, pos := q } := by
  refine ⟨fun r' hr' => ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [Function.update_of_ne (by omega)]; exact h.1 r' hr'
  · rw [Function.update_of_ne (Ne.symm hr2)]; exact h.2.1
  · rw [Function.update_of_ne (Ne.symm hr3)]; exact h.2.2.1
  · rw [Function.update_of_ne (Ne.symm hr4)]; exact h.2.2.2

theorem regs_of_f {V : OneV} {st : State} (h : st.regs = V.f) : V.Regs st := by
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩ <;> rw [h] <;> simp [f, *]

end OneV

/-- The memory facts that the loads of `oneP` use. -/
structure OneFacts (w : ℕ) (V : OneV) (M : ℕ → ℕ) : Prop where
  g3 : M (V.GB + 3) = V.IN
  g4 : M (V.GB + 4) = V.PW
  g5 : M (V.GB + 5) = V.EXP
  g6 : M (V.GB + 6) = V.LAB
  g7 : M (V.GB + 7) = V.LOC
  g14 : M (V.GB + 14) = V.HEAD
  g11 : M (V.GB + 11) = V.KMW
  g12 : M (V.GB + 12) = V.KSZ
  g19 : M (V.GB + 19) = V.J
  g20 : M (V.GB + 20) = V.INF
  g18 : M (V.GB + 18) = V.B
  x8 : M (V.XB + 8) = V.PAR
  x9 : M (V.XB + 9) = V.PP
  x10 : M (V.XB + 10) = V.PF
  x11 : M (V.XB + 11) = V.PA
  x12 : M (V.XB + 12) = V.PB
  x14 : M (V.XB + 14) = V.ACT
  x15 : M (V.XB + 15) = V.Dc
  r3 : M (V.RB + 3) = V.lθ
  r4 : M (V.RB + 4) = V.NAp
  ct : M (M (V.XB + 6) + V.k) = V.ct
  cc : M (M (V.XB + 7) + V.k) = V.cc
  u0 : M (V.LOC + M (V.LAB + V.ct)) = V.u0
  v0 : M (V.LOC + M (V.LAB + V.cc)) = V.v0
  rg : V.rg = (if 0 < V.k then 1 else 0) * (1 - (if M (V.XB + 1) = 1 then 1 else 0) *
    (if V.k = 1 then 1 else 0))
  srck : V.SRCK = V.ORDK + M (V.OFFK + V.k)
  cnt : V.cnt = M (V.OFFK + V.k + 1) - M (V.OFFK + V.k)
  srcn : V.SRCN = V.ORDN + M (V.OFFN + V.k)
  sN : V.sN = M (V.OFFN + V.k + 1) - M (V.OFFN + V.k)
  bGB : V.GB + 21 < 2 ^ w
  bXB : V.XB + 16 < 2 ^ w
  bRB : V.RB + 9 < 2 ^ w
  bct : M (V.XB + 6) + V.k < 2 ^ w ∧ M (V.XB + 7) + V.k < 2 ^ w
  blab : V.LAB + V.ct < 2 ^ w ∧ V.LAB + V.cc < 2 ^ w
  bloc : V.LOC + M (V.LAB + V.ct) < 2 ^ w ∧ V.LOC + M (V.LAB + V.cc) < 2 ^ w
  bk : V.OFFK + V.k + 1 < 2 ^ w ∧ V.OFFN + V.k + 1 < 2 ^ w
  bkv : M (V.OFFK + V.k + 1) < 2 ^ w ∧ M (V.OFFN + V.k + 1) < 2 ^ w
  bsrc : V.SRCK < 2 ^ w ∧ V.SRCN < 2 ^ w
  bw : 2 < 2 ^ w

theorem onePro_pairwise : onePro.Pairwise (fun a b => a.1 < b.1) := by decide

theorem onePro_cost : (onePro.map fun q => q.2.size + 2).sum ≤ 600 := by decide

/-- **The loads.** Started on the arguments of `V`, the loads of `oneP` put the words of `V` in
the registers. -/
theorem onePro_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {V : OneV} {M : ℕ → ℕ} {pos : ℕ}
    (hF : OneFacts w V M) {s : Stmt} {Q : Outcome → State → Prop} {T : ℕ}
    (hrest : ∀ st : State, V.Regs st → st.mem = M →
      ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ 600 + c ≤ T) :
    ∃ o st' c, Runs w p ω (assigns onePro s) (startState V.args M pos) o st' c ∧ Q o st' ∧
      c ≤ T := by
  refine runs_start_le (runs_assigns_le V.f (fun i => V.args.getD i 0) onePro _ 0
    onePro_pairwise rfl (fun r => ?_) ?_ (fun st' h1 h2 => ?_))
  · split_ifs with h
    · rfl
    · simp only [onePro, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      rcases Nat.lt_or_ge r 11 with h11 | h11
      · interval_cases r <;> rfl
      · have : V.args.getD r 0 = 0 := List.getD_eq_default _ _ (by simp [OneV.args]; omega)
        show V.args.getD r 0 = V.f r
        rw [this]
        unfold OneV.f
        split_ifs <;> first | rfl | omega
  · intro q hq st' hM hr
    have hM' : st'.mem = M := hM
    have hw := hF.bw
    have ld : ∀ {r i x v : ℕ}, st'.regs r = x → x + i < 2 ^ w → st'.mem (x + i) = v →
        (ldO r i).eval w st' = some v := fun hr hb hm =>
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const
        (by omega)) hb) hm
    simp only [onePro, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    have R := fun i (hi : i < _) => hr i hi <;> dsimp only at R
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g3)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g4)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g5)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g6)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g7)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g14)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g11)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g12)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g19)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g20)
    · exact ld (show st'.regs 2 = V.XB from R 2 (by norm_num)) (by have := hF.bXB; omega)
            ((congrFun hM' _).trans hF.x8)
    · exact ld (show st'.regs 2 = V.XB from R 2 (by norm_num)) (by have := hF.bXB; omega)
            ((congrFun hM' _).trans hF.x9)
    · exact ld (show st'.regs 2 = V.XB from R 2 (by norm_num)) (by have := hF.bXB; omega)
            ((congrFun hM' _).trans hF.x10)
    · exact ld (show st'.regs 2 = V.XB from R 2 (by norm_num)) (by have := hF.bXB; omega)
            ((congrFun hM' _).trans hF.x11)
    · exact ld (show st'.regs 2 = V.XB from R 2 (by norm_num)) (by have := hF.bXB; omega)
            ((congrFun hM' _).trans hF.x12)
    · exact ld (show st'.regs 2 = V.XB from R 2 (by norm_num)) (by have := hF.bXB; omega)
            ((congrFun hM' _).trans hF.x14)
    · exact ld (show st'.regs 2 = V.XB from R 2 (by norm_num)) (by have := hF.bXB; omega)
            ((congrFun hM' _).trans hF.x15)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by have := hF.bRB; omega)
            ((congrFun hM' _).trans hF.r3)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by have := hF.bRB; omega)
            ((congrFun hM' _).trans hF.r4)
    · exact Expr.eval_load_of_eq (Expr.eval_add (ld (show st'.regs 2 = V.XB from R 2
            (by norm_num)) (by have := hF.bXB; omega)
        (congrFun hM' _)) (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4
                (by norm_num))) hF.bct.1) ((congrFun hM' _).trans hF.ct)
    · exact Expr.eval_load_of_eq (Expr.eval_add (ld (show st'.regs 2 = V.XB from R 2
            (by norm_num)) (by have := hF.bXB; omega)
        (congrFun hM' _)) (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4
                (by norm_num))) hF.bct.2) ((congrFun hM' _).trans hF.cc)
    · exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
            (show st'.regs 15 = V.LOC from R 15 (by norm_num)))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
                (show st'.regs 14 = V.LAB from R 14 (by norm_num)))
          (Expr.eval_reg_of_eq (show st'.regs 30 = V.ct from R 30 (by norm_num))) hF.blab.1)
                  (congrFun hM' _)) hF.bloc.1) ((congrFun hM' _).trans hF.u0)
    · exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
            (show st'.regs 15 = V.LOC from R 15 (by norm_num)))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
                (show st'.regs 14 = V.LAB from R 14 (by norm_num)))
          (Expr.eval_reg_of_eq (show st'.regs 31 = V.cc from R 31 (by norm_num))) hF.blab.2)
                  (congrFun hM' _)) hF.bloc.2) ((congrFun hM' _).trans hF.v0)
    · show _ = some V.rg
      rw [hF.rg]
      refine Expr.eval_mul (Expr.eval_lt_op (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4 (by norm_num))) (by omega))
        (Expr.eval_sub (Expr.eval_const (by omega)) (Expr.eval_mul (Expr.eval_eq_op
          (ld (show st'.regs 2 = V.XB from R 2 (by norm_num)) (by have := hF.bXB; omega)
                  (congrFun hM' _)) (Expr.eval_const (by omega))
          (by omega)) (Expr.eval_eq_op (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4
                  (by norm_num)))
          (Expr.eval_const (by omega)) (by omega)) ?_) (by omega)) ?_
      · split_ifs <;> omega
      · split_ifs <;> omega
    · show _ = some V.SRCK
      rw [hF.srck]
      exact Expr.eval_add (Expr.eval_reg_of_eq (show st'.regs 9 = V.ORDK from R 9 (by norm_num)))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
                (show st'.regs 8 = V.OFFK from R 8 (by norm_num)))
          (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4 (by norm_num)))
                  (by have := hF.bk.1; omega)) (congrFun hM' _))
        (by rw [← hF.srck]; exact hF.bsrc.1)
    · show _ = some V.cnt
      rw [hF.cnt]
      exact Expr.eval_sub (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq (show st'.regs 8 = V.OFFK from R 8 (by norm_num)))
                  (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4 (by norm_num)))
          (by have := hF.bk.1; omega)) (Expr.eval_const (by omega)) hF.bk.1) (congrFun hM' _))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
                (show st'.regs 8 = V.OFFK from R 8 (by norm_num)))
          (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4 (by norm_num)))
                  (by have := hF.bk.1; omega)) (congrFun hM' _))
        hF.bkv.1
    · show _ = some V.SRCN
      rw [hF.srcn]
      exact Expr.eval_add (Expr.eval_reg_of_eq (show st'.regs 7 = V.ORDN from R 7 (by norm_num)))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
                (show st'.regs 6 = V.OFFN from R 6 (by norm_num)))
          (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4 (by norm_num)))
                  (by have := hF.bk.2; omega)) (congrFun hM' _))
        (by rw [← hF.srcn]; exact hF.bsrc.2)
    · show _ = some V.sN
      rw [hF.sN]
      exact Expr.eval_sub (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq (show st'.regs 6 = V.OFFN from R 6 (by norm_num)))
                  (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4 (by norm_num)))
          (by have := hF.bk.2; omega)) (Expr.eval_const (by omega)) hF.bk.2) (congrFun hM' _))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
                (show st'.regs 6 = V.OFFN from R 6 (by norm_num)))
          (Expr.eval_reg_of_eq (show st'.regs 4 = V.k from R 4 (by norm_num)))
                  (by have := hF.bk.2; omega)) (congrFun hM' _))
        hF.bkv.2
    · exact Expr.eval_const (by omega)
    · exact Expr.eval_const (by omega)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by have := hF.bGB; omega)
            ((congrFun hM' _).trans hF.g18)
  · obtain ⟨o, st'', c, a1, a2, a3⟩ := hrest st' (OneV.regs_of_f h2) h1
    exact ⟨o, st'', c, a1, a2, by have := onePro_cost; omega⟩

end MinCostFlow.LowStretch
