module

public import MinCostFlow.LowStretch.ProgChildOneA

/-!
# The reset of a child: the loads

`rsP` starts with its arguments in the registers `0` to `13` and loads the addresses it needs
into the registers `14` to `32` (`rsPro`). This file names these words (`RsV`) and proves the run
of the loads (`rsPro_runs`) by `runs_assigns_le`, as `onePro_runs` does for `oneP`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The words of `rsP`: the arguments (registers `0`–`13`) and the loads (registers `14`–`28`). -/
structure RsV where
  GB : ℕ
  BK : ℕ
  A : ℕ
  Δ : ℕ
  sz : ℕ
  μ : ℕ
  SRCK : ℕ
  cnt : ℕ
  NA : ℕ
  sN : ℕ
  cc : ℕ
  HM : ℕ
  XB : ℕ
  B : ℕ
  CH1 : ℕ
  CH2 : ℕ
  MW : ℕ
  SZ : ℕ
  LO : ℕ
  ORDL : ℕ
  LAB : ℕ
  n : ℕ
  HEAD : ℕ
  LOC : ℕ
  GOFF : ℕ
  GPR : ℕ
  IN : ℕ
  ACT : ℕ
  PP : ℕ

namespace RsV

variable (V : RsV)

/-- The arguments of `rsP`. -/
def args : List ℕ := [V.GB, V.BK, V.A, V.Δ, V.sz, V.μ, V.SRCK, V.cnt, V.NA, V.sN, V.cc, V.HM, V.XB,
  V.B]

/-- The words in the registers `0` to `28`. -/
def vals : List ℕ := V.args ++ [V.CH1, V.CH2, V.MW, V.SZ, V.LO, V.ORDL, V.LAB, V.n, V.HEAD, V.LOC,
  V.GOFF, V.GPR, V.IN, V.ACT, V.PP]

/-- All registers after the loads. -/
def f (r : ℕ) : ℕ :=
  if r < 29 then V.vals.getD r 0 else if r = 29 then 0 else if r = 30 then 3 else
    if r = 31 then 1 else if r = 32 then V.A + 2 else 0

/-- The registers after the loads, as later steps use them. -/
def Regs (st : State) : Prop := ∀ r < 33, st.regs r = V.f r

end RsV

/-- The memory facts that the loads of `rsP` use. -/
structure RsFacts (w : ℕ) (V : RsV) (M : ℕ → ℕ) : Prop where
  g9 : M (V.GB + 9) = V.CH1
  g10 : M (V.GB + 10) = V.CH2
  g11 : M (V.GB + 11) = V.MW
  g12 : M (V.GB + 12) = V.SZ
  g13 : M (V.GB + 13) = V.LO
  g15 : M (V.GB + 15) = V.ORDL
  g6 : M (V.GB + 6) = V.LAB
  g0 : M (V.GB + 0) = V.n
  g14 : M (V.GB + 14) = V.HEAD
  g7 : M (V.GB + 7) = V.LOC
  g16 : M (V.GB + 16) = V.GOFF
  g17 : M (V.GB + 17) = V.GPR
  g3 : M (V.GB + 3) = V.IN
  x14 : M (V.XB + 14) = V.ACT
  x9 : M (V.XB + 9) = V.PP
  bGB : V.GB + 17 < 2 ^ w
  bXB : V.XB + 14 < 2 ^ w
  bA : V.A + 2 < 2 ^ w
  bw : 3 < 2 ^ w

theorem rsPro_pairwise : rsPro.Pairwise (fun a b => a.1 < b.1) := by decide

theorem rsPro_cost : (rsPro.map fun q => q.2.size + 2).sum ≤ 200 := by decide

/-- **The loads of `rsP`.** Started on the arguments of `V`, the loads put the words of `V` in
the registers. -/
theorem rsPro_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {V : RsV} {M : ℕ → ℕ} {pos : ℕ}
    (hF : RsFacts w V M) {s : Stmt} {Q : Outcome → State → Prop} {T : ℕ}
    (hrest : ∀ st : State, V.Regs st → st.mem = M →
      ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ 200 + c ≤ T) :
    ∃ o st' c, Runs w p ω (assigns rsPro s) (startState V.args M pos) o st' c ∧ Q o st' ∧
      c ≤ T := by
  have hw : 3 < 2 ^ w := hF.bw
  refine runs_start_le (runs_assigns_le V.f (fun i => V.args.getD i 0) rsPro _ 0
    rsPro_pairwise rfl (fun r => ?_) ?_ (fun st' h1 h2 => ?_))
  · split_ifs with h
    · rfl
    · simp only [rsPro, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      rcases Nat.lt_or_ge r 14 with h14 | h14
      · interval_cases r <;> rfl
      · have : V.args.getD r 0 = 0 := List.getD_eq_default _ _ (by simp [RsV.args]; omega)
        show V.args.getD r 0 = V.f r
        rw [this]
        unfold RsV.f
        split_ifs <;> first | rfl | omega
  · intro q hq st' hM hr
    have hM' : st'.mem = M := hM
    have ld : ∀ {r i x v : ℕ}, st'.regs r = x → x + i < 2 ^ w → st'.mem (x + i) = v →
        (ldO r i).eval w st' = some v := fun hr hb hm =>
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const
        (by omega)) hb) hm
    have bG := hF.bGB
    have bX := hF.bXB
    simp only [rsPro, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    have hGB : st'.regs 0 = V.GB := (by rw [hr 0 (by norm_num)]; rfl) <;>
    have hXB : st'.regs 12 = V.XB := (by rw [hr 12 (by norm_num)]; rfl)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g9)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g10)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g11)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g12)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g13)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g15)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g6)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g0)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g14)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g7)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g16)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g17)
    · exact ld hGB (by omega) ((congrFun hM' _).trans hF.g3)
    · exact ld hXB (by omega) ((congrFun hM' _).trans hF.x14)
    · exact ld hXB (by omega) ((congrFun hM' _).trans hF.x9)
    · exact Expr.eval_const (by omega)
    · exact Expr.eval_const (by omega)
    · exact Expr.eval_const (by omega)
    · exact Expr.eval_add (Expr.eval_reg_of_eq (show st'.regs 2 = V.A by rw [hr 2 (by norm_num)]; rfl))
        (Expr.eval_const (by omega)) hF.bA
  · obtain ⟨o, st'', c, a1, a2, a3⟩ := hrest st' (fun r _ => by rw [h2]) h1
    exact ⟨o, st'', c, a1, a2, by have := rsPro_cost; omega⟩

end MinCostFlow.LowStretch
