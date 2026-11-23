module

public import MinCostFlow.LowStretch.ProgClusterSetupTc

/-!
# The setup of a cluster: the call of `pgP`

After `actP`, the setup calls `pgP` to build the graph of the petal searches. Its arguments are
the active entries `ACT`, the arrays of the pairs, the distances `FD` of the first run, `lθ`, the
class bound `Jc = J + 3`, the parents `PCI` and the costs `SCc` and classes `SCk` of the parent
arcs, and the arrays of the graph from `Z + 2 nS + 8 s + 2` on (`suPGA`). This file proves the
run of the call (`suPg_runs`) from the registers `SuR` and the precondition of `pgP`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The setting of `pgP` in the setup, for the loads `V`, `L` buckets and `nA` active
entries. -/
def suPGA (V : SuV) (L nA : ℕ) : PGA :=
  ⟨nA, (V.N L).z 0 8 0 2, V.IN, V.PW, V.LAB, V.LOC, V.h + 51 + 16 * V.nS + 4 * V.s + 5, V.lθ,
    V.J + 3, (V.N L).z 2 8 0 2, (V.N L).z 4 9 0 2, (V.N L).z 6 10 0 2, (V.N L).z 8 11 0 2,
    2 * V.nS + V.s, V.s, V.x0, (V.N L).z 0 7 0 1, (V.N L).z 0 5 0 1, (V.N L).z 0 6 0 1,
    (V.N L).z 10 12 0 2, (V.N L).z 10 13 0 4, (V.N L).z 10 14 0 5, (V.N L).z 12 15 0 5,
    (V.N L).z 14 16 0 5, (V.N L).z 16 17 0 5, (V.N L).z 18 18 0 5, 0⟩

/-- The arguments of the call of `pgP`. -/
def suPgArgs : List Expr :=
  [.reg 30, suZ 0 8 0 2, .reg 5, .reg 6, .reg 8, .reg 9, suFD, .reg 16,
    .bin .add (.reg 11) (.const 3), suZ 2 8 0 2, suZ 4 9 0 2, suZ 6 10 0 2, suZ 8 11 0 2,
    suNI, .reg 13, .reg 17, suZ 0 7 0 1, suZ 0 5 0 1, suZ 0 6 0 1, suZ 10 12 0 2,
    suZ 10 13 0 4, suZ 10 14 0 5, suZ 12 15 0 5, suZ 14 16 0 5, suZ 16 17 0 5, suZ 18 18 0 5,
    .const 0]

theorem suPgArgs_size : argsSize suPgArgs ≤ 400 := by decide

/-- **The graph of the petal searches.** From the registers `SuR` and a memory `M` that meets
the precondition of `pgP` for `suPGA`, the call of `pgP` leaves the graph in `M'`. -/
theorem suPg_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : SuIdx}
    (hPg : MeetsContract w p I.pg (pgPC w)) {V : SuV} {L Δ nA : ℕ} {st : State}
    (hR : SuR w V L Δ nA st) {m n NL NS MM : ℕ}
    (hpre : (suPGA V L nA).Pre w st.mem m n NL NS MM)
    (hw : V.IN < 2 ^ w ∧ V.PW < 2 ^ w ∧ V.LAB < 2 ^ w ∧ V.LOC < 2 ^ w ∧ V.lθ < 2 ^ w ∧
      V.x0 < 2 ^ w)
    {s : Stmt} {Q : Outcome → State → Prop} {k K : ℕ}
    (hrest : ∀ v M', (pgPC w).post (suPGA V L nA).args st.mem v M' →
      ∀ st' : State, SuR w V L Δ nA st' → st'.mem = M' →
        ∃ o st'' c', Runs w p ω s st' o st'' c' ∧ Q o st'' ∧
          k + nA * (80 * Nat.clog 2 (V.J + 3) + 1000) + 500 * V.s + 1000 + c' ≤ K) :
    ∃ o st' c', Runs w p ω (.seq (.call 25 I.pg suPgArgs) s) st o st' c' ∧ Q o st' ∧
      k + c' ≤ K := by
  obtain ⟨wIN, wPW, wLAB, wLOC, wlθ, wx0⟩ := hw
  set N := V.N L with hN
  have w20 := hR.w20
  have ez : ∀ a b c k, N.z a b c k = N.Z + a * N.nS + b * N.s + c * N.L + k := fun _ _ _ _ => rfl
  have hbig : N.z 23 26 2 16 < 2 ^ w := hR.z_lt (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hzb := ez 23 26 2 16
  have eZ : N.Z = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) := rfl
  have vs : N.s = V.s := rfl
  have vn : N.nS = V.nS := rfl
  have vh : N.h = V.h := rfl
  have vJ : N.J = V.J := rfl
  have hnA := hR.nA_le
  have hJ3 : V.J + 3 < 2 ^ w := by
    have : V.J ≤ 4 * N.J := by omega
    omega
  have hFD : V.h + 51 + 16 * V.nS + 4 * V.s + 5 < 2 ^ w := by omega
  have hNI : 2 * V.nS + V.s < 2 ^ w := by omega
  have zv : ∀ {a b c k : ℕ}, a ≤ 23 → b ≤ 26 → c ≤ 2 → k ≤ 16 →
      (suZ a b c k).eval w st = some (N.z a b c k) := fun ha hb hc hk => hR.z_eval ha hb hc hk
  have rr : ∀ {i : ℕ} (hi : i < 23), (Expr.reg i).eval w st = some (V.vals.getD i 0) :=
    fun hi => Expr.eval_reg_of_eq (hR.r hi)
  have hargs : evalArgs w st suPgArgs = some (suPGA V L nA).args := by
    refine evalArgs_cons (Expr.eval_reg_of_eq hR.r30) (evalArgs_cons (zv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (evalArgs_cons (rr (i := 5) (by norm_num))
      (evalArgs_cons (rr (i := 6) (by norm_num)) (evalArgs_cons (rr (i := 8) (by norm_num))
      (evalArgs_cons (rr (i := 9) (by norm_num)) (evalArgs_cons ?_
      (evalArgs_cons (rr (i := 16) (by norm_num)) (evalArgs_cons ?_ ?_))))))))
    · exact suH_eval (hR.r (i := 21) (by norm_num)) (hR.r (i := 14) (by norm_num))
        (hR.r (i := 13) (by norm_num)) w20 (by norm_num) (by norm_num) (by norm_num) rfl hFD
    · exact Expr.eval_add (Expr.eval_reg_of_eq (hR.r (i := 11) (by norm_num)))
        (Expr.eval_const (by omega)) hJ3
    refine evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons ?_ (evalArgs_cons (rr (i := 13) (by norm_num))
      (evalArgs_cons (rr (i := 17) (by norm_num)) ?_))))))
    · exact Expr.eval_add (mulC_eval (a := 2) (hR.r (i := 14) (by norm_num)) (by omega)
        (show 2 * V.nS < 2 ^ w by omega)) (Expr.eval_reg_of_eq (hR.r (i := 13) (by norm_num)))
        hNI
    refine evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (zv (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (Expr.eval_const (by omega)) (evalArgs_nil _ _)))))))))))
  have hwords : ∀ v ∈ (suPGA V L nA).args, v < 2 ^ w := by
    intro v hv
    simp only [PGA.args, suPGA, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | assumption
      | exact hR.z_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      | omega
  refine runs_seq_call_le hPg hargs hwords ⟨_, _, _, _, _, _, rfl, hpre⟩ (fun v M' pos hp => ?_)
  have hR1 := hR.upd (r := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) v M' pos
  obtain ⟨o, st', c', r1, r2, r3⟩ := hrest v M' hp _ hR1 rfl
  refine ⟨o, st', c', r1, r2, ?_⟩
  have := suPgArgs_size
  have e : (pgPC w).cost (suPGA V L nA).args st.mem =
      nA * (80 * Nat.clog 2 (V.J + 3) + 1000) + 500 * V.s + 500 := rfl
  omega

end MinCostFlow.LowStretch
