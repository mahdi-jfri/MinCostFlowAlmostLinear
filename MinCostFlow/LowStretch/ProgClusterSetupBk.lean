module

public import MinCostFlow.LowStretch.ProgClusterSetupT2

/-!
# The setup of a cluster: the run of the stores of the block

The setup ends with the stores of the block at `h` (`suBlk`) and returns. This file names the
`51` words of the block (`suBlkL`) and proves the run of the stores (`suBlk_runs`) from the
registers `SuR` with `Es`, `bw` and `RR` in registers `31`, `32`, `33`: each expression of
`suBlk` evaluates to its word, by `SuR.z_eval` and `suR_eval` for the addresses. The five words
of the block that are `0` are not stored; the cells of the block hold `0` before the stores.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The words of the block at `h`, for the layout `N`, `INF`, `m`, `n`, the number `nA` of
active entries, the largest exponent `Es`, the radius `Δ`, the distance `dt` of the target, the
node `ts` of the target and the target `t`. -/
def suBlkL (N : SuN) (INF m n nA Es Δ dt ts t : ℕ) : List ℕ :=
  [N.D, N.J + 5, N.A2, INF, N.z 10 12 0 2, N.z 10 12 0 3, N.z 12 15 0 5, N.z 14 16 0 5,
    N.z 16 17 0 5, N.z 18 18 0 5, 0, N.z 23 21 2 11, N.s + 1, 0, N.RR, N.z 18 20 0 7,
    N.z 20 21 0 7, N.z 22 21 0 7, Es, N.r 0 6, 1 <<< Es, m / (n * n) + 1, nA, 0, Δ / 8 / N.L,
    N.L, N.z 23 21 0 7, N.z 23 21 1 9, N.z 18 19 0 6, N.r 0 11, N.s, N.r 0 2, 0, N.r 1 13,
    N.r 2 13, N.r 3 14, N.r 4 15, N.r 5 16, N.z 0 1 0 1, N.z 0 3 0 1,
    N.H + 16 * N.nS + 4 * N.s + 5, 0, Δ, dt - (Δ + 1) / 2 - Δ / 8, ts, t,
    if 5 * Δ < 8 * dt then 1 else 0, N.z 0 2 0 1, N.z 0 4 0 1, N.z 0 8 0 2, N.r 6 16]

theorem suBlkL_length (N : SuN) (INF m n nA Es Δ dt ts t : ℕ) :
    (suBlkL N INF m n nA Es Δ dt ts t).length = 51 := rfl

theorem suBlk_pairwise : suBlk.Pairwise (fun a b => a.1 < b.1) := by decide

theorem suBlk_lt : ∀ q ∈ suBlk, q.1 < 51 := by decide

theorem suBlk_offs : suBlk.map Prod.fst =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27,
      28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50] := rfl

theorem suStCost_suBlk : suStCost suBlk ≤ 2000 := by decide

private theorem blk_cover : ∀ i < 51, i ∈ suBlk.map Prod.fst ∨
    (i = 10 ∨ i = 13 ∨ i = 23 ∨ i = 32 ∨ i = 41) := by
  rw [suBlk_offs]; decide

private theorem blk_zero (N : SuN) (INF m n nA Es Δ dt ts t : ℕ) :
    ∀ i, (i = 10 ∨ i = 13 ∨ i = 23 ∨ i = 32 ∨ i = 41) →
      i ∉ suBlk.map Prod.fst ∧ (suBlkL N INF m n nA Es Δ dt ts t).getD i 0 = 0 := by
  rw [suBlk_offs]
  rintro i (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, rfl⟩

/-- The word bounds of the values of the block. -/
structure BkW (w : ℕ) (V : SuV) (Es Δ dt : ℕ) : Prop where
  hJ : V.J + 5 < 2 ^ w
  hnn : V.n * V.n < 2 ^ w
  hm : V.m < 2 ^ w
  hκ : V.m / (V.n * V.n) + 1 < 2 ^ w
  hM : 1 <<< Es < 2 ^ w
  hΔ : 5 * Δ + 1 < 2 ^ w
  hdt : 8 * dt < 2 ^ w

variable {w : ℕ} {p : Program} {ω : ℕ → Bool} {V : SuV} {L Δ nA : ℕ}

theorem SuR.of_regs {st st' : State} (h : SuR w V L Δ nA st) (he : st'.regs = st.regs) :
    SuR w V L Δ nA st' :=
  ⟨fun r hr => by rw [he]; exact h.regs r hr, by rw [he]; exact h.r23, by rw [he]; exact h.r24,
    by rw [he]; exact h.r28, by rw [he]; exact h.r30, h.hS, h.w20, h.nA_le⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The stores of the block.** From the registers `SuR` with `Es`, `bw = Δ / 8 / L` and `RR`
in registers `31` to `33`, and a block of zero cells at `h`, the stores of `suBlk` and the return
leave the words `suBlkL` at `h` and change no other cell. -/
theorem suBlk_runs {st : State} (hR : SuR w V L Δ nA st) {Es dt : ℕ}
    (r31 : st.regs 31 = Es) (r32 : st.regs 32 = Δ / 8 / L) (r33 : st.regs 33 = (V.N L).RR)
    (hdt : st.mem (V.h + 51 + 16 * V.nS + 4 * V.s + 5 + V.ts) = dt)
    (hts : V.ts < V.s) (hz : ∀ i < 51, st.mem (V.h + i) = 0) (hW : BkW w V Es Δ dt)
    {Q : Outcome → State → Prop} {k K : ℕ}
    (hrest : ∀ st' : State, st'.regs = st.regs →
      (∀ i < 51, st'.mem (V.h + i) =
        (suBlkL (V.N L) V.INF V.m V.n nA Es Δ dt V.ts V.t).getD i 0) →
      (∀ a, (a < V.h ∨ V.h + 51 ≤ a) → st'.mem a = st.mem a) →
      Q (.returned 0) st' ∧ k + 2002 ≤ K) :
    ∃ o st' c, Runs w p ω (suStores suBlk (.ret (.const 0))) st o st' c ∧ Q o st' ∧ k + c ≤ K := by
  set N := V.N L with hN
  set f := fun i => (suBlkL N V.INF V.m V.n nA Es Δ dt V.ts V.t).getD i 0 with hf
  have w20 := hR.w20
  have hS : N.hS < 2 ^ w := hR.hS
  have ez : ∀ a b c k, N.z a b c k = N.Z + a * N.nS + b * N.s + c * N.L + k := fun _ _ _ _ => rfl
  have er : ∀ b k, N.r b k = N.RR + b * N.s + k := fun _ _ => rfl
  have eS : N.hS = N.RR + 6 * N.s + 16 := rfl
  have eRR := N.RR_eq'
  have eD := ez 23 26 2 16
  have eDD : N.D = N.z 23 26 2 16 := rfl
  have eZ : N.Z = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) := rfl
  have vs : N.s = V.s := rfl
  have vn : N.nS = V.nS := rfl
  have vh : N.h = V.h := rfl
  have vJ : N.J = V.J := rfl
  have vL : N.L = L := rfl
  have hh : V.h + 51 < 2 ^ w := by omega
  obtain ⟨wJ, wnn, wm, wκ, wM, wΔ, wdt⟩ := hW
  have hFD : V.h + 51 + 16 * V.nS + 4 * V.s + 5 < 2 ^ w := by omega
  refine runs_suStores_le (M := st.mem) f suBlk st k suBlk_pairwise rfl
    (show st.regs 2 = V.h from hR.r (i := 2) (by norm_num)) suBlk_lt hh (fun _ _ => rfl) ?_ ?_
  · intro q hq st' h1 h3
    have hR' := hR.of_regs h1
    have rg : ∀ {i : ℕ} (hi : i < 23), (Expr.reg i).eval w st' = some (V.vals.getD i 0) :=
      fun hi => Expr.eval_reg_of_eq (hR'.r hi)
    have zv : ∀ {a b c k : ℕ}, a ≤ 23 → b ≤ 26 → c ≤ 2 → k ≤ 16 →
        (suZ a b c k).eval w st' = some (N.z a b c k) := fun ha hb hc hk =>
      hR'.z_eval ha hb hc hk
    have rv : ∀ {b k : ℕ}, b ≤ 6 → k ≤ 16 → (suR b k).eval w st' = some (N.r b k) :=
      fun hb hk => suR_eval (by rw [h1]; exact r33) hR'.r13 w20 (by omega) (by omega) rfl
        (by have := Nat.mul_le_mul_right N.s hb; rw [er]; omega)
    have fd : suFD.eval w st' = some (V.h + 51 + 16 * V.nS + 4 * V.s + 5) :=
      suH_eval (hR'.r (i := 21) (by norm_num)) (hR'.r (i := 14) (by norm_num))
        (hR'.r (i := 13) (by norm_num)) w20 (by norm_num) (by norm_num) (by norm_num) rfl hFD
    have dtv : suDt.eval w st' = some dt := by
      refine Expr.eval_load_of_eq (Expr.eval_add fd (Expr.eval_reg_of_eq
        (show st'.regs 22 = V.ts from hR'.r (i := 22) (by norm_num))) ?_) ?_
      · have := N.z_le_hS (a := 0) (b := 8) (c := 0) (k := 2) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
        show _ < 2 ^ w
        rw [ez] at this; omega
      · rw [h3 (V.h + 51 + 16 * V.nS + 4 * V.s + 5 + V.ts) (Or.inr (by omega))]; exact hdt
    have w1 : 1 < 2 ^ w := by omega
    have r23 : st'.regs 23 = Δ := hR'.r23
    have r30 : st'.regs 30 = nA := hR'.r30
    have r31' : st'.regs 31 = Es := by rw [h1]; exact r31
    have r32' : st'.regs 32 = Δ / 8 / L := by rw [h1]; exact r32
    have r33' : st'.regs 33 = N.RR := by rw [h1]; exact r33
    have hdt8 : dt < 2 ^ w := by omega
    simp only [suBlk, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals dsimp only
    all_goals first
      | exact zv (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      | exact rv (by norm_num) (by norm_num)
      | skip
    · show Expr.eval w st' suJq = some (V.J + 5)
      exact Expr.eval_add (Expr.eval_reg_of_eq (show st'.regs 11 = V.J from hR'.r (by norm_num)))
        (Expr.eval_const (by omega)) wJ
    · show Expr.eval w st' suA = some (2 * V.nS + 2 * V.s)
      exact Expr.eval_add (mulC_eval (a := 2) (show st'.regs 14 = V.nS from hR'.r (by norm_num))
        (by omega) (by omega)) (mulC_eval (a := 2)
        (show st'.regs 13 = V.s from hR'.r (by norm_num)) (by omega) (by omega)) (by omega)
    · exact Expr.eval_reg_of_eq (show st'.regs 12 = V.INF from hR'.r (by norm_num))
    · show Expr.eval w st' _ = some (V.s + 1)
      exact Expr.eval_add (Expr.eval_reg_of_eq (show st'.regs 13 = V.s from hR'.r (by norm_num)))
        (Expr.eval_const (by omega)) (by omega)
    · exact Expr.eval_reg_of_eq r33'
    · exact Expr.eval_reg_of_eq r31'
    · exact Expr.eval_shiftLeft (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r31') wM
    · show Expr.eval w st' _ = some (V.m / (V.n * V.n) + 1)
      exact Expr.eval_add (Expr.eval_div (Expr.eval_reg_of_eq
        (show st'.regs 4 = V.m from hR'.r (by norm_num))) (Expr.eval_mul (Expr.eval_reg_of_eq
        (show st'.regs 3 = V.n from hR'.r (by norm_num))) (Expr.eval_reg_of_eq
        (show st'.regs 3 = V.n from hR'.r (by norm_num))) wnn) wm) (Expr.eval_const (by omega)) wκ
    · exact Expr.eval_reg_of_eq r30
    · exact Expr.eval_reg_of_eq r32'
    · exact Expr.eval_reg_of_eq hR'.r28
    · exact Expr.eval_reg_of_eq (show st'.regs 13 = V.s from hR'.r (by norm_num))
    · exact fd
    · exact Expr.eval_reg_of_eq r23
    · show Expr.eval w st' _ = some (dt - (Δ + 1) / 2 - Δ / 8)
      exact Expr.eval_sub (Expr.eval_sub dtv (Expr.eval_div (Expr.eval_add
        (Expr.eval_reg_of_eq r23) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_const (by omega)) (by omega)) hdt8)
        (Expr.eval_div (Expr.eval_reg_of_eq r23) (Expr.eval_const (by omega)) (by omega))
        (by omega)
    · exact Expr.eval_reg_of_eq (show st'.regs 22 = V.ts from hR'.r (by norm_num))
    · exact Expr.eval_reg_of_eq (show st'.regs 18 = V.t from hR'.r (by norm_num))
    · show Expr.eval w st' _ = some (if 5 * Δ < 8 * dt then 1 else 0)
      exact Expr.eval_lt_op (mulC_eval (a := 5) r23 (by omega) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) dtv wdt) w1
  · intro st' h1 h3 h4
    have hq := hrest st' h1 (fun i hi => by
      rcases blk_cover i hi with hm | hm
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact h3 q hq
      · obtain ⟨hn, h0⟩ := blk_zero N V.INF V.m V.n nA Es Δ dt V.ts V.t i hm
        rw [h4 (V.h + i) (fun q hq he => hn (List.mem_map.mpr ⟨q, hq, by omega⟩)), hz i hi]
        exact h0.symm)
      (fun a ha => h4 a (fun q hq => by have := suBlk_lt q hq; omega))
    have hc := suStCost_suBlk
    exact runs_ret_le (Expr.eval_const (by omega)) hq.1 (by simp [Expr.size]; omega)

end MinCostFlow.LowStretch
