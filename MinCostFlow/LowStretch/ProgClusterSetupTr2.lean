module

public import MinCostFlow.LowStretch.ProgClusterSetupTr

/-!
# The setup of a cluster: the call of `treeP`

After `drawP`, the setup computes the end `Z` of the cells of `drawP` into register `24` and calls
`treeP` with its arrays from `Z` on. This file proves the run of these two steps (`suTr_runs`),
from register equations and `Rec.First`. All addresses are below the end `hS` of the heap of the
setup, which is a word (`ClPre.hS_lt`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The layout of the setup for the loads `V` and `L` buckets. -/
def SuV.N (V : SuV) (L : ℕ) : SuN := ⟨V.h, V.nS, V.s, V.J, L⟩

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- **The end of the heap of the setup is a word.** -/
theorem ClPre.hS_lt (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    ((suVOf GB RB h mem).N P.L).hS < 2 ^ w := by
  have hW := hp.words hX
  have h1 := SuN.hS_le ((suVOf GB RB h mem).N P.L)
  have hnS : (RecL.read mem RB).nS ≤ G.m := by
    have e : (RecL.read mem RB).nS = R.S.length := hp.recAt.arcs.nS
    rw [e]; exact hp.ok.S_le
  have hs : (RecL.read mem RB).s ≤ T.N := by
    have e : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
    rw [e]; exact hp.ok.s_le
  have h2 : 1000 * ((GlobL.read mem GB).J + 1) *
      ((RecL.read mem RB).nS + (RecL.read mem RB).s + P.L + 10) ≤
      1000 * ((GlobL.read mem GB).J + 1) * (G.m + T.N + P.L + 10) :=
    Nat.mul_le_mul_left _ (by omega)
  have e : ((suVOf GB RB h mem).N P.L).h + 1000 * (((suVOf GB RB h mem).N P.L).J + 1) *
      (((suVOf GB RB h mem).N P.L).nS + ((suVOf GB RB h mem).N P.L).s +
        ((suVOf GB RB h mem).N P.L).L + 10) =
      h + 1000 * ((GlobL.read mem GB).J + 1) *
        ((RecL.read mem RB).nS + (RecL.read mem RB).s + P.L + 10) := rfl
  omega

/-- The end `Z` of `drawP` is the start `Z` of the layout. -/
theorem SuV.drawEnd_eq (V : SuV) (L : ℕ) : drawEnd V.dwE = (V.N L).Z := by
  simp only [drawEnd, DWE.Rr, DWE.Dq, DWE.Aq, SuV.dwE, SuV.N, SuN.Z, SuN.H]
  ring

/-- The arguments of the call of `treeP`. -/
def suTrArgs : List Expr :=
  [.reg 13, .reg 17, suH 16 3 4, .bin .add (.reg 13) (.const 1), suH 8 2 3, suH 12 2 3,
    suH 14 2 3, .reg 15, .reg 5, .reg 8, .reg 9, suZ 0 0 0 0, suZ 0 1 0 1, suZ 0 2 0 1,
    suZ 0 3 0 1, suZ 0 4 0 1, suZ 0 5 0 1, suZ 0 6 0 1, suZ 0 7 0 1]

theorem suTrArgs_size : argsSize suTrArgs ≤ 200 := by decide

theorem suZE_size : suZE.size ≤ 50 := by decide

/-- **The tree.** From registers that hold the loads and `L` and a memory `M` after the first
run, the assignment of `Z` and the call of `treeP` leave the tree arrays at `Z`. -/
theorem suTr_runs {p : Program} {ω : ℕ → Bool} {I : SuIdx}
    (hTr : MeetsContract w p I.tr (treePC w)) (hp : ClPre w A T G P c R GB RB h mem)
    (hX : 2 ≤ c.X.card) {M : ℕ → ℕ}
    (hF : Rec.First w T G c R (suVOf GB RB h mem).dwE mem M) {st : State}
    (hR : (suVOf GB RB h mem).Regs st) (h28 : st.regs 28 = P.L) (hm : st.mem = M)
    {s : Stmt} {Q : Outcome → State → Prop} {k K : ℕ}
    (hrest : ∀ v M2 pos, ((suVOf GB RB h mem).dwE.tf ((suVOf GB RB h mem).N P.L).Z).Done M M2
        (RecL.read mem RB).s →
      M2 (((suVOf GB RB h mem).N P.L).Z + (RecL.read mem RB).s) = (RecL.read mem RB).s →
      (∀ a, ¬ ((suVOf GB RB h mem).dwE.tf ((suVOf GB RB h mem).N P.L).Z).Out a → M2 a = M a) →
      ∃ o st' c', Runs w p ω s ⟨M2, Function.update (Function.update st.regs 24
          ((suVOf GB RB h mem).N P.L).Z) 25 v, pos⟩ o st' c' ∧
        Q o st' ∧ k + 300 * (RecL.read mem RB).s + 400 + c' ≤ K) :
    ∃ o st' c', Runs w p ω (.seq (.assign 24 suZE) (.seq (.call 25 I.tr suTrArgs) s)) st o st' c' ∧
      Q o st' ∧ k + c' ≤ K := by
  set V := suVOf GB RB h mem with hV
  set N := V.N P.L with hN
  have hS := hp.hS_lt hX
  rw [← hV, ← hN] at hS
  have h20 : 2 ^ 20 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    (lt_of_le_of_lt (Nat.le_add_left _ h) hp.room_h)
  have r : ∀ i < 23, st.regs i = V.vals.getD i 0 := hR
  have r13 : st.regs 13 = N.s := r 13 (by norm_num)
  have r14 : st.regs 14 = N.nS := r 14 (by norm_num)
  have r21 : st.regs 21 = N.h + 51 := r 21 (by norm_num)
  have r11 : st.regs 11 = N.J := r 11 (by norm_num)
  have eS : N.hS = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) + 23 * N.nS + 26 * N.s + 2 * N.L + 16 + 3 + 4 * (N.J + 5) +
      2 * (N.J + 5) * (2 * N.nS + 2 * N.s) + 6 * N.s + 16 := by
    simp only [SuN.hS, SuN.r, SuN.RR, SuN.D, SuN.z, SuN.Z, SuN.H, SuN.A2, SuN.Jq] <;> ring
  have eZ : N.Z = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) := rfl
  have eH : N.H = N.h + 51 := rfl
  have hZE : suZE.eval w st = some N.Z := by
    have e1 : (mulC 2 11).eval w st = some (2 * N.J) :=
      mulC_eval (a := 2) r11 (by omega) (by omega)
    refine Expr.eval_add (Expr.eval_add (suH_eval r21 r14 r13 h20 (by norm_num) (by norm_num)
      (by norm_num) rfl (by omega)) (mulC_eval (a := 4) r11 (by omega) (by omega)) (by omega))
      (Expr.eval_mul e1 (Expr.eval_add (Expr.eval_add (mulC_eval (a := 2) r14 (by omega) (by omega))
        (Expr.eval_reg_of_eq r13) (by omega)) (Expr.eval_const (by omega)) (by omega)) (by omega))
      (by omega)
  refine runs_seq_assign_le hZE ?_
  set st1 : State := { st with regs := Function.update st.regs 24 N.Z } with hst1
  have q : ∀ i < 23, st1.regs i = V.vals.getD i 0 := fun i hi => by
    rw [hst1]; dsimp only; rw [Function.update_of_ne (by omega)]; exact r i hi
  have q24 : st1.regs 24 = N.Z := by rw [hst1]; dsimp only; rw [Function.update_self]
  have q28 : st1.regs 28 = N.L := by
    rw [hst1]; dsimp only; rw [Function.update_of_ne (by omega)]; exact h28
  have q13 : st1.regs 13 = N.s := q 13 (by norm_num)
  have q14 : st1.regs 14 = N.nS := q 14 (by norm_num)
  have q21 : st1.regs 21 = N.h + 51 := q 21 (by norm_num)
  have g : ∀ i (hi : i < 23), (Expr.reg i).eval w st1 = some (V.vals.getD i 0) :=
    fun i hi => Expr.eval_reg_of_eq (q i hi)
  obtain ⟨E', hE', -, -, hAP, -, -, -, -, -, hx0s, -, -, -, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hx0s' : V.x0 < N.s := hx0s
  have hz : ∀ a b k, a < 2 ^ 20 → b < 2 ^ 20 → k < 2 ^ 20 → N.Z + a * N.nS + b * N.s + k < 2 ^ w →
      (suZ a b 0 k).eval w st1 = some (N.Z + a * N.nS + b * N.s + k) := fun a b k ha hb hk hlt =>
    suZ_eval q24 q14 q13 q28 h20 ha hb (by norm_num) hk (by ring) hlt
  have hH : ∀ a b k, a < 2 ^ 20 → b < 2 ^ 20 → k < 2 ^ 20 →
      N.h + 51 + a * N.nS + b * N.s + k < 2 ^ w →
      (suH a b k).eval w st1 = some (N.h + 51 + a * N.nS + b * N.s + k) :=
    fun a b k ha hb hk hlt => suH_eval q21 q14 q13 h20 ha hb hk rfl hlt
  have hargs : evalArgs w st1 suTrArgs = some (V.dwE.tf N.Z).args := by
    have d1 : V.dwE.s = N.s := rfl
    have d2 : V.dwE.nS = N.nS := rfl
    have d3 : V.dwE.H = N.h + 51 := rfl
    have d4 : V.dwE.J = N.J := rfl
    have d5 : N.s = V.s := rfl
    simp only [suTrArgs]
    refine evalArgs_cons (g 13 (by norm_num)) (evalArgs_cons (g 17 (by norm_num))
      (evalArgs_cons (hH 16 3 4 (by norm_num) (by norm_num) (by norm_num) (by omega))
      (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq q13) (Expr.eval_const (by omega))
        (by omega))
      (evalArgs_cons (hH 8 2 3 (by norm_num) (by norm_num) (by norm_num) (by omega))
      (evalArgs_cons (hH 12 2 3 (by norm_num) (by norm_num) (by norm_num) (by omega))
      (evalArgs_cons (hH 14 2 3 (by norm_num) (by norm_num) (by norm_num) (by omega))
      (evalArgs_cons (g 15 (by norm_num)) (evalArgs_cons (g 5 (by norm_num))
      (evalArgs_cons (g 8 (by norm_num)) (evalArgs_cons (g 9 (by norm_num))
      (evalArgs_cons (Expr.eval_eq_of_eq (hz 0 0 0 (by norm_num) (by norm_num) (by norm_num)
        (by omega)) (by simp only [DWE.tf, SuV.dwE] <;> omega))
      (evalArgs_cons (Expr.eval_eq_of_eq (hz 0 1 1 (by norm_num) (by norm_num) (by norm_num)
        (by omega)) (by simp only [DWE.tf, SuV.dwE] <;> omega))
      (evalArgs_cons (Expr.eval_eq_of_eq (hz 0 2 1 (by norm_num) (by norm_num) (by norm_num)
        (by omega)) (by simp only [DWE.tf, SuV.dwE] <;> omega))
      (evalArgs_cons (Expr.eval_eq_of_eq (hz 0 3 1 (by norm_num) (by norm_num) (by norm_num)
        (by omega)) (by simp only [DWE.tf, SuV.dwE] <;> omega))
      (evalArgs_cons (Expr.eval_eq_of_eq (hz 0 4 1 (by norm_num) (by norm_num) (by norm_num)
        (by omega)) (by simp only [DWE.tf, SuV.dwE] <;> omega))
      (evalArgs_cons (Expr.eval_eq_of_eq (hz 0 5 1 (by norm_num) (by norm_num) (by norm_num)
        (by omega)) (by simp only [DWE.tf, SuV.dwE] <;> omega))
      (evalArgs_cons (Expr.eval_eq_of_eq (hz 0 6 1 (by norm_num) (by norm_num) (by norm_num)
        (by omega)) (by simp only [DWE.tf, SuV.dwE] <;> omega))
      (evalArgs_cons (Expr.eval_eq_of_eq (hz 0 7 1 (by norm_num) (by norm_num) (by norm_num)
        (by omega)) (by simp only [DWE.tf, SuV.dwE] <;> omega))
      (evalArgs_nil _ _)))))))))))))))))))
  have hb : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h := hp.below
  have bSA := hb ((RecL.read mem RB).SA, 2 * (RecL.read mem RB).nS) (by simp [recRegs, RecL.regs])
  have bIN := hb ((GlobL.read mem GB).IN, 3 * (GlobL.read mem GB).m) (by simp [recRegs])
  dsimp only at bSA bIN
  have hm' : (GlobL.read mem GB).m = G.m := hp.glob.m
  have hlab : (GlobL.read mem GB).LAB + G.n ≤ h := hp.lab_below
  have hloc : (GlobL.read mem GB).LOC + T.N ≤ h := hp.loc_below
  have hZd : drawEnd V.dwE ≤ N.Z := (V.drawEnd_eq P.L).le
  have hpre : (V.dwE.tf N.Z).Pre M w :=
    hF.tfPre hAP
      (show V.dwE.SA + 2 * V.dwE.nS ≤ V.dwE.H from
        show (RecL.read mem RB).SA + 2 * (RecL.read mem RB).nS ≤ h + 51 by omega)
      (show V.dwE.IN + 3 * G.m ≤ V.dwE.H from
        show (GlobL.read mem GB).IN + 3 * G.m ≤ h + 51 by rw [← hm']; omega)
      (show V.dwE.LAB + G.n ≤ V.dwE.H from show (GlobL.read mem GB).LAB + G.n ≤ h + 51 by omega)
      (show V.dwE.LOC + T.N ≤ V.dwE.H from show (GlobL.read mem GB).LOC + T.N ≤ h + 51 by omega)
      hZd (by
        show N.Z + 8 * N.s + 8 < 2 ^ w
        omega)
  have hroom := hp.room_h
  have v2 : V.SA = (RecL.read mem RB).SA := rfl
  have v3 : V.IN = (GlobL.read mem GB).IN := rfl
  have v6 : V.LAB = (GlobL.read mem GB).LAB := rfl
  have v7 : V.LOC = (GlobL.read mem GB).LOC := rfl
  have v8 : N.nS = (RecL.read mem RB).nS := rfl
  have v9 : N.h = h := rfl
  have hwords : ∀ v ∈ (V.dwE.tf N.Z).args, v < 2 ^ w := by
    intro v hv
    simp only [TF.args, DWE.tf, SuV.dwE, DWE.TS, DWE.ap, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    have d5 : N.s = V.s := rfl
    have d6 : N.J = V.J := rfl
    have d7 : N.nS = V.nS := rfl
    have d8 : N.h = V.h := rfl
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hm1 : st1.mem = M := hm
  rw [← hm1] at hpre
  refine runs_seq_call_le hTr hargs hwords ⟨_, rfl, hpre⟩ (fun v mem' pos' hpost => ?_)
  obtain ⟨h1, h2, h3⟩ := hpost _ rfl
  rw [hm1] at h1 h3
  obtain ⟨o, st', c', a1, a2, a3⟩ := hrest v mem' pos' h1 h2 h3
  refine ⟨o, st', c', a1, a2, ?_⟩
  have := suTrArgs_size
  have := suZE_size
  have e : (treePC w).cost (V.dwE.tf N.Z).args st1.mem = 300 * N.s + 50 := rfl
  have e2 : N.s = (RecL.read mem RB).s := rfl
  omega

end MinCostFlow.LowStretch
