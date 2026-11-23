module

public import MinCostFlow.LowStretch.ProgClusterSetupTr2

/-!
# The setup of a cluster: the call of `hwFix`

After `treeP`, the setup calls `hwFix` on the tree arrays at `Z`, with the stored highway of the
record. Its precondition comes from `HF.V.pre`: the record block gives the stored highway
(`RecAt.hwSt`), the labels, local indices, weights and exponents, and the memory below
`H = h + 51` is still the memory at the start of the setup, since `drawP` and `treeP` write only
from `H` on (`ClPre.hfV`). `suHf_runs` is the run of the call.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- The weights are words, and so are the exponents plus two. -/
theorem ClPre.pw_words (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    ∀ p < G.m, G.pω p < 2 ^ w ∧ mem ((GlobL.read mem GB).EXP + p) + 2 < 2 ^ w := by
  intro p hp'
  have hW := hp.words hX
  have hG := hp.glob
  have h1 := hG.hINF p hp'
  have hn : 1 ≤ G.n := by have := (hG.hG p hp').1; omega
  have h6 : 2 * 1 * G.pω p ≤ 2 * G.n * G.pω p := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
  have e := hp.recAt.arcs.ex p hp'
  have e' : G.pω p = 2 ^ mem ((GlobL.read mem GB).EXP + p) := e
  have h3 : mem ((GlobL.read mem GB).EXP + p) < 2 ^ mem ((GlobL.read mem GB).EXP + p) :=
    Nat.lt_two_pow_self
  have h7 : 1 ≤ 2 ^ mem ((GlobL.read mem GB).EXP + p) := Nat.one_le_two_pow
  omega

/-- **The setting of `hwFix`** after `treeP`, at the tree arrays at `Z`. -/
theorem ClPre.hfV (hp : ClPre w A T G P c R GB RB h mem) {M M2 : ℕ → ℕ} {Z : ℕ}
    (hF : Rec.First w T G c R (suVOf GB RB h mem).dwE mem M)
    (hH : h + 51 ≤ Z)
    (hfr : ∀ a, ¬ ((suVOf GB RB h mem).dwE.tf Z).Out a → M2 a = M a) :
    ((suVOf GB RB h mem).dwE.hfx Z (RecL.read mem RB).nH (RecL.read mem RB).HW).V T G P c R mem
      M2 (h + 51) T.N := by
  have hb : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h := hp.below
  have bHW := hb ((RecL.read mem RB).HW, 4 * (RecL.read mem RB).nH) (by simp [recRegs, RecL.regs])
  have bPW := hb ((GlobL.read mem GB).PW, (GlobL.read mem GB).m) (by simp [recRegs])
  have bEX := hb ((GlobL.read mem GB).EXP, (GlobL.read mem GB).m) (by simp [recRegs])
  dsimp only at bHW bPW bEX
  have hm' : (GlobL.read mem GB).m = G.m := hp.glob.m
  have hlab : (GlobL.read mem GB).LAB + G.n ≤ h := hp.lab_below
  have hloc : (GlobL.read mem GB).LOC + T.N ≤ h := hp.loc_below
  obtain ⟨hn, hw⟩ := hp.recAt.hwSt
  refine ⟨hp.ok, hn, hw, hp.recAt.arcs.loc, fun v hv => hp.lab_lt v (hp.ok.n_of_mem hv),
    hp.recAt.arcs.pw, hp.recAt.arcs.ex, hp.recAt.arcs.th, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_,
    hp.recAt.arcs.s⟩
  · rw [hfr a (fun ho => by
      have : ((suVOf GB RB h mem).dwE.tf Z).PAR = Z := rfl
      have := ho.1
      omega)]
    exact hF.low ha
  · show (RecL.read mem RB).HW + 4 * (RecL.read mem RB).nH ≤ h + 51; omega
  · show (GlobL.read mem GB).LAB + G.n ≤ h + 51; omega
  · show (GlobL.read mem GB).LOC + T.N ≤ h + 51; omega
  · show (GlobL.read mem GB).PW + G.m ≤ h + 51; omega
  · show (GlobL.read mem GB).EXP + G.m ≤ h + 51; omega

/-- The arguments of the call of `hwFix`. -/
def suHfArgs : List Expr :=
  [.reg 19, .reg 20, .reg 8, .reg 9, .reg 6, .reg 7, .reg 16, suZ 0 0 0 0, suZ 0 1 0 1,
    suZ 0 2 0 1, suZ 0 3 0 1, suZ 0 4 0 1, suZ 0 5 0 1, suZ 0 6 0 1, .reg 13]

theorem suHfArgs_size : argsSize suHfArgs ≤ 150 := by decide

/-- **The fix of the highway.** From registers that hold the loads, `Z` and `L`, and the memory
`M2` after `treeP`, the call of `hwFix` writes the parent arcs of the split highway. -/
theorem suHf_runs {p : Program} {ω : ℕ → Bool} {I : SuIdx}
    (hHf : MeetsContract w p I.hf (hwFixC w)) (hp : ClPre w A T G P c R GB RB h mem)
    (hX : 2 ≤ c.X.card) {M M2 : ℕ → ℕ}
    (hF : Rec.First w T G c R (suVOf GB RB h mem).dwE mem M)
    (hfr : ∀ a, ¬ ((suVOf GB RB h mem).dwE.tf ((suVOf GB RB h mem).N P.L).Z).Out a → M2 a = M a)
    {st : State} (hR : (suVOf GB RB h mem).Regs st)
    (h24 : st.regs 24 = ((suVOf GB RB h mem).N P.L).Z) (h28 : st.regs 28 = P.L)
    (hm : st.mem = M2) {s : Stmt} {Q : Outcome → State → Prop} {k K : ℕ}
    (hrest : ∀ v M3 pos,
      ((suVOf GB RB h mem).dwE.hfx ((suVOf GB RB h mem).N P.L).Z (RecL.read mem RB).nH
        (RecL.read mem RB).HW).Done M2 M3 (RecL.read mem RB).nH →
      (∀ a, ((suVOf GB RB h mem).dwE.hfx ((suVOf GB RB h mem).N P.L).Z (RecL.read mem RB).nH
        (RecL.read mem RB).HW).Free M2 (RecL.read mem RB).nH a → M3 a = M2 a) →
      ∃ o st' c', Runs w p ω s ⟨M3, Function.update st.regs 25 v, pos⟩ o st' c' ∧
        Q o st' ∧ k + 250 * (RecL.read mem RB).nH + 300 + c' ≤ K) :
    ∃ o st' c', Runs w p ω (.seq (.call 25 I.hf suHfArgs) s) st o st' c' ∧ Q o st' ∧
      k + c' ≤ K := by
  set V := suVOf GB RB h mem with hV
  set N := V.N P.L with hN
  have hS := hp.hS_lt hX
  rw [← hV, ← hN] at hS
  have hW := hp.words hX
  have h20 : 2 ^ 20 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    (lt_of_le_of_lt (Nat.le_add_left _ h) hp.room_h)
  have r : ∀ i < 23, st.regs i = V.vals.getD i 0 := hR
  have q13 : st.regs 13 = N.s := r 13 (by norm_num)
  have q14 : st.regs 14 = N.nS := r 14 (by norm_num)
  have eS : N.hS = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) + 23 * N.nS + 26 * N.s + 2 * N.L + 16 + 3 + 4 * (N.J + 5) +
      2 * (N.J + 5) * (2 * N.nS + 2 * N.s) + 6 * N.s + 16 := by
    simp only [SuN.hS, SuN.r, SuN.RR, SuN.D, SuN.z, SuN.Z, SuN.H, SuN.A2, SuN.Jq] <;> ring
  have eZ : N.Z = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) := rfl
  have g : ∀ i (hi : i < 23), (Expr.reg i).eval w st = some (V.vals.getD i 0) :=
    fun i hi => Expr.eval_reg_of_eq (r i hi)
  have hz : ∀ b, b < 2 ^ 20 → N.Z + b * N.s + 1 < 2 ^ w →
      (suZ 0 b 0 1).eval w st = some (N.Z + b * N.s + 1) := fun b hb hlt =>
    suZ_eval h24 q14 q13 h28 h20 (by norm_num) hb (by norm_num) (by norm_num) (by ring) hlt
  have d5 : N.s = V.s := rfl
  set F := V.dwE.hfx N.Z (RecL.read mem RB).nH (RecL.read mem RB).HW with hFd
  have hargs : evalArgs w st suHfArgs = some F.args := by
    have ee : ∀ b x, x = N.Z + b * N.s + 1 → (suZ 0 b 0 1).eval w st = some (N.Z + b * N.s + 1) →
        (suZ 0 b 0 1).eval w st = some x := fun b x hx h1 => hx ▸ h1
    simp only [suHfArgs]
    refine evalArgs_cons (g 19 (by norm_num)) (evalArgs_cons (g 20 (by norm_num))
      (evalArgs_cons (g 8 (by norm_num)) (evalArgs_cons (g 9 (by norm_num))
      (evalArgs_cons (g 6 (by norm_num)) (evalArgs_cons (g 7 (by norm_num))
      (evalArgs_cons (g 16 (by norm_num))
      (evalArgs_cons (Expr.eval_eq_of_eq (suZ_eval h24 q14 q13 h28 h20 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) rfl (by omega))
        (by simp only [hFd, DWE.hfx] <;> ring))
      (evalArgs_cons (ee 1 _ (by simp only [hFd, DWE.hfx, SuV.dwE]; omega)
        (hz 1 (by norm_num) (by omega)))
      (evalArgs_cons (ee 2 _ (by simp only [hFd, DWE.hfx, SuV.dwE]; omega)
        (hz 2 (by norm_num) (by omega)))
      (evalArgs_cons (ee 3 _ (by simp only [hFd, DWE.hfx, SuV.dwE]; omega)
        (hz 3 (by norm_num) (by omega)))
      (evalArgs_cons (ee 4 _ (by simp only [hFd, DWE.hfx, SuV.dwE]; omega)
        (hz 4 (by norm_num) (by omega)))
      (evalArgs_cons (ee 5 _ (by simp only [hFd, DWE.hfx, SuV.dwE]; omega)
        (hz 5 (by norm_num) (by omega)))
      (evalArgs_cons (ee 6 _ (by simp only [hFd, DWE.hfx, SuV.dwE]; omega)
        (hz 6 (by norm_num) (by omega)))
      (evalArgs_cons (g 13 (by norm_num)) (evalArgs_nil _ _)))))))))))))))
  have hb : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h := hp.below
  have bHW := hb ((RecL.read mem RB).HW, 4 * (RecL.read mem RB).nH) (by simp [recRegs, RecL.regs])
  have bPW := hb ((GlobL.read mem GB).PW, (GlobL.read mem GB).m) (by simp [recRegs])
  have bEX := hb ((GlobL.read mem GB).EXP, (GlobL.read mem GB).m) (by simp [recRegs])
  dsimp only at bHW bPW bEX
  have hlab : (GlobL.read mem GB).LAB + G.n ≤ h := hp.lab_below
  have hloc : (GlobL.read mem GB).LOC + T.N ≤ h := hp.loc_below
  have hroom := hp.room_h
  have hθ : c.θ = 2 ^ (RecL.read mem RB).lθ := hp.recAt.arcs.th
  have hlθ : (RecL.read mem RB).lθ < c.θ := by rw [hθ]; exact Nat.lt_two_pow_self
  have hθJ : c.θ ≤ 2 ^ (GlobL.read mem GB).J * c.θ :=
    Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  have v9 : N.h = h := rfl
  have w1 : V.nH = (RecL.read mem RB).nH := rfl
  have w2 : V.HW = (RecL.read mem RB).HW := rfl
  have w3 : V.LAB = (GlobL.read mem GB).LAB := rfl
  have w4 : V.LOC = (GlobL.read mem GB).LOC := rfl
  have w5 : V.PW = (GlobL.read mem GB).PW := rfl
  have w6 : V.EXP = (GlobL.read mem GB).EXP := rfl
  have w7 : V.lθ = (RecL.read mem RB).lθ := rfl
  have w8 : V.s = (RecL.read mem RB).s := rfl
  have hm' : (GlobL.read mem GB).m = G.m := hp.glob.m
  have v10 : N.s = (RecL.read mem RB).s := rfl
  have w9 : (suVOf GB RB h mem).s = N.s := rfl
  have hHV := hp.hfV hF (Z := N.Z) (by omega) hfr
  have hpre : F.Pre M2 w := by
    refine hHV.pre (by simp only [DWE.hfx]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega)
      (fun p hp' => hp.pw_words hX p hp')
    all_goals (simp only [DWE.hfx, SuV.dwE]; omega)
  have hwords : ∀ v ∈ F.args, v < 2 ^ w := by
    intro v hv
    simp only [hFd, HF.args, DWE.hfx, SuV.dwE, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals omega
  rw [← hm] at hpre
  refine runs_seq_call_le hHf hargs hwords ⟨_, rfl, hpre⟩ (fun v mem' pos' hpost => ?_)
  obtain ⟨h1, h2⟩ := hpost _ rfl
  rw [hm] at h1 h2
  obtain ⟨o, st', c', a1, a2, a3⟩ := hrest v mem' pos' h1 h2
  refine ⟨o, st', c', a1, a2, ?_⟩
  have := suHfArgs_size
  have e : (hwFixC w).cost F.args st.mem = 250 * (RecL.read mem RB).nH + 20 := rfl
  omega

/-- **The memory below `H = h + 51` is unchanged** by `drawP`, `treeP` and `hwFix`. -/
theorem ClPre.low3 {M M2 M3 : ℕ → ℕ} {Z nH HW : ℕ}
    (hF : Rec.First w T G c R (suVOf GB RB h mem).dwE mem M) (hH : h + 51 ≤ Z)
    (hfr : ∀ a, ¬ ((suVOf GB RB h mem).dwE.tf Z).Out a → M2 a = M a)
    (hfr3 : ∀ a, ((suVOf GB RB h mem).dwE.hfx Z nH HW).Free M2 nH a → M3 a = M2 a) :
    ∀ a < h + 51, M3 a = mem a := by
  intro a ha
  have e1 : ((suVOf GB RB h mem).dwE.tf Z).PAR = Z := rfl
  have e2 : ((suVOf GB RB h mem).dwE.hfx Z nH HW).PAR = Z := rfl
  have e3 : ((suVOf GB RB h mem).dwE.hfx Z nH HW).PP = Z + (suVOf GB RB h mem).s + 1 := rfl
  have e4 : ((suVOf GB RB h mem).dwE.hfx Z nH HW).PF = Z + 2 * (suVOf GB RB h mem).s + 1 := rfl
  have e5 : ((suVOf GB RB h mem).dwE.hfx Z nH HW).PA = Z + 3 * (suVOf GB RB h mem).s + 1 := rfl
  have e6 : ((suVOf GB RB h mem).dwE.hfx Z nH HW).PB = Z + 4 * (suVOf GB RB h mem).s + 1 := rfl
  have e7 : ((suVOf GB RB h mem).dwE.hfx Z nH HW).SCc = Z + 5 * (suVOf GB RB h mem).s + 1 := rfl
  have e8 : ((suVOf GB RB h mem).dwE.hfx Z nH HW).SCk = Z + 6 * (suVOf GB RB h mem).s + 1 := rfl
  rw [hfr3 a (fun j _ => by
      rw [e2, e3, e4, e5, e6, e7, e8]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega),
    hfr a (fun ho => by have := ho.1; omega)]
  exact hF.low ha

/-- **The quadratic word bounds of the setup**: the bound `Q Δ θ = 512 B n² Δ θ` of the active
pairs and the squares of the weights are words. They use the factor `(Mw + 2)²` of
`ClPre.room`. -/
theorem ClPre.words2 (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    h + 512 * P.B * G.n ^ 2 * c.Δ G * c.θ < 2 ^ w ∧ ∀ p < G.m, G.pω p * G.pω p < 2 ^ w := by
  obtain ⟨Mw, hM, -, hroom⟩ := hp.room_sq
  set J := (GlobL.read mem GB).J
  have hcard : c.X.card ≤ G.n := by
    have := Finset.card_le_card hp.ok.inv.sub
    simpa using this
  have hΔ : c.Δ G ≤ G.n * Mw :=
    (Cl.Δ_le_card_mul hp.ok.inv.good.conn hM).trans (Nat.mul_le_mul_right _ hcard)
  have hθΔ : c.θ ≤ c.Δ G := by
    have hB : 1 ≤ P.B := hp.ok.hB
    rcases hp.ok.inv.big with h | h
    · omega
    · have : 1 * 1 * c.θ ≤ P.B * c.X.card * c.θ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hB (by omega))
      omega
  have hN := hp.ok.tree.n_lt
  set X0 := T.N + G.m + 2
  set Y0 := Mw + 2
  have hnM : G.n * Mw ≤ X0 * Y0 := Nat.mul_le_mul (by omega) (by omega)
  have hJ : 128 * P.B * G.n ^ 2 < 2 ^ J := hp.glob.hJ
  have hK : 2 ^ (2 * J + 20) * X0 ^ 2 * Y0 ^ 2 =
      2 ^ 20 * (2 ^ J * 2 ^ J) * ((X0 * Y0) * (X0 * Y0)) := by
    rw [show 2 * J + 20 = 20 + (J + J) by omega, pow_add, pow_add]; ring
  have hE : 1 ≤ 2 ^ J := Nat.one_le_two_pow
  have hZZ : c.Δ G * c.θ ≤ (X0 * Y0) * (X0 * Y0) := Nat.mul_le_mul (by omega) (by omega)
  have h1 : 512 * P.B * G.n ^ 2 * c.Δ G * c.θ ≤ (4 * 2 ^ J) * ((X0 * Y0) * (X0 * Y0)) := by
    have e : 512 * P.B * G.n ^ 2 * c.Δ G * c.θ = (512 * P.B * G.n ^ 2) * (c.Δ G * c.θ) := by ring
    have e2 : 512 * P.B * G.n ^ 2 = 4 * (128 * P.B * G.n ^ 2) := by ring
    rw [e]; exact Nat.mul_le_mul (by omega) hZZ
  have h2 : (4 * 2 ^ J) * ((X0 * Y0) * (X0 * Y0)) ≤
      2 ^ 20 * (2 ^ J * 2 ^ J) * ((X0 * Y0) * (X0 * Y0)) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have h0 := Nat.zero_le ((J + 2) * recCost w A T G P c R)
  refine ⟨by omega, fun p hp' => ?_⟩
  have h3 : G.pω p * G.pω p ≤ (X0 * Y0) * (X0 * Y0) := by
    have := hM p hp'
    have hY : G.pω p ≤ X0 * Y0 := le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
    exact Nat.mul_le_mul hY hY
  have h4 : (X0 * Y0) * (X0 * Y0) ≤ 2 ^ 20 * (2 ^ J * 2 ^ J) * ((X0 * Y0) * (X0 * Y0)) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  omega

end MinCostFlow.LowStretch
