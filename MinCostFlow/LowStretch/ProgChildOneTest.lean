module

public import MinCostFlow.LowStretch.ProgChildOneRun
public import MinCostFlow.LowStretch.ProgChildOneDraw2
public import MinCostFlow.LowStretch.ProgChildStepRaw2

/-!
# One child: the size test, the radius and the reset test

After `oneMid_runs` the program tests `|X| < 2`. A child with fewer than two vertices is kept as
it is, and `oneP` returns `OUTK + 2`. Otherwise `drawP` finds the radius `Δ` of the raw child
(`CS.drawPre_mid` gives its precondition), and `oneP` compares `Δ` with `B |X| θ`. If `Δ` is not
smaller, the child is kept and `oneP` returns the end of the cells of `drawP`. In both cases
`CInv.step_raw` gives the invariant for `k + 1`. The reset branch is a hypothesis of
`CS.oneT_runs`; the run of `rsP` proves it.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- What child `k` leaves: it returns the new heap pointer `H'`, and the invariant holds for
`k + 1` with some record `R'` for child `k`. -/
def OneQ (w : ℕ) (S : CS) (M1 : ℕ → ℕ) (k : ℕ) (Rs : ℕ → Rec) (o : Outcome) (st : State) :
    Prop :=
  ∃ H' R', o = .returned H' ∧ CInv w S M1 (k + 1) H' (Function.update Rs k R') st.mem

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The threshold `B |X| θ` of the reset test is a word: `B n ≤ Mw` since the pairs are heavy,
and `θ ≤ Δ_c ≤ n Mw`, so the threshold is at most `n Mw²`, which `ChildPre.room` bounds. -/
theorem bxθ_lt (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) (k : ℕ) :
    S.P.B * (S.raw k).X.card * S.c.θ < 2 ^ w := by
  obtain ⟨Mw, hM, -, hroom⟩ := hpre.room
  set J := (GlobL.read S.mem S.GB).J
  have hm := m_pos hpre
  have hheavy : 8 * S.P.B * S.G.n ≤ S.G.pω 0 := hpre.glob.heavy 0 hm
  have hBn : S.P.B * S.G.n ≤ Mw := by
    have := hM 0 hm
    have e : 8 * S.P.B * S.G.n = 8 * (S.P.B * S.G.n) := by ring
    omega
  have hcard : S.c.X.card ≤ S.G.n := by
    have := Finset.card_le_card hpre.ok.inv.sub
    simpa using this
  have hrc : (S.raw k).X.card ≤ S.c.X.card :=
    Finset.card_le_card (fun v hv => Cl.raw_X_subset k hv)
  have hΔ : S.c.Δ S.G ≤ S.G.n * Mw :=
    (Cl.Δ_le_card_mul hpre.ok.inv.good.conn hM).trans (Nat.mul_le_mul_right _ hcard)
  have hθΔ : S.c.θ ≤ S.c.Δ S.G := by
    have hB : 1 ≤ S.P.B := hpre.ok.hB
    have two := hpre.two
    rcases hpre.ok.inv.big with h | h
    · omega
    · have : 1 * 1 * S.c.θ ≤ S.P.B * S.c.X.card * S.c.θ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hB (by omega))
      omega
  have h1 : S.P.B * (S.raw k).X.card * S.c.θ ≤ Mw * (S.G.n * Mw) :=
    Nat.mul_le_mul (le_trans (Nat.mul_le_mul_left _ (hrc.trans hcard)) hBn) (hθΔ.trans hΔ)
  have hN := hpre.ok.tree.n_lt
  have hZ : Mw * (S.G.n * Mw) ≤ (S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) ^ 2 := by
    have h2 : S.G.n * Mw ≤ (S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) := by
      have h3 : S.G.n ≤ (S.T.N + S.G.m + 2) ^ 2 :=
        le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
      exact Nat.mul_le_mul h3 (by omega)
    calc Mw * (S.G.n * Mw) ≤ (Mw + 2) * ((S.T.N + S.G.m + 2) ^ 2 * (Mw + 2)) :=
          Nat.mul_le_mul (by omega) h2
      _ = (S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) ^ 2 := by ring
  have hA : 1 ≤ 2 ^ (2 * J + 20) := Nat.one_le_two_pow
  have h4 : (S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) ^ 2 ≤
      2 ^ (2 * J + 20) * (S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) ^ 2 := by
    rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ hA
  omega

/-- The end of the cells of `drawP`, in the form in which `oneD` computes it. -/
theorem drawEnd_eq : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k +
    8 * S.sNK M1 k + (14 + 4 * S.E.J) + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1) := by
  simp only [drawEnd, DWE.Rr, DWE.Dq, DWE.Aq, dwE]
  ring

/-- The size test, `drawP` and the reset test of child `k`, from the state that `oneMid_runs`
gives. The reset branch is the hypothesis `hrs`: its state keeps the registers below `50`, holds
the radius in register `51` and the end of the cells of `drawP` in register `52`, and its memory
differs from `M6` only on the cells of `drawP`. -/
theorem oneT_runs {p : Program} {ω : ℕ → Bool} {I : CIdx} (fdr : MeetsContract w p I.dr (drawC w))
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hroom : H + S.spaceK M1 k + 2 < 2 ^ w) (hmid : MidOk S M1 k H M M6)
    {st : State} (hm : st.mem = M6) (hR : (S.oneV M1 k H).Regs st)
    (h40 : st.regs 40 = S.SAK H k) (h47 : st.regs 47 = (S.raw k).X.card)
    (h49 : st.regs 49 = S.OUTK M1 H k + 2) {A T : ℕ}
    (hcost : A + 300 + drawCost (S.dwE M1 k H).args M6 ≤ T)
    (hrs : S.resetQ k → ∀ (st' : State),
      (∀ a, (a < S.OUTK M1 H k + 2 ∨ drawEnd (S.dwE M1 k H) ≤ a) → st'.mem a = M6 a) →
      (∀ r < 50, st'.regs r = st.regs r) → st'.regs 51 = (S.raw k).Δ S.G →
      st'.regs 52 = drawEnd (S.dwE M1 k H) →
      ∃ o st'' c, Runs w p ω (.seq (.call 54 I.rs (rgs [0, 3, 52, 51, 47, 48, 35, 36, 45, 38, 31,
        10, 2, 44])) (.ret (.reg 54))) st' o st'' c ∧ OneQ w S M1 k Rs o st'' ∧
        A + 300 + drawCost (S.dwE M1 k H).args M6 + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond (.bin .lt (.reg 47) (.const 2)) (.ret (.reg 49)) (oneD I))
      st o st' c ∧ OneQ w S M1 k Rs o st' ∧ A + c ≤ T := by
  have hend := drawEnd_le (H := H) hpre hT hk
  have hend' := drawEnd_eq (S := S) (M1 := M1) (k := k) (H := H)
  have hO : S.OUTK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k + S.sNK M1 k := rfl
  have hSA : S.SAK H k = H + 4 * S.ℓK k := rfl
  have hNw : S.T.N < 2 ^ w := by
    have := big_words hpre
    have : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
    omega
  have w2 : 2 < 2 ^ w := by omega
  have W := (callsOk hpre hT hI hk hroom).words
  refine runs_cond_le (v := if (S.raw k).X.card < 2 then 1 else 0)
    (Expr.eval_lt_op (Expr.eval_reg_of_eq h47) (Expr.eval_const w2) (by omega)) ?_ ?_
  · -- fewer than two vertices: the raw child is kept
    intro hv
    have hc : (S.raw k).X.card < 2 := by by_contra h; exact hv (if_neg h)
    refine runs_ret_le (Expr.eval_reg_of_eq h49) ⟨_, S.rawRec M1 k, rfl, ?_⟩ ?_
    · rw [hm]
      exact CInv.step_raw hpre hT hI hk hmid (fun h => by have := h.1; omega) le_rfl
        (by omega) (fun _ _ => rfl) hNw
    · simp only [Expr.size]; omega
  intro hv
  have hc : 2 ≤ (S.raw k).X.card := by
    by_contra h; rw [if_pos (by omega)] at hv; exact absurd hv (by norm_num)
  unfold oneD
  -- the local index of the center
  have hx0 : S.mem (S.X.CC + k) = (S.raw k).x0 := hpre.pet.cc k hk
  have hx0X : (S.raw k).x0 ∈ (S.raw k).X := (raw_good' hpre hk).conn.1
  have hx0n : (S.raw k).x0 < S.G.n := hpre.ok.n_of_mem (Cl.raw_X_subset k hx0X)
  have hA := (rawRecAt hpre hT hI hk hmid).arcs
  have hloc : M6 (S.E.LOC + M6 (S.E.LAB + (S.raw k).x0)) =
      (S.rawRec M1 k).sv S.T (S.raw k) (S.raw k).x0 := hA.loc _ hx0X
  have hlab : M6 (S.E.LAB + (S.raw k).x0) < S.T.N := by
    rw [lab6 hpre hT hI hk hmid hx0n]; exact hI.lab _ hx0n
  have bw := big_words hpre
  have hlb : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hlc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hOK := (pre_of hpre).rawRec_okW hT hk
  have hsv := hOK.sv_lt hx0X
  have hn : (S.rawRec M1 k).nodes.length = S.sNK M1 k := length_nodesK k
  refine runs_seq_assign_le (v := (S.rawRec M1 k).sv S.T (S.raw k) (S.raw k).x0)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (hR.1 15 (by norm_num)))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (hR.1 14 (by norm_num)))
        (Expr.eval_reg_of_eq ((hR.1 31 (by norm_num)).trans hx0)) (by
          show S.E.LAB + (S.raw k).x0 < 2 ^ w; omega)) (by rw [hm]))
      (by show S.E.LOC + M6 (S.E.LAB + (S.raw k).x0) < 2 ^ w; omega)) (by rw [hm]; exact hloc)) ?_
  -- the radius
  have hdp := drawPre_mid hpre hT hI hk hmid hroom
  rw [← hm] at hdp
  have R1 : ∀ r < 39, (Function.update st.regs 50
      ((S.rawRec M1 k).sv S.T (S.raw k) (S.raw k).x0)) r = (S.oneV M1 k H).vals.getD r 0 :=
    fun r hr => by rw [Function.update_of_ne (by omega)]; exact hR.1 r hr
  refine runs_seq_callR_le (vs := (S.dwE M1 k H).args) fdr ?_ ?_ ⟨S.dwG M1 k, hdp⟩ ?_
  · simp only [List.map_cons, List.map_nil, DWE.args, dwE, List.cons.injEq, and_true]
    refine ⟨R1 38 (by norm_num), R1 36 (by norm_num), ?_, R1 11 (by norm_num),
      R1 12 (by norm_num), R1 13 (by norm_num), R1 14 (by norm_num), R1 15 (by norm_num),
      R1 27 (by norm_num), R1 28 (by norm_num), by simp, R1 19 (by norm_num),
      R1 20 (by norm_num), ?_⟩
    · rw [Function.update_of_ne (by norm_num)]; exact h40
    · rw [Function.update_of_ne (by norm_num)]; exact h49
  · simp only [DWE.args, dwE, List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [W 38 (by norm_num), W 36 (by norm_num), by omega, W 11 (by norm_num),
      W 12 (by norm_num), W 13 (by norm_num), W 14 (by norm_num), W 15 (by norm_num),
      W 27 (by norm_num), W 28 (by norm_num), by omega, W 19 (by norm_num), W 20 (by norm_num),
      by omega]
  intro v M7 q hpost
  obtain ⟨hv1, hfr⟩ := hpost (S.dwG M1 k) hdp
  have hv1' : v = (S.raw k).Δ S.G := hv1
  have hM7 : ∀ a, (a < S.OUTK M1 H k + 2 ∨ drawEnd (S.dwE M1 k H) ≤ a) → M7 a = M6 a :=
    fun a ha => by rw [hfr (S.dwE M1 k H) rfl a ha, hm]
  have hcd : (drawC w).cost (S.dwE M1 k H).args st.mem = drawCost (S.dwE M1 k H).args M6 := rfl
  rw [hcd]
  have h36 : st.regs 36 = S.cntK M1 k := hR.1 36 (by norm_num)
  have h38 : st.regs 38 = S.sNK M1 k := hR.1 38 (by norm_num)
  have h19 : st.regs 19 = S.E.J := hR.1 19 (by norm_num)
  have h28 : st.regs 28 = S.L.lθ := hR.1 28 (by norm_num)
  have h44 : st.regs 44 = S.E.B := hR.2.2.2
  -- the end of the cells of `drawP`
  refine runs_seq_assign_le (v := drawEnd (S.dwE M1 k H)) (by rw [hend']; simp only [mulC]; eval_expr) ?_
  -- the threshold `B |X| θ`
  have hB : S.E.B = S.P.B := hpre.glob.B
  have hθ : S.c.θ = 2 ^ S.L.lθ := hpre.recAt.arcs.th
  have hbx := bxθ_lt hpre k
  have hsh : (S.E.B * (S.raw k).X.card) <<< S.L.lθ = S.P.B * (S.raw k).X.card * S.c.θ := by
    rw [Nat.shiftLeft_eq, hB, hθ]
  have hθ1 : 1 ≤ S.c.θ := hpre.ok.inv.one_le
  have hbx1 : S.E.B * (S.raw k).X.card < 2 ^ w := by
    rw [hB]
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hbx
  have hbx2 : (S.E.B * (S.raw k).X.card) <<< S.L.lθ < 2 ^ w := by rw [hsh]; exact hbx
  refine runs_seq_assign_le (v := S.P.B * (S.raw k).X.card * S.c.θ) (by
    rw [← hsh]; eval_expr) ?_
  have hθr : (S.raw k).θ = S.c.θ := Cl.raw_θ k
  refine runs_cond_le (v := if (S.raw k).Δ S.G < S.P.B * (S.raw k).X.card * S.c.θ then 1 else 0)
    (by eval_expr) ?_ ?_
  · -- the reset
    intro hv2
    have hlt : (S.raw k).Δ S.G < S.P.B * (S.raw k).X.card * S.c.θ := by
      by_contra h; exact hv2 (if_neg h)
    refine runs_exists_mono (hrs ⟨hc, by rw [hθr]; exact hlt⟩ _ hM7 (fun r hr => by
      simp only [Function.update_apply]; split_ifs <;> first | omega | rfl)
      (by simp [hv1']) (by simp)) ?_
    simp only [Expr.size, mulC, addR, rgs, List.length_cons, List.length_nil, List.map_cons,
      List.map_nil, locOf]
    omega
  · -- no reset: the raw child is kept
    intro hv2
    have hge : ¬ (S.raw k).Δ S.G < S.P.B * (S.raw k).X.card * S.c.θ := by
      intro h; rw [if_pos h] at hv2; exact absurd hv2 (by norm_num)
    refine runs_ret_le (v := drawEnd (S.dwE M1 k H)) (Expr.eval_reg_of_eq (by simp))
      ⟨_, S.rawRec M1 k, rfl, ?_⟩ ?_
    · exact CInv.step_raw hpre hT hI hk hmid (fun h => hge (hθr ▸ h.2)) (by omega) hend hM7 hNw
    · simp only [Expr.size, mulC, addR, rgs, List.length_cons, List.length_nil, List.map_cons,
        List.map_nil, locOf]
      omega

end CS

end MinCostFlow.LowStretch
