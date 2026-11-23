module

public import MinCostFlow.LowStretch.ProgChildOneRun

/-!
# One child: the numbers that the radius search needs

Before `drawP` runs on raw child `k`, its precondition asks for some facts on numbers: there is a
pair (`CS.m_pos`), the radius of the parent is below `INF` and bounds the radius of the child
(`CS.Δc_lt_INF`, `CS.raw_Δ_le`), the classes fit below `J` (`CS.four_Δ_lt`, `CS.J_pos`), the
products of `drawP` are words (`CS.inf_words`), and the memory after the record is zero from the
end of the arrays of the child on (`CS.zero_mid`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The cluster has two vertices, so its radius is at least `2`. -/
theorem two_le_Δ (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    2 ≤ S.c.Δ S.G := by
  have hB : 1 ≤ S.P.B := hpre.ok.hB
  have two := hpre.two
  have hθ := hpre.ok.inv.one_le
  rcases hpre.ok.inv.big with h | h
  · omega
  · have : 1 * 2 * 1 ≤ S.P.B * S.c.X.card * S.c.θ :=
      Nat.mul_le_mul (Nat.mul_le_mul hB two) hθ
    omega

/-- **There is a pair**: with no pair the radius would be `0` (`Cl.Δ_le_card_mul`). -/
theorem m_pos (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    0 < S.G.m := by
  rcases Nat.eq_zero_or_pos S.G.m with h | h
  · have hM : ∀ p < S.G.m, S.G.pω p ≤ 0 := fun p hp => absurd hp (by omega)
    have := Cl.Δ_le_card_mul hpre.ok.inv.good.conn hM
    have := two_le_Δ hpre
    simp at *
    omega
  · exact h

theorem Δc_lt_INF (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.c.Δ S.G < S.E.INF :=
  Cl.Δ_lt_INF hpre.ok.inv.good.conn hpre.ok.inv.sub (m_pos hpre) hpre.glob.hINF

/-- The radius of a raw child is at most the radius of the parent (`Cl.raw_Δ`). -/
theorem raw_Δ_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) : (S.raw k).Δ S.G ≤ S.c.Δ S.G := by
  have := Cl.raw_Δ hpre.ok.inv.good hpre.dec hpre.ok.hGo (k := k) hk
  unfold raw
  omega

/-- **The classes fit below `J`**: `4 Δ ≤ 128 B n² θ < 2 ^ J · 2 ^ lθ` (`Inv.small`, `GlobL.Ok.hJ`). -/
theorem four_Δ_lt (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    4 * S.c.Δ S.G < 2 ^ (S.E.J + S.L.lθ) := by
  have hs := hpre.ok.inv.small
  have hJ : 128 * S.P.B * S.G.n ^ 2 < 2 ^ S.E.J := hpre.glob.hJ
  have hθ : S.c.θ = 2 ^ S.L.lθ := hpre.recAt.arcs.th
  have h1 := hpre.ok.inv.one_le
  have h2 : 128 * S.P.B * S.G.n ^ 2 * S.c.θ < 2 ^ S.E.J * S.c.θ :=
    Nat.mul_lt_mul_of_pos_right hJ (by omega)
  rw [pow_add, ← hθ]
  have e : 4 * (32 * S.P.B * S.G.n ^ 2 * S.c.θ) = 128 * S.P.B * S.G.n ^ 2 * S.c.θ := by ring
  omega

theorem J_pos (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    1 ≤ S.E.J := by
  have hJ : 128 * S.P.B * S.G.n ^ 2 < 2 ^ S.E.J := hpre.glob.hJ
  have hB : 1 ≤ S.P.B := hpre.ok.hB
  have hn : 1 ≤ S.G.n := by
    have := Finset.card_le_card hpre.ok.inv.sub
    have := hpre.two
    simp at *
    omega
  rcases Nat.eq_zero_or_pos S.E.J with h | h
  · rw [h] at hJ
    have : 1 * 1 ≤ S.P.B * S.G.n ^ 2 := Nat.mul_le_mul hB (Nat.one_le_pow _ _ (by omega))
    simp at hJ
    omega
  · exact h

/-- **The products of `drawP` are words**, by `ChildPre.room`. -/
theorem inf_words (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.E.INF * S.E.J + S.E.J + S.E.INF + S.c.Δ S.G + S.h < 2 ^ w := by
  obtain ⟨Mw, hM, hINF, hroom⟩ := hpre.room
  have hJ' : S.E.J = (GlobL.read S.mem S.GB).J := rfl
  have hI' : S.E.INF = (GlobL.read S.mem S.GB).INF := rfl
  rw [hJ', hI']
  set J := (GlobL.read S.mem S.GB).J
  set INF := (GlobL.read S.mem S.GB).INF
  have hcard : S.c.X.card ≤ S.G.n := by
    have := Finset.card_le_card hpre.ok.inv.sub
    simpa using this
  have hΔ : S.c.Δ S.G ≤ S.G.n * Mw :=
    (Cl.Δ_le_card_mul hpre.ok.inv.good.conn hM).trans (Nat.mul_le_mul_right _ hcard)
  have hN := hpre.ok.tree.n_lt
  set X := S.G.n * Mw with hX
  set A := 2 ^ (2 * J + 20) with hA
  have hAJ : 2 ^ 20 * (J + 1) ≤ A := by
    have h1 : J + 1 ≤ 2 ^ (2 * J) :=
      le_trans Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    have e : A = 2 ^ 20 * 2 ^ (2 * J) := by rw [hA, ← pow_add]; ring_nf
    rw [e]
    exact Nat.mul_le_mul_left _ h1
  have hZ : X + 4 ≤ (S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) ^ 2 := by
    have h1 : S.G.n + 2 ≤ (S.T.N + S.G.m + 2) ^ 2 :=
      le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have h2 : Mw + 2 ≤ (Mw + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    calc X + 4 ≤ (S.G.n + 2) * (Mw + 2) := by rw [hX]; nlinarith
      _ ≤ _ := Nat.mul_le_mul h1 h2
  have h3 : A * (X + 4) ≤ A * ((S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) ^ 2) :=
    Nat.mul_le_mul_left _ hZ
  have h4 : 2 ^ 20 * (J + 1) * (X + 4) ≤ A * (X + 4) := Nat.mul_le_mul_right _ hAJ
  have hI2 : INF ≤ 4 * X + 4 := by rw [hX, ← mul_assoc]; exact hINF
  have h5 : INF * J ≤ (4 * X + 4) * J := Nat.mul_le_mul_right _ hI2
  have e1 : (4 * X + 4) * J = 4 * (X * J) + 4 * J := by ring
  have e2 : 2 ^ 20 * (J + 1) * (X + 4) = 2 ^ 20 * (X * J) + 2 ^ 22 * J + 2 ^ 20 * X + 2 ^ 22 := by
    ring
  rw [← mul_assoc] at h3
  omega

/-- **The memory after the record is zero from the end of the arrays of the child on.** -/
theorem zero_mid (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6) :
    ZeroFrom M6 (S.OUTK M1 H k + 2) := by
  intro a ha
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hO := S.OUTK_ge M1 H k
  rw [hmid.frame a (by omega) (by omega) (fun u hu => by have := walk_lt hpre hk hu; omega)
    (fun i hi => by have := hd_nodesK_lt hpre hT hk hi; omega)]
  exact hI.zero a (by omega)

end CS

end MinCostFlow.LowStretch
