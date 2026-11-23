module

public import MinCostFlow.LowStretch.ProgClusterSetupPg

/-!
# The setup of a cluster: facts for the precondition of `pgP`

Three facts that the precondition of `pgP` needs and that do not depend on the layout.
- Every node holds a vertex of the cluster (`Rec.Ok.sv_surj`), so the distances of the first run
  are known at every node.
- After `treeP` and `hwFix`, the slot of every node has class below `J` and cost at most `Δ`
  (`Rec.slot_bd`). The cost of a parent arc is its length, which is at most `Δ`, and it is the cost
  `2^(lθ + k - 2)` of its class `k`. The center has class `0` and cost `0`.
- A word bound with room for the classes of the petal graph: `h + 2^(J + 8) θ < 2^w`
  (`ClPre.words_hi`), from `ClPre.room`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec}

/-- **Every node holds a vertex of the cluster.** -/
theorem Rec.Ok.sv_surj (hr : R.Ok T G P c) {u : ℕ} (hu : u < R.nodes.length) :
    ∃ a ∈ c.X, R.sv T c a = u := by
  have hk : R.nodes[u] ∈ R.nodes := List.getElem_mem hu
  obtain ⟨v, hv, hvk⟩ := KT.exists_leaf hr.tree _ (hr.node_lt _ hk)
  have htop := hr.node_top _ hk v hv hvk
  refine ⟨v, (hr.X_iff v).mpr ⟨hv, by rw [htop]; exact hk⟩, ?_⟩
  show R.nodes.idxOf (T.top c.θ v) = u
  rw [htop]; exact List.Nodup.idxOf_getElem hr.nodup u hu

namespace Rec

variable {w : ℕ} {E : DWE} {mem M M2 M3 : ℕ → ℕ}

set_option maxHeartbeats 1000000 in
/-- **The slots are small.** After `treeP` and `hwFix`, the slot of each node `v` has class below
`J` and cost at most `Δ`, when `4 Δ < 2^(lθ + J)`. -/
theorem slot_bd (h : First w T G c R E mem M) {m n NL : ℕ} (hAP : E.ap.Pre w mem m n NL)
    (hSA : E.SA + 2 * E.nS ≤ E.H) (Q nH HW : ℕ) {NL' : ℕ}
    (hV : (E.hfx Q nH HW).V T G P c R mem M2 E.H NL')
    (hT : (E.tf Q).Done M M2 E.s)
    (hX : (E.hfx Q nH HW).Done M2 M3 nH)
    (hfr : ∀ a, (E.hfx Q nH HW).Free M2 nH a → M3 a = M2 a) {J : ℕ} (hJ1 : 1 ≤ J)
    (hJ : 4 * c.Δ G < 2 ^ (E.lθ + J)) (hθ : c.θ = 2 ^ E.lθ) {v : ℕ} (hv : v < E.s) :
    M3 (Q + 6 * E.s + 1 + v) < J ∧ M3 (Q + 5 * E.s + 1 + v) ≤ c.Δ G := by
  have hcl := tree_cls h hAP hSA Q nH HW hV hT hX hfr hv
  have hpt := tree_fix h hAP hSA Q nH HW hV hT hX hfr
  by_cases hr : v = R.sv T c c.x0
  · subst hr
    have hnu : ∀ j < nH, (E.hfx Q nH HW).nu M2 j < E.s := fun j hj => by
      rw [hV.nu_eq hj]
      have : E.s = R.nodes.length := hV.hs
      rw [this]; exact hV.ok.sv_lt (hV.step hj).2.1
    have hne : ∀ j < nH, (E.hfx Q nH HW).nu M2 j ≠ R.sv T c c.x0 := fun j hj =>
      nu_ne_root hV hj
    have e6 : M3 (Q + 6 * E.s + 1 + R.sv T c c.x0) = 0 := by
      rw [hfr _ fun j hj => by
        have := hne j hj; have := hnu j hj
        generalize (E.hfx Q nH HW).nu M2 j = x at *
        simp only [DWE.hfx]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega]
      have := (hT _ hv).2.2.2.2.2.2.1
      simp only [DWE.tf] at this
      rw [this]
      show (if R.sv T c c.x0 = E.x0 then 0 else _) = 0
      rw [if_pos h.hx0.symm]
    rw [hcl, e6]
    simp only [cofK, if_true]
    omega
  · obtain ⟨-, hPA, -, -, -, -, hd, hpos, hsc, -⟩ := hpt.edge v hv hr
    have hle := c.d_le_Δ (G := G) hPA
    have hlen : c.len G (M3 (Q + E.s + 1 + v)) ≤ c.Δ G := by omega
    rw [← hsc] at hlen hpos
    refine ⟨?_, hlen⟩
    rw [hcl] at hlen hpos
    unfold cofK at hlen hpos
    split_ifs at hlen hpos with hk
    · omega
    · by_contra hc
      have hΔ1 : 1 ≤ c.Δ G := le_trans Nat.one_le_two_pow hlen
      have h3 : 2 ≤ E.lθ + J := by
        by_contra hc'
        have : 2 ^ (E.lθ + J) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h1 : 2 ^ (E.lθ + J - 2) ≤ 2 ^ (E.lθ + M3 (Q + 6 * E.s + 1 + v) - 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (E.lθ + J) = 4 * 2 ^ (E.lθ + J - 2) := by
        rw [show E.lθ + J = (E.lθ + J - 2) + 2 by omega, pow_add]
        rw [show E.lθ + J - 2 + 2 - 2 = E.lθ + J - 2 by omega]; ring
      omega

end Rec

variable {w A : ℕ} {GB RB h : ℕ} {mem : ℕ → ℕ}

/-- **Room for the classes of the petal graph**: `h + 2^(J + 8) θ < 2^w`. -/
theorem ClPre.words_hi (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    h + 2 ^ ((GlobL.read mem GB).J + 8) * c.θ < 2 ^ w := by
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
  have hnM : G.n * Mw ≤ X0 * Y0 := by
    have : (G.n + 2) * (Mw + 2) ≤ X0 * Y0 := Nat.mul_le_mul (by omega) le_rfl
    have e : (G.n + 2) * (Mw + 2) = G.n * Mw + 2 * G.n + 2 * Mw + 4 := by ring
    omega
  have hθZ : c.θ ≤ X0 * Y0 := hθΔ.trans (hΔ.trans hnM)
  have hE : 1 ≤ 2 ^ J := Nat.one_le_two_pow
  have hZ : 1 ≤ X0 * Y0 := le_trans hp.ok.inv.one_le hθZ
  have h1 : 2 ^ (J + 8) * c.θ ≤ 2 ^ 8 * (2 ^ J * (X0 * Y0)) := by
    rw [pow_add, mul_comm (2 ^ J) (2 ^ 8), mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hθZ)
  have h2 : 2 ^ 8 * (2 ^ J * (X0 * Y0)) < 2 ^ (2 * J + 20) * X0 ^ 2 * Y0 ^ 2 := by
    have e : 2 ^ (2 * J + 20) * X0 ^ 2 * Y0 ^ 2 = 2 ^ 20 * ((2 ^ J * 2 ^ J) * (X0 * Y0) ^ 2) := by
      rw [show 2 * J + 20 = 20 + (J + J) by omega, pow_add, pow_add]; ring
    rw [e]
    have h3 : 2 ^ J * (X0 * Y0) ≤ (2 ^ J * 2 ^ J) * (X0 * Y0) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul (Nat.le_mul_of_pos_right _ hE) (Nat.le_mul_of_pos_right _ hZ)
    have h4 : 0 < 2 ^ J * (X0 * Y0) := Nat.mul_pos hE hZ
    omega
  have h0 := Nat.zero_le ((J + 2) * recCost w A T G P c R)
  omega

end MinCostFlow.LowStretch
