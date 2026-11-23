module

public import MinCostFlow.LowStretch.ProgClusterSet7

/-!
# The setup of a cluster: the costs and classes of the parent arcs

The petal graph gives the slot of node `u` the cost `SCc[u]` and the class `SCk[u]` of its parent
arc. The petal searches need the cost of an arc to be a function of its class (`PW.Ok.classes`).
For the arcs of pairs, `pgP` gives the cost `cofK lθ k` of class `k`. Here we show the same for
the slots: after `treeP` and `hwFix`, `SCc[u] = cofK lθ SCk[u]` for every node `u`
(`Rec.tree_cls`). The reason is that a parent arc has positive length, so its weight is at least
`θ`, and then its length `2^e` or `2^(e-1)` is the cost of its class (`Cl.len_eq_cofK`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- **The length of a pair is the cost of its class**, when the length is positive. -/
theorem len_eq_cofK {lθ e p : ℕ} (hθ : c.θ = 2 ^ lθ) (hex : G.pω p = 2 ^ e)
    (hpos : 0 < c.len G p) :
    c.len G p = cofK lθ (e + 2 - (if p ∈ c.half then 1 else 0) - lθ) := by
  unfold Cl.len at hpos ⊢
  have hnl : ¬ G.pω p < c.θ := fun h => by simp [h] at hpos
  have hle : lθ ≤ e := by
    rw [hθ, hex] at hnl
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by omega)
  unfold cofK
  by_cases hh : p ∈ c.half
  · have he : 1 ≤ e := by
      by_contra h0
      have : e = 0 := by omega
      simp [hnl, hh, hex, this] at hpos
    simp only [hnl, hh, ite_true, ite_false]
    rw [if_neg (by omega), hex, show lθ + (e + 2 - 1 - lθ) - 2 = e - 1 by omega]
    rw [show e = e - 1 + 1 by omega, pow_succ]
    simp
  · simp only [hnl, hh, ite_false]
    rw [if_neg (by omega), hex, show lθ + (e + 2 - 0 - lθ) - 2 = e by omega]

end Cl

namespace HF

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {F : HF} {mem M : ℕ → ℕ} {H NL : ℕ}

/-- The class that `hwFix` writes for step `j`. -/
theorem V.hk_eq (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.hk M j = mem (F.EXP + (sj G c j).1) + 2 - (if (sj G c j).1 ∈ c.half then 1 else 0) - F.lθ := by
  have hm := (h.step hj).1.1
  have := h.rEXP
  unfold HF.hk
  rw [V.hp_eq h hj, V.hf_eq h hj, h.low (F.EXP + (sj G c j).1) (by omega)]

/-- The cost that `hwFix` writes for step `j` is the cost of its class. -/
theorem V.hl_cofK (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.hl M j = cofK F.lθ (F.hk M j) := by
  rw [h.hl_eq hj, h.hk_eq hj]
  exact Cl.len_eq_cofK h.th (h.ex _ (h.step hj).1.1) (h.pos hj)

end HF

namespace Rec

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {w : ℕ} {E : DWE}
  {mem M M2 M3 : ℕ → ℕ}

/-- The first run does not change the cells below the heap pointer. -/
theorem First.low (h : First w T G c R E mem M) {a : ℕ} (ha : a < E.H) : M a = mem a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hM0⟩ := h.run
  exact hM0 a (Or.inl ha)

/-- The class of the parent arc that `treeP` writes. -/
theorem First.cls (h : First w T G c R E mem M) {m n NL : ℕ} (hAP : E.ap.Pre w mem m n NL)
    (hSA : E.SA + 2 * E.nS ≤ E.H) (P : ℕ) {u : ℕ} (hu : u < E.s) (hux : u ≠ E.x0) :
    (E.tf P).vSK M u = mem (E.EXP + (E.tf P).vPP M u) + 2 -
      (if (E.tf P).vPP M u ∈ c.half then 1 else 0) - E.lθ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, e10, e11, e12, -, -, e14, -⟩ := h.edge hAP hSA P hu hux
  rw [e11, ← e10]
  have hpp : (E.tf P).vPP M u = (E.tf P).pp M u := by unfold TF.vPP; exact if_neg (show u ≠ (E.tf P).x0 from hux)
  have hpf : (E.tf P).vPF M u = (E.tf P).pf M u := by unfold TF.vPF; exact if_neg (show u ≠ (E.tf P).x0 from hux)
  rw [hpp, hpf, e14]
  show mem (E.EXP + E.ap.toAF.pr mem _) + 2 - mem (E.SA + 2 * _ + 1) - E.lθ = _
  unfold TF.pf
  rw [h.low (by have : (E.tf P).SA = E.SA := rfl; omega)]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The cost of each parent arc is the cost of its class**, after `treeP` and `hwFix`. -/
theorem tree_cls (h : First w T G c R E mem M) {m n NL : ℕ} (hAP : E.ap.Pre w mem m n NL)
    (hSA : E.SA + 2 * E.nS ≤ E.H) (Q nH HW : ℕ) {NL' : ℕ}
    (hV : (E.hfx Q nH HW).V T G P c R mem M2 E.H NL')
    (hT : (E.tf Q).Done M M2 E.s)
    (hX : (E.hfx Q nH HW).Done M2 M3 nH)
    (hfr : ∀ a, (E.hfx Q nH HW).Free M2 nH a → M3 a = M2 a) {v : ℕ} (hv : v < E.s) :
    M3 (Q + 5 * E.s + 1 + v) = cofK E.lθ (M3 (Q + 6 * E.s + 1 + v)) := by
  have hx0 := h.hx0
  have hnu : ∀ j < nH, (E.hfx Q nH HW).nu M2 j < E.s := fun j hj => by
    rw [hV.nu_eq hj]
    have : E.s = R.nodes.length := hV.hs
    rw [this]; exact hV.ok.sv_lt (hV.step hj).2.1
  by_cases hex : ∃ j < nH, (E.hfx Q nH HW).nu M2 j = v
  · obtain ⟨j, hj, rfl⟩ := hex
    obtain ⟨-, -, -, -, -, d6, d7⟩ := hX j hj
    set F := E.hfx Q nH HW with hF
    have d6 : M3 (Q + 5 * E.s + 1 + F.nu M2 j) = F.hl M2 j := d6
    have d7 : M3 (Q + 6 * E.s + 1 + F.nu M2 j) = F.hk M2 j := d7
    rw [d6, d7]
    exact hV.hl_cofK hj
  · push_neg at hex
    have k : ∀ a, (∀ j < nH, a ≠ Q + (E.hfx Q nH HW).nu M2 j ∧
        a ≠ Q + E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
        a ≠ Q + 2 * E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
        a ≠ Q + 3 * E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
        a ≠ Q + 4 * E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
        a ≠ Q + 5 * E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
        a ≠ Q + 6 * E.s + 1 + (E.hfx Q nH HW).nu M2 j) → M3 a = M2 a :=
      fun a ha => hfr a ha
    have g5 : M3 (Q + 5 * E.s + 1 + v) = M2 (Q + 5 * E.s + 1 + v) := k _ fun j hj => by
      have := hex j hj; have := hnu j hj
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    have g6 : M3 (Q + 6 * E.s + 1 + v) = M2 (Q + 6 * E.s + 1 + v) := k _ fun j hj => by
      have := hex j hj; have := hnu j hj
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    obtain ⟨-, -, -, -, -, t6, t7, -⟩ := hT v hv
    simp only [DWE.tf] at t6 t7
    rw [g5, g6, t6, t7]
    by_cases hvr : v = E.x0
    · subst hvr
      unfold TF.vSC TF.vSK
      simp [cofK, DWE.tf]
    · have e := h.edge hAP hSA Q hv hvr
      obtain ⟨-, -, -, -, -, e6, -, e8, e9, -⟩ := e
      have hcl := h.cls hAP hSA Q hv hvr
      have hm : (E.tf Q).vPP M v < G.m := e6.1
      have hex' := hV.ex _ hm
      have heq : (E.hfx Q nH HW).EXP = E.EXP := rfl
      have hth : (E.hfx Q nH HW).lθ = E.lθ := rfl
      rw [heq] at hex'
      have hth' := hV.th
      rw [hth] at hth'
      show (E.tf Q).vSC M v = cofK E.lθ ((E.tf Q).vSK M v)
      rw [e9, hcl]
      exact Cl.len_eq_cofK hth' hex' e8

end Rec

end MinCostFlow.LowStretch
