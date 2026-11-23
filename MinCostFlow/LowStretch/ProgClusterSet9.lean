module

public import MinCostFlow.LowStretch.ProgClusterSet8
public import MinCostFlow.LowStretch.ProgPGraph
public import MinCostFlow.LowStretch.Volume2

/-!
# The setup of a cluster: the arcs of the petal graph

`pgP` gives node `u` one arc for each direction of each active entry at `u`, with the cost
`cofK lθ k` of the class `k` of its shifted length (`pgPC`). The petal searches want the cost
`rc θ (wbar p a b)` (`PW.Ok.arcsN`). The two agree when the memory holds the right values: the
ends of entry `j` are read through the labels and local indices (`PGA.ea_eq`), the distances `DV`
of the nodes are the distances to the center, and the length `PW[p] >>> fl` is the length of the
pair (`PGA.x1_eq`). Then `cofK lθ (rcK lθ x) = rc θ x` (`cofK_rcK`) finishes (`PGA.arcsN`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- The length of a pair that is not light is its weight, halved when the pair is in `half`. -/
theorem shr_len {p : ℕ} (hθ : c.θ ≤ G.pω p) :
    G.pω p >>> (if p ∈ c.half then 1 else 0) = c.len G p := by
  unfold Cl.len
  have hnl : ¬ G.pω p < c.θ := by omega
  by_cases hh : p ∈ c.half
  · simp only [hh, hnl, ite_true, ite_false]; simp [Nat.shiftRight_eq_div_pow]
  · simp only [hh, hnl, ite_false]; simp

end Cl

namespace PGA

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} (A : PGA) {mem : ℕ → ℕ}

/-- The node of the first end of an entry, read through its label. -/
theorem ea_eq {j : ℕ} (hin : mem (A.IN + 3 * A.toPF.pr mem j) = G.pu (A.toPF.pr mem j))
    (hX : G.pu (A.toPF.pr mem j) ∈ c.X)
    (hloc : ∀ v ∈ c.X, mem (A.LOC + mem (A.LAB + v)) = R.sv T c v) :
    A.toPF.ea mem j = R.sv T c (G.pu (A.toPF.pr mem j)) := by
  show mem (A.LOC + mem (A.LAB + mem (A.IN + 3 * A.toPF.pr mem j))) = _
  rw [hin]; exact hloc _ hX

/-- The node of the second end of an entry, read through its label. -/
theorem eb_eq {j : ℕ} (hin : mem (A.IN + 3 * A.toPF.pr mem j + 1) = G.pv (A.toPF.pr mem j))
    (hX : G.pv (A.toPF.pr mem j) ∈ c.X)
    (hloc : ∀ v ∈ c.X, mem (A.LOC + mem (A.LAB + v)) = R.sv T c v) :
    A.toPF.eb mem j = R.sv T c (G.pv (A.toPF.pr mem j)) := by
  show mem (A.LOC + mem (A.LAB + mem (A.IN + 3 * A.toPF.pr mem j + 1))) = _
  rw [hin]; exact hloc _ hX

/-- The length that `pfill` reads is the length of the pair. -/
theorem ln_eq {j : ℕ} (hpw : mem (A.PW + A.toPF.pr mem j) = G.pω (A.toPF.pr mem j))
    (hfl : A.toPF.fl mem j = if A.toPF.pr mem j ∈ c.half then 1 else 0)
    (hθ : c.θ ≤ G.pω (A.toPF.pr mem j)) :
    A.toPF.ln mem j = c.len G (A.toPF.pr mem j) := by
  show mem (A.PW + A.toPF.pr mem j) >>> A.toPF.fl mem j = _
  rw [hpw, hfl]; exact Cl.shr_len hθ

/-- **The shifted lengths** are the reduced lengths `wbar` of the two directions. -/
theorem x1_eq {j : ℕ} (hea : A.toPF.ea mem j = R.sv T c (G.pu (A.toPF.pr mem j)))
    (heb : A.toPF.eb mem j = R.sv T c (G.pv (A.toPF.pr mem j)))
    (hX1 : G.pu (A.toPF.pr mem j) ∈ c.X) (hX2 : G.pv (A.toPF.pr mem j) ∈ c.X)
    (hDV : ∀ a ∈ c.X, mem (A.DV + R.sv T c a) = c.d G c.x0 a)
    (hln : A.toPF.ln mem j = c.len G (A.toPF.pr mem j)) :
    A.toPF.x1 mem j = c.wbar G (A.toPF.pr mem j) (G.pu (A.toPF.pr mem j)) (G.pv (A.toPF.pr mem j)) ∧
      A.toPF.x2 mem j =
        c.wbar G (A.toPF.pr mem j) (G.pv (A.toPF.pr mem j)) (G.pu (A.toPF.pr mem j)) := by
  unfold PF.x1 PF.x2 Cl.wbar
  have e1 : mem (A.toPF.DV + A.toPF.ea mem j) = c.d G c.x0 (G.pu (A.toPF.pr mem j)) := by
    rw [hea]; exact hDV _ hX1
  have e2 : mem (A.toPF.DV + A.toPF.eb mem j) = c.d G c.x0 (G.pv (A.toPF.pr mem j)) := by
    rw [heb]; exact hDV _ hX2
  rw [e1, e2, hln]
  exact ⟨rfl, rfl⟩

/-- **The arcs of a node before its slot**, in the form `PW.Ok.arcsN` asks. -/
theorem arcsN {mem' : ℕ → ℕ} {s nA LO HI HD CS lθ θ : ℕ} {ea eb pr : ℕ → ℕ}
    {wb1 wb2 : ℕ → ℕ}
    (hpg : ∀ u < A.s, ∀ P : ℕ → ℕ → ℕ → Prop,
      (∃ k, mem' (A.OFF + u) ≤ k ∧ k + 1 < mem' (A.OFF + 1 + u) ∧
        P (mem' (A.HD + k)) (mem' (A.CS + k)) (mem' (A.CL + k))) ↔
      ∃ j < A.nA,
        (A.toPF.ea mem j = u ∧ P (A.toPF.eb mem j) (cofK A.lθ (A.toPF.k1 mem j)) (A.toPF.k1 mem j)) ∨
        (A.toPF.eb mem j = u ∧ P (A.toPF.ea mem j) (cofK A.lθ (A.toPF.k2 mem j)) (A.toPF.k2 mem j)))
    (hs : s = A.s) (hnA : nA = A.nA) (hLO : LO = A.OFF) (hHI : HI = A.OFF + 1) (hHD : HD = A.HD)
    (hCS : CS = A.CS) (hlθ : lθ = A.lθ) (hθ : θ = 2 ^ lθ)
    (hea : ∀ j < nA, A.toPF.ea mem j = ea j) (heb : ∀ j < nA, A.toPF.eb mem j = eb j)
    (hx1 : ∀ j < nA, A.toPF.x1 mem j = wb1 j) (hx2 : ∀ j < nA, A.toPF.x2 mem j = wb2 j) :
    ∀ u < s, ∀ Q : ℕ → ℕ → Prop,
      (∃ k, mem' (LO + u) ≤ k ∧ k + 1 < mem' (HI + u) ∧ Q (mem' (HD + k)) (mem' (CS + k))) ↔
        ∃ j < nA, (ea j = u ∧ Q (eb j) (rc θ (wb1 j))) ∨ (eb j = u ∧ Q (ea j) (rc θ (wb2 j))) := by
  intro u hu Q
  subst hs hnA hLO hHI hHD hCS hlθ hθ
  rw [hpg u hu (fun a b _ => Q a b)]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  unfold PF.k1 PF.k2
  rw [show A.toPF.lθ = A.lθ from rfl, cofK_rcK, cofK_rcK, hea j hj, heb j hj, hx1 j hj, hx2 j hj]

end PGA

end MinCostFlow.LowStretch
