module

public import MinCostFlow.LowStretch.ProgChildCtx
public import MinCostFlow.LowStretch.ProgChildFrame

/-!
# The child step: the children, their cost, and the invariant of the loop

The program of the child step treats the children one after the other. This file fixes what the
loop has done after the children before `k` (`CInv`).
* The child that the program makes from raw child `k` is `CS.csOf k`: the raw child itself, or its
  reset at the threshold `thr S B |X|` of `Cl.next_reset` when it has two vertices and a radius
  below `B |X| θ`.
* The cells that child `j` writes below the heap (`CS.WrJ`): the labels of its vertices, the local
  indices at the heads of the nodes between its vertices and their `θ`-nodes, and the highway
  marks of its tree path.
* The cost `CS.costK` and the heap `CS.spaceK` of child `k`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable (S : CS)

/-- Raw child `k` is reset: it has two vertices and its radius is below `B |X| θ`. -/
def resetQ (k : ℕ) : Prop :=
  2 ≤ (S.raw k).X.card ∧ (S.raw k).Δ S.G < S.P.B * (S.raw k).X.card * (S.raw k).θ

/-- The new threshold of a reset child. -/
noncomputable def thrK (k : ℕ) : ℕ :=
  thr (Cl.resetS S.T S.G S.P (S.raw k)) S.P.B (S.raw k).X.card

open Classical in
/-- **The child made from raw child `k`.** -/
noncomputable def csOf (k : ℕ) : Cl := if S.resetQ k then (S.raw k).reset (S.thrK k) else S.raw k

/-- The length of the stored highway of raw child `k`. -/
noncomputable def ℓK (k : ℕ) : ℕ := (Cl.hwE S.G (S.raw k).t (S.raw k).hw S.c.θ S.c.half).length

/-- The numbers of stored pairs and of nodes of raw child `k`. -/
noncomputable def cntK (M : ℕ → ℕ) (k : ℕ) : ℕ := (grp (S.keyF M) S.nA k).length
noncomputable def sNK (M : ℕ → ℕ) (k : ℕ) : ℕ := (grp (S.chxF M) S.s k).length

/-- The work of the splits of child `k`. -/
noncomputable def visK (k : ℕ) : ℕ := S.T.visW S.G (S.raw k) (S.csOf k).θ

/-- **The cost of child `k`.** -/
noncomputable def costK (M : ℕ → ℕ) (k : ℕ) : ℕ :=
  (400 * (Nat.log 2 S.E.J + 2) + 9000) * (S.cntK M k + S.sNK M k) + 9000 * (S.E.J + 1) +
    log2Cost (Cl.resetS S.T S.G S.P (S.raw k) / (4 * S.P.B * (S.raw k).X.card)) +
    1000 * S.visK k

/-- **The heap of child `k`.** -/
noncomputable def spaceK (M : ℕ → ℕ) (k : ℕ) : ℕ :=
  (S.E.J + 1) * (50 * (S.cntK M k + S.sNK M k + 1) + 10 * S.visK k)

/-- The flag of a regular petal. -/
def rgK (k : ℕ) : ℕ := if S.D.Reg k then 1 else 0

/-- The tree path of raw child `k`. -/
noncomputable def walk (k : ℕ) : List ℕ := Rec.walkK S.T S.G S.c S.R S.D S.X S.mem k

/-- **The cells below the heap that child `j` writes.** -/
def WrJ (j a : ℕ) : Prop :=
  (∃ v ∈ (S.raw j).X, a = S.E.LAB + v) ∨
    (∃ v ∈ (S.raw j).X, ∃ u, S.T.Under v u ∧ S.T.Under u (S.T.top S.c.θ v) ∧
      a = S.E.LOC + S.T.hd S.G u) ∨
    ∃ u ∈ S.walk j, a = S.HM + u

/-- The cells written by the children before `k`, with heap pointer `H`. -/
def Wr (k H a : ℕ) : Prop :=
  (S.h ≤ a ∧ a < S.h + 9 * k) ∨ (S.H0 ≤ a ∧ a < H) ∨ ∃ j < k, S.WrJ j a

/-- A cell that no child writes: below `h`, away from the labels and the local indices. -/
def Safe (a : ℕ) : Prop :=
  a < S.h ∧ (a < S.E.LAB ∨ S.E.LAB + S.G.n ≤ a) ∧ (a < S.E.LOC ∨ S.E.LOC + S.T.N ≤ a)

end CS

/-- **The invariant of the loop over the children**, before child `k`, with heap pointer `H`,
records `Rs` and memory `M`; `M1` is the memory after the top level. -/
structure CInv (w : ℕ) (S : CS) (M1 : ℕ → ℕ) (k H : ℕ) (Rs : ℕ → Rec) (M : ℕ → ℕ) : Prop where
  hle : S.H0 ≤ H
  hspace : H ≤ S.H0 + ∑ j ∈ Finset.range k, S.spaceK M1 j
  zero : ZeroFrom M H
  frame : ∀ a, ¬ S.Wr k H a → M a = M1 a
  recs : ∀ j < k, Next S.G S.P (S.raw j) (S.csOf j) ∧ (Rs j).Ok S.T S.G S.P (S.csOf j) ∧
    RecAt S.T S.G (S.csOf j) (Rs j) S.E (RecL.read M (S.h + 9 * j)) M ∧
    ∀ r ∈ (RecL.read M (S.h + 9 * j)).regs, S.H0 ≤ r.1 ∧ r.1 + r.2 ≤ H
  lab : ∀ v < S.G.n, M (S.E.LAB + v) < S.T.N
  loc : ∀ x < S.T.N, M (S.E.LOC + x) < 2 ^ w ∧
    (M (S.E.LOC + x) = S.mem (S.E.LOC + x) ∨ M (S.E.LOC + x) < S.T.N)
  hm : ∀ u < S.s, M (S.HM + u) ≤ 1
  /-- Child `j` stores its active pairs and at most `visK j` more, made visible by a reset. -/
  stor : ∀ j < k, (Rs j).S.length ≤ S.cntK M1 j + S.visK j

namespace CS

variable {S : CS}

theorem Safe.not_wrJ {w : ℕ} (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {a : ℕ} (ha : S.Safe a) (j : ℕ) : ¬ S.WrJ j a := by
  obtain ⟨h1, h2, h3⟩ := ha
  rintro (⟨v, hv, rfl⟩ | ⟨v, hv, u, hu, hut, rfl⟩ | ⟨u, -, rfl⟩)
  · have : v < S.G.n := hpre.ok.n_of_mem (Cl.raw_X_subset j hv)
    rcases h2 with h2 | h2 <;> omega
  · have hvn : v < S.G.n := hpre.ok.n_of_mem (Cl.raw_X_subset j hv)
    have hN := hpre.ok.tree.n_lt
    have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
    have : S.T.hd S.G u < S.T.N := (KT.hd_under hpre.ok.tree u huN).lt_N hpre.ok.tree huN
    rcases h3 with h3 | h3 <;> omega
  · have : S.h ≤ S.HM := by unfold HM ORDK CNTK OFFK KEY ORDN CNTN OFFN CHX; omega
    omega

theorem Safe.not_wr {w : ℕ} (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {a : ℕ} (ha : S.Safe a) (k H : ℕ) : ¬ S.Wr k H a := by
  have hH : S.h ≤ S.H0 := by unfold H0 HM ORDK CNTK OFFK KEY ORDN CNTN OFFN CHX; omega
  have h1 := ha.1
  rintro (⟨h2, -⟩ | ⟨h2, -⟩ | ⟨j, -, hj⟩)
  · omega
  · omega
  · exact ha.not_wrJ hpre j hj

/-- The cells of the regions that the child step reads are safe. -/
theorem safe_of_read {w : ℕ}
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) {r : ℕ × ℕ}
    (hr : r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem) {a : ℕ} (h1 : r.1 ≤ a)
    (h2 : a < r.1 + r.2) : S.Safe a := by
  have hb := hpre.below r hr
  have hl : RegDisj r (S.E.LAB, S.G.n) := hpre.lab_disj r hr
  have hc : RegDisj r (S.E.LOC, S.T.N) := hpre.loc_disj r hr
  unfold RegDisj at hl hc
  refine ⟨by omega, by omega, by omega⟩

end CS

end MinCostFlow.LowStretch
