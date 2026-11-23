module

public import MinCostFlow.LowStretch.ProgClusterSet2
public import MinCostFlow.LowStretch.ProgClusterSet5

/-!
# The setup of a cluster: the tree after `hwFix`

After `treeP` and `hwFix`, every node `v` other than the node of the center has a parent arc:
at the node of the start of a step of the highway it is that step (`hwFix`), and at every other
node it is the parent arc of the first run (`treeP`). In both cases the parent is a node, the
arc joins a vertex of `v` to a vertex of the parent, and the distance drops by its positive
length (`tree_fix`). This is what `PW.Tree` asks, with the parent array still at `PAR`; the setup
then copies `PAR` to `NXT`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace DWE

variable (E : DWE)

/-- The layout of `hwFix` over the arrays of `treeP` at `Q`. -/
def hfx (Q nH HW : ℕ) : HF :=
  ⟨nH, HW, E.LAB, E.LOC, E.PW, E.EXP, E.lθ, Q, Q + E.s + 1, Q + 2 * E.s + 1, Q + 3 * E.s + 1,
    Q + 4 * E.s + 1, Q + 5 * E.s + 1, Q + 6 * E.s + 1, E.s⟩

end DWE

/-- **The tree of parents** in memory, at the arrays `PAR`, `PP`, `PF`, `PA`, `PB` and the slot
costs `SC`: the node `rt` of the center has the parent `s`, and every other node has a parent
arc as `PW.Tree` asks. -/
structure PTree (T : KT) (G : PG) (c : Cl) (R : Rec) (s rt PAR PP PF PA PB SC : ℕ)
    (mem : ℕ → ℕ) : Prop where
  root : mem (PAR + rt) = s
  edge : ∀ v < s, v ≠ rt →
    mem (PAR + v) < s ∧ mem (PA + v) ∈ c.X ∧ R.sv T c (mem (PA + v)) = v ∧
    mem (PB + v) ∈ c.X ∧ R.sv T c (mem (PB + v)) = mem (PAR + v) ∧
    G.Joins (mem (PP + v)) (mem (PA + v)) (mem (PB + v)) ∧
    c.d G c.x0 (mem (PA + v)) = c.d G c.x0 (mem (PB + v)) + c.len G (mem (PP + v)) ∧
    0 < c.len G (mem (PP + v)) ∧ mem (SC + v) = c.len G (mem (PP + v)) ∧
    mem (PF + v) = if mem (PP + v) ∈ c.half then 1 else 0

namespace Rec

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {w : ℕ} {E : DWE}
  {mem M M2 M3 : ℕ → ℕ}

/-- The node of the center is the node of no step of the highway. -/
theorem nu_ne_root {F : HF} {H NL : ℕ} (hV : F.V T G P c R mem M2 H NL) {j : ℕ} (hj : j < F.nH) :
    F.nu M2 j ≠ R.sv T c c.x0 := by
  intro he
  rw [hV.nu_eq hj] at he
  have hc := hV.ok.inv.good.conn
  have hl := (hV.ok.sv_iff (hV.step hj).2.1 hc.1).mp he
  have h1 := Cl.d_lconn hc hl
  have h0 : c.d G c.x0 c.x0 = 0 := PG.dist_self (by simpa using hc.1)
  have := hV.split.d_start_pos (Cl.hwSt_pos hV.ok.hGo hV.ok.inv.good.high) (hV.nH ▸ hj)
  simp only [HF.sj] at h1
  omega

set_option maxHeartbeats 1000000 in
/-- **The tree after `hwFix`.** -/
theorem tree_fix (h : First w T G c R E mem M) {m n NL : ℕ} (hAP : E.ap.Pre w mem m n NL)
    (hSA : E.SA + 2 * E.nS ≤ E.H) (Q nH HW : ℕ) {NL' : ℕ}
    (hV : (E.hfx Q nH HW).V T G P c R mem M2 E.H NL')
    (hT : (E.tf Q).Done M M2 E.s)
    (hX : (E.hfx Q nH HW).Done M2 M3 nH)
    (hfr : ∀ a, (E.hfx Q nH HW).Free M2 nH a → M3 a = M2 a) :
    PTree T G c R E.s (R.sv T c c.x0) Q (Q + E.s + 1) (Q + 2 * E.s + 1) (Q + 3 * E.s + 1)
      (Q + 4 * E.s + 1) (Q + 5 * E.s + 1) M3 := by
  have hx0 := h.hx0
  have hnu : ∀ j < nH, (E.hfx Q nH HW).nu M2 j < E.s := fun j hj => by
    rw [hV.nu_eq hj]
    have : E.s = R.nodes.length := hV.hs
    rw [this]; exact hV.ok.sv_lt (hV.step hj).2.1
  have hroot : (E.tf Q).x0 = R.sv T c c.x0 := hx0
  refine ⟨?_, fun v hv hvr => ?_⟩
  · have hne : ∀ j < nH, (E.hfx Q nH HW).nu M2 j ≠ R.sv T c c.x0 := fun j hj =>
      nu_ne_root hV hj
    have hr : R.sv T c c.x0 < E.s := by
      have : E.s = R.nodes.length := hV.hs
      rw [this]; exact hV.ok.sv_lt hV.ok.inv.good.conn.1
    rw [hfr _ fun j hj => by
      have := hne j hj; have := hnu j hj
      generalize (E.hfx Q nH HW).nu M2 j = x at *
      simp only [DWE.hfx]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega]
    have := (hT _ hr).1
    simp only [DWE.tf] at this
    rw [this]
    show (if R.sv T c c.x0 = E.x0 then E.s else _) = E.s
    rw [if_pos hx0.symm]
  · by_cases hex : ∃ j < nH, (E.hfx Q nH HW).nu M2 j = v
    · obtain ⟨j, hj, rfl⟩ := hex
      obtain ⟨d1, d2, d3, d4, d5, d6, -⟩ := hX j hj
      set F := E.hfx Q nH HW with hF
      have d1 : M3 (Q + F.nu M2 j) = F.nv M2 j := d1
      have d2 : M3 (Q + E.s + 1 + F.nu M2 j) = F.hp M2 j := d2
      have d3 : M3 (Q + 2 * E.s + 1 + F.nu M2 j) = F.hf M2 j := d3
      have d4 : M3 (Q + 3 * E.s + 1 + F.nu M2 j) = F.ha M2 j := d4
      have d5 : M3 (Q + 4 * E.s + 1 + F.nu M2 j) = F.hb M2 j := d5
      have d6 : M3 (Q + 5 * E.s + 1 + F.nu M2 j) = F.hl M2 j := d6
      rw [d1, d2, d3, d4, d5, d6]
      have hj' : j < (E.hfx Q nH HW).nH := hj
      obtain ⟨s1, s2, s3, s4⟩ := hV.step hj'
      rw [hV.nv_eq hj', hV.hp_eq hj', hV.ha_eq hj', hV.hb_eq hj', hV.hl_eq hj', hV.hf_eq hj']
      refine ⟨?_, s2, (hV.nu_eq hj').symm, s3, rfl, s1, s4, hV.pos hj', rfl, rfl⟩
      have : E.s = R.nodes.length := hV.hs
      rw [this]; exact hV.ok.sv_lt s3
    · push_neg at hex
      have k : ∀ a, (∀ j < nH, a ≠ Q + (E.hfx Q nH HW).nu M2 j ∧
          a ≠ Q + E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
          a ≠ Q + 2 * E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
          a ≠ Q + 3 * E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
          a ≠ Q + 4 * E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
          a ≠ Q + 5 * E.s + 1 + (E.hfx Q nH HW).nu M2 j ∧
          a ≠ Q + 6 * E.s + 1 + (E.hfx Q nH HW).nu M2 j) → M3 a = M2 a :=
        fun a ha => hfr a ha
      have g0 : M3 (Q + v) = M2 (Q + v) := k _ fun j hj => by
        have := hex j hj; have := hnu j hj
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      have g1 : M3 (Q + E.s + 1 + v) = M2 (Q + E.s + 1 + v) := k _ fun j hj => by
        have := hex j hj; have := hnu j hj
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      have g2 : M3 (Q + 2 * E.s + 1 + v) = M2 (Q + 2 * E.s + 1 + v) := k _ fun j hj => by
        have := hex j hj; have := hnu j hj
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      have g3 : M3 (Q + 3 * E.s + 1 + v) = M2 (Q + 3 * E.s + 1 + v) := k _ fun j hj => by
        have := hex j hj; have := hnu j hj
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      have g4 : M3 (Q + 4 * E.s + 1 + v) = M2 (Q + 4 * E.s + 1 + v) := k _ fun j hj => by
        have := hex j hj; have := hnu j hj
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      have g5 : M3 (Q + 5 * E.s + 1 + v) = M2 (Q + 5 * E.s + 1 + v) := k _ fun j hj => by
        have := hex j hj; have := hnu j hj
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      obtain ⟨t1, t2, t3, t4, t5, t6, -, -⟩ := hT v hv
      simp only [DWE.tf] at t1 t2 t3 t4 t5 t6
      rw [g0, g1, g2, g3, g4, g5, t1, t2, t3, t4, t5, t6]
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, -⟩ :=
        h.edge hAP hSA Q hv (by rw [hx0]; exact hvr)
      exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩

end Rec

end MinCostFlow.LowStretch
