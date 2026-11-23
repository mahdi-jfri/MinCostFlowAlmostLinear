module

public import MinCostFlow.LowStretch.ProgClusterSetupO2

/-!
# The setup of a cluster: the tree arrays after `actP`

`actP` writes only its entries from `ACT = Z + 8 s + 2` on, so the tree of parents of `treeP` and
`hwFix` (`Rec.tree_fix`), the classes of the parent arcs (`Rec.tree_cls`) and the bounds of the
slots hold in the memory `M4` after `actP` too (`SuMem.ptree`, `SuMem.tcls`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- The tree of parents depends only on its arrays. -/
theorem PTree.congr {s rt PAR PP PF PA PB SC : ℕ} {M M' : ℕ → ℕ}
    (hT : PTree T G c R s rt PAR PP PF PA PB SC M)
    (hm : ∀ v < s, M' (PAR + v) = M (PAR + v) ∧ M' (PP + v) = M (PP + v) ∧
      M' (PF + v) = M (PF + v) ∧ M' (PA + v) = M (PA + v) ∧ M' (PB + v) = M (PB + v) ∧
      M' (SC + v) = M (SC + v)) (hrt : rt < s) :
    PTree T G c R s rt PAR PP PF PA PB SC M' where
  root := by rw [(hm rt hrt).1]; exact hT.root
  edge v hv hr := by
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hm v hv
    rw [f1, f2, f3, f4, f5, f6]
    exact hT.edge v hv hr

namespace SuMem

variable {M M2 M3 M4 : ℕ → ℕ}

set_option maxHeartbeats 1000000 in
/-- **The tree of parents after `actP`.** -/
theorem ptree (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4)
    (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    PTree T G c R (RecL.read mem RB).s (R.sv T c c.x0) ((suVOf GB RB h mem).N P.L).Z
      (((suVOf GB RB h mem).N P.L).Z + (RecL.read mem RB).s + 1)
      (((suVOf GB RB h mem).N P.L).Z + 2 * (RecL.read mem RB).s + 1)
      (((suVOf GB RB h mem).N P.L).Z + 3 * (RecL.read mem RB).s + 1)
      (((suVOf GB RB h mem).N P.L).Z + 4 * (RecL.read mem RB).s + 1)
      (((suVOf GB RB h mem).N P.L).Z + 5 * (RecL.read mem RB).s + 1) M4 := by
  have hZ : h + 51 ≤ ((suVOf GB RB h mem).N P.L).Z := by
    simp only [SuN.Z, SuN.H, SuV.N, suVOf]; omega
  have hVf := hp.hfV hM.first hZ hM.tr_fr
  obtain ⟨E', hE', -, -, hAP, -, -, -, -, -, -, -, -, -, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hb := hp.below
  have bSA := hb ((RecL.read mem RB).SA, 2 * (RecL.read mem RB).nS)
    (by simp [recRegs, RecL.regs])
  dsimp only at bSA
  have ht := Rec.tree_fix hM.first hAP
    (show (RecL.read mem RB).SA + 2 * (RecL.read mem RB).nS ≤ h + 51 by omega) _ _ _ hVf hM.tr
    hM.hf hM.hf_fr
  have hs : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
  refine PTree.congr ht (fun v hv => ?_) (hs ▸ hp.ok.sv_lt hp.ok.inv.good.conn.1)
  have hv' : v < (RecL.read mem RB).s := hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact hM.ac_fr _ (by omega)

set_option maxHeartbeats 1000000 in
/-- **The cost of each parent arc is the cost of its class**, after `actP`. -/
theorem tcls (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4)
    (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) {v : ℕ}
    (hv : v < (RecL.read mem RB).s) :
    M4 (((suVOf GB RB h mem).N P.L).Z + 5 * (RecL.read mem RB).s + 1 + v) =
      cofK (RecL.read mem RB).lθ
        (M4 (((suVOf GB RB h mem).N P.L).Z + 6 * (RecL.read mem RB).s + 1 + v)) := by
  have hZ : h + 51 ≤ ((suVOf GB RB h mem).N P.L).Z := by
    simp only [SuN.Z, SuN.H, SuV.N, suVOf]; omega
  have hVf := hp.hfV hM.first hZ hM.tr_fr
  obtain ⟨E', hE', -, -, hAP, -, -, -, -, -, -, -, -, -, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hb := hp.below
  have bSA := hb ((RecL.read mem RB).SA, 2 * (RecL.read mem RB).nS)
    (by simp [recRegs, RecL.regs])
  dsimp only at bSA
  have hc := Rec.tree_cls hM.first hAP
    (show (RecL.read mem RB).SA + 2 * (RecL.read mem RB).nS ≤ h + 51 by omega) _ _ _ hVf hM.tr
    hM.hf hM.hf_fr hv
  rw [hM.ac_fr _ (by omega), hM.ac_fr _ (by omega)]
  exact hc

end SuMem

end MinCostFlow.LowStretch
