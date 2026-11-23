module

public import MinCostFlow.LowStretch.ProgClusterSet6

/-!
# The setup of a cluster: the path of the target after `hwFix`

After `hwFix`, the path of parents from the node of the target `c.t` follows the stored highway:
after `i` steps it is at the node of entry `i` of the split highway (`stEnt`), and the parent arc
at that node is step `i` (`HF.V.path`, `HF.V.path_arc`). After all steps it is at the node of the
center. So the steps of this path are the split highway, and the highway `c.hw` splits along them
(`IsHighway.hwDec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace HF

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {F : HF} {mem M M' : ℕ → ℕ} {H NL : ℕ}

/-- Entry `i + 1` of the split highway is the far end of step `i`. -/
theorem stEnt_succ (e : ℕ) {st : List (ℕ × ℕ × ℕ)} {i : ℕ} (hi : i < st.length) :
    Cl.stEnt e st (i + 1) = (st.getD i (0, 0, 0)).2.2 := by
  unfold Cl.stEnt
  rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hi),
    List.getD_eq_getElem _ _ hi]
  simp

/-- The entries of the split highway lie in `X`. -/
theorem V.ent_mem (hV : F.V T G P c R mem M H NL) {i : ℕ} (hi : i ≤ F.nH) :
    Cl.stEnt c.t (Cl.hwSt G c.θ c.t c.hw) i ∈ c.X := by
  cases i with
  | zero => exact hV.ok.inv.good.high.1.start_mem
  | succ i =>
    rw [stEnt_succ _ (by rw [← hV.nH]; omega)]
    exact (hV.step (by omega)).2.2.1

/-- The node of entry `i` is the node of the start of step `i`. -/
theorem V.nu_ent (hV : F.V T G P c R mem M H NL) {i : ℕ} (hi : i < F.nH) :
    F.nu M i = R.sv T c (Cl.stEnt c.t (Cl.hwSt G c.θ c.t c.hw) i) := by
  rw [hV.nu_eq hi]
  exact ((hV.ok.sv_iff (hV.ent_mem hi.le) (hV.step hi).2.1).mpr
    (hV.split.lconn_ent (hV.nH ▸ hi))).symm

/-- **The path of the target follows the stored highway.** -/
theorem V.path (hV : F.V T G P c R mem M H NL) (hX : F.Done M M' F.nH) {i : ℕ} (hi : i ≤ F.nH) :
    parEnd M' F.PAR (R.sv T c c.t) i = R.sv T c (Cl.stEnt c.t (Cl.hwSt G c.θ c.t c.hw) i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i < F.nH := by omega
    unfold parEnd at ih ⊢
    rw [Function.iterate_succ_apply', ih (by omega), ← hV.nu_ent hi', (hX i hi').1, hV.nv_eq hi',
      stEnt_succ _ (by rw [← hV.nH]; exact hi')]

/-- The parent arc at the node of entry `i` is step `i`. -/
theorem V.path_arc (hV : F.V T G P c R mem M H NL) (hX : F.Done M M' F.nH) {i : ℕ}
    (hi : i < F.nH) :
    M' (F.PP + parEnd M' F.PAR (R.sv T c c.t) i) = (sj G c i).1 ∧
      M' (F.PA + parEnd M' F.PAR (R.sv T c c.t) i) = (sj G c i).2.1 ∧
      M' (F.PB + parEnd M' F.PAR (R.sv T c c.t) i) = (sj G c i).2.2 := by
  rw [hV.path hX hi.le, ← hV.nu_ent hi]
  obtain ⟨-, d2, -, d4, d5, -⟩ := hX i hi
  rw [d2, d4, d5, hV.hp_eq hi, hV.ha_eq hi, hV.hb_eq hi]
  exact ⟨rfl, rfl, rfl⟩

/-- After all steps the path is at the node of the center. -/
theorem V.path_end (hV : F.V T G P c R mem M H NL) (hX : F.Done M M' F.nH) :
    parEnd M' F.PAR (R.sv T c c.t) F.nH = R.sv T c c.x0 := by
  rw [hV.path hX le_rfl]
  have hc := hV.ok.inv.good.conn
  refine (hV.ok.sv_iff (hV.ent_mem le_rfl) hc.1).mpr ?_
  have := hV.split.lconn_last
  rwa [← hV.nH] at this

/-- Before its end the path is not at the node of the center. -/
theorem V.path_ne (hV : F.V T G P c R mem M H NL) (hX : F.Done M M' F.nH) {i : ℕ}
    (hi : i < F.nH) : parEnd M' F.PAR (R.sv T c c.t) i ≠ R.sv T c c.x0 := by
  rw [hV.path hX hi.le, ← hV.nu_ent hi]
  exact Rec.nu_ne_root hV hi

/-- The nodes of the path are nodes. -/
theorem V.path_lt (hV : F.V T G P c R mem M H NL) (hX : F.Done M M' F.nH) {i : ℕ}
    (hi : i ≤ F.nH) : parEnd M' F.PAR (R.sv T c c.t) i < R.nodes.length := by
  rw [hV.path hX hi]
  exact hV.ok.sv_lt (hV.ent_mem hi)

end HF

end MinCostFlow.LowStretch
