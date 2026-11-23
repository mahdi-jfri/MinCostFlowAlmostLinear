module

public import MinCostFlow.Spanner.ProgRevWalk
public import MinCostFlow.Spanner.ProgComposeEdges
public import MinCostFlow.LSF.Program.Utils

@[expose] public section

/-!
# Writing One Step of a Composed Walk

A step of `composeAux B embBC` along the pair `(u, v)` and the edge `j` of `B` is the walk
`embBC j`, turned around when edge `j` of `B` does not go from `u` to `v` (`composeStep`). This
file gives the procedure that writes this step: it reads the two ends of edge `j` of `B`, and
then copies walk `j` with `memCopy` or writes it turned around with `revWalkBody`. The result is
`composeStep_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- Procedure body, at `args = [bAddr, E, u, v, j, dst]`. Here `fc` holds `memCopyStmt` and
`frw` holds `revWalkBody`. -/
def composeStepBody (fc frw : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .add (.reg 4) (.reg 4))))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .add (.reg 4) (.reg 4))))) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.reg 4))) ;;
  .assign 9 (.load (.reg 8)) ;;
  .assign 10 (.load (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 9))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 9) (.reg 10)) (.const 2)) ;;
  .cond (.bin .mul (.bin .eq (.reg 6) (.reg 2)) (.bin .eq (.reg 7) (.reg 3)))
    (.call 11 fc [.reg 5, .reg 8, .reg 10])
    (.call 11 frw [.reg 8, .reg 5]) ;;
  .ret (.const 0)

/-- The graph `B` is at `bAddr` and its embedding `embBC` at `E`, all below the output `dst`.
The edge `j` is an edge of `B`, and the output fits in a word. -/
def ComposeStepPre (mem : ℕ → ℕ) (bAddr E j dst : ℕ) (B : Graph) (embBC : ℕ → Walk)
    (w : ℕ) : Prop :=
  GraphAt mem bAddr B ∧ EmbAt mem E B.m embBC ∧ EmbBounded mem E B.m embBC dst ∧
    bAddr + (2 + 2 * B.m) ≤ dst ∧ j < B.m ∧ dst + (Walk.encode (embBC j)).length < 2 ^ w ∧
    1 < 2 ^ w

/-- Contract of `composeStepBody`. The cost bound uses the length of the stored walk `j`. -/
def composeStepContract (w : ℕ) : Contract where
  pre args mem := ∃ bAddr E u v j dst B embBC, args = [bAddr, E, u, v, j, dst] ∧
    ComposeStepPre mem bAddr E j dst B embBC w
  post args mem _ mem' := ∀ bAddr E u v j dst B embBC, args = [bAddr, E, u, v, j, dst] →
    ComposeStepPre mem bAddr E j dst B embBC w →
    WalkAt mem' dst (composeStep B embBC u v j) ∧
      ∀ x, x < dst ∨ dst + (Walk.encode (embBC j)).length ≤ x → mem' x = mem x
  cost args mem :=
    let P := mem (args.getD 1 0 + args.getD 4 0)
    30 * (mem P + mem (P + 1 + mem P)) + 300

lemma ev_reg' {w r : ℕ} {st : State} {v : ℕ} (hr : st.regs r = v) :
    (Expr.reg r).eval w st = some v := by
  simp [Expr.eval, hr]

lemma ev_eq_mul {w : ℕ} {st : State} {e₁ e₂ e₃ e₄ : Expr} {a b c d : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (h₃ : e₃.eval w st = some c)
    (h₄ : e₄.eval w st = some d) (hw : 1 < 2 ^ w) :
    (Expr.bin .mul (.bin .eq e₁ e₂) (.bin .eq e₃ e₄)).eval w st =
      some (if a = b ∧ c = d then 1 else 0) := by
  by_cases hab : a = b <;> by_cases hcd : c = d
  · rw [ev_mul (ev_eq_t h₁ h₂ hab hw) (ev_eq_t h₃ h₄ hcd hw) (by omega)]; simp [hab, hcd]
  · rw [ev_mul (ev_eq_t h₁ h₂ hab hw) (ev_eq_f h₃ h₄ hcd hw) (by omega)]; simp [hcd]
  · rw [ev_mul (ev_eq_f h₁ h₂ hab hw) (ev_eq_t h₃ h₄ hcd hw) (by omega)]; simp [hab]
  · rw [ev_mul (ev_eq_f h₁ h₂ hab hw) (ev_eq_f h₃ h₄ hcd hw) (by omega)]; simp [hab]

/-- `composeStepBody fc frw` at `f` meets `composeStepContract`, given that `fc` holds
`memCopyStmt` and `frw` holds `revWalkBody`. -/
theorem composeStep_meetsContract {w : ℕ} {p : Program} {f fc frw : ℕ}
    (hproc : p.procs[f]? = some (composeStepBody fc frw))
    (hfc : MeetsContract w p fc (memCopyContract w))
    (hfrw : MeetsContract w p frw (revWalkContract w)) :
    MeetsContract w p f (composeStepContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨bAddr, E, u, v, j, dst, B, embBC, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hG, hEmb, hBnd, hGd, hj, hdw, hw1⟩ := hP'
  have huw : u < 2 ^ w := hwords u (by simp)
  have hvw : v < 2 ^ w := hwords v (by simp)
  have hjw : j < 2 ^ w := hwords j (by simp)
  have hEj : E + j < dst := by have := hBnd.1; omega
  set P := mem (E + j) with hPdef
  have hW := hEmb j hj
  obtain ⟨hnv, -, hne, -⟩ := walkAt_iff.mp hW
  have hPb := hBnd.2 j hj
  have hlen := walk_encode_length (embBC j)
  set nv := (embBC j).verts.length with hnvdef
  set ne := (embBC j).edges.length with hnedef
  set a := (B.edges.getD j (0, 0)).1 with hadef
  set b := (B.edges.getD j (0, 0)).2 with hbdef
  have ha : mem (bAddr + (2 + 2 * j)) = a := graphAt_edge_fst_getD hG hj
  have hb : mem (bAddr + (3 + 2 * j)) = b := graphAt_edge_snd_getD hG hj
  let s0 := startState [bAddr, E, u, v, j, dst] mem pos
  have r0 : s0.regs 0 = bAddr := by simp [s0, startState]
  have r1 : s0.regs 1 = E := by simp [s0, startState]
  have r2 : s0.regs 2 = u := by simp [s0, startState]
  have r3 : s0.regs 3 = v := by simp [s0, startState]
  have r4 : s0.regs 4 = j := by simp [s0, startState]
  have r5 : s0.regs 5 = dst := by simp [s0, startState]
  have hdst : dst < 2 ^ w := by omega
  have e6 : (Expr.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .add (.reg 4) (.reg 4))))).eval
      w s0 = some a :=
    ev_load' (ev_add (ev_reg r0 (by omega)) (ev_add (ev_const (c := 2) (by omega))
      (ev_add (ev_reg r4 hjw) (ev_reg r4 hjw) (by omega)) (by omega)) (by omega))
      (by rw [show j + j = 2 * j by omega]; exact ha)
  let s1 : State := { s0 with regs := Function.update s0.regs 6 a }
  have e7 : (Expr.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .add (.reg 4) (.reg 4))))).eval
      w s1 = some b :=
    ev_load' (ev_add (ev_reg (v := bAddr) (by simp [s1, r0]) (by omega))
      (ev_add (ev_const (c := 3) (by omega)) (ev_add (ev_reg (v := j) (by simp [s1, r4]) hjw)
        (ev_reg (v := j) (by simp [s1, r4]) hjw) (by omega)) (by omega)) (by omega))
      (by rw [show j + j = 2 * j by omega]; exact hb)
  let s2 : State := { s1 with regs := Function.update s1.regs 7 b }
  have e8 : (Expr.load (.bin .add (.reg 1) (.reg 4))).eval w s2 = some P :=
    ev_load' (ev_add (ev_reg (v := E) (by simp [s2, s1, r1]) (by omega))
      (ev_reg (v := j) (by simp [s2, s1, r4]) hjw) (by omega)) rfl
  let s3 : State := { s2 with regs := Function.update s2.regs 8 P }
  have e9 : (Expr.load (.reg 8)).eval w s3 = some nv :=
    ev_load' (ev_reg (v := P) (by simp [s3]) (by omega)) hnv
  let s4 : State := { s3 with regs := Function.update s3.regs 9 nv }
  have e10 : (Expr.load (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 9))).eval w s4 =
      some ne :=
    ev_load' (ev_add (ev_add (ev_reg (v := P) (by simp [s4, s3]) (by omega)) (ev_const hw1)
      (by omega)) (ev_reg (v := nv) (by simp [s4]) (by omega)) (by omega)) hne
  let s5 : State := { s4 with regs := Function.update s4.regs 10 ne }
  have e10' : (Expr.bin .add (.bin .add (.reg 9) (.reg 10)) (.const 2)).eval w s5 =
      some (nv + ne + 2) :=
    ev_add (ev_add (ev_reg (v := nv) (by simp [s5, s4]) (by omega))
      (ev_reg (v := ne) (by simp [s5]) (by omega)) (by omega)) (ev_const (c := 2) (by omega))
      (by omega)
  let s6 : State := { s5 with regs := Function.update s5.regs 10 (nv + ne + 2) }
  have ec := ev_eq_mul (st := s6) (e₁ := .reg 6) (e₂ := .reg 2) (e₃ := .reg 7) (e₄ := .reg 3)
    (ev_reg' (v := a) (by simp [s6, s5, s4, s3, s2, s1]))
    (ev_reg (v := u) (by simp [s6, s5, s4, s3, s2, s1, r2]) huw)
    (ev_reg' (v := b) (by simp [s6, s5, s4, s3, s2]))
    (ev_reg (v := v) (by simp [s6, s5, s4, s3, s2, s1, r3]) hvw) hw1
  have hm6 : s6.mem = mem := rfl
  refine runs_start_le ?_
  refine runs_seq_assign_le e6 ?_
  refine runs_seq_assign_le e7 ?_
  refine runs_seq_assign_le e8 ?_
  refine runs_seq_assign_le e9 ?_
  refine runs_seq_assign_le e10 ?_
  refine runs_seq_assign_le e10' ?_
  refine runs_seq_cond_le ec (fun hc => ?_) (fun hc => ?_)
  · -- Edge `j` goes from `u` to `v`: copy the walk.
    have hab : a = u ∧ b = v := by by_contra h; simp [h] at hc
    have hargs : evalArgs w s6 [.reg 5, .reg 8, .reg 10] = some [dst, P, nv + ne + 2] := by
      have a1 : (Expr.reg 5).eval w s6 = some dst :=
        ev_reg (v := dst) (by simp [s6, s5, s4, s3, s2, s1, r5]) hdst
      have a2 : (Expr.reg 8).eval w s6 = some P :=
        ev_reg (v := P) (by simp [s6, s5, s4, s3]) (by omega)
      have a3 : (Expr.reg 10).eval w s6 = some (nv + ne + 2) :=
        ev_reg (v := nv + ne + 2) (by simp [s6]) (by omega)
      simp [evalArgs, a1, a2, a3]
    refine runs_seq_call_le hfc hargs ?_ ⟨dst, P, nv + ne + 2, rfl, by omega, by omega,
      Or.inr (by omega)⟩ ?_
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> omega
    intro v₁ mem₁ pos₁ hpost
    obtain ⟨d', s', l', hargs', -, hcopy0, hother0⟩ := hpost
    simp only [List.cons.injEq, and_true] at hargs'
    obtain ⟨hd', hs', hl'⟩ := hargs'
    subst hd' hs' hl'
    have hcopy : ∀ i < nv + ne + 2, mem₁ (dst + i) = mem (P + i) := hcopy0
    have hother : ∀ x, x < dst ∨ dst + (nv + ne + 2) ≤ x → mem₁ x = mem x := hother0
    refine runs_ret_le (v := 0) (ev_const (by omega))
      (fun bA' E' u' v' j' d' B' emb' h1 h2 => ?_) ?_
    · simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
      have hB : B = B' := graphAt_unique hG h2.1
      subst hB
      have hE : embBC j = emb' j := walkAt_unique hW (h2.2.1 j hj)
      have hstep : composeStep B embBC u v j = embBC j := by
        simp only [composeStep, ← hadef, ← hbdef, hab, and_self, ite_true]
      have hstep' : composeStep B emb' u v j = composeStep B embBC u v j := by
        simp only [composeStep, hE]
      rw [hstep', hstep, ← hE]
      refine ⟨fun i hi => ?_, fun x hx => hother x (by omega)⟩
      rw [hlen] at hi
      show mem₁ (dst + i) = _
      rw [hcopy i (by omega)]
      exact hW i (by rw [hlen]; omega)
    · simp only [Expr.size, argsSize, memCopyContract, composeStepContract, List.getD_cons_succ,
        List.getD_cons_zero]
      rw [← hPdef, hnv, hne]
      omega
  · -- Otherwise write the walk turned around.
    have hab : ¬ (a = u ∧ b = v) := by intro h; simp [h] at hc
    have hargs : evalArgs w s6 [.reg 8, .reg 5] = some [P, dst] := by
      have a1 : (Expr.reg 8).eval w s6 = some P :=
        ev_reg (v := P) (by simp [s6, s5, s4, s3]) (by omega)
      have a2 : (Expr.reg 5).eval w s6 = some dst :=
        ev_reg (v := dst) (by simp [s6, s5, s4, s3, s2, s1, r5]) hdst
      simp [evalArgs, a1, a2]
    have hpre : RevWalkPre s6.mem P dst (embBC j) w := ⟨hW, by omega, hdw, hw1⟩
    refine runs_seq_call_le hfrw hargs ?_ ⟨P, dst, embBC j, rfl, hpre⟩ ?_
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega
    intro v₁ mem₁ pos₁ hpost
    obtain ⟨hR, hother⟩ := hpost _ _ _ rfl hpre
    refine runs_ret_le (v := 0) (ev_const (by omega))
      (fun bA' E' u' v' j' d' B' emb' h1 h2 => ?_) ?_
    · simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
      have hB : B = B' := graphAt_unique hG h2.1
      subst hB
      have hE : embBC j = emb' j := walkAt_unique hW (h2.2.1 j hj)
      have hstep : composeStep B embBC u v j = (embBC j).reverse := by
        simp only [composeStep, ← hadef, ← hbdef]
        rw [ite_eq_right hab]
      have hstep' : composeStep B emb' u v j = composeStep B embBC u v j := by
        simp only [composeStep, hE]
      rw [hstep', hstep, ← hE]
      exact ⟨hR, hother⟩
    · simp only [Expr.size, argsSize, revWalkContract, composeStepContract,
        List.getD_cons_succ, List.getD_cons_zero]
      show _ + (30 * (mem P + mem (P + 1 + mem P)) + 100) + 2 + _ ≤ _
      rw [← hPdef, hnv, hne]
      omega

end MinCostFlow.Spanner
