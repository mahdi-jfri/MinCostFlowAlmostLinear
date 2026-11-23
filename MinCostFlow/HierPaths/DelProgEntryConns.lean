module

public import MinCostFlow.HierPaths.DelProgEntryStart

/-!
# Collecting the ineligible connectors at the Delete entry

With the lost-terminal list complete, the second work list begins just after it. The
connector pass writes the new ineligible bits and keeps both lists for the cursor passes.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Pass the lost list to the connector scan and start an empty second work list. -/
def delEntryConnSetup : Stmt :=
  .seq (.assign 36 (.reg 71))
    (.seq (.assign 37 (.reg 23))
      (.seq (.assign 72 (.reg 23))
        (.seq (.assign 33 (.bin .add (.reg 71) (.reg 23)))
          (.seq (.assign 73 (.reg 33)) (.assign 34 (.const 0))))))

/-- Set up and run the connector work-list pass. -/
def delEntryConns : Stmt := .seq delEntryConnSetup delLostConnPass

theorem delEntryConns_noRand : delEntryConns.NoRand := by
  simp [delEntryConns, delEntryConnSetup, Stmt.NoRand, delLostConnPass_noRand]

/-- Register values after the connector setup. -/
def delConnSetupRegs (R : ℕ → ℕ) (wb len : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    R 36 wb) 37 len) 72 len) 33 (wb + len)) 73 (wb + len)) 34 0

/-- The connector setup changes only registers. -/
theorem delEntryConnSetup_triple {w : ℕ} {p : Program} {wb len : ℕ}
    {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop} (h71 : R 71 = wb) (h23 : R 23 = len)
    (hw : wb + len < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) delEntryConnSetup
      (normalPost fun s => s.regs = delConnSetupRegs R wb len ∧ M s.mem) (fun _ => 22) := by
  let R₁ := Function.update R 36 wb
  let R₂ := Function.update R₁ 37 len
  let R₃ := Function.update R₂ 72 len
  let R₄ := Function.update R₃ 33 (wb + len)
  let R₅ := Function.update R₄ 73 (wb + len)
  have t₁ : Triple w p (fun s => s.regs = R ∧ M s.mem) (.assign 36 (.reg 71))
      (normalPost fun s => s.regs = R₁ ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ hs _ => Expr.eval_reg_of_eq (hs ▸ h71)
  have t₂ : Triple w p (fun s => s.regs = R₁ ∧ M s.mem) (.assign 37 (.reg 23))
      (normalPost fun s => s.regs = R₂ ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ hs _ => Expr.eval_reg_of_eq (by simpa [hs, R₁] using h23)
  have t₃ : Triple w p (fun s => s.regs = R₂ ∧ M s.mem) (.assign 72 (.reg 23))
      (normalPost fun s => s.regs = R₃ ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ hs _ => Expr.eval_reg_of_eq (by simpa [hs, R₁, R₂] using h23)
  have t₄ : Triple w p (fun s => s.regs = R₃ ∧ M s.mem)
      (.assign 33 (.bin .add (.reg 71) (.reg 23)))
      (normalPost fun s => s.regs = R₄ ∧ M s.mem) (fun _ => 4) :=
    triple_assign_exact fun _ hs _ => Expr.eval_add
      (Expr.eval_reg_of_eq (by simpa [hs, R₁, R₂, R₃] using h71))
      (Expr.eval_reg_of_eq (by simpa [hs, R₁, R₂, R₃] using h23)) hw
  have t₅ : Triple w p (fun s => s.regs = R₄ ∧ M s.mem) (.assign 73 (.reg 33))
      (normalPost fun s => s.regs = R₅ ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ hs _ => Expr.eval_reg_of_eq (by simp [hs, R₄])
  have t₆ : Triple w p (fun s => s.regs = R₅ ∧ M s.mem) (.assign 34 (.const 0))
      (normalPost fun s => s.regs = delConnSetupRegs R wb len ∧ M s.mem) (fun _ => 2) :=
    triple_assign_exact fun _ _ _ => Expr.eval_const (Nat.two_pow_pos _)
  exact (Triple.seq_normal_const t₁ (Triple.seq_normal_const t₂
    (Triple.seq_normal_const t₃ (Triple.seq_normal_const t₄ (Triple.seq_normal_const t₅ t₆))))).mono_cost
    (fun _ _ => by decide)

/-- Loss counter writes preserve the length of the original block. -/
theorem HierConcrete.length_encode_afterDelLoss (x : HierConcrete) {e : ℕ}
    (hnew : e ∉ x.ms.st.deleted) : (x.afterDelLoss e).encode.length = x.encode.length := by
  unfold afterDelLoss
  rw [HierConcrete.length_encode_withLoss, x.length_encode_markDeleted hnew]

/-- Run the connector pass after the loss scan, preserving the first work list. -/
theorem delEntryConns_triple {w : ℕ} {p : Program} (x : HierConcrete) {b e h wb : ℕ}
    {R mem0 : ℕ → ℕ}
    (h0 : R 0 = b) (h70 : R 70 = h) (h71 : R 71 = wb)
    (h23 : R 23 = (x.H.A.newLost x.ms.st e).length)
    (hnew : e ∉ x.ms.st.deleted) (hb : b + x.encode.length ≤ wb)
    (hA : x.H.A.Spec x.ms.abs.G x.H.ξ x.H.κ)
    (ht : ∀ t ∈ x.H.A.newLost x.ms.st e, t < x.H.A.C.numTerm)
    (hw : wb + (x.H.A.newLost x.ms.st e).length +
      ((x.H.A.newLost x.ms.st e).flatMap x.H.A.termConns).length < 2 ^ w) :
    let lost := x.H.A.newLost x.ms.st e
    let cb := wb + lost.length
    let cs := x.delWorkConns e
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b (x.afterDelLoss e).encode ∧
      ListAt s.mem wb lost ∧ s.mem = mem0) delEntryConns
      (normalPost fun s => s.regs 0 = b ∧ s.regs 70 = h ∧ s.regs 71 = wb ∧
        s.regs 72 = lost.length ∧ s.regs 73 = cb ∧ s.regs 34 = cs.length ∧
        ListAt s.mem b (x.afterDelConns e).encode ∧ ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → (j < cb ∨ cb + cs.length ≤ j) → s.mem j = mem0 j)
      (fun _ => 99 * (lost.flatMap x.H.A.termConns).length + 104 * lost.length + 30) := by
  dsimp only
  let lost := x.H.A.newLost x.ms.st e
  let cb := wb + lost.length
  let cs := x.delWorkConns e
  let y := x.afterDelLoss e
  let M := fun mem => ListAt mem b y.encode ∧ ListAt mem wb lost ∧ mem = mem0
  let R' := delConnSetupRegs R wb lost.length
  have hy : y.encode.length = x.encode.length := x.length_encode_afterDelLoss hnew
  have hfit : b + y.encode.length ≤ cb := by rw [hy]; omega
  have hcb : cb < 2 ^ w := by change wb + (x.H.A.newLost x.ms.st e).length < 2 ^ w; omega
  have H := delEntryConnSetup_triple (w := w) (p := p) (M := M) h71 h23 hcb
  have HT := delLostConnPass_triple (w := w) (p := p) (R := R') (mem0 := mem0)
    (lost := lost) y (by simpa [R', delConnSetupRegs] using h0)
    (by simp [R', delConnSetupRegs, cb]) (by simp [R', delConnSetupRegs])
    (by simp [R', delConnSetupRegs]) (by simp [R', delConnSetupRegs]) ht
    (fun t ht' c hc => ((hA.mem_termConns t (ht t ht') c).mp hc).1)
    hfit
    (fun j _ => Or.inr (by rw [hy]; omega)) (Or.inl le_rfl) hw hcb
  have HF := Triple.regs_frame (n := 39)
    (show Stmt.WritesBelow 39 delLostConnPass by
      simp [delLostConnPass, delLostConnBody, delTerminalConns, delTermSetup, delCsrSetup,
        delIncidentLoop, forRange, forUp, delConnAt, delConnVisit, delIneligBit, delConnPush,
        Stmt.WritesBelow]) HT R'
  have HF' := (HF.weaken_pre (fun s (hs : s.regs = R' ∧ M s.mem) =>
    ⟨hs, fun j _ => congrFun hs.1 j⟩)).strengthen_post
      (Q' := normalPost fun s => s.regs 0 = b ∧ s.regs 70 = h ∧ s.regs 71 = wb ∧
        s.regs 72 = lost.length ∧ s.regs 73 = cb ∧ s.regs 34 = cs.length ∧
        ListAt s.mem b (x.afterDelConns e).encode ∧ ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → (j < cb ∨ cb + cs.length ≤ j) → s.mem j = mem0 j)
      (fun o s hp => by
        cases o <;> try exact False.elim hp.1
        obtain ⟨⟨h0', _, h34, _, _, hB, hC, hL, hf⟩, hg⟩ := hp
        refine ⟨h0', by simpa [R', delConnSetupRegs, h70] using hg 70 (by decide),
          by simpa [R', delConnSetupRegs, h71] using hg 71 (by decide),
          by simpa [R', delConnSetupRegs] using hg 72 (by decide),
          by simpa [R', delConnSetupRegs, cb] using hg 73 (by decide),
          h34, hB, hL, hC, ?_⟩
        intro j hj
        exact hf j (by rwa [hy]))
  exact (Triple.seq_normal_const H HF').mono_cost (fun _ _ => by
    change 22 + (99 * (lost.flatMap x.H.A.termConns).length + 104 * lost.length + 7) + 1 ≤
      99 * (lost.flatMap x.H.A.termConns).length + 104 * lost.length + 30
    omega)

end MinCostFlow.HierPaths

end
