module

public import MinCostFlow.LinkCut.Prog.MathForestExecHelpers

/-!
# `SafeMem` Invariant and Compound Splay-Statement Safety

Defines `PtrAllowed` and `SafeMem`, proves atomic preservation lemmas for updates to
`nb - 1`, heap addresses `≥ hp0`, and node fields in `1 .. cap`, and verifies memory and
pointer safety for all compound splay blocks (`swapFieldsStmt`, `shiftPtrStmt`,
`addOptPtrStmt`, `combineNumAggStmt`, `pullMinNumStmt`, and `setChildAndParentStmt`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num

section SafeMemInvariant

/-- Allowed pointer targets stored in any `ptrOffs` field of node slots `1 .. cap`:
either null (`0`), newly allocated (`≥ hp0`), or inherited from initial `mem0`. -/
def PtrAllowed (mem0 : ℕ → ℕ) (nb cap hp0 p : ℕ) : Prop :=
  p = 0 ∨ hp0 ≤ p ∨ ∃ y off, 1 ≤ y ∧ y ≤ cap ∧ off ∈ ptrOffs ∧ p = nodeField mem0 nb y off

/-- Memory safety invariant preserved across all splay and LCT tree operations. -/
def SafeMem (mem0 : ℕ → ℕ) (nb cap hp0 : ℕ) (mem : ℕ → ℕ) : Prop :=
  hp0 ≤ mem (nb - 1) ∧
  (∀ a, (a < nb - 1 ∨ (nb ≤ a ∧ a < nb + NODE_STRIDE) ∨
    (nb + NODE_STRIDE * (cap + 1) ≤ a ∧ a < hp0)) → mem a = mem0 a) ∧
  (∀ x, 1 ≤ x → x ≤ cap →
    nodeField mem nb x OFF_LEFT ≤ cap ∧
    nodeField mem nb x OFF_RIGHT ≤ cap ∧
    nodeField mem nb x OFF_PARENT ≤ cap) ∧
  (∀ x off, 1 ≤ x → x ≤ cap → off ∈ ptrOffs →
    PtrAllowed mem0 nb cap hp0 (nodeField mem nb x off))

theorem PtrAllowed.mono_trans {mem0 mem1 : ℕ → ℕ} {nb cap hp0 p : ℕ}
    (hallow : ∀ x off, 1 ≤ x → x ≤ cap → off ∈ ptrOffs →
      PtrAllowed mem0 nb cap hp0 (nodeField mem1 nb x off))
    (hp : PtrAllowed mem1 nb cap hp0 p) :
    PtrAllowed mem0 nb cap hp0 p := by
  rcases hp with rfl | hge | ⟨y, off, hy1, hy2, hoff, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hge)
  · exact hallow y off hy1 hy2 hoff

theorem SafeMem.refl {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ}
    (hhp : hp0 ≤ mem0 (nb - 1))
    (hstr : ∀ x, 1 ≤ x → x ≤ cap →
      nodeField mem0 nb x OFF_LEFT ≤ cap ∧
      nodeField mem0 nb x OFF_RIGHT ≤ cap ∧
      nodeField mem0 nb x OFF_PARENT ≤ cap) :
    SafeMem mem0 nb cap hp0 mem0 :=
  ⟨hhp, fun _ _ => rfl, hstr, fun x off hx1 hx2 hoff =>
    Or.inr (Or.inr ⟨x, off, hx1, hx2, hoff, rfl⟩)⟩

theorem SafeMem.trans {mem0 mem1 mem2 : ℕ → ℕ} {nb cap hp0 : ℕ}
    (h12 : SafeMem mem0 nb cap hp0 mem1) (h23 : SafeMem mem1 nb cap hp0 mem2) :
    SafeMem mem0 nb cap hp0 mem2 :=
  ⟨h23.1,
   fun a ha => (h23.2.1 a ha).trans (h12.2.1 a ha),
   h23.2.2.1,
   fun x off hx1 hx2 hoff => PtrAllowed.mono_trans h12.2.2.2 (h23.2.2.2 x off hx1 hx2 hoff)⟩

theorem SafeMem.of_agree_below_hp {mem0 mem mem' : ℕ → ℕ} {nb cap hp0 hp : ℕ}
    (hs : SafeMem mem0 nb cap hp0 mem)
    (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hhp : hp0 ≤ hp)
    (hag : ∀ a < hp, mem' a = mem a) :
    SafeMem mem0 nb cap hp0 mem' := by
  have hnb1 : nb - 1 < hp := by unfold NODE_STRIDE at harena; omega
  have hfld : ∀ x off, x ≤ cap → off < NODE_STRIDE →
      nodeField mem' nb x off = nodeField mem nb x off := fun x off hx hoff => by
    apply hag
    have hmul : NODE_STRIDE * x + off < NODE_STRIDE * (cap + 1) := by
      unfold NODE_STRIDE at *; nlinarith
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hag _ hnb1]; exact hs.1
  · intro a ha
    have halt : a < hp := by
      rcases ha with h1 | h2 | h3 <;> unfold NODE_STRIDE at * <;> omega
    rw [hag _ halt]; exact hs.2.1 a ha
  · intro x hx1 hx2
    rw [hfld x OFF_LEFT hx2 (by decide), hfld x OFF_RIGHT hx2 (by decide),
      hfld x OFF_PARENT hx2 (by decide)]
    exact hs.2.2.1 x hx1 hx2
  · intro x off hx1 hx2 hoff
    have hoff_lt : off < NODE_STRIDE := by
      simp only [ptrOffs, List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hfld x off hx2 hoff_lt]
    exact hs.2.2.2 x off hx1 hx2 hoff

theorem SafeMem.update_hp {mem0 mem : ℕ → ℕ} {nb cap hp0 v : ℕ}
    (hs : SafeMem mem0 nb cap hp0 mem)
    (hnb : 3 ≤ nb) (hv : hp0 ≤ v) :
    SafeMem mem0 nb cap hp0 (Function.update mem (nb - 1) v) := by
  refine ⟨by simp [hv], fun a ha => ?_, fun x hx1 hx2 => ?_, fun x off hx1 hx2 hoff => ?_⟩
  · have hne : a ≠ nb - 1 := by
      rcases ha with h1 | h2 | h3 <;> unfold NODE_STRIDE at * <;> omega
    simp [Function.update_of_ne hne, hs.2.1 a ha]
  · have hne : ∀ off, nb + NODE_STRIDE * x + off ≠ nb - 1 := fun _ => by
      have : NODE_STRIDE ≤ NODE_STRIDE * x := Nat.le_mul_of_pos_right _ (by omega)
      unfold NODE_STRIDE at *; omega
    simp only [nodeField, Function.update_of_ne (hne _)]
    exact hs.2.2.1 x hx1 hx2
  · have hne : nb + NODE_STRIDE * x + off ≠ nb - 1 := by
      have : NODE_STRIDE ≤ NODE_STRIDE * x := Nat.le_mul_of_pos_right _ (by omega)
      unfold NODE_STRIDE at *; omega
    simp only [nodeField, Function.update_of_ne hne]
    exact hs.2.2.2 x off hx1 hx2 hoff

private theorem nodeAddr_ne_outside {nb cap hp0 x off a : ℕ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap) (hoff : off < NODE_STRIDE)
    (ha : a < nb - 1 ∨ (nb ≤ a ∧ a < nb + NODE_STRIDE) ∨
      (nb + NODE_STRIDE * (cap + 1) ≤ a ∧ a < hp0)) :
    a ≠ nb + NODE_STRIDE * x + off := by
  have hlo : nb + NODE_STRIDE ≤ nb + NODE_STRIDE * x := by
    unfold NODE_STRIDE at *; nlinarith
  have hhi : nb + NODE_STRIDE * x + off < nb + NODE_STRIDE * (cap + 1) := by
    unfold NODE_STRIDE at *; nlinarith
  rcases ha with h1 | h2 | h3 <;> omega

private theorem nodeAddr_inj {nb x₁ off₁ x₂ off₂ : ℕ}
    (ho1 : off₁ < NODE_STRIDE) (ho2 : off₂ < NODE_STRIDE)
    (heq : nb + NODE_STRIDE * x₁ + off₁ = nb + NODE_STRIDE * x₂ + off₂) :
    x₁ = x₂ ∧ off₁ = off₂ := by
  have hx : x₁ = x₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : NODE_STRIDE * (x₁ + 1) ≤ NODE_STRIDE * x₂ :=
        Nat.mul_le_mul_left _ (by omega)
      unfold NODE_STRIDE at *; nlinarith
    · have : NODE_STRIDE * (x₂ + 1) ≤ NODE_STRIDE * x₁ :=
        Nat.mul_le_mul_left _ (by omega)
      unfold NODE_STRIDE at *; nlinarith
  subst hx
  exact ⟨rfl, by omega⟩

theorem SafeMem.update_field {mem0 mem : ℕ → ℕ} {nb cap hp0 x off v : ℕ}
    (hs : SafeMem mem0 nb cap hp0 mem)
    (hnb : 3 ≤ nb) (_harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap) (hoff : off < NODE_STRIDE)
    (hstr : (off = OFF_LEFT ∨ off = OFF_RIGHT ∨ off = OFF_PARENT) → v ≤ cap)
    (hptr : off ∈ ptrOffs → PtrAllowed mem0 nb cap hp0 v) :
    SafeMem mem0 nb cap hp0 (Function.update mem (nb + NODE_STRIDE * x + off) v) := by
  have hmul : NODE_STRIDE ≤ NODE_STRIDE * x := Nat.le_mul_of_pos_right _ hx1
  have hne_hp : nb - 1 ≠ nb + NODE_STRIDE * x + off := by
    unfold NODE_STRIDE at hmul; omega
  refine ⟨by simpa [Function.update_of_ne hne_hp] using hs.1, fun a ha => ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (nodeAddr_ne_outside hx1 hx2 hoff ha)]
    exact hs.2.1 a ha
  · intro y hy1 hy2
    have hupd : ∀ f (hf : f < NODE_STRIDE) (hfold : nodeField mem nb y f ≤ cap)
        (hfstr : f = OFF_LEFT ∨ f = OFF_RIGHT ∨ f = OFF_PARENT),
        nodeField (Function.update mem (nb + NODE_STRIDE * x + off) v) nb y f ≤ cap := by
      intro f hf hfold hfstr
      dsimp only [nodeField]
      by_cases he : nb + NODE_STRIDE * y + f = nb + NODE_STRIDE * x + off
      · rcases nodeAddr_inj hf hoff he with ⟨rfl, rfl⟩
        simp [Function.update_self, hstr hfstr]
      · simpa [nodeField, Function.update_of_ne he] using hfold
    rcases hs.2.2.1 y hy1 hy2 with ⟨hl, hr, hp⟩
    exact ⟨hupd OFF_LEFT (by decide) hl (Or.inl rfl),
      hupd OFF_RIGHT (by decide) hr (Or.inr (Or.inl rfl)),
      hupd OFF_PARENT (by decide) hp (Or.inr (Or.inr rfl))⟩
  · intro y f hy1 hy2 hf
    have hf_lt : f < NODE_STRIDE := by
      simp only [ptrOffs, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    dsimp only [nodeField]
    by_cases he : nb + NODE_STRIDE * y + f = nb + NODE_STRIDE * x + off
    · rcases nodeAddr_inj hf_lt hoff he with ⟨rfl, rfl⟩
      simp [Function.update_self, hptr hf]
    · simp only [Function.update_of_ne he]
      exact hs.2.2.2 y f hy1 hy2 hf

theorem SafeMem.slot0_parent {mem0 mem : ℕ → ℕ} {nb cap hp0 : ℕ}
    (hs : SafeMem mem0 nb cap hp0 mem) (hz0 : nodeField mem0 nb 0 OFF_PARENT = 0) :
    nodeField mem nb 0 OFF_PARENT = 0 := by
  have ha : nb ≤ nb + NODE_STRIDE * 0 + OFF_PARENT ∧
      nb + NODE_STRIDE * 0 + OFF_PARENT < nb + NODE_STRIDE := by
    unfold NODE_STRIDE OFF_PARENT; omega
  simpa [nodeField] using (hs.2.1 _ (Or.inr (Or.inl ha))).trans hz0

end SafeMemInvariant

section CompoundStmtSafe

theorem swapFields_safeExec {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    {ptrReg f1 f2 t1 t2 : ℕ} (hf1 : f1 < NODE_STRIDE) (hf2 : f2 < NODE_STRIDE)
    (hsym : (f1 = OFF_LEFT ∨ f1 = OFF_RIGHT ∨ f1 = OFF_PARENT ↔
        f2 = OFF_LEFT ∨ f2 = OFF_RIGHT ∨ f2 = OFF_PARENT) ∧
      (f1 ∈ ptrOffs ↔ f2 ∈ ptrOffs))
    {fuel : ℕ} {st st' : State} {o : Outcome} {c : ℕ} {x : ℕ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap) (hptr : st.regs ptrReg = nb + NODE_STRIDE * x)
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hex : exec w p ω fuel (swapFieldsStmt ptrReg f1 f2 t1 t2) st = some (o, st', c))
    (ht12 : t1 ≠ t2) (ht1p : t1 ≠ ptrReg) (ht2p : t2 ≠ ptrReg) :
    o = .normal ∧ SafeMem mem0 nb cap hp0 st'.mem ∧
    (∀ r, r ≠ t1 → r ≠ t2 → st'.regs r = st.regs r) := by
  dsimp only [swapFieldsStmt] at hex
  rcases exec_seq_assign_elim hex with ⟨_, v1, _, _, hv1, h2, _⟩
  rcases exec_seq_assign_elim h2 with ⟨_, v2, _, _, hv2, h3, _⟩
  rcases exec_seq_store_elim h3 with ⟨_, a1, val1, _, _, ha1, hval1, h4, _⟩
  rcases exec_store_iff.1 h4 with ⟨_, a2, val2, _, ha2, hval2, rfl, rfl, _⟩
  have hv1_eq : v1 = nodeField st.mem nb x f1 := by
    rw [eval_fieldLoad_some hv1, hptr]; rfl
  have hv2_eq : v2 = nodeField st.mem nb x f2 := by
    have h := eval_fieldLoad_some hv2
    dsimp only at h
    rw [Function.update_of_ne ht1p.symm, hptr] at h
    exact h
  have ha1_eq : a1 = nb + NODE_STRIDE * x + f1 := by
    rcases eval_fieldAddr_some ha1 with ⟨rfl, _⟩
    dsimp only
    rw [Function.update_of_ne ht2p.symm, Function.update_of_ne ht1p.symm, hptr]
  have ha2_eq : a2 = nb + NODE_STRIDE * x + f2 := by
    rcases eval_fieldAddr_some ha2 with ⟨rfl, _⟩
    dsimp only
    rw [Function.update_of_ne ht2p.symm, Function.update_of_ne ht1p.symm, hptr]
  have hval1_eq : val1 = v2 := by
    simp only [Expr.eval, Function.update_self] at hval1
    exact (Option.some.inj hval1).symm
  have hval2_eq : val2 = v1 := by
    simp only [Expr.eval, Function.update_of_ne ht12, Function.update_self] at hval2
    exact (Option.some.inj hval2).symm
  rw [ha1_eq, ha2_eq, hval1_eq, hval2_eq, hv1_eq, hv2_eq]
  have hstr1 : (f1 = OFF_LEFT ∨ f1 = OFF_RIGHT ∨ f1 = OFF_PARENT) →
      nodeField st.mem nb x f2 ≤ cap := fun h => by
    rcases hsym.1.1 h with hL | hR | hP
    · rw [hL]; exact (hs.2.2.1 x hx1 hx2).1
    · rw [hR]; exact (hs.2.2.1 x hx1 hx2).2.1
    · rw [hP]; exact (hs.2.2.1 x hx1 hx2).2.2
  have hptr1 : f1 ∈ ptrOffs → PtrAllowed mem0 nb cap hp0 (nodeField st.mem nb x f2) := fun h =>
    hs.2.2.2 x f2 hx1 hx2 (hsym.2.1 h)
  have hs1 := hs.update_field hnb harena hx1 hx2 hf1 hstr1 hptr1
  have hstr2 : (f2 = OFF_LEFT ∨ f2 = OFF_RIGHT ∨ f2 = OFF_PARENT) →
      nodeField st.mem nb x f1 ≤ cap := fun h => by
    rcases hsym.1.2 h with hL | hR | hP
    · rw [hL]; exact (hs.2.2.1 x hx1 hx2).1
    · rw [hR]; exact (hs.2.2.1 x hx1 hx2).2.1
    · rw [hP]; exact (hs.2.2.1 x hx1 hx2).2.2
  have hptr2 : f2 ∈ ptrOffs → PtrAllowed mem0 nb cap hp0 (nodeField st.mem nb x f1) := fun h =>
    hs.2.2.2 x f1 hx1 hx2 (hsym.2.2 h)
  have hs2 := hs1.update_field hnb harena hx1 hx2 hf2 hstr2 hptr2
  refine ⟨rfl, hs2, fun r hr1 hr2 => ?_⟩
  simp [Function.update_of_ne hr2, Function.update_of_ne hr1]

theorem shiftPtr_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    {isAddExpr : Expr} {valPtrReg tPtrReg LReg hpReg outPtrReg : ℕ}
    (hne_hl : hpReg ≠ LReg) (hne_oh : outPtrReg ≠ hpReg)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c : ℕ}
    (hs : SafeMem mem0 nb cap hp0 st.mem) (hhp : hp0 ≤ st.regs hpReg)
    (hex : exec w p ω fuel (shiftPtrStmt (SplayProcs.atBase spBase) isAddExpr
      valPtrReg tPtrReg LReg hpReg outPtrReg) st = some (o, st', c)) :
    o = .normal ∧ SafeMem mem0 nb cap hp0 st'.mem ∧
    st.regs hpReg ≤ st'.regs hpReg ∧ hp0 ≤ st'.regs outPtrReg ∧
    (∀ r, r ≠ hpReg → r ≠ outPtrReg → st'.regs r = st.regs r) := by
  rcases splayBodies_procs_eq hp_prog with ⟨_, _, hadd, haddc, hsub, _, _, _, _, _⟩
  let sp := SplayProcs.atBase spBase
  dsimp only [shiftPtrStmt] at hex
  rcases exec_cond_elim hex with ⟨f, v, _, _, _, hcond_ex, _⟩
  by_cases hv : v = 0
  · simp only [hv, ↓reduceIte] at hcond_ex
    rcases exec_seq_call_elim hcond_ex with ⟨f1, f1', vs, body, o1, st1, _, _, _, _, hvs, hpb, hrec, hass, _⟩
    have hbody : body = subtractBody (sp.numSub + 1) (sp.numSub + 3) := Option.some.inj (hpb.symm.trans hsub)
    subst hbody
    rcases evalArgs_cons.1 hvs with ⟨_, a1, _, ha1, rfl⟩
    rcases evalArgs_cons.1 ha1 with ⟨_, a2, _, ha2, rfl⟩
    rcases evalArgs_cons.1 ha2 with ⟨vL, a3, hvL, ha3, rfl⟩
    rcases evalArgs_cons.1 ha3 with ⟨vhp, a4, hvhp, ha4, rfl⟩
    rw [evalArgs_nil.1 ha4] at *
    simp only [Expr.eval] at hvL hvhp; cases hvL; cases hvhp
    rcases subtract_exec_safe hp_prog f1' _ _ _ _ hrec with ⟨ho1, hmem1⟩
    simp only [List.getD] at ho1 hmem1
    cases o1 with
    | normal => cases ho1
    | returned u1 =>
        cases ho1
        rcases exec_assign_iff.1 hass with ⟨_, vout, _, he_out, rfl, rfl, _⟩
        have hvout : vout = st.regs hpReg + 2 * st.regs LReg - st.regs LReg := by
          rcases eval_bin_some he_out with ⟨x1, x2, hx1, hx2, _, rfl⟩
          simp only [Expr.eval, Function.update_self, Function.update_of_ne hne_hl.symm] at hx1 hx2
          cases hx1; cases hx2; rfl
        have hmem_s := hs.of_agree_below_hp harena hhp (fun a ha => hmem1 a (Or.inl ha))
        refine ⟨rfl, hmem_s, ?_, ?_, fun r hr1 hr2 => ?_⟩
        · simp [Function.update_of_ne hne_oh.symm, Function.update_self]
        · simp only [Function.update_self, hvout]; omega
        · simp [Function.update_of_ne hr2, Function.update_of_ne hr1]
  · simp only [hv, ↓reduceIte] at hcond_ex
    rcases exec_seq_call_elim hcond_ex with ⟨f1, f1', vs, body, o1, st1, _, _, _, _, hvs, hpb, hrec, hass, _⟩
    have hbody : body = addBody (sp.numAdd + 1) := Option.some.inj (hpb.symm.trans hadd)
    subst hbody
    rcases evalArgs_cons.1 hvs with ⟨_, a1, _, ha1, rfl⟩
    rcases evalArgs_cons.1 ha1 with ⟨_, a2, _, ha2, rfl⟩
    rcases evalArgs_cons.1 ha2 with ⟨vL, a3, hvL, ha3, rfl⟩
    rcases evalArgs_cons.1 ha3 with ⟨vhp, a4, hvhp, ha4, rfl⟩
    rw [evalArgs_nil.1 ha4] at *
    simp only [Expr.eval] at hvL hvhp; cases hvL; cases hvhp
    rcases add_exec_safe haddc f1' _ _ _ _ hrec with ⟨ho1, hmem1⟩
    simp [List.getD] at ho1 hmem1
    cases o1 with
    | normal => cases ho1
    | returned u1 =>
        cases ho1
        rcases exec_assign_iff.1 hass with ⟨_, vout, _, he_out, rfl, rfl, _⟩
        have hvout : vout = st.regs hpReg + st.regs LReg - st.regs LReg := by
          rcases eval_bin_some he_out with ⟨x1, x2, hx1, hx2, _, rfl⟩
          simp only [Expr.eval, Function.update_self, Function.update_of_ne hne_hl.symm] at hx1 hx2
          cases hx1; cases hx2; rfl
        have hmem_s := hs.of_agree_below_hp harena hhp (fun a ha => hmem1 a (Or.inl ha))
        refine ⟨rfl, hmem_s, ?_, ?_, fun r hr1 hr2 => ?_⟩
        · simp [Function.update_of_ne hne_oh.symm, Function.update_self]
        · simp only [Function.update_self, hvout]; omega
        · simp [Function.update_of_ne hr2, Function.update_of_ne hr1]

theorem addOptPtr_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    {p1Reg p2Reg LReg hpReg outReg : ℕ}
    (hne_hl : hpReg ≠ LReg) (hne_oh : outReg ≠ hpReg)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c : ℕ}
    (hs : SafeMem mem0 nb cap hp0 st.mem) (hhp : hp0 ≤ st.regs hpReg)
    (hp1 : PtrAllowed mem0 nb cap hp0 (st.regs p1Reg))
    (hp2 : PtrAllowed mem0 nb cap hp0 (st.regs p2Reg))
    (hex : exec w p ω fuel (addOptPtrStmt (SplayProcs.atBase spBase) p1Reg p2Reg LReg hpReg outReg) st =
      some (o, st', c)) :
    o = .normal ∧ SafeMem mem0 nb cap hp0 st'.mem ∧
    st.regs hpReg ≤ st'.regs hpReg ∧ PtrAllowed mem0 nb cap hp0 (st'.regs outReg) ∧
    (∀ r, r ≠ hpReg → r ≠ outReg → st'.regs r = st.regs r) := by
  rcases splayBodies_procs_eq hp_prog with ⟨_, _, hadd, haddc, _⟩
  let sp := SplayProcs.atBase spBase
  dsimp only [addOptPtrStmt] at hex
  rcases exec_cond_elim hex with ⟨f1, v1, _, _, he1, hcond1, _⟩
  simp only [Expr.eval] at he1; cases he1
  by_cases hv1 : st.regs p1Reg = 0
  · simp only [hv1, ↓reduceIte] at hcond1
    rcases exec_assign_iff.1 hcond1 with ⟨_, vout, _, he_out, rfl, rfl, _⟩
    simp only [Expr.eval] at he_out; cases he_out
    refine ⟨rfl, hs, by simp [Function.update_of_ne hne_oh.symm], ?_,
      fun r _ hr2 => by simp [Function.update_of_ne hr2]⟩
    simpa [Function.update_self] using hp2
  · simp only [hv1, ↓reduceIte] at hcond1
    rcases exec_cond_elim hcond1 with ⟨f2, v2, _, _, he2, hcond2, _⟩
    simp only [Expr.eval] at he2; cases he2
    by_cases hv2 : st.regs p2Reg = 0
    · simp only [hv2, ↓reduceIte] at hcond2
      rcases exec_assign_iff.1 hcond2 with ⟨_, vout, _, he_out, rfl, rfl, _⟩
      simp only [Expr.eval] at he_out; cases he_out
      refine ⟨rfl, hs, by simp [Function.update_of_ne hne_oh.symm], ?_,
        fun r _ hr2 => by simp [Function.update_of_ne hr2]⟩
      simpa [Function.update_self] using hp1
    · simp only [hv2, ↓reduceIte] at hcond2
      rcases exec_seq_call_elim hcond2 with ⟨f3, f3', vs, body, o1, st1, _, _, _, _, hvs, hpb, hrec, hass, _⟩
      have hbody : body = addBody (sp.numAdd + 1) := Option.some.inj (hpb.symm.trans hadd)
      subst hbody
      rcases evalArgs_cons.1 hvs with ⟨_, a1, _, ha1, rfl⟩
      rcases evalArgs_cons.1 ha1 with ⟨_, a2, _, ha2, rfl⟩
      rcases evalArgs_cons.1 ha2 with ⟨vL, a3, hvL, ha3, rfl⟩
      rcases evalArgs_cons.1 ha3 with ⟨vhp, a4, hvhp, ha4, rfl⟩
      rw [evalArgs_nil.1 ha4] at *
      simp only [Expr.eval] at hvL hvhp; cases hvL; cases hvhp
      rcases add_exec_safe haddc f3' _ _ _ _ hrec with ⟨ho1, hmem1⟩
      simp [List.getD] at ho1 hmem1
      cases o1 with
      | normal => cases ho1
      | returned u1 =>
          cases ho1
          rcases exec_assign_iff.1 hass with ⟨_, vout, _, he_out, rfl, rfl, _⟩
          have hvout : vout = st.regs hpReg + st.regs LReg - st.regs LReg := by
            rcases eval_bin_some he_out with ⟨x1, x2, hx1, hx2, _, rfl⟩
            simp only [Expr.eval, Function.update_self, Function.update_of_ne hne_hl.symm] at hx1 hx2
            cases hx1; cases hx2; rfl
          have hmem_s := hs.of_agree_below_hp harena hhp (fun a ha => hmem1 a (Or.inl ha))
          refine ⟨rfl, hmem_s, ?_, ?_, fun r hr1 hr2 => ?_⟩
          · simp [Function.update_of_ne hne_oh.symm, Function.update_self]
          · simp only [Function.update_self, hvout]; exact Or.inr (Or.inl (by omega))
          · simp [Function.update_of_ne hr2, Function.update_of_ne hr1]

theorem combineNumAgg_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ}
    {rHA rVA rFA rLA rHB rVB rFB rLB LReg cmpReg : ℕ}
    (hpw : ([rHA, rVA, rFA, rLA, rHB, rVB, rFB, rLB, cmpReg] : List ℕ).Nodup)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c : ℕ}
    (hva : PtrAllowed mem0 nb cap hp0 (st.regs rVA))
    (hvb : PtrAllowed mem0 nb cap hp0 (st.regs rVB))
    (hex : exec w p ω fuel
      (combineNumAggStmt (SplayProcs.atBase spBase) rHA rVA rFA rLA rHB rVB rFB rLB LReg cmpReg) st =
      some (o, st', c)) :
    o = .normal ∧ st'.mem = st.mem ∧ PtrAllowed mem0 nb cap hp0 (st'.regs rVA) ∧
    (∀ r, r ≠ rHA → r ≠ rVA → r ≠ rFA → r ≠ rLA → r ≠ cmpReg → st'.regs r = st.regs r) := by
  have hne_vb_ha : rVB ≠ rHA := by
    intro heq; simp [List.nodup_cons, heq] at hpw
  have hne_va_fa : rVA ≠ rFA := by
    intro heq; simp [List.nodup_cons, heq] at hpw
  have hne_va_la : rVA ≠ rLA := by
    intro heq; simp [List.nodup_cons, heq] at hpw
  have hne_va_cmp : rVA ≠ cmpReg := by
    intro heq; simp [List.nodup_cons, heq] at hpw
  have hne_cmp_vb : cmpReg ≠ rVB := fun heq => by
    simp [List.nodup_cons, heq] at hpw
  rcases splayBodies_procs_eq hp_prog with ⟨_, _, _, _, _, _, _, _, _, hless, _, _, heq, _⟩
  rcases numReadOnly_mem_eq (w := w) (ω := ω) hp_prog with ⟨hless_ro, heq_ro, _⟩
  let sp := SplayProcs.atBase spBase
  dsimp only [combineNumAggStmt] at hex
  rcases exec_cond_elim hex with ⟨f1, vhb, _, _, he1, hcond1, _⟩
  simp only [Expr.eval] at he1; cases he1
  by_cases h0hb : st.regs rHB = 0
  · simp only [h0hb, ↓reduceIte] at hcond1
    rcases exec_nop_iff.1 hcond1 with ⟨_, rfl, rfl, _⟩
    exact ⟨rfl, rfl, hva, fun _ _ _ _ _ _ => rfl⟩
  · simp only [h0hb, ↓reduceIte] at hcond1
    rcases exec_cond_elim hcond1 with ⟨f2, vha, _, _, he2, hcond2, _⟩
    simp only [Expr.eval] at he2; cases he2
    by_cases h0ha : st.regs rHA = 0
    · simp only [h0ha, ↓reduceIte] at hcond2
      rcases exec_seq_assign_elim hcond2 with ⟨_, _, _, _, _, h_va, _⟩
      rcases exec_seq_assign_elim h_va with ⟨_, v_va, _, _, hv_va, h_fa, _⟩
      rcases exec_seq_assign_elim h_fa with ⟨_, v_fa, _, _, _, h_la, _⟩
      rcases exec_assign_iff.1 h_la with ⟨_, v_la, _, _, rfl, rfl, _⟩
      simp only [Expr.eval, Function.update_of_ne hne_vb_ha] at hv_va; cases hv_va
      refine ⟨rfl, rfl, ?_, fun r hr1 hr2 hr3 hr4 _ => ?_⟩
      · dsimp only
        rw [Function.update_of_ne hne_va_la, Function.update_of_ne hne_va_fa, Function.update_self]
        exact hvb
      · simp [Function.update_of_ne hr4, Function.update_of_ne hr3,
          Function.update_of_ne hr2, Function.update_of_ne hr1]
    · simp only [h0ha, ↓reduceIte] at hcond2
      rcases exec_seq_call_elim hcond2 with ⟨_, _, _, body1, o1, st1, _, _, _, _, _, hpb1, hrec1, hcond3, _⟩
      have hb1 : body1 = lessBody (sp.numLess + 1) (sp.numLess + 2) := Option.some.inj (hpb1.symm.trans hless)
      subst hb1
      have hm1 := hless_ro _ _ _ _ _ hrec1
      rcases exec_cond_elim hcond3 with ⟨_, vcmp1, _, _, hecmp1, hbr3, _⟩
      have hv1_eq : vcmp1 = Outcome.rec 0 (fun u => u) o1 := by
        simp only [Expr.eval, Function.update_self] at hecmp1; exact (Option.some.inj hecmp1).symm
      rw [hv1_eq] at hbr3
      by_cases hvc1 : Outcome.rec 0 (fun u => u) o1 = 0
      · simp only [hvc1, ↓reduceIte] at hbr3
        rcases exec_seq_call_elim hbr3 with ⟨_, _, _, body2, o2, st2, _, _, _, _, _, hpb2, hrec2, hcond4, _⟩
        have hb2 : body2 = equalBody sp.numEqual := Option.some.inj (hpb2.symm.trans heq)
        subst hb2
        have hm2 := heq_ro _ _ _ _ _ hrec2
        rcases exec_cond_elim hcond4 with ⟨_, vcmp2, _, _, hecmp2, hbr4, _⟩
        have hv2_eq : vcmp2 = Outcome.rec 0 (fun u => u) o2 := by
          simp only [Expr.eval, Function.update_self] at hecmp2; exact (Option.some.inj hecmp2).symm
        rw [hv2_eq] at hbr4
        by_cases hvc2 : Outcome.rec 0 (fun u => u) o2 = 0
        · simp only [hvc2, ↓reduceIte] at hbr4
          rcases exec_nop_iff.1 hbr4 with ⟨_, rfl, rfl, _⟩
          refine ⟨rfl, hm2.trans hm1, ?_, fun r _ _ _ _ hrcmp => ?_⟩
          · simp only [Function.update_of_ne hne_va_cmp]; exact hva
          · simp [Function.update_of_ne hrcmp]
        · simp only [hvc2, ↓reduceIte] at hbr4
          rcases exec_assign_iff.1 hbr4 with ⟨_, _, _, _, rfl, rfl, _⟩
          refine ⟨rfl, hm2.trans hm1, ?_, fun r _ _ _ hrla hrcmp => ?_⟩
          · simp only [Function.update_of_ne hne_va_la, Function.update_of_ne hne_va_cmp]; exact hva
          · simp [Function.update_of_ne hrla, Function.update_of_ne hrcmp]
      · simp only [hvc1, ↓reduceIte] at hbr3
        rcases exec_seq_assign_elim hbr3 with ⟨_, v_va, _, _, hv_va, h_fa, _⟩
        rcases exec_seq_assign_elim h_fa with ⟨_, v_fa, _, _, _, h_la, _⟩
        rcases exec_assign_iff.1 h_la with ⟨_, v_la, _, _, rfl, rfl, _⟩
        simp only [Expr.eval, Function.update_of_ne hne_cmp_vb.symm] at hv_va; cases hv_va
        refine ⟨rfl, hm1, ?_, fun r _ hr2 hr3 hr4 hrcmp => ?_⟩
        · dsimp only
          rw [Function.update_of_ne hne_va_la, Function.update_of_ne hne_va_fa, Function.update_self]
          exact hvb
        · simp [Function.update_of_ne hr4, Function.update_of_ne hr3,
            Function.update_of_ne hr2, Function.update_of_ne hrcmp]

theorem pullMinNum_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    {fSelfVal fMinHas fMinVal fMinFirst fMinLast : ℕ}
    (hself_ptr : fSelfVal ∈ ptrOffs)
    (hmh_lt : fMinHas < NODE_STRIDE) (hmh_np : fMinHas ∉ [OFF_LEFT, OFF_RIGHT, OFF_PARENT] ∧ fMinHas ∉ ptrOffs)
    (hmv_lt : fMinVal < NODE_STRIDE) (hmv_nstr : fMinVal ∉ [OFF_LEFT, OFF_RIGHT, OFF_PARENT])
    (hmf_lt : fMinFirst < NODE_STRIDE) (hmf_np : fMinFirst ∉ [OFF_LEFT, OFF_RIGHT, OFF_PARENT] ∧ fMinFirst ∉ ptrOffs)
    (hml_lt : fMinLast < NODE_STRIDE) (hml_np : fMinLast ∉ [OFF_LEFT, OFF_RIGHT, OFF_PARENT] ∧ fMinLast ∉ ptrOffs)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c : ℕ} {x l r : ℕ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap)
    (hptr2 : st.regs 2 = nb + NODE_STRIDE * x)
    (hptr4 : st.regs 4 = nb + NODE_STRIDE * l)
    (hptr6 : st.regs 6 = nb + NODE_STRIDE * r)
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hl_mv : PtrAllowed mem0 nb cap hp0 (nodeField st.mem nb l fMinVal))
    (hr_mv : PtrAllowed mem0 nb cap hp0 (nodeField st.mem nb r fMinVal))
    (hex : exec w p ω fuel
      (pullMinNumStmt (SplayProcs.atBase spBase) 1 2 4 6 fSelfVal fMinHas fMinVal fMinFirst fMinLast) st =
      some (o, st', c)) :
    o = .normal ∧ SafeMem mem0 nb cap hp0 st'.mem ∧
    (∀ reg, reg ∈ [0, 1, 2, 4, 6, 15, 16] → st'.regs reg = st.regs reg) := by
  dsimp only [pullMinNumStmt] at hex
  rcases exec_seq_assign_elim hex with ⟨_, _, _, _, _, hex1, _⟩
  rcases exec_seq_assign_elim hex1 with ⟨_, v8, _, _, hv8, hex2, _⟩
  rcases exec_seq_assign_elim hex2 with ⟨_, _, _, _, _, hex3, _⟩
  rcases exec_seq_assign_elim hex3 with ⟨_, _, _, _, _, hex4, _⟩
  rcases exec_seq_assign_elim hex4 with ⟨_, _, _, _, _, hex5, _⟩
  rcases exec_seq_assign_elim hex5 with ⟨_, v12, _, _, hv12, hex6, _⟩
  rcases exec_seq_assign_elim hex6 with ⟨_, _, _, _, _, hex7, _⟩
  rcases exec_seq_assign_elim hex7 with ⟨_, _, _, _, _, hex8, _⟩
  have hcb_nr : stmtNoRet (combineNumAggStmt (SplayProcs.atBase spBase) 7 8 9 10 11 12 13 14 15 17) = true := by
    simp [stmtNoRet, combineNumAggStmt]
  rcases exec_seq_of_noRet hcb_nr hex8 with ⟨_, st1, _, _, _, hcb1, hex9, _⟩
  have hv8_eq : v8 = nodeField st.mem nb l fMinVal := by
    rw [eval_fieldLoad_some hv8]; simp [Function.update_of_ne, hptr4, nodeField]
  have hv12_eq : v12 = nodeField st.mem nb x fSelfVal := by
    rw [eval_fieldLoad_some hv12]; simp [Function.update_of_ne, hptr2, nodeField]
  have hcb1_ok := combineNumAgg_safeExec hp_prog (mem0 := mem0) (nb := nb) (cap := cap) (hp0 := hp0)
    (by decide : ([7, 8, 9, 10, 11, 12, 13, 14, 17] : List ℕ).Nodup)
    (by rw [hv8_eq]; exact hl_mv)
    (by rw [hv12_eq]; exact hs.2.2.2 x fSelfVal hx1 hx2 hself_ptr) hcb1
  rcases hcb1_ok with ⟨_, hm1, hreg8_1, hregs_1⟩
  rcases exec_seq_assign_elim hex9 with ⟨_, _, _, _, _, hex10, _⟩
  rcases exec_seq_assign_elim hex10 with ⟨_, v12', _, _, hv12', hex11, _⟩
  rcases exec_seq_assign_elim hex11 with ⟨_, _, _, _, _, hex12, _⟩
  rcases exec_seq_assign_elim hex12 with ⟨_, _, _, _, _, hex13, _⟩
  rcases exec_seq_of_noRet hcb_nr hex13 with ⟨_, st2, _, _, _, hcb2, hex14, _⟩
  have hv12'_eq : v12' = nodeField st.mem nb r fMinVal := by
    rw [eval_fieldLoad_some hv12', hm1]
    have hr6' : st1.regs 6 = st.regs 6 := hregs_1 6 (by decide) (by decide) (by decide) (by decide) (by decide)
    simp [Function.update_of_ne, hr6', hptr6, nodeField]
  have hcb2_ok := combineNumAgg_safeExec hp_prog (mem0 := mem0) (nb := nb) (cap := cap) (hp0 := hp0)
    (by decide : ([7, 8, 9, 10, 11, 12, 13, 14, 17] : List ℕ).Nodup)
    (by simpa [Function.update_of_ne] using hreg8_1)
    (by rw [hv12'_eq]; exact hr_mv) hcb2
  rcases hcb2_ok with ⟨_, hm2, hreg8_2, hregs_2⟩
  rcases exec_seq_store_elim hex14 with ⟨_, a1, val1, _, _, ha1, _, hex15, _⟩
  rcases exec_seq_store_elim hex15 with ⟨_, a2, val2, _, _, ha2, hval2, hex16, _⟩
  rcases exec_seq_store_elim hex16 with ⟨_, a3, val3, _, _, ha3, _, hex17, _⟩
  rcases exec_store_iff.1 hex17 with ⟨_, a4, val4, _, ha4, _, rfl, rfl, _⟩
  have hpres_reg : ∀ g, g ∈ [0, 1, 2, 4, 6, 15, 16] → st2.regs g = st.regs g := fun g hg => by
    have hneq : g ≠ 7 ∧ g ≠ 8 ∧ g ≠ 9 ∧ g ≠ 10 ∧ g ≠ 11 ∧ g ≠ 12 ∧ g ≠ 13 ∧ g ≠ 14 ∧ g ≠ 17 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hregs_2 g hneq.1 hneq.2.1 hneq.2.2.1 hneq.2.2.2.1 hneq.2.2.2.2.2.2.2.2]
    simp only [Function.update_of_ne hneq.2.2.2.2.2.2.2.1, Function.update_of_ne hneq.2.2.2.2.2.2.1,
      Function.update_of_ne hneq.2.2.2.2.2.1, Function.update_of_ne hneq.2.2.2.2.1]
    rw [hregs_1 g hneq.1 hneq.2.1 hneq.2.2.1 hneq.2.2.2.1 hneq.2.2.2.2.2.2.2.2]
    simp [Function.update_of_ne hneq.2.2.2.2.2.2.2.1, Function.update_of_ne hneq.2.2.2.2.2.2.1,
      Function.update_of_ne hneq.2.2.2.2.2.1, Function.update_of_ne hneq.2.2.2.2.1,
      Function.update_of_ne hneq.2.2.1, Function.update_of_ne hneq.2.2.2.1,
      Function.update_of_ne hneq.2.1, Function.update_of_ne hneq.1]
  have hreg2_2 := hpres_reg 2 (by simp)
  rw [hptr2] at hreg2_2
  have ha1_eq : a1 = nb + NODE_STRIDE * x + fMinHas := by
    rcases eval_fieldAddr_some ha1 with ⟨rfl, _⟩; rw [hreg2_2]
  have ha2_eq : a2 = nb + NODE_STRIDE * x + fMinVal := by
    rcases eval_fieldAddr_some ha2 with ⟨rfl, _⟩; rw [hreg2_2]
  have ha3_eq : a3 = nb + NODE_STRIDE * x + fMinFirst := by
    rcases eval_fieldAddr_some ha3 with ⟨rfl, _⟩; rw [hreg2_2]
  have ha4_eq : a4 = nb + NODE_STRIDE * x + fMinLast := by
    rcases eval_fieldAddr_some ha4 with ⟨rfl, _⟩; rw [hreg2_2]
  have hval2_eq : val2 = st2.regs 8 := by simp [Expr.eval] at hval2; exact hval2.symm
  rw [ha1_eq, ha2_eq, ha3_eq, ha4_eq, hval2_eq]
  have hs_base : SafeMem mem0 nb cap hp0 st2.mem := by rw [hm2, hm1]; exact hs
  have hs_a := hs_base.update_field (v := val1) hnb harena hx1 hx2 hmh_lt
    (fun h => False.elim (hmh_np.1 (by simpa [List.mem_cons] using h))) (fun h => False.elim (hmh_np.2 h))
  have hs_b := hs_a.update_field (v := st2.regs 8) hnb harena hx1 hx2 hmv_lt
    (fun h => False.elim (hmv_nstr (by simpa [List.mem_cons] using h))) (fun _ => hreg8_2)
  have hs_c := hs_b.update_field (v := val3) hnb harena hx1 hx2 hmf_lt
    (fun h => False.elim (hmf_np.1 (by simpa [List.mem_cons] using h))) (fun h => False.elim (hmf_np.2 h))
  have hs_d := hs_c.update_field (v := val4) hnb harena hx1 hx2 hml_lt
    (fun h => False.elim (hml_np.1 (by simpa [List.mem_cons] using h))) (fun h => False.elim (hml_np.2 h))
  exact ⟨rfl, by dsimp only; exact hs_d, fun reg hreg => by dsimp only; exact hpres_reg reg hreg⟩

theorem setChildAndParent_safeExec {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    {pPtrReg childOff bReg pReg bPtrReg : ℕ}
    (hco : childOff = OFF_LEFT ∨ childOff = OFF_RIGHT)
    (hne_bp : bPtrReg ≠ pReg)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c : ℕ} {pid bv : ℕ}
    (hp1 : 1 ≤ pid) (hp2 : pid ≤ cap) (hbv : bv ≤ cap)
    (hnb0 : st.regs 0 = nb)
    (hptr : st.regs pPtrReg = nb + NODE_STRIDE * pid)
    (hpr : st.regs pReg = pid) (hbr : st.regs bReg = bv)
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hex : exec w p ω fuel (setChildAndParentStmt pPtrReg childOff bReg pReg bPtrReg) st =
      some (o, st', c)) :
    o = .normal ∧ SafeMem mem0 nb cap hp0 st'.mem ∧
    (∀ r, r ≠ bPtrReg → st'.regs r = st.regs r) := by
  dsimp only [setChildAndParentStmt] at hex
  rcases exec_seq_store_elim hex with ⟨_, a1, val1, _, _, ha1, hval1, hcond, _⟩
  have ha1_eq : a1 = nb + NODE_STRIDE * pid + childOff := by
    rcases eval_fieldAddr_some ha1 with ⟨rfl, _⟩; rw [hptr]
  have hval1_eq : val1 = bv := by simp [Expr.eval, hbr] at hval1; exact hval1.symm
  rw [ha1_eq, hval1_eq] at hcond
  have hco_lt : childOff < NODE_STRIDE := by rcases hco with rfl | rfl <;> decide
  have hco_np : childOff ∉ ptrOffs := by rcases hco with rfl | rfl <;> decide
  have hs1 : SafeMem mem0 nb cap hp0
      (Function.update st.mem (nb + NODE_STRIDE * pid + childOff) bv) :=
    hs.update_field hnb harena hp1 hp2 hco_lt (fun _ => hbv) (fun h => False.elim (hco_np h))
  rcases exec_cond_elim hcond with ⟨_, vb, _, _, heb, hbr_ex, _⟩
  simp only [Expr.eval, hbr] at heb; cases heb
  by_cases hbv0 : bv = 0
  · simp only [hbv0, ↓reduceIte] at hbr_ex
    rcases exec_nop_iff.1 hbr_ex with ⟨_, rfl, rfl, _⟩
    exact ⟨rfl, by simpa [hbv0] using hs1, fun _ _ => rfl⟩
  · simp only [hbv0, ↓reduceIte] at hbr_ex
    rcases exec_seq_assign_elim hbr_ex with ⟨_, vbp, _, _, hvbp, hst2, _⟩
    rcases exec_store_iff.1 hst2 with ⟨_, a2, val2, _, ha2, hval2, rfl, rfl, _⟩
    have hvbp_eq : vbp = nb + NODE_STRIDE * bv := by
      rcases eval_nodePtr_some hvbp with ⟨rfl, _⟩; dsimp only; rw [hnb0, hbr]
    have ha2_eq : a2 = nb + NODE_STRIDE * bv + OFF_PARENT := by
      rcases eval_fieldAddr_some ha2 with ⟨rfl, _⟩; dsimp only; rw [Function.update_self, hvbp_eq]
    have hval2_eq : val2 = pid := by
      simp [Expr.eval, Function.update_of_ne hne_bp.symm, hpr] at hval2; exact hval2.symm
    rw [ha2_eq, hval2_eq]
    have hs2 := hs1.update_field hnb harena (Nat.pos_of_ne_zero hbv0) hbv
      (by decide : OFF_PARENT < NODE_STRIDE)
      (fun _ => hp2) (fun h => False.elim ((by decide : OFF_PARENT ∉ ptrOffs) h))
    exact ⟨rfl, hs2, fun r hr => Function.update_of_ne hr _ _⟩

end CompoundStmtSafe

end MinCostFlow.LinkCut.Prog
