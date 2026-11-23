module

public import MinCostFlow.LinkCut.Prog.SplayMem
public import MinCostFlow.Num.ModulePlacement
public import MinCostFlow.Num.WordBounds

namespace MinCostFlow.LinkCut.Prog

/-!
# Evaluation, framing, and subtree surgery helpers for splay steps

Expression evaluation helpers, memory update and arena framing, algebra of `evalMemSteps`, and
the first pure `AuxTree` operations (`revRoot`, `pathTo`, `findSubtree`, `replaceSubtree`).
-/

open WordRAM MinCostFlow.Num

@[expose] public section

def K_REV_NODE : ℕ := 300
def K_APPLY_TAG (L : ℕ) : ℕ := 700 * (L + 1)
def K_PUSH_DOWN (L : ℕ) : ℕ := 2200 * (L + 1)
def K_PULL (L : ℕ) : ℕ := 800 * (L + 1)
def K_PUSH_PATH (L : ℕ) : ℕ := K_PUSH_DOWN L + 120
def K_ROTATE (L : ℕ) : ℕ := 2 * K_PULL L + 450
def K_DOUBLE (L : ℕ) : ℕ := 2 * K_ROTATE L + 200
def K_SPLAY_STEP (L : ℕ) : ℕ := K_DOUBLE L + 2 * K_PUSH_PATH L + 200
def C_SPLAY_CONST (L : ℕ) : ℕ := 6800 * (L + 1)

/-- Static node fields never modified by `revNode`, `applyTag`, `pushDown`, `pull`, or `rotate`. -/
def IsStaticPayloadOff (off : ℕ) : Prop :=
  off = OFF_ISV ∨ off = OFF_HASE ∨ off = OFF_EU ∨ off = OFF_EV ∨ off = OFF_EID

theorem isStaticPayloadOff_ne_struct {off : ℕ} (h : IsStaticPayloadOff off) :
    off < NODE_STRIDE ∧ off ≠ OFF_LEFT ∧ off ≠ OFF_RIGHT ∧ off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR ∧
    off ≠ OFF_REV ∧ off ≠ OFF_VCNT ∧
    off ≠ OFF_DIR ∧ off ≠ OFF_FLOW_PTR ∧ off ≠ OFF_AF_PTR ∧ off ≠ OFF_AB_PTR ∧
    off ≠ OFF_COST_FWD ∧ off ≠ OFF_COST_BWD ∧ off ≠ OFF_CSUM_FWD ∧ off ≠ OFF_CSUM_BWD ∧
    off ≠ OFF_HAS_TAG ∧ off ≠ OFF_TAG_PTR ∧ off ≠ OFF_TAG_NEG ∧
    off ≠ OFF_MIN1_HAS ∧ off ≠ OFF_MIN1_VAL ∧ off ≠ OFF_MIN1_FIRST ∧ off ≠ OFF_MIN1_LAST ∧
    off ≠ OFF_MIN2_HAS ∧ off ≠ OFF_MIN2_VAL ∧ off ≠ OFF_MIN2_FIRST ∧ off ≠ OFF_MIN2_LAST := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

end

/-! ### Expression evaluation helpers -/

public section EvalHelpers

theorem eval_nodePtrExpr {w bReg nReg b n : ℕ} {st : State}
    (hstride : NODE_STRIDE < 2 ^ w)
    (hb : st.regs bReg = b) (hn : st.regs nReg = n)
    (hlt : b + NODE_STRIDE * n < 2 ^ w) :
    (nodePtrExpr bReg nReg).eval w st = some (b + NODE_STRIDE * n) := by
  have h3 : NODE_STRIDE * n < 2 ^ w := by omega
  simp only [nodePtrExpr]
  exact Expr.eval_add (Expr.eval_reg_of_eq hb)
    (Expr.eval_mul (Expr.eval_const hstride) (Expr.eval_reg_of_eq hn) h3) hlt

theorem eval_fieldAddrExpr {w pReg off p : ℕ} {st : State}
    (hp : st.regs pReg = p) (hlt : p + off < 2 ^ w) :
    (fieldAddrExpr pReg off).eval w st = some (p + off) := by
  have hoff : off < 2 ^ w := by omega
  simp only [fieldAddrExpr]
  exact Expr.eval_add (Expr.eval_reg_of_eq hp) (Expr.eval_const hoff) hlt

theorem eval_fieldLoadExpr {w pReg off p : ℕ} {st : State}
    (hp : st.regs pReg = p) (hlt : p + off < 2 ^ w) :
    (fieldLoadExpr pReg off).eval w st = some (st.mem (p + off)) := by
  simp only [fieldLoadExpr]
  exact Expr.eval_load (eval_fieldAddrExpr hp hlt)

theorem nodeAddr_lt_pow {w nodesBase cap x off : ℕ}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hx : x ≤ cap) (hoff : off < NODE_STRIDE) :
    nodesBase + NODE_STRIDE * x + off < 2 ^ w := by
  have hmul : NODE_STRIDE * x + off < NODE_STRIDE * (cap + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have := Nat.mul_le_mul_left NODE_STRIDE hx
    omega
  omega

theorem nodePtr_lt_pow {w nodesBase cap x : ℕ}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w) (hx : x ≤ cap) :
    nodesBase + NODE_STRIDE * x < 2 ^ w :=
  nodeAddr_lt_pow (off := 0) hbase hx (by unfold NODE_STRIDE; decide)

end EvalHelpers

/-! ### Memory update and node-arena framing helpers -/

public section ArenaHelpers

theorem memPreservedOutside_update {lo hi addr val : ℕ} {mem : ℕ → ℕ}
    (hlo : lo ≤ addr) (hhi : addr < hi) :
    MemPreservedOutside lo hi mem (Function.update mem addr val) := by
  intro a ha
  have hne : a ≠ addr := by rcases ha with h | h <;> omega
  exact Function.update_of_ne hne val mem

theorem memPreservedOutside_trans {lo hi : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁₂ : MemPreservedOutside lo hi m₁ m₂)
    (h₂₃ : MemPreservedOutside lo hi m₂ m₃) :
    MemPreservedOutside lo hi m₁ m₃ :=
  fun a ha => (h₂₃ a ha).trans (h₁₂ a ha)

theorem memPreservedOutside_refl (lo hi : ℕ) (m : ℕ → ℕ) :
    MemPreservedOutside lo hi m m :=
  fun _ _ => rfl

theorem memPreservedOutside_weaken {lo₁ hi₁ lo₂ hi₂ : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂)
    (h : MemPreservedOutside lo₁ hi₁ m₁ m₂) :
    MemPreservedOutside lo₂ hi₂ m₁ m₂ :=
  fun a ha => h a (by rcases ha with h1 | h2 <;> [left; right] <;> omega)

theorem nodeField_update_self (mem : ℕ → ℕ) (nodesBase x off val : ℕ) :
    nodeField (Function.update mem (nodesBase + NODE_STRIDE * x + off) val) nodesBase x off = val := by
  simp [nodeField, Function.update_self]

theorem nodeField_update_ne_node {mem : ℕ → ℕ} {nodesBase x y off₁ off₂ val : ℕ}
    (hxy : x ≠ y) (h₁ : off₁ < NODE_STRIDE) (h₂ : off₂ < NODE_STRIDE) :
    nodeField (Function.update mem (nodesBase + NODE_STRIDE * x + off₁) val) nodesBase y off₂ =
      nodeField mem nodesBase y off₂ := by
  simp only [nodeField]
  apply Function.update_of_ne
  unfold NODE_STRIDE at *
  rcases lt_or_gt_of_ne hxy with h | h <;> omega

theorem nodeField_update_ne_off {mem : ℕ → ℕ} {nodesBase x off₁ off₂ val : ℕ}
    (hoff : off₁ ≠ off₂) :
    nodeField (Function.update mem (nodesBase + NODE_STRIDE * x + off₁) val) nodesBase x off₂ =
      nodeField mem nodesBase x off₂ := by
  simp only [nodeField]
  have hne : nodesBase + NODE_STRIDE * x + off₂ ≠ nodesBase + NODE_STRIDE * x + off₁ := by omega
  exact Function.update_of_ne hne val mem

theorem memAgree_slotZero_of_lctFrame {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    (hnb : 1 ≤ nodesBase)
    (h0 : SlotZeroOk mem₁ nodesBase)
    (hfr : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₁ mem₂) :
    SlotZeroOk mem₂ nodesBase := by
  intro off hoff
  have ha : nodesBase + off < nodesBase + NODE_STRIDE := by unfold NODE_STRIDE at hoff ⊢; omega
  have hne : nodesBase + off ≠ nodesBase - 1 := by omega
  rw [hfr.2.2.2.2.2 _ (Or.inl ⟨ha, hne⟩)]
  exact h0 off hoff

theorem memAgree_slotZero_of_preserved {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    (h0 : SlotZeroOk mem₁ nodesBase)
    (hpre : MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1)) mem₁ mem₂) :
    SlotZeroOk mem₂ nodesBase := by
  intro off hoff
  have ha : nodesBase + off < nodesBase + NODE_STRIDE := by omega
  rw [hpre _ (Or.inl ha)]
  exact h0 off hoff

theorem memAgree_treeMemMatch_of_lctFrame {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap t p pp)
    (hfields : ∀ u ∈ t.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (hfr : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₁ mem₂) :
    TreeMemMatch w h L mem₂ nodesBase cap t p pp :=
  memAgree_treeMemMatch_of_nodeList ht hfields hfr.2.2.1
    (fun a ha1 ha2 => hfr.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩))

end ArenaHelpers

/-! ### Algebraic properties of `evalMemSteps` and `IntMinAgg` shifts -/

public section EvalMemStepsAlgebra

theorem fits_zero (h L : ℕ) : Fits h L 0 := by
  have hc : (0 : ℤ) < capacity h L := by exact_mod_cast capacity_pos h L
  unfold Fits; omega

theorem fits_wrap (h L : ℕ) (n : ℤ) : Fits h L (wrap h L n) := by
  unfold wrap Fits signedVal
  have hr := residue_lt h L n
  split_ifs <;> omega

theorem TreeMemMatch.nodeOwn_fits {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ} (ht : TreeMemMatch w h L mem nodesBase cap t p pp) :
    ∀ u ∈ t.toList, ∀ s, nodeOwnRawStep mem nodesBase h L u = some s →
      Fits h L s.flow ∧ Fits h L s.availFwd ∧ Fits h L s.availBwd := by
  induction t generalizing p pp with
  | leaf => intro u hu; simp [AuxTree.toList] at hu
  | node x l r ihl ihr =>
      rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        he1, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      intro u hu s hs
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hlm | rfl) | hrm
      · exact ihl hl u hlm s hs
      · simp only [nodeOwnRawStep] at hs
        by_cases hhe : nodeField mem nodesBase u OFF_HASE = 0
        · simp [hhe] at hs
        · simp only [hhe, ↓reduceIte, Option.some.injEq] at hs
          rcases he1 (by omega) with ⟨pf, paf, pab, _⟩
          rw [← hs]
          refine ⟨intVal_fits pf.2.2.2, ?_, ?_⟩
          · cases decide (nodeField mem nodesBase u OFF_DIR ≠ 0) <;>
              simp [intVal_fits paf.2.2.2, intVal_fits pab.2.2.2]
          · cases decide (nodeField mem nodesBase u OFF_DIR ≠ 0) <;>
              simp [intVal_fits paf.2.2.2, intVal_fits pab.2.2.2]
      · exact ihr hr u hrm s hs

theorem TreeMemMatch.evalMemSteps_fits {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ} (ht : TreeMemMatch w h L mem nodesBase cap t p pp) :
    ∀ flipAcc δAcc, ∀ s ∈ evalMemSteps mem nodesBase h L t flipAcc δAcc,
      Fits h L s.flow ∧ Fits h L s.availFwd ∧ Fits h L s.availBwd := by
  have hown := ht.nodeOwn_fits
  clear ht
  induction t with
  | leaf => intro _ _ s hs; simp [evalMemSteps] at hs
  | node x l r ihl ihr =>
      intro flipAcc δAcc s hs
      have hl' := ihl (fun u hu => hown u (by simp [AuxTree.toList, hu]))
      have hr' := ihr (fun u hu => hown u (by simp [AuxTree.toList, hu]))
      cases flipAcc <;> simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte,
          List.mem_append] at hs
      · rcases hs with (hs | hs) | hs
        · exact hl' _ _ s hs
        · rcases Option.map_eq_some_iff.mp (Option.mem_toList.mp hs) with ⟨s₀, _, rfl⟩
          cases hs₀_f : s₀.fwd <;>
            simp [RawStep.addDeltaMod, hs₀_f, fits_wrap]
        · exact hr' _ _ s hs
      · rcases hs with (hs | hs) | hs
        · exact hr' _ _ s hs
        · rcases Option.map_eq_some_iff.mp (Option.mem_toList.mp hs) with ⟨s₀, _, rfl⟩
          cases hs₀_f : s₀.flip.fwd <;>
            simp [RawStep.addDeltaMod, hs₀_f, fits_wrap]
        · exact hl' _ _ s hs

theorem evalMemSteps_addDeltaMod {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ} (ht : TreeMemMatch w h L mem nodesBase cap t p pp)
    (flipAcc : Bool) (δ₁ δ₂ : ℤ) :
    evalMemSteps mem nodesBase h L t flipAcc (δ₁ + δ₂) =
      (evalMemSteps mem nodesBase h L t flipAcc δ₂).map (fun s => s.addDeltaMod h L δ₁) := by
  have hown := ht.nodeOwn_fits
  clear ht
  induction t generalizing flipAcc δ₁ δ₂ with
  | leaf => simp [evalMemSteps]
  | node x l r ihl ihr =>
      have hl' : ∀ u ∈ l.toList, ∀ s, nodeOwnRawStep mem nodesBase h L u = some s →
          Fits h L s.flow ∧ Fits h L s.availFwd ∧ Fits h L s.availBwd :=
        fun u hu => hown u (by simp [AuxTree.toList, hu])
      have hr' : ∀ u ∈ r.toList, ∀ s, nodeOwnRawStep mem nodesBase h L u = some s →
          Fits h L s.flow ∧ Fits h L s.availFwd ∧ Fits h L s.availBwd :=
        fun u hu => hown u (by simp [AuxTree.toList, hu])
      have hown_map : ((nodeOwnRawStep mem nodesBase h L x).map
          (fun s => (if flipAcc then s.flip else s).addDeltaMod h L (δ₁ + δ₂))).toList =
          (((nodeOwnRawStep mem nodesBase h L x).map
          (fun s => (if flipAcc then s.flip else s).addDeltaMod h L δ₂)).toList).map
          (fun s => s.addDeltaMod h L δ₁) := by
        cases hso : nodeOwnRawStep mem nodesBase h L x with
        | none => rfl
        | some s₀ =>
            cases flipAcc <;>
              simp [RawStep.addDeltaMod_addDeltaMod, add_comm]
      cases flipAcc <;> simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte,
        List.map_append]
      · have hδ : δ₁ + δ₂ + nodeTagInt mem nodesBase h L x =
            δ₁ + (δ₂ + nodeTagInt mem nodesBase h L x) := by ring
        rw [hδ, ihl _ _ _ hl', ihr _ _ _ hr']
        simpa using congrArg (fun m => List.map (fun s => RawStep.addDeltaMod h L s δ₁) (evalMemSteps mem nodesBase h L l (false ^^ revFlag mem nodesBase x) (δ₂ + nodeTagInt mem nodesBase h L x)) ++ m ++ List.map (fun s => RawStep.addDeltaMod h L s δ₁) (evalMemSteps mem nodesBase h L r (false ^^ revFlag mem nodesBase x) (δ₂ + nodeTagInt mem nodesBase h L x))) hown_map
      · have hδ : δ₁ + δ₂ + -nodeTagInt mem nodesBase h L x =
            δ₁ + (δ₂ + -nodeTagInt mem nodesBase h L x) := by ring
        rw [hδ, ihr _ _ _ hr', ihl _ _ _ hl']
        simpa using congrArg (fun m => List.map (fun s => RawStep.addDeltaMod h L s δ₁) (evalMemSteps mem nodesBase h L r (true ^^ revFlag mem nodesBase x) (δ₂ + -nodeTagInt mem nodesBase h L x)) ++ m ++ List.map (fun s => RawStep.addDeltaMod h L s δ₁) (evalMemSteps mem nodesBase h L l (true ^^ revFlag mem nodesBase x) (δ₂ + -nodeTagInt mem nodesBase h L x))) hown_map

theorem evalMemSteps_true_eq {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ} (ht : TreeMemMatch w h L mem nodesBase cap t p pp)
    (δ : ℤ) :
    evalMemSteps mem nodesBase h L t true (-δ) =
      (evalMemSteps mem nodesBase h L t false δ).reverse.map RawStep.flip := by
  induction t generalizing p pp δ with
  | leaf => rfl
  | node x l r ihl ihr =>
      rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      have hl_rev := fun d => ihl hl d
      have hr_rev := fun d => ihr hr d
      have hown_flip : ((nodeOwnRawStep mem nodesBase h L x).map
          (fun s => s.flip.addDeltaMod h L (-δ))).toList =
          (((nodeOwnRawStep mem nodesBase h L x).map
          (fun s => s.addDeltaMod h L δ)).toList).reverse.map RawStep.flip := by
        cases hso : nodeOwnRawStep mem nodesBase h L x with
        | none => rfl
        | some s₀ => simp [RawStep.addDeltaMod_flip]
      cases hr_flag : revFlag mem nodesBase x
      · have he_r : evalMemSteps mem nodesBase h L r true (-δ + -nodeTagInt mem nodesBase h L x) =
            (evalMemSteps mem nodesBase h L r false (δ + nodeTagInt mem nodesBase h L x)).reverse.map RawStep.flip := by
          rw [show -δ + -nodeTagInt mem nodesBase h L x = -(δ + nodeTagInt mem nodesBase h L x) by ring]
          exact hr_rev (δ + nodeTagInt mem nodesBase h L x)
        have he_l : evalMemSteps mem nodesBase h L l true (-δ + -nodeTagInt mem nodesBase h L x) =
            (evalMemSteps mem nodesBase h L l false (δ + nodeTagInt mem nodesBase h L x)).reverse.map RawStep.flip := by
          rw [show -δ + -nodeTagInt mem nodesBase h L x = -(δ + nodeTagInt mem nodesBase h L x) by ring]
          exact hl_rev (δ + nodeTagInt mem nodesBase h L x)
        simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.true_xor, Bool.false_xor,
          hr_flag, Bool.not_false, List.reverse_append, List.map_append, List.append_assoc]
        rw [he_r, hown_flip, he_l]
      · have hr_inv : ∀ d, evalMemSteps mem nodesBase h L r false d =
            (evalMemSteps mem nodesBase h L r true (-d)).reverse.map RawStep.flip := fun d => by
          rw [hr_rev d]
          simp [List.map_reverse, List.map_map, Function.comp_def, RawStep.flip]
        have hl_inv : ∀ d, evalMemSteps mem nodesBase h L l false d =
            (evalMemSteps mem nodesBase h L l true (-d)).reverse.map RawStep.flip := fun d => by
          rw [hl_rev d]
          simp [List.map_reverse, List.map_map, Function.comp_def, RawStep.flip]
        have he_r := hr_inv (-δ + -nodeTagInt mem nodesBase h L x)
        have he_l := hl_inv (-δ + -nodeTagInt mem nodesBase h L x)
        simp only [neg_add, neg_neg] at he_r he_l
        simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.true_xor, Bool.false_xor,
          hr_flag, Bool.not_true, List.reverse_append, List.map_append, List.append_assoc]
        rw [show δ + nodeTagInt mem nodesBase h L x = nodeTagInt mem nodesBase h L x + δ by ring] at he_r he_l ⊢
        rw [he_r, hown_flip, he_l]

theorem listIntMinAgg_shift (xs : List (ℕ × ℤ)) (d : ℤ) :
    listIntMinAgg (xs.map fun p => (p.1, p.2 - d)) =
      let a := listIntMinAgg xs
      { a with val := if a.has then a.val - d else 0 } := by
  induction xs with
  | nil => simp [listIntMinAgg]
  | cons p xs ih =>
      rcases p with ⟨id, v⟩
      rcases hxs : listIntMinAgg xs with ⟨hb, vb, fb, lb⟩
      simp only [List.map_cons, listIntMinAgg, ih, hxs]
      cases hb
      · simp [combineIntMinAgg]
      · simp only [combineIntMinAgg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hlt : vb < v <;> by_cases heq : v = vb
        · omega
        · simp [hlt, sub_lt_sub_iff_right]
        · subst heq; simp
        · have hlt' : ¬ (vb - d < v - d) := by omega
          have heq' : ¬ (v - d = vb - d) := by omega
          simp [hlt, heq, hlt', heq']

theorem stepsShiftFit_map_addDeltaMod_eq {h L : ℕ} {steps : List RawStep} {d δ : ℤ}
    (hfit : StepsShiftFit h L steps d)
    (hmod : δ % (capacity h L : ℤ) = d % (capacity h L : ℤ)) :
    steps.map (fun s => s.addDeltaMod h L δ) = steps.map (fun s => s.addDelta d) := by
  apply List.map_congr_left
  intro s hs
  rcases hfit s hs with ⟨_, _, _, hf_s, haf_s, hab_s⟩
  have h1 : ∀ a : ℤ, (a + δ) % (capacity h L : ℤ) = (a + d) % (capacity h L : ℤ) := fun a => by
    rw [Int.add_emod, hmod, ← Int.add_emod]
  have h2 : ∀ a : ℤ, (a - δ) % (capacity h L : ℤ) = (a - d) % (capacity h L : ℤ) := fun a => by
    rw [Int.sub_emod, hmod, ← Int.sub_emod]
  cases hdir : s.fwd
  · simp only [RawStep.addDeltaMod, RawStep.addDelta, hdir, Bool.false_eq_true, ↓reduceIte] at hf_s haf_s hab_s ⊢
    rw [wrap_congr (h2 s.flow), wrap_of_fits hf_s,
      wrap_congr (h1 s.availFwd), wrap_of_fits haf_s,
      wrap_congr (h2 s.availBwd), wrap_of_fits hab_s]
  · simp only [RawStep.addDeltaMod, RawStep.addDelta, hdir, ↓reduceIte] at hf_s haf_s hab_s ⊢
    rw [wrap_congr (h1 s.flow), wrap_of_fits hf_s,
      wrap_congr (h2 s.availFwd), wrap_of_fits haf_s,
      wrap_congr (h1 s.availBwd), wrap_of_fits hab_s]

theorem TreeMemMatch.min1Has_iff_evalSteps_ne_nil {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {q : AuxTree} {p pp : ℕ} (hq : TreeMemMatch w h L mem nodesBase cap q p pp) :
    (q ≠ .leaf ∧ nodeField mem nodesBase q.rootId OFF_MIN1_HAS = 1) ↔
      evalMemSteps mem nodesBase h L q false 0 ≠ [] := by
  cases q with
  | leaf => simp [evalMemSteps]
  | node x l r =>
      rcases hq with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, hmiff, _⟩, _⟩
      simpa [AuxTree.rootId] using hmiff

end EvalMemStepsAlgebra

/-! ### Pure `AuxTree` operations and subtree surgery -/

public section AuxTreeSurgery

@[expose] def AuxTree.revRoot : AuxTree → AuxTree
  | .leaf => .leaf
  | .node id l r => .node id r l

@[expose] def AuxTree.pathTo (x : ℕ) : AuxTree → List ℕ
  | .leaf => []
  | .node id l r =>
      if x = id then [id]
      else if x ∈ l.toList then id :: l.pathTo x
      else if x ∈ r.toList then id :: r.pathTo x
      else []

@[expose] def AuxTree.depthOf (x : ℕ) : AuxTree → ℕ
  | .leaf => 0
  | .node id l r =>
      if x = id then 0
      else if x ∈ l.toList then l.depthOf x + 1
      else if x ∈ r.toList then r.depthOf x + 1
      else 0

@[expose] def AuxTree.findSubtree (subId : ℕ) : AuxTree → AuxTree
  | .leaf => .leaf
  | .node id l r =>
      if id = subId then .node id l r
      else if subId ∈ l.toList then l.findSubtree subId
      else r.findSubtree subId

@[expose] def AuxTree.parentIn (subId p₀ : ℕ) : AuxTree → ℕ
  | .leaf => p₀
  | .node id l r =>
      if id = subId then p₀
      else if subId ∈ l.toList then l.parentIn subId id
      else r.parentIn subId id

@[expose] def AuxTree.replaceSubtree : AuxTree → ℕ → AuxTree → AuxTree
  | .leaf, _, _ => .leaf
  | .node id l r, subId, s' =>
      if id = subId then s'
      else .node id (l.replaceSubtree subId s') (r.replaceSubtree subId s')

theorem AuxTree.revRoot_rootId (t : AuxTree) : t.revRoot.rootId = t.rootId := by
  cases t <;> rfl

theorem AuxTree.revRoot_countNodes (t : AuxTree) : t.revRoot.countNodes = t.countNodes := by
  cases t <;> simp [revRoot, countNodes]; omega

theorem AuxTree.revRoot_toList_perm (t : AuxTree) : t.revRoot.toList.Perm t.toList := by
  cases t with
  | leaf => rfl
  | node id l r =>
      simp only [revRoot, toList, List.append_assoc]
      apply List.Perm.trans List.perm_append_comm
      rw [List.append_assoc]
      apply List.Perm.trans List.perm_append_comm
      rw [List.append_assoc]
      exact List.Perm.append_left l.toList List.perm_append_comm

theorem AuxTree.revRoot_treeSize (vSize : ℕ → ℕ) (t : AuxTree) :
    t.revRoot.treeSize vSize = t.treeSize vSize := by
  cases t <;> simp [revRoot, treeSize]; omega

theorem AuxTree.revRoot_treePhi (vSize : ℕ → ℕ) (t : AuxTree) :
    t.revRoot.treePhi vSize = t.treePhi vSize := by
  cases t with
  | leaf => rfl
  | node id l r =>
      have hsz : 1 + r.treeSize vSize + l.treeSize vSize + vSize id =
          1 + l.treeSize vSize + r.treeSize vSize + vSize id := by omega
      have hrank : (AuxTree.node id r l).rank vSize = (AuxTree.node id l r).rank vSize := by
        simp only [AuxTree.rank, AuxTree.treeSize, hsz]
      simp [revRoot, treePhi, hrank]; omega

theorem AuxTree.evalInorder_agree (rev₁ rev₂ : ℕ → Bool) (t : AuxTree) (b : Bool)
    (heq : ∀ u ∈ t.toList, rev₁ u = rev₂ u) :
    t.evalInorder rev₁ b = t.evalInorder rev₂ b := by
  induction t generalizing b with
  | leaf => rfl
  | node y l r ihl ihr =>
      have hy := heq y (by simp [toList])
      have hl : ∀ u ∈ l.toList, rev₁ u = rev₂ u := fun u hu => heq u (by simp [toList, hu])
      have hr : ∀ u ∈ r.toList, rev₁ u = rev₂ u := fun u hu => heq u (by simp [toList, hu])
      cases b <;> simp only [evalInorder, hy, ihl _ hl, ihr _ hr]

theorem AuxTree.revRoot_evalInorder_false (id : ℕ) (l r : AuxTree) (rev : ℕ → Bool)
    (hid_l : id ∉ l.toList) (hid_r : id ∉ r.toList) :
    (AuxTree.node id r l).evalInorder (fun u => if u = id then !rev u else rev u) false =
      ((AuxTree.node id l r).evalInorder rev false).reverse := by
  have hl : ∀ b, l.evalInorder (fun u => if u = id then !rev u else rev u) b = l.evalInorder rev b :=
    fun b => l.evalInorder_agree _ rev b fun u hu => by
      have hne : u ≠ id := fun h => by subst h; exact hid_l hu
      simp [hne]
  have hr : ∀ b, r.evalInorder (fun u => if u = id then !rev u else rev u) b = r.evalInorder rev b :=
    fun b => r.evalInorder_agree _ rev b fun u hu => by
      have hne : u ≠ id := fun h => by subst h; exact hid_r hu
      simp [hne]
  simp only [evalInorder, ↓reduceIte, hl, hr, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc]
  cases rev id <;> simp [AuxTree.evalInorder_true]

theorem AuxTree.revRoot_depthOf (t : AuxTree) (x : ℕ) (hnd : t.toList.Nodup) :
    t.revRoot.depthOf x = t.depthOf x := by
  cases t with
  | leaf => rfl
  | node id l r =>
      simp only [toList, List.nodup_append] at hnd
      rcases hnd with ⟨_, _, hdisj⟩
      simp only [revRoot, depthOf]
      by_cases hxeq : x = id
      · simp [hxeq]
      · by_cases hxl : x ∈ l.toList
        · have hxr : x ∉ r.toList := fun hr => hdisj x (List.mem_append_left _ hxl) x hr rfl
          simp [hxeq, hxl, hxr]
        · by_cases hxr : x ∈ r.toList <;> simp [hxeq, hxl, hxr]

theorem AuxTree.revRoot_pathTo (t : AuxTree) (x : ℕ) (hnd : t.toList.Nodup) :
    t.revRoot.pathTo x = t.pathTo x := by
  cases t with
  | leaf => rfl
  | node id l r =>
      simp only [toList, List.nodup_append] at hnd
      rcases hnd with ⟨_, _, hdisj⟩
      simp only [revRoot, pathTo]
      by_cases hxeq : x = id
      · simp [hxeq]
      · by_cases hxl : x ∈ l.toList
        · have hxr : x ∉ r.toList := fun hr => hdisj x (List.mem_append_left _ hxl) x hr rfl
          simp [hxeq, hxl, hxr]
        · by_cases hxr : x ∈ r.toList <;> simp [hxeq, hxl, hxr]

theorem AuxTree.mem_pathTo {x u : ℕ} {t : AuxTree} (hu : u ∈ t.pathTo x) : u ∈ t.toList := by
  induction t with
  | leaf => simp [pathTo] at hu
  | node id l r ihl ihr =>
      simp only [pathTo] at hu
      split_ifs at hu with h1 h2 h3
      · simp only [List.mem_singleton] at hu; subst hu; simp [toList]
      · rcases List.mem_cons.1 hu with rfl | hu'
        · simp [toList]
        · simp [toList, ihl hu']
      · rcases List.mem_cons.1 hu with rfl | hu'
        · simp [toList]
        · simp [toList, ihr hu']
      · contradiction

theorem AuxTree.length_pathTo {x : ℕ} {t : AuxTree} (hx : x ∈ t.toList) :
    (t.pathTo x).length = t.depthOf x + 1 := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      simp only [toList, List.mem_append, List.mem_singleton] at hx
      simp only [pathTo, depthOf]
      by_cases heq : x = id
      · simp [heq]
      · by_cases hxl : x ∈ l.toList
        · simp [heq, hxl, ihl hxl]
        · have hxr : x ∈ r.toList := by rcases hx with (hl | rfl) | hr <;> [contradiction; contradiction; exact hr]
          simp [heq, hxl, hxr, ihr hxr]

theorem AuxTree.self_mem_pathTo {x : ℕ} {t : AuxTree} (hx : x ∈ t.toList) :
    x ∈ t.pathTo x := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      simp only [toList, List.mem_append, List.mem_singleton] at hx
      simp only [pathTo]
      by_cases heq : x = id
      · simp [heq]
      · by_cases hxl : x ∈ l.toList
        · simp [heq, hxl, ihl hxl]
        · have hxr : x ∈ r.toList := by rcases hx with (hl | rfl) | hr <;> [contradiction; contradiction; exact hr]
          simp [heq, hxl, hxr, ihr hxr]

theorem AuxTree.findSubtree_mem_toList {subId : ℕ} {t : AuxTree}
    (hmem : subId ∈ t.toList) :
    t.findSubtree subId ≠ .leaf ∧ (t.findSubtree subId).rootId = subId := by
  induction t with
  | leaf => simp [toList] at hmem
  | node id l r ihl ihr =>
      simp only [findSubtree]
      by_cases heq : id = subId
      · subst heq; simp [rootId]
      · by_cases hnl : subId ∈ l.toList
        · simp only [heq, hnl, ↓reduceIte]; exact ihl hnl
        · have hnr : subId ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hmem
            rcases hmem with (hl | rfl) | hr <;> [contradiction; exact absurd rfl heq; exact hr]
          simp only [heq, hnl, ↓reduceIte]; exact ihr hnr

theorem AuxTree.findSubtree_subset {subId u : ℕ} {t : AuxTree}
    (hu : u ∈ (t.findSubtree subId).toList) : u ∈ t.toList := by
  induction t with
  | leaf => simp [findSubtree, toList] at hu
  | node id l r ihl ihr =>
      simp only [findSubtree] at hu
      split_ifs at hu with h1 h2
      · exact hu
      · simp [toList, ihl hu]
      · simp [toList, ihr hu]

theorem AuxTree.findSubtree_match {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p₀ pp₀ subId : ℕ}
    (ht : TreeMemMatch w h L mem nodesBase cap t p₀ pp₀)
    (hsub : subId ∈ t.toList) :
    TreeMemMatch w h L mem nodesBase cap (t.findSubtree subId) (t.parentIn subId p₀)
      (if t.rootId = subId then pp₀ else 0) := by
  induction t generalizing p₀ pp₀ with
  | leaf => simp [AuxTree.toList] at hsub
  | node id l r ihl ihr =>
      simp only [AuxTree.findSubtree, AuxTree.parentIn, AuxTree.rootId]
      by_cases heq : id = subId
      · simpa [heq] using ht
      · rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
        by_cases hnl : subId ∈ l.toList
        · have h0 : (if l.rootId = subId then (0 : ℕ) else 0) = 0 := by split_ifs <;> rfl
          simpa [heq, hnl, h0] using ihl hl hnl
        · have hnr : subId ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hsub
            rcases hsub with (h1 | rfl) | h2 <;> [exact absurd h1 hnl; exact absurd rfl heq; exact h2]
          have h0 : (if r.rootId = subId then (0 : ℕ) else 0) = 0 := by split_ifs <;> rfl
          simpa [heq, hnl, h0] using ihr hr hnr

theorem AuxTree.parentIn_eq_nodeField {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p₀ pp₀ subId : ℕ}
    (ht : TreeMemMatch w h L mem nodesBase cap t p₀ pp₀)
    (hsub : subId ∈ t.toList) :
    nodeField mem nodesBase subId OFF_PARENT = t.parentIn subId p₀ := by
  have hm := AuxTree.findSubtree_match ht hsub
  rcases AuxTree.findSubtree_mem_toList hsub with ⟨hne, hr⟩
  cases hs : t.findSubtree subId with
  | leaf => contradiction
  | node y sl sr =>
      rw [hs] at hr hm
      dsimp only [AuxTree.rootId] at hr
      subst hr
      exact hm.2.2.2.2.1

theorem AuxTree.replaceSubtree_not_mem {subId : ℕ} {s' t : AuxTree}
    (hnin : subId ∉ t.toList) : t.replaceSubtree subId s' = t := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      have hne : id ≠ subId := fun h => hnin (by subst h; simp [toList])
      simp only [replaceSubtree, hne, ↓reduceIte]
      rw [ihl (fun h => hnin (by simp [toList, h])), ihr (fun h => hnin (by simp [toList, h]))]

end AuxTreeSurgery
end MinCostFlow.LinkCut.Prog
