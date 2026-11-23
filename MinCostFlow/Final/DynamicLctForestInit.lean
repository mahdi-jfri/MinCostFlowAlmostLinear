module

public import MinCostFlow.LinkCut.Prog.LctForestImplements
import Mathlib.Tactic

/-!
# Runtime-parameterized dynamic LCT wrappers: layout, space bounds, and `init`

`lctForestBodies h L P b0` embeds `L` and `P` as compile-time constants
(`lctForestBodies_ne_of_limbs_ne`). Because the inner link-cut procedures
(`findRoot`, `link`, `cut`, `pathAdd`, `pathMin`, `pathSum`, `expose`, `reroot`,
`copyWords`, `splayBodies`) read `L` and `P` from the arena header (`LCT_HDR_L`,
`LCT_HDR_P`), this file builds fixed wrappers (`dynLctForestBodies`) independent of
`(L, P)`, establishes polynomial space bounds on `lctArenaWords` and `lctForestOpSpace`,
and proves `dynLctInitWrap_runs`.
-/

@[expose] public section

namespace MinCostFlow.Final

open WordRAM MinCostFlow.Num MinCostFlow.Rounding MinCostFlow.IPM.Machine
open MinCostFlow.LinkCut.Prog

section Obstruction

/-- Distinct limb counts produce distinct `lctForestBodies` instruction lists, so a single fixed
solver program cannot directly contain `lctForestBodies h L P b0` for two different `L`. -/
theorem lctForestBodies_ne_of_limbs_ne {h L₁ L₂ P₁ P₂ b0 : ℕ} (hne : L₁ ≠ L₂) :
    lctForestBodies h L₁ P₁ b0 ≠ lctForestBodies h L₂ P₂ b0 := by
  intro heq
  have h1 := congrArg (fun l : List Stmt => l[1]?) heq
  simp only [lctForestBodies, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at h1
  have hc := congrArg
    (fun s => match s with
      | .seq (.call _ _ [_, _, _, _, _, .bin _ _ (.const k), _, _, _]) _ => k
      | _ => 0) h1
  simp only [lctLinkWrap] at hc
  omega

end Obstruction

section DynamicWrappers

/-- Dynamic `init` wrapper (`args = [n, L, P, heap]`): calls `lctInitBody 0 0` on `[n, heap]`,
then stores `(L, P)` into `LCT_HDR_L` and `LCT_HDR_P`. -/
def dynLctInitWrap (lp : LctProcs) : Stmt :=
  .call 4 lp.init [.reg 0, .reg 3] ;;
  .store (.bin .add (.reg 3) (.const LCT_HDR_L)) (.reg 1) ;;
  .store (.bin .add (.reg 3) (.const LCT_HDR_P)) (.reg 2) ;;
  .ret (.reg 4)

/-- Dynamic `link` wrapper (`args = [b, a, heap]`): reads `L` from `mem[b + LCT_HDR_L]`
and passes block pointers `a + 3`, `a + 3 + L`, `a + 3 + 2 * L`, `a + 3 + 3 * L` to `lp.link`. -/
def dynLctLinkWrap (lp : LctProcs) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))) ;;
  .assign 11 (.bin .add (.reg 1) (.const 3)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 10)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 10)) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 10)) ;;
  .call 3 lp.link [.reg 0, .load (.bin .add (.reg 1) (.const 1)),
    .load (.bin .add (.reg 1) (.const 2)), .load (.reg 1),
    .reg 11, .reg 12, .reg 13, .reg 14, .reg 2] ;;
  .ret (.reg 3)

/-- Dynamic `lctWrapTail` reading answer word count `A` from register `rA`. -/
def dynLctWrapTail (lp : LctProcs) (rh rA : ℕ) (q : Stmt) : Stmt :=
  .assign 20 (.bin .add (.reg rh) (.reg rA)) ;;
  .call 21 lp.findRoot [.reg 0, .reg 1, .reg 20] ;;
  .assign 22 (.load (.reg 20)) ;;
  q ;;
  .call 25 lp.copyWords [.reg 21, .reg rh, .reg rA] ;;
  .call 24 lp.cut [.reg 0, .reg 22, .reg 22, .reg 23] ;;
  .ret (.reg 24)

/-- Dynamic `lctWrapBody` returning at once when `u = v`. -/
def dynLctWrapBody (lp : LctProcs) (rh rA : ℕ) (q : Stmt) : Stmt :=
  .cond (.bin .eq (.reg 1) (.reg 2)) (.ret (.reg rh)) (dynLctWrapTail lp rh rA q)

/-- Dynamic `pathAdd` wrapper (`args = [b, u, v, a, heap]`). -/
def dynLctPathAddWrap (lp : LctProcs) : Stmt :=
  .cond (.bin .eq (.reg 1) (.reg 2)) (.ret (.reg 4))
    (.assign 19 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))) ;;
     .call 26 lp.copyWords [.reg 3, .reg 4, .reg 19] ;;
     dynLctWrapTail lp 4 19
       (.call 23 lp.pathAdd [.reg 0, .reg 1, .reg 2, .reg 4, .const 0, .reg 21]))

/-- Dynamic `pathMin` wrapper (`args = [b, u, v, hp]`), answer width `2 * L + 4`. -/
def dynLctPathMinWrap (lp : LctProcs) : Stmt :=
  .assign 18 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))) ;;
  .assign 19 (.bin .add (.bin .mul (.const 2) (.reg 18)) (.const 4)) ;;
  dynLctWrapBody lp 3 19 (.call 23 lp.pathMin [.reg 0, .reg 1, .reg 2, .reg 21])

/-- Dynamic `pathSum` wrapper (`args = [b, u, v, hp]`), answer width `L`. -/
def dynLctPathSumWrap (lp : LctProcs) : Stmt :=
  .assign 19 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))) ;;
  dynLctWrapBody lp 3 19 (.call 23 lp.pathSum [.reg 0, .reg 1, .reg 2, .reg 21])

/-- Complete fixed dynamic-forest module independent of `(L, P)`. -/
def dynLctForestBodies (h b0 : ℕ) : List Stmt :=
  let lp := LctProcs.atBase (b0 + 5)
  [dynLctInitWrap lp, dynLctLinkWrap lp, dynLctPathAddWrap lp, dynLctPathMinWrap lp,
    dynLctPathSumWrap lp] ++ lctBodies h 0 0 (b0 + 5)

theorem dynLctForestBodies_noRand (h b0 : ℕ) :
    ∀ s ∈ dynLctForestBodies h b0, s.NoRand := by
  intro s hs
  simp only [dynLctForestBodies, List.cons_append, List.mem_cons, List.nil_append] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | hs
  · simp [dynLctInitWrap, Stmt.NoRand]
  · simp [dynLctLinkWrap, Stmt.NoRand]
  · simp [dynLctPathAddWrap, dynLctWrapTail, Stmt.NoRand]
  · simp [dynLctPathMinWrap, dynLctWrapBody, dynLctWrapTail, Stmt.NoRand]
  · simp [dynLctPathSumWrap, dynLctWrapBody, dynLctWrapTail, Stmt.NoRand]
  · exact lctBodies_noRand h 0 0 (b0 + 5) s hs

theorem dynLctForestBodies_procs {p : Program} {h b0 : ℕ}
    (hp : p.HasAt b0 (dynLctForestBodies h b0)) :
    let lp := LctProcs.atBase (b0 + 5)
    p.procs[b0]? = some (dynLctInitWrap lp) ∧
    p.procs[b0 + 1]? = some (dynLctLinkWrap lp) ∧
    p.procs[b0 + 2]? = some (dynLctPathAddWrap lp) ∧
    p.procs[b0 + 3]? = some (dynLctPathMinWrap lp) ∧
    p.procs[b0 + 4]? = some (dynLctPathSumWrap lp) ∧
    p.HasAt (b0 + 5) (lctBodies h 0 0 (b0 + 5)) := by
  have hf := hasAt_append_left hp
  have g : ∀ i (hi : i < 5), _ := fun i hi => hf i (by simpa using hi)
  exact ⟨by simpa using g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
    g 4 (by decide), by simpa using hasAt_append_right hp⟩

theorem dynLctBaseOk {w h L P b0 : ℕ} {p : Program} (hh : 0 < h)
    (hw : 2 * h + 2 ≤ w) (hL : L < 2 ^ w) (hP : P < 2 ^ w)
    (hp : p.HasAt (b0 + 5) (lctBodies h 0 0 (b0 + 5))) :
    LctBaseOk w h L P p (LctProcs.atBase (b0 + 5)) := by
  have hb0 := lctBaseOk_of_hasAt hh hw (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)) hp
  exact ⟨hh, hw, hL, hP, hb0.splay_hasAt, hb0.splay_ok, hb0.copyWords_ok⟩

end DynamicWrappers

section PolynomialBounds

/-- Linear space bound on link-cut initialization. -/
theorem lctArenaWords_bound (n : ℕ) : lctArenaWords (n + 1) + 10 ≤ 128 * (n + 2) := by
  unfold lctArenaWords LCT_HDR_SIZE NODE_STRIDE lctCap
  omega

/-- Polynomial (`(L + 1) * (N + 2)^2`) bound on `lctForestOpSpace`. -/
theorem lctForestOpSpace_bound (L N : ℕ) :
    lctForestOpSpace L N ≤ 2000000 * (L + 1) * (N + 2) ^ 2 := by
  have hlog : Nat.log 2 (N + 2) + 1 ≤ N + 2 := by
    have hh : Nat.log 2 (N + 2) < N + 2 :=
      Nat.log_lt_of_lt_pow (by omega) Nat.lt_two_pow_self
    omega
  have hKs : K_SPLAY_STEP L ≤ 9200 * (L + 1) := by
    unfold K_SPLAY_STEP K_DOUBLE K_PUSH_PATH K_ROTATE K_PUSH_DOWN K_PULL; omega
  have hCh : C_HEAVY L ≤ 8200 * (L + 1) := c_heavy_le L
  have hPhi : lctPhiBound L N ≤ 34800 * (L + 1) * (N + 2) ^ 2 := by
    unfold lctPhiBound
    have h1 : 2 * (K_SPLAY_STEP L + C_HEAVY L) ≤ 34800 * (L + 1) := by omega
    have h2 : N * (Nat.log 2 (N + 2) + 1) ≤ (N + 2) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul (by omega) hlog
    calc 2 * (K_SPLAY_STEP L + C_HEAVY L) * N * (Nat.log 2 (N + 2) + 1)
        = (2 * (K_SPLAY_STEP L + C_HEAVY L)) * (N * (Nat.log 2 (N + 2) + 1)) := by
            simp only [Nat.mul_assoc]
      _ ≤ (34800 * (L + 1)) * (N + 2) ^ 2 := Nat.mul_le_mul h1 h2
  set B := (L + 1) * (N + 2) ^ 2
  have hPhi' : lctPhiBound L N ≤ 34800 * B := by
    calc lctPhiBound L N ≤ (34800 * (L + 1)) * (N + 2) ^ 2 := hPhi
      _ = 34800 * B := Nat.mul_assoc _ _ _
  have hN2 : N + 2 ≤ (N + 2) ^ 2 := by
    rw [sq]; exact Nat.le_mul_of_pos_left _ (by omega)
  have h2_ge1 : 1 ≤ (N + 2) ^ 2 := Nat.le_trans (by omega) hN2
  have hOp : lctForestOpSpace L N =
      lctPhiBound L N + 1000000 * (L + 1) * (Nat.log 2 (N + 2) + 1) + 7000 * (L + 1) * (N + 2) +
        (100 * L + 1000) := by
    unfold lctForestOpSpace
    exact Nat.add_assoc _ _ _
  have hT2 : 1000000 * (L + 1) * (Nat.log 2 (N + 2) + 1) ≤ 1000000 * B := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hlog.trans hN2))
  have hT3 : 7000 * (L + 1) * (N + 2) ≤ 7000 * B := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hN2)
  have hT4 : 100 * L + 1000 ≤ 1000 * B := by
    have h4a : 100 * L + 1000 ≤ 1000 * (L + 1) := by
      rw [Nat.mul_add]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right L (by decide)) 1000
    have h4b : 1000 * (L + 1) ≤ 1000 * ((L + 1) * (N + 2) ^ 2) :=
      Nat.mul_le_mul_left 1000 (Nat.le_mul_of_pos_right _ h2_ge1)
    exact h4a.trans h4b
  rw [hOp]
  have hSum :
      lctPhiBound L N + 1000000 * (L + 1) * (Nat.log 2 (N + 2) + 1) + 7000 * (L + 1) * (N + 2) +
        (100 * L + 1000) ≤
      34800 * B + 1000000 * B + 7000 * B + 1000 * B :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hPhi' hT2) hT3) hT4
  have hCoef : 34800 * B + 1000000 * B + 7000 * B + 1000 * B ≤ 2000000 * B := by
    rw [← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right B (by decide)
  calc lctPhiBound L N + 1000000 * (L + 1) * (Nat.log 2 (N + 2) + 1) + 7000 * (L + 1) * (N + 2) +
        (100 * L + 1000) ≤ 34800 * B + 1000000 * B + 7000 * B + 1000 * B := hSum
    _ ≤ 2000000 * B := hCoef
    _ = 2000000 * (L + 1) * (N + 2) ^ 2 := (Nat.mul_assoc _ _ _).symm

end PolynomialBounds

section InitLift

private theorem evalMemSteps_eq_nil_of_hase_zero {mem : ℕ → ℕ} {nb h L : ℕ}
    (t : AuxTree) (ht : ∀ u ∈ t.toList, nodeField mem nb u OFF_HASE = 0)
    (flipAcc : Bool) (δAcc : ℤ) :
    evalMemSteps mem nb h L t flipAcc δAcc = [] := by
  induction t generalizing flipAcc δAcc with
  | leaf => rfl
  | node x l r ihl ihr =>
      have hx : nodeField mem nb x OFF_HASE = 0 := ht x (by simp [AuxTree.toList])
      have hown : nodeOwnRawStep mem nb h L x = none := by simp [nodeOwnRawStep, hx]
      have hl : ∀ u ∈ l.toList, nodeField mem nb u OFF_HASE = 0 := fun u hu =>
        ht u (by simp [AuxTree.toList, hu])
      have hr : ∀ u ∈ r.toList, nodeField mem nb u OFF_HASE = 0 := fun u hu =>
        ht u (by simp [AuxTree.toList, hu])
      simp [evalMemSteps, hown, ihl hl, ihr hr]

private theorem treeMemMatch_empty_lift {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {nb cap parentId pparVal : ℕ} (t : AuxTree)
    (ht0 : TreeMemMatch w h 0 mem₁ nb cap t parentId pparVal)
    (hmem : ∀ u ≤ cap, ∀ off < NODE_STRIDE, nodeField mem₂ nb u off = nodeField mem₁ nb u off)
    (hHase0 : ∀ u ∈ t.toList, nodeField mem₁ nb u OFF_HASE = 0)
    (hPtr0 : ∀ u ∈ t.toList, ∀ off ∈ ptrOffs, nodeField mem₁ nb u off = 0)
    (htSub : ∀ u ∈ t.toList, u ≤ cap) :
    TreeMemMatch w h L mem₂ nb cap t parentId pparVal := by
  induction t generalizing parentId pparVal with
  | leaf => trivial
  | node x l r ihl ihr =>
      rcases ht0 with ⟨hx1, hx2, hL, hR, hP, hPP, hRev, hIsv, hHe, hSum, hDir, hHasTag, hTagNeg,
        hEu, hEv, hEid, hEdge1, hEdge0, hC1, hC2, hTag1, hTag0, hM1, hM2, hM1p, hM0p, hAgg, htl, htr⟩
      have hx_mem : x ∈ (AuxTree.node x l r).toList := by simp [AuxTree.toList]
      have hl_list : ∀ u ∈ l.toList, u ∈ (AuxTree.node x l r).toList := fun u hu => by
        simp [AuxTree.toList, hu]
      have hr_list : ∀ u ∈ r.toList, u ∈ (AuxTree.node x l r).toList := fun u hu => by
        simp [AuxTree.toList, hu]
      have hfn : ∀ off < NODE_STRIDE, nodeField mem₂ nb x off = nodeField mem₁ nb x off :=
        hmem x hx2
      have hxHase : nodeField mem₁ nb x OFF_HASE = 0 := hHase0 x hx_mem
      have hxSteps0 : evalMemSteps mem₁ nb h 0 (.node x l r) false 0 = [] :=
        evalMemSteps_eq_nil_of_hase_zero _ hHase0 false 0
      have hxStepsL : evalMemSteps mem₂ nb h L (.node x l r) false 0 = [] :=
        evalMemSteps_eq_nil_of_hase_zero _ (fun u hu => by
          rw [hmem u (htSub u hu) OFF_HASE (by decide)]
          exact hHase0 u hu) false 0
      have hM1zero : nodeField mem₁ nb x OFF_MIN1_HAS = 0 := by
        have iff0 := hAgg.2.2.2.1
        rw [hxSteps0] at iff0
        by_contra hne
        have h1 : nodeField mem₁ nb x OFF_MIN1_HAS = 1 := by omega
        exact (iff0.mp h1) rfl
      have hTagZero : nodeField mem₁ nb x OFF_HAS_TAG = 0 := by
        by_contra hne
        have h1 : nodeField mem₁ nb x OFF_HAS_TAG = 1 := by omega
        rcases (hTag1 h1).2.1 with ⟨hl_ne, hl_m⟩ | ⟨hr_ne, hr_m⟩
        · cases l with
          | leaf => exact hl_ne rfl
          | node xl ll rl =>
              dsimp only [TreeMemMatch] at htl
              obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hAgg_l, _⟩ := htl
              have hm1_l := hAgg_l.2.2.2.1
              have hls0 : evalMemSteps mem₁ nb h 0 (.node xl ll rl) false 0 = [] :=
                evalMemSteps_eq_nil_of_hase_zero _ (fun u hu => hHase0 u (hl_list u hu)) false 0
              rw [hls0] at hm1_l
              exact (hm1_l.mp hl_m) rfl
        · cases r with
          | leaf => exact hr_ne rfl
          | node xr lr rr =>
              dsimp only [TreeMemMatch] at htr
              obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hAgg_r, _⟩ := htr
              have hm1_r := hAgg_r.2.2.2.1
              have hrs0 : evalMemSteps mem₁ nb h 0 (.node xr lr rr) false 0 = [] :=
                evalMemSteps_eq_nil_of_hase_zero _ (fun u hu => hHase0 u (hr_list u hu)) false 0
              rw [hrs0] at hm1_r
              exact (hm1_r.mp hr_m) rfl
      have hcf0 : nodeField mem₁ nb x OFF_CSUM_FWD = 0 := hPtr0 x hx_mem OFF_CSUM_FWD (by simp [ptrOffs])
      have hcb0 : nodeField mem₁ nb x OFF_CSUM_BWD = 0 := hPtr0 x hx_mem OFF_CSUM_BWD (by simp [ptrOffs])
      have hm1v0 : nodeField mem₁ nb x OFF_MIN1_VAL = 0 := (hM0p hM1zero).1
      have hm2v0 : nodeField mem₁ nb x OFF_MIN2_VAL = 0 := (hM0p hM1zero).2.2.2.1
      have hrev_eq : ∀ u ∈ (AuxTree.node x l r).toList,
          nodeField mem₂ nb u OFF_REV = nodeField mem₁ nb u OFF_REV := fun u hu =>
        hmem u (htSub u hu) OFF_REV (by decide)
      have hisv_eq : ∀ u ∈ (AuxTree.node x l r).evalInorder (revFlag mem₁ nb) false,
          nodeField mem₂ nb u OFF_ISV = nodeField mem₁ nb u OFF_ISV := fun u hu =>
        hmem u (htSub u (((AuxTree.node x l r).evalInorder_perm (revFlag mem₁ nb) false).mem_iff.mp hu))
          OFF_ISV (by decide)
      refine ⟨hx1, hx2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfn OFF_LEFT (by decide)]; exact hL
      · rw [hfn OFF_RIGHT (by decide)]; exact hR
      · rw [hfn OFF_PARENT (by decide)]; exact hP
      · rw [hfn OFF_PPAR (by decide)]; exact hPP
      · rw [hfn OFF_REV (by decide)]; exact hRev
      · rw [hfn OFF_ISV (by decide)]; exact hIsv
      · rw [hfn OFF_HASE (by decide)]; exact hHe
      · rw [hfn OFF_ISV (by decide), hfn OFF_HASE (by decide)]; exact hSum
      · rw [hfn OFF_DIR (by decide)]; exact hDir
      · rw [hfn OFF_HAS_TAG (by decide)]; exact hHasTag
      · rw [hfn OFF_TAG_NEG (by decide)]; exact hTagNeg
      · rw [hfn OFF_EU (by decide)]; exact hEu
      · rw [hfn OFF_EV (by decide)]; exact hEv
      · rw [hfn OFF_EID (by decide)]; exact hEid
      · intro hh1; rw [hfn OFF_HASE (by decide)] at hh1; omega
      · intro _; simpa [hfn OFF_DIR (by decide), hfn OFF_FLOW_PTR (by decide),
          hfn OFF_AF_PTR (by decide), hfn OFF_AB_PTR (by decide),
          hfn OFF_COST_FWD (by decide), hfn OFF_COST_BWD (by decide)] using hEdge0 hxHase
      · left; rw [hfn OFF_CSUM_FWD (by decide)]; exact hcf0
      · left; rw [hfn OFF_CSUM_BWD (by decide)]; exact hcb0
      · intro ht1; rw [hfn OFF_HAS_TAG (by decide)] at ht1; omega
      · intro _; simpa [hfn OFF_TAG_PTR (by decide), hfn OFF_TAG_NEG (by decide)] using hTag0 hTagZero
      · rw [hfn OFF_MIN1_HAS (by decide)]; exact hM1
      · rw [hfn OFF_MIN2_HAS (by decide), hfn OFF_MIN1_HAS (by decide)]; exact hM2
      · intro hm1; rw [hfn OFF_MIN1_HAS (by decide)] at hm1; omega
      · intro _; simpa [hfn OFF_MIN1_VAL (by decide), hfn OFF_MIN1_FIRST (by decide),
          hfn OFF_MIN1_LAST (by decide), hfn OFF_MIN2_VAL (by decide),
          hfn OFF_MIN2_FIRST (by decide), hfn OFF_MIN2_LAST (by decide)] using hM0p hM1zero
      · dsimp only
        rw [hxStepsL]
        have hvc : nodeField mem₂ nb x OFF_VCNT =
            listVcnt mem₂ nb ((AuxTree.node x l r).evalInorder (revFlag mem₂ nb) false) := by
          rw [hfn OFF_VCNT (by decide), hAgg.1,
            evalInorder_agree_of_list hrev_eq false, listVcnt_agree_of_mem hisv_eq]
        have hm1_has : nodeField mem₂ nb x OFF_MIN1_HAS = 0 := by
          rw [hfn OFF_MIN1_HAS (by decide)]; exact hM1zero
        have hm2_has : nodeField mem₂ nb x OFF_MIN2_HAS = 0 := by
          rw [hfn OFF_MIN2_HAS (by decide), hM2]; exact hM1zero
        refine ⟨hvc, ?_, ?_, ?_, ?_, ?_⟩
        · simp [optIntVal, hfn OFF_CSUM_FWD (by decide), hcf0, listRawCost, wrap_of_fits (fits_zero h L)]
        · simp [optIntVal, hfn OFF_CSUM_BWD (by decide), hcb0, listRawCost, wrap_of_fits (fits_zero h L)]
        · simp [hm1_has]
        · have hAgg1 := hAgg.2.2.2.2.1
          rw [hxSteps0] at hAgg1
          have h1f := (hM0p hM1zero).2.1
          have h1l := (hM0p hM1zero).2.2.1
          simp [nodeIntMinAgg1, optIntVal, listIntMinAgg, hm1_has,
            hfn OFF_MIN1_VAL (by decide), hm1v0, hfn OFF_MIN1_FIRST (by decide), h1f,
            hfn OFF_MIN1_LAST (by decide), h1l]
        · have h2f := (hM0p hM1zero).2.2.2.2.1
          have h2l := (hM0p hM1zero).2.2.2.2.2
          simp [nodeIntMinAgg2, optIntVal, listIntMinAgg, hm2_has,
            hfn OFF_MIN2_VAL (by decide), hm2v0, hfn OFF_MIN2_FIRST (by decide), h2f,
            hfn OFF_MIN2_LAST (by decide), h2l]
      · exact ihl htl (fun u hu => hHase0 u (hl_list u hu))
          (fun u hu off hoff => hPtr0 u (hl_list u hu) off hoff)
          (fun u hu => htSub u (hl_list u hu))
      · exact ihr htr (fun u hu => hHase0 u (hr_list u hu))
          (fun u hu off hoff => hPtr0 u (hr_list u hu) off hoff)
          (fun u hu => htSub u (hr_list u hu))

private theorem lctMemRep_empty_set_LP {w h L P b n : ℕ} {x : LctConc} {mem₁ : ℕ → ℕ}
    (hrep : LctMemRep w h 0 0 b (MathForest.empty n) x mem₁)
    (hfoot_lt : ∀ a, lctFoot b x a → a < lctArenaHi b (lctCap n)) :
    let mem₂ := Function.update (Function.update mem₁ (b + LCT_HDR_L) L) (b + LCT_HDR_P) P
    LctMemRep w h L P b (MathForest.empty n) x mem₂ := by
  dsimp only
  set mem₂ := Function.update (Function.update mem₁ (b + LCT_HDR_L) L) (b + LCT_HDR_P) P
  rcases hrep with ⟨hh, hw, hval, _, hxn, hhi_ar, hhi_pos, hhi_ft, hregs, hN, hCAP, hL0, hP0,
    hhp_lo, hhp_hi, hhp_w, hedge_snd, hedge_all, hfc, hfree_ok, hslot0, hperm_trees, htrees_ok,
    hv_ok, _, haux_ok, hsub_ok, hptr_ok⟩
  have hmem_above : ∀ a, b + LCT_HDR_SIZE ≤ a → mem₂ a = mem₁ a := fun a ha => by
    have hL3 : b + LCT_HDR_L ≠ a := by unfold LCT_HDR_L LCT_HDR_SIZE at *; omega
    have hP4 : b + LCT_HDR_P ≠ a := by unfold LCT_HDR_P LCT_HDR_SIZE at *; omega
    dsimp only [mem₂]
    rw [Function.update_of_ne hP4.symm, Function.update_of_ne hL3.symm]
  have hnf_eq : ∀ u off, nodeField mem₂ (lctNodesBase b) u off =
      nodeField mem₁ (lctNodesBase b) u off := fun u off =>
    hmem_above _ (by unfold lctNodesBase LCT_HDR_SIZE; omega)
  have hedge_nil : x.edgeMap = [] := by
    have hlen := hedge_snd.length_eq
    simp only [List.length_map, MathForest.empty, List.length_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  have hfree_all : ∀ ed, n + 1 ≤ ed → ed ≤ lctCap n → ed ∈ x.freeEdges := fun ed h1 h2 => by
    have hmem : ed ∈ ((x.edgeMap.map Prod.fst) ++ x.freeEdges) := by
      have hem : (MathForest.empty n).n = n := rfl
      rw [hem] at hedge_all
      rw [hedge_all.mem_iff, List.mem_map]
      refine ⟨ed - (n + 1), List.mem_range.mpr ?_, ?_⟩
      · unfold lctCap at h2; omega
      · omega
    simpa [hedge_nil] using hmem
  have hv_ok' : VertexNodeOk mem₁ (lctNodesBase b) n := hv_ok
  have hHase0 : ∀ u ≤ lctCap n, nodeField mem₁ (lctNodesBase b) u OFF_HASE = 0 := fun u hu => by
    by_cases hu0 : u = 0
    · subst hu0; exact hslot0 OFF_HASE (by decide)
    · by_cases hun : u ≤ n
      · rw [show u = u - 1 + 1 by omega]
        exact (hv_ok' (u - 1) (by omega)).2
      · exact (hfree_ok u (hfree_all u (by omega) hu)).2.2.2.2.2
  have hPtr0 : ∀ u ≤ lctCap n, ∀ off ∈ ptrOffs, nodeField mem₁ (lctNodesBase b) u off = 0 := by
    intro u hu off hoff
    rcases hptr_ok u (hxn ▸ hu) off hoff with hz | ⟨ha1, _, hft⟩
    · exact hz
    · exfalso
      have hlt := hfoot_lt (nodeField mem₁ (lctNodesBase b) u off)
        (hft _ le_rfl (by omega))
      rw [hxn] at ha1
      change lctArenaHi b (lctCap n) ≤ _ at ha1
      omega
  have hagree_nb : MemAgreeOn (lctNodesBase b) (lctArenaHi b (lctCap n)) mem₁ mem₂ :=
    fun a ha _ => (hmem_above a (by unfold lctNodesBase at ha; exact ha)).symm
  have hfree_eq : mem₂ (b + LCT_HDR_FREE) = mem₁ (b + LCT_HDR_FREE) := by
    have h1 : b + LCT_HDR_P ≠ b + LCT_HDR_FREE := by unfold LCT_HDR_P LCT_HDR_FREE; omega
    have h2 : b + LCT_HDR_L ≠ b + LCT_HDR_FREE := by unfold LCT_HDR_L LCT_HDR_FREE; omega
    dsimp only [mem₂]; rw [Function.update_of_ne h1.symm, Function.update_of_ne h2.symm]
  have haux_eq : lctAuxParent mem₂ (lctNodesBase b) (lctCap n) =
      lctAuxParent mem₁ (lctNodesBase b) (lctCap n) := by
    funext u
    exact lctAuxParent_agree
      (fun a ha1 ha2 => hagree_nb a ha1 (by simpa [lctArenaHi] using ha2)) u
  have hrev_eq : ∀ u, revFlag mem₂ (lctNodesBase b) u = revFlag mem₁ (lctNodesBase b) u := fun u => by
    simp [revFlag, hnf_eq]
  have hp_val : mem₂ (b + LCT_HDR_P) = P := by simp [mem₂]
  have hl_val : mem₂ (b + LCT_HDR_L) = L := by
    have hne : b + LCT_HDR_P ≠ b + LCT_HDR_L := by unfold LCT_HDR_P LCT_HDR_L; omega
    simp [mem₂, Function.update_of_ne hne.symm]
  have hN_val : mem₂ (b + LCT_HDR_N) = (MathForest.empty n).n := by
    have h1 : b + LCT_HDR_P ≠ b + LCT_HDR_N := by unfold LCT_HDR_P LCT_HDR_N; omega
    have h2 : b + LCT_HDR_L ≠ b + LCT_HDR_N := by unfold LCT_HDR_L LCT_HDR_N; omega
    simpa [mem₂, Function.update_of_ne h1.symm, Function.update_of_ne h2.symm] using hN
  have hCAP_val : mem₂ (b + LCT_HDR_CAP) = lctCap (MathForest.empty n).n := by
    have h1 : b + LCT_HDR_P ≠ b + LCT_HDR_CAP := by unfold LCT_HDR_P LCT_HDR_CAP; omega
    have h2 : b + LCT_HDR_L ≠ b + LCT_HDR_CAP := by unfold LCT_HDR_L LCT_HDR_CAP; omega
    simpa [mem₂, Function.update_of_ne h1.symm, Function.update_of_ne h2.symm] using hCAP
  have hHP_eq : mem₂ (b + LCT_HDR_HP) = mem₁ (b + LCT_HDR_HP) := by
    have h1 : b + LCT_HDR_P ≠ b + LCT_HDR_HP := by unfold LCT_HDR_P LCT_HDR_HP; omega
    have h2 : b + LCT_HDR_L ≠ b + LCT_HDR_HP := by unfold LCT_HDR_L LCT_HDR_HP; omega
    dsimp only [mem₂]; rw [Function.update_of_ne h1.symm, Function.update_of_ne h2.symm]
  refine ⟨hh, hw, hval, fun e he => by simp [MathForest.empty] at he, hxn, hhi_ar, hhi_pos,
    hhi_ft, hregs, hN_val, hCAP_val, hl_val, hp_val, hHP_eq ▸ hhp_lo, hHP_eq ▸ hhp_hi,
    hHP_eq ▸ hhp_w, hedge_snd, hedge_all, ?_, ?_, ?_, hperm_trees, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfree_eq]
    exact (freeSlotChain_agree (fun ed _ => (hnf_eq ed OFF_EU).symm)).mp hfc
  · intro ed hed
    simpa only [hnf_eq] using hfree_ok ed hed
  · intro off hoff
    rw [hmem_above _ (by unfold lctNodesBase LCT_HDR_SIZE; omega)]
    exact hslot0 off hoff
  · intro t ht
    obtain ⟨htne, hppw, htm0⟩ := htrees_ok t ht
    have ht_le : ∀ u ∈ t.toList, u ≤ lctCap n := fun u hu => by
      have hm := hperm_trees.mem_iff.mp (List.mem_flatMap.mpr ⟨t, ht, hu⟩)
      rcases List.mem_map.mp hm with ⟨k, hk, rfl⟩
      rw [List.mem_range] at hk
      dsimp only [MathForest.empty] at hk
      unfold lctCap at hk ⊢; omega
    refine ⟨htne, by simpa only [hnf_eq] using hppw, ?_⟩
    rw [hnf_eq]
    exact treeMemMatch_empty_lift t htm0 (fun u _ off _ => hnf_eq u off)
      (fun u hu => hHase0 u (ht_le u hu))
      (fun u hu off hoff => hPtr0 u (ht_le u hu) off hoff) ht_le
  · intro v hv; simpa only [hnf_eq] using hv_ok v hv
  · intro p hp; rw [hedge_nil] at hp; cases hp
  · intro t ht
    obtain ⟨hseq, hpp, hcat⟩ := haux_ok t ht
    have hrev_fun : revFlag mem₂ (lctNodesBase b) = revFlag mem₁ (lctNodesBase b) := funext hrev_eq
    simpa only [hnf_eq, hrev_fun] using And.intro hseq (And.intro hpp hcat)
  · simpa only [LctSubdivOk, MathForest.empty, haux_eq] using hsub_ok
  · intro u hu off hoff
    have hz : nodeField mem₂ (lctNodesBase b) u off = 0 := by
      rw [hnf_eq]; exact hPtr0 u (by rw [hxn] at hu; exact hu) off hoff
    exact Or.inl hz

private theorem lctPhi_le_of_phi0 {L b n : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hmem : ∀ a, lctNodesBase b ≤ a → a < lctArenaHi b (lctCap n) → mem₂ a = mem₁ a) :
    lctPhi L mem₂ b n ≤ 46 * (L + 1) * lctPhi 0 mem₁ b n := by
  have hag : MemAgreeOn (lctNodesBase b) (lctArenaHi b (lctCap n)) mem₁ mem₂ := fun a ha1 ha2 =>
    (hmem a ha1 ha2).symm
  rw [lctPhi_agree (L := L) hag]
  have hK0 : 200 ≤ K_SPLAY_STEP 0 := by unfold K_SPLAY_STEP; omega
  have hKL : K_SPLAY_STEP L ≤ 9200 * (L + 1) := by
    unfold K_SPLAY_STEP K_DOUBLE K_PUSH_PATH K_ROTATE K_PUSH_DOWN K_PULL; omega
  have hC0 : 500 ≤ C_HEAVY 0 := by unfold C_HEAVY; omega
  have hCL : C_HEAVY L ≤ 8200 * (L + 1) := c_heavy_le L
  have hKmul : K_SPLAY_STEP L ≤ 46 * (L + 1) * K_SPLAY_STEP 0 := by
    have := Nat.mul_le_mul_left (46 * (L + 1)) hK0
    omega
  have hCmul : C_HEAVY L ≤ 46 * (L + 1) * C_HEAVY 0 := by
    have := Nat.mul_le_mul_left (46 * (L + 1)) hC0
    omega
  unfold lctPhi splayMemPhi
  have h1 := Nat.mul_le_mul_right ((auxRootIds mem₁ (lctNodesBase b) (lctCap n)).map
    fun r => (readAuxTree mem₁ (lctNodesBase b) (lctCap n) (lctCap n) r).treePhi
      (lctVSize mem₁ (lctNodesBase b) (lctCap n))).sum hKmul
  have h2 := Nat.mul_le_mul_right (lctHeavyCount mem₁ (lctNodesBase b) (lctCap n)) hCmul
  calc K_SPLAY_STEP L * _ + C_HEAVY L * _
      ≤ 46 * (L + 1) * K_SPLAY_STEP 0 * _ + 46 * (L + 1) * C_HEAVY 0 * _ := Nat.add_le_add h1 h2
    _ = 46 * (L + 1) * (K_SPLAY_STEP 0 * _ + C_HEAVY 0 * _) := by ring

/-- Running `dynLctInitWrap lp` on `[n, L, P, heap]` initializes `MathForest.empty n` with
`LCT_HDR_L = L` and `LCT_HDR_P = P`, cost `≤ 100000 * (L + 1) * (n + 1)`, and space
`lctArenaWords n`. -/
theorem dynLctInitWrap_runs {w h L P n heap pos : ℕ} (p : Program) (lp : LctProcs)
    (mem₀ : ℕ → ℕ) (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (_hL : L < 2 ^ w) (_hP : P < 2 ^ w)
    (hinit_eq : p.procs[lp.init]? = some (lctInitBody 0 0))
    (hz₀ : ZeroFrom mem₀ heap) (hb_w : heap + lctArenaWords n < 2 ^ w) (ω : ℕ → Bool) :
    ∃ hp' st' c x,
      Runs w p ω (dynLctInitWrap lp) (startState [n, L, P, heap] mem₀ pos) (.returned hp') st' c ∧
      LctMemRep w h L P heap (MathForest.empty n) x st'.mem ∧
      (lctDSRep w h L P).Respects (fun _ => False) heap (lctArenaWords n) mem₀ hp' heap x
        st'.mem ∧
      c + lctPhi L st'.mem heap n ≤ 100000 * (L + 1) * (n + 1) := by
  have hw4 : 4 ≤ w := by omega
  have h16_w : 16 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw4
  have h0w : 0 < 2 ^ w := by omega
  have h3w : LCT_HDR_L < 2 ^ w := by unfold LCT_HDR_L; omega
  have h4w : LCT_HDR_P < 2 ^ w := by unfold LCT_HDR_P; omega
  have harena_eq := lctArenaWords_eq heap n
  have hb3_lt : heap + LCT_HDR_L < heap + lctArenaWords n := by
    unfold lctArenaWords LCT_HDR_SIZE LCT_HDR_L; omega
  have hb4_lt : heap + LCT_HDR_P < heap + lctArenaWords n := by
    unfold lctArenaWords LCT_HDR_SIZE LCT_HDR_P; omega
  have hb3_w : heap + LCT_HDR_L < 2 ^ w := by omega
  have hb4_w : heap + LCT_HDR_P < 2 ^ w := by omega
  obtain ⟨o, st₁, c₁, x, hrun₁, ho, hrep₁, hresp₁, hc₁⟩ :=
    lctInit_runs (n := n) (b := heap) (L := 0) (P := 0) p mem₀ pos hh hw h0w h0w hz₀ hb_w ω
  let st : State := startState [n, L, P, heap] mem₀ pos
  let regs₁ := Function.update st.regs 4 o.value
  have hcall : Runs w p ω (.call 4 lp.init [.reg 0, .reg 3]) st .normal
      { st₁ with regs := regs₁ } (2 + c₁ + 1) :=
    runs_call_iff.mpr ⟨[n, heap], lctInitBody 0 0, o, st₁, c₁,
      by simp [evalArgs, Expr.eval, st, startState], hinit_eq, hrun₁, rfl, rfl, rfl⟩
  let stMid : State := { st₁ with regs := regs₁ }
  let mem₂ := Function.update st₁.mem (heap + LCT_HDR_L) L
  let mem₃ := Function.update mem₂ (heap + LCT_HDR_P) P
  have hr1 : regs₁ 1 = L := by simp [regs₁, st, startState, Function.update_of_ne]
  have hr2 : regs₁ 2 = P := by simp [regs₁, st, startState, Function.update_of_ne]
  have hr3 : regs₁ 3 = heap := by simp [regs₁, st, startState, Function.update_of_ne]
  have hr4 : regs₁ 4 = o.value := by simp [regs₁]
  have hp_store1 : Runs w p ω (.store (.bin .add (.reg 3) (.const LCT_HDR_L)) (.reg 1))
      stMid .normal { mem := mem₂, regs := regs₁, pos := st₁.pos } 5 := by
    refine runs_store_iff.mpr ⟨heap + LCT_HDR_L, L, ?_, ?_, rfl, rfl, rfl⟩
    · simp [Expr.eval, stMid, hr3, h3w, hb3_w]
    · simp [Expr.eval, stMid, hr1]
  have hp_store2 : Runs w p ω (.store (.bin .add (.reg 3) (.const LCT_HDR_P)) (.reg 2))
      { mem := mem₂, regs := regs₁, pos := st₁.pos } .normal
      { mem := mem₃, regs := regs₁, pos := st₁.pos } 5 := by
    refine runs_store_iff.mpr ⟨heap + LCT_HDR_P, P, ?_, ?_, rfl, rfl, rfl⟩
    · simp [Expr.eval, hr3, h4w, hb4_w]
    · simp [Expr.eval, hr2]
  have hret : Runs w p ω (.ret (.reg 4)) { mem := mem₃, regs := regs₁, pos := st₁.pos }
      (.returned o.value) { mem := mem₃, regs := regs₁, pos := st₁.pos } 2 :=
    runs_ret_iff.mpr ⟨o.value, Expr.eval_reg_of_eq hr4, rfl, rfl, rfl⟩
  have hfull : Runs w p ω (dynLctInitWrap lp) st (.returned o.value)
      { mem := mem₃, regs := regs₁, pos := st₁.pos } _ :=
    runs_seq_normal hcall (runs_seq_normal hp_store1 (runs_seq_normal hp_store2 hret))
  obtain ⟨r1, r2, r3, r4, r5⟩ := hresp₁
  have hxn : x.n = n := hrep₁.2.2.2.2.1
  have hfoot_lt : ∀ a, lctFoot heap x a → a < lctArenaHi heap (lctCap n) := fun a ha => by
    rcases r5 a ha with hf | ⟨_, ha_hi⟩
    · exact False.elim hf
    · omega
  have hrep_final : LctMemRep w h L P heap (MathForest.empty n) x mem₃ :=
    lctMemRep_empty_set_LP hrep₁ hfoot_lt
  have hphi_le : lctPhi L mem₃ heap n ≤ 46 * (L + 1) * lctPhi 0 st₁.mem heap n := by
    apply lctPhi_le_of_phi0
    intro a ha1 _
    dsimp only [mem₃, mem₂]
    have hL3 : heap + LCT_HDR_L ≠ a := by unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_L at *; omega
    have hP4 : heap + LCT_HDR_P ≠ a := by unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_P at *; omega
    rw [Function.update_of_ne hP4.symm, Function.update_of_ne hL3.symm]
  have hresp_final : (lctDSRep w h L P).Respects (fun _ => False) heap (lctArenaWords n)
      mem₀ o.value heap x mem₃ := by
    refine ⟨r1, r2, ?_, ?_, r5⟩
    · intro a ha
      have hneL : heap + LCT_HDR_L ≠ a := by omega
      have hneP : heap + LCT_HDR_P ≠ a := by omega
      dsimp only [mem₃, mem₂]
      rw [Function.update_of_ne hneP.symm, Function.update_of_ne hneL.symm]
      exact r3 a ha
    · intro a ha hn
      have hneL : heap + LCT_HDR_L ≠ a := by omega
      have hneP : heap + LCT_HDR_P ≠ a := by omega
      dsimp only [mem₃, mem₂]
      rw [Function.update_of_ne hneP.symm, Function.update_of_ne hneL.symm]
      exact r4 a ha hn
  refine ⟨o.value, { mem := mem₃, regs := regs₁, pos := st₁.pos }, _, x, hfull, hrep_final,
    hresp_final, ?_⟩
  have hmul_bd : 46 * (L + 1) * lctPhi 0 st₁.mem heap n ≤
      46 * (L + 1) * (C_LCT_INIT * (n + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have hconst_le : 46 * (L + 1) * (C_LCT_INIT * (n + 1)) + c₁ + 20 ≤
      100000 * (L + 1) * (n + 1) := by
    have hL1 : 1 ≤ L + 1 := Nat.succ_pos L
    have hn1 : 1 ≤ n + 1 := Nat.succ_pos n
    have hLn : 1 ≤ (L + 1) * (n + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hc₁_le : c₁ ≤ C_LCT_INIT * (n + 1) := by omega
    have hc₁_mul : c₁ ≤ C_LCT_INIT * (L + 1) * (n + 1) := by
      calc c₁ ≤ C_LCT_INIT * (n + 1) := hc₁_le
        _ ≤ C_LCT_INIT * ((L + 1) * (n + 1)) :=
            Nat.mul_le_mul_left C_LCT_INIT (Nat.le_mul_of_pos_left (n + 1) hL1)
        _ = C_LCT_INIT * (L + 1) * (n + 1) := (Nat.mul_assoc _ _ _).symm
    unfold C_LCT_INIT at hc₁_mul ⊢
    nlinarith
  show 2 + c₁ + 1 + (5 + (5 + 2 + 1) + 1) + 1 + lctPhi L mem₃ heap n ≤ 100000 * (L + 1) * (n + 1)
  omega

end InitLift

end MinCostFlow.Final