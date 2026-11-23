module

public import MinCostFlow.SparseCore.Program.OrdStoreWalkJoin
import Mathlib.Tactic

/-!
# Order Store Zero-Scratch Tree Freeing

This file implements and verifies `ordFreeTreeBody` on `[b, r]`: frees every node in a detached
auxiliary tree rooted at `r` by clearing `eNode[cur.key] := 0`, zeroing the node record, and
pushing it onto `freeHead`, using an in-place right-rotation tree-peeling loop (zero recursion,
zero heap scratch) in `≤ 2 * t.countNodes` iterations (`≤ 260 * t.countNodes + 80` cost).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-- Cost weight per live node in the order-store potential (pays for `ordFreeTreeBody`). -/
def ORD_DEL_WEIGHT : ℕ := 300
def ORD_FREE_STEP_COST : ℕ := 130
def ORD_FREE_PER_NODE : ℕ := 260

/-- Minimal binary-tree pointer invariant preserved during right-rotation peeling. -/
def FreeTreeShape (st : SplayState ℕ Unit Unit) : AuxTree → Prop
  | .leaf => True
  | .node id l r =>
      id ≠ 0 ∧ (st.nodes id).left = l.rootId ∧ (st.nodes id).right = r.rootId ∧
      FreeTreeShape st l ∧ FreeTreeShape st r

theorem freeTreeShape_of_subtreeInv {st : SplayState ℕ Unit Unit} {p : ℕ} {t : AuxTree}
    (h : SplayState.SubtreeInv ordPayload st p t) : FreeTreeShape st t := by
  induction t generalizing p with
  | leaf => trivial
  | node id l r ihl ihr =>
    rcases h with ⟨h1, h2, h3, -, -, -, -, hL, hR⟩
    exact ⟨h1, h2, h3, ihl hL, ihr hR⟩

theorem freeTreeShape_agree {st₁ st₂ : SplayState ℕ Unit Unit} {t : AuxTree}
    (h : FreeTreeShape st₁ t) (hag : ∀ u ∈ t.toList, st₂.nodes u = st₁.nodes u) :
    FreeTreeShape st₂ t := by
  induction t with
  | leaf => trivial
  | node id l r ihl ihr =>
    rcases h with ⟨h1, h2, h3, hL, hR⟩
    have hid := hag id (by simp [AuxTree.toList])
    exact ⟨h1, hid ▸ h2, hid ▸ h3,
      ihl hL fun u hu => hag u (by simp [AuxTree.toList, hu]),
      ihr hR fun u hu => hag u (by simp [AuxTree.toList, hu])⟩

theorem rightSpineLen_lt_countNodes {t : AuxTree} (ht : t ≠ .leaf) :
    rightSpineLen t < t.countNodes := by
  induction t with
  | leaf => exact absurd rfl ht
  | node id l r _ ihr =>
    cases r with
    | leaf => simp [rightSpineLen, AuxTree.countNodes]
    | node rid rl rr =>
      have := ihr (by simp)
      simp only [rightSpineLen, AuxTree.countNodes] at this ⊢
      omega

/-- `ordFreeTree` on `[b, r]`: frees every node in the detached auxiliary tree rooted at `r`
(clearing `eNode[key] := 0` and pushing each node onto `freeHead`), in `≤ 2 * t.countNodes`
right-rotation/peeling iterations with zero recursion and zero heap scratch. -/
def ordFreeTreeBody : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 5 (.reg 1) ;;
  .loop (.reg 5)
    (.assign 6 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 5))) ;;
     .assign 7 (.load (.reg 6)) ;;
     .cond (.reg 7)
       (.assign 8 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 7))) ;;
        .assign 9 (.load (.bin .add (.reg 8) (.const 1))) ;;
        .store (.reg 6) (.reg 9) ;;
        .store (.bin .add (.reg 8) (.const 1)) (.reg 5) ;;
        .assign 5 (.reg 7))
       (.assign 8 (.load (.bin .add (.reg 6) (.const 1))) ;;
        .assign 9 (.load (.bin .add (.reg 6) (.const 5))) ;;
        .store (.bin .add (.reg 3) (.reg 9)) (.const 0) ;;
        .store (.reg 6) (.const 0) ;;
        .store (.bin .add (.reg 6) (.const 1)) (.const 0) ;;
        .store (.bin .add (.reg 6) (.const 2)) (.const 0) ;;
        .store (.bin .add (.reg 6) (.const 3)) (.const 0) ;;
        .store (.bin .add (.reg 6) (.const 4)) (.const 0) ;;
        .store (.bin .add (.reg 6) (.const 6)) (.const 0) ;;
        .store (.bin .add (.reg 6) (.const 7)) (.reg 4) ;;
        .assign 4 (.reg 5) ;;
        .assign 5 (.reg 8))) ;;
  .store (.bin .add (.reg 0) (.const 6)) (.reg 4) ;;
  .ret (.const 0)

theorem ordFreeTreeBody_noRand : ordFreeTreeBody.NoRand := by
  simp [ordFreeTreeBody, Stmt.NoRand]

private theorem freeChain_congr {h : ℕ} {nf₁ nf₂ : ℕ → ℕ} {fl : List ℕ}
    (hc : FreeChain h nf₁ fl) (hag : ∀ x ∈ fl, nf₂ x = nf₁ x) :
    FreeChain h nf₂ fl := by
  induction fl generalizing h with
  | nil => exact hc
  | cons a tl ih =>
    rcases hc with ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [hag a List.mem_cons_self]
    exact ih h3 fun x hx => hag x (List.mem_cons_of_mem a hx)

theorem ordFreeTreeBody_runs {w b vCap eCap cap r fh pos : ℕ} {p : Program} (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState ℕ Unit Unit} {nf eNode : ℕ → ℕ} {fl : List ℕ} {t : AuxTree}
    (hnb_hdr : mem (b + 4) = ordNodesBase b vCap eCap)
    (hen_hdr : mem (b + 3) = ordENodeBase b vCap)
    (hfh_hdr : mem (b + 6) = fh)
    (hen_at : ∀ k < 2 * eCap, mem (ordENodeBase b vCap + k) = eNode k)
    (hnodes : OrdNodesAt mem (ordNodesBase b vCap eCap) cap st nf)
    (hnd : t.toList.Nodup) (hshape : FreeTreeShape st t) (hr : r = t.rootId)
    (hmem_le : ∀ u ∈ t.toList, 1 ≤ u ∧ u ≤ cap)
    (hkey_lt : ∀ u ∈ t.toList, (st.nodes u).val < 2 * eCap)
    (hdisj_fl : ∀ u ∈ t.toList, u ∉ fl)
    (hfl_nd : fl.Nodup) (hfc : FreeChain fh nf fl)
    (hcap : cap ≤ 2 * eCap) (hw : b + ordArenaSize vCap eCap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω ordFreeTreeBody (startState [b, r] mem pos) o st' c ∧
      (∃ (fh' : ℕ) (fl' : List ℕ) (sp' : SplayState ℕ Unit Unit) (nf' eNode' : ℕ → ℕ),
        st'.mem (b + 6) = fh' ∧
        OrdNodesAt st'.mem (ordNodesBase b vCap eCap) cap sp' nf' ∧
        (∀ k < 2 * eCap, st'.mem (ordENodeBase b vCap + k) = eNode' k) ∧
        (∀ a, ¬ InOrdNodes (ordNodesBase b vCap eCap) cap a →
          ¬ (ordENodeBase b vCap ≤ a ∧ a < ordENodeBase b vCap + 2 * eCap) →
          a ≠ b + 6 → st'.mem a = mem a) ∧
        fl'.Perm (t.toList ++ fl) ∧ fl'.Nodup ∧ FreeChain fh' nf' fl' ∧
        (∀ u, (sp'.nodes u).rev = (st.nodes u).rev) ∧
        (∀ u ∉ t.toList, sp'.nodes u = st.nodes u ∧ nf' u = nf u) ∧
        (∀ k < 2 * eCap, eNode' k = if (∃ u ∈ t.toList, (st.nodes u).val = k) then 0 else eNode k)) ∧
      0 + c ≤ ORD_FREE_PER_NODE * t.countNodes + 80 := by
  classical
  set nb := ordNodesBase b vCap eCap with hnb
  set en := ordENodeBase b vCap with hen
  have hw' : b + (16 + vCap + 18 * eCap) < 2 ^ w := hw
  have hnb_w : nb + 8 * (cap + 1) < 2 ^ w := by
    have := ordNodesBase_end b vCap eCap; unfold ordArenaSize at this; omega
  have hen_w : en + 2 * eCap < 2 ^ w := by unfold ordENodeBase at hen; omega
  have hloop : ∀ (M : ℕ) (stM : State) (s : SplayState ℕ Unit Unit) (nf0 eN0 : ℕ → ℕ)
      (fh0 : ℕ) (fl0 : List ℕ) (t0 : AuxTree),
      2 * t0.countNodes - rightSpineLen t0 ≤ M →
      OrdNodesAt stM.mem nb cap s nf0 →
      (∀ k < 2 * eCap, stM.mem (en + k) = eN0 k) →
      t0.toList.Nodup → FreeTreeShape s t0 →
      (∀ u ∈ t0.toList, 1 ≤ u ∧ u ≤ cap) →
      (∀ u ∈ t0.toList, (s.nodes u).val < 2 * eCap) →
      (∀ u ∈ t0.toList, u ∉ fl0) →
      fl0.Nodup → FreeChain fh0 nf0 fl0 →
      stM.regs 0 = b → stM.regs 2 = nb → stM.regs 3 = en →
      stM.regs 4 = fh0 → stM.regs 5 = t0.rootId →
      ∃ (stE : State) (cE fh' : ℕ) (fl' : List ℕ) (s' : SplayState ℕ Unit Unit) (nf' eN' : ℕ → ℕ),
        Runs w p ω
          (.loop (.reg 5)
            (.assign 6 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 5))) ;;
             .assign 7 (.load (.reg 6)) ;;
             .cond (.reg 7)
               (.assign 8 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 7))) ;;
                .assign 9 (.load (.bin .add (.reg 8) (.const 1))) ;;
                .store (.reg 6) (.reg 9) ;;
                .store (.bin .add (.reg 8) (.const 1)) (.reg 5) ;;
                .assign 5 (.reg 7))
               (.assign 8 (.load (.bin .add (.reg 6) (.const 1))) ;;
                .assign 9 (.load (.bin .add (.reg 6) (.const 5))) ;;
                .store (.bin .add (.reg 3) (.reg 9)) (.const 0) ;;
                .store (.reg 6) (.const 0) ;;
                .store (.bin .add (.reg 6) (.const 1)) (.const 0) ;;
                .store (.bin .add (.reg 6) (.const 2)) (.const 0) ;;
                .store (.bin .add (.reg 6) (.const 3)) (.const 0) ;;
                .store (.bin .add (.reg 6) (.const 4)) (.const 0) ;;
                .store (.bin .add (.reg 6) (.const 6)) (.const 0) ;;
                .store (.bin .add (.reg 6) (.const 7)) (.reg 4) ;;
                .assign 4 (.reg 5) ;;
                .assign 5 (.reg 8)))) stM .normal stE cE ∧
        stE.regs 0 = b ∧ stE.regs 4 = fh' ∧
        OrdNodesAt stE.mem nb cap s' nf' ∧
        (∀ k < 2 * eCap, stE.mem (en + k) = eN' k) ∧
        (∀ a, ¬ InOrdNodes nb cap a → ¬ (en ≤ a ∧ a < en + 2 * eCap) → stE.mem a = stM.mem a) ∧
        fl'.Perm (t0.toList ++ fl0) ∧ fl'.Nodup ∧ FreeChain fh' nf' fl' ∧
        (∀ u, (s'.nodes u).rev = (s.nodes u).rev) ∧
        (∀ u ∉ t0.toList, s'.nodes u = s.nodes u ∧ nf' u = nf0 u) ∧
        (∀ k < 2 * eCap, eN' k = if (∃ u ∈ t0.toList, (s.nodes u).val = k) then 0 else eN0 k) ∧
        cE ≤ (2 * t0.countNodes - rightSpineLen t0) * ORD_FREE_STEP_COST + 10 := by
    intro M
    induction M with
    | zero =>
      intro stM s nf0 eN0 fh0 fl0 t0 hM hn0 he0 hnd0 hsh0 hle0 hkl0 hdj0 hflnd0 hfc0 r0 r2 r3 r4 r5
      have ht0_leaf : t0 = .leaf := by
        cases t0 with
        | leaf => rfl
        | node id l r =>
          have := rightSpineLen_lt_countNodes (t := .node id l r) (by simp)
          simp [AuxTree.countNodes] at hM this; omega
      subst ht0_leaf
      simp only [AuxTree.rootId] at r5
      refine ⟨stM, _, fh0, fl0, s, nf0, eN0, ord_runs_loop_false (Expr.eval_reg_of_eq r5),
        r0, r4, hn0, he0, fun _ _ _ => rfl, by simp [AuxTree.toList], hflnd0, hfc0, fun _ => rfl,
        fun _ _ => ⟨rfl, rfl⟩,
        fun k _ => by simp [AuxTree.toList], by simp [Expr.size_reg]⟩
    | succ M ih =>
      intro stM s nf0 eN0 fh0 fl0 t0 hM hn0 he0 hnd0 hsh0 hle0 hkl0 hdj0 hflnd0 hfc0 r0 r2 r3 r4 r5
      cases t0 with
      | leaf =>
        simp only [AuxTree.rootId] at r5
        refine ⟨stM, _, fh0, fl0, s, nf0, eN0, ord_runs_loop_false (Expr.eval_reg_of_eq r5),
          r0, r4, hn0, he0, fun _ _ _ => rfl, by simp [AuxTree.toList], hflnd0, hfc0, fun _ => rfl,
          fun _ _ => ⟨rfl, rfl⟩,
          fun k _ => by simp [AuxTree.toList], by simp [Expr.size_reg]⟩
      | node id l r =>
        rcases hsh0 with ⟨hid0, hidL, hidR, hshL, hshR⟩
        rcases AuxTree.nodup_node_unfold hnd0 with ⟨hLnd, hid_nL, hRnd, hid_nR, hLR⟩
        have hid_le : id ≤ cap := (hle0 id (by simp [AuxTree.toList])).2
        simp only [AuxTree.rootId] at r5
        have hcond5 : (Expr.reg 5).eval w stM = some id := Expr.eval_reg_of_eq r5
        have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 5)))) stM .normal
            { stM with regs := Function.update stM.regs 6 (nb + 8 * id) } _ :=
          runs_assign_iff.mpr ⟨nb + 8 * id, Expr.eval_add (Expr.eval_reg_of_eq r2)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r5) (by omega)) (by omega),
            rfl, rfl, rfl⟩
        set stM1 : State := { stM with regs := Function.update stM.regs 6 (nb + 8 * id) }
        have hm_idL : stM.mem (nb + 8 * id) = l.rootId := by rw [← hidL]; exact (hn0 id hid_le).1
        have ha7 : Runs w p ω (.assign 7 (.load (.reg 6))) stM1 .normal
            { stM1 with regs := Function.update stM1.regs 7 l.rootId } _ :=
          runs_assign_iff.mpr ⟨l.rootId, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [stM1])) hm_idL,
            rfl, rfl, rfl⟩
        set stM2 : State := { stM1 with regs := Function.update stM1.regs 7 l.rootId }
        cases l with
        | leaf =>
          have hcond7 : (Expr.reg 7).eval w stM2 = some 0 := Expr.eval_reg_of_eq (by simp [stM2, AuxTree.rootId])
          have hm_idR : stM.mem (nb + 8 * id + 1) = r.rootId := by rw [← hidR]; exact (hn0 id hid_le).2.1
          have hm_idk : stM.mem (nb + 8 * id + 5) = (s.nodes id).val := (hn0 id hid_le).2.2.2.2.2.1
          have hid_klt : (s.nodes id).val < 2 * eCap := hkl0 id (by simp [AuxTree.toList])
          have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 6) (.const 1)))) stM2 .normal
              { stM2 with regs := Function.update stM2.regs 8 r.rootId } _ :=
            runs_assign_iff.mpr ⟨r.rootId, Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [stM2, stM1])) (Expr.eval_const (by omega)) (by omega)) hm_idR,
              rfl, rfl, rfl⟩
          set stM3 : State := { stM2 with regs := Function.update stM2.regs 8 r.rootId }
          have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.const 5)))) stM3 .normal
              { stM3 with regs := Function.update stM3.regs 9 (s.nodes id).val } _ :=
            runs_assign_iff.mpr ⟨(s.nodes id).val, Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [stM3, stM2, stM1])) (Expr.eval_const (by omega)) (by omega)) hm_idk,
              rfl, rfl, rfl⟩
          set stM4 : State := { stM3 with regs := Function.update stM3.regs 9 (s.nodes id).val }
          have hpeel : ∃ stP cP, Runs w p ω
              (.store (.bin .add (.reg 3) (.reg 9)) (.const 0) ;;
               .store (.reg 6) (.const 0) ;;
               .store (.bin .add (.reg 6) (.const 1)) (.const 0) ;;
               .store (.bin .add (.reg 6) (.const 2)) (.const 0) ;;
               .store (.bin .add (.reg 6) (.const 3)) (.const 0) ;;
               .store (.bin .add (.reg 6) (.const 4)) (.const 0) ;;
               .store (.bin .add (.reg 6) (.const 6)) (.const 0) ;;
               .store (.bin .add (.reg 6) (.const 7)) (.reg 4) ;;
               .assign 4 (.reg 5) ;;
               .assign 5 (.reg 8)) stM4 .normal stP cP ∧
              cP ≤ 90 ∧
              stP.regs 0 = b ∧ stP.regs 2 = nb ∧ stP.regs 3 = en ∧
              stP.regs 4 = id ∧ stP.regs 5 = r.rootId ∧
              OrdNodesAt stP.mem nb cap
                (s.updateNode id fun nd => { nd with left := 0, right := 0, par := 0, ppar := 0, sz := 0 })
                (Function.update nf0 id fh0) ∧
              (∀ k < 2 * eCap, stP.mem (en + k) = Function.update eN0 (s.nodes id).val 0 k) ∧
              (∀ a, ¬ InOrdNodes nb cap a → ¬ (en ≤ a ∧ a < en + 2 * eCap) → stP.mem a = stM.mem a) := by
            have hs1 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 9)) (.const 0)) stM4 .normal
                { stM4 with mem := Function.update stM.mem (en + (s.nodes id).val) 0 } _ :=
              runs_store_iff.mpr ⟨en + (s.nodes id).val, 0,
                Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1, r3]))
                  (Expr.eval_reg_of_eq (by simp [stM4])) (by omega),
                Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m1 := Function.update stM.mem (en + (s.nodes id).val) 0
            have hs2 : Runs w p ω (.store (.reg 6) (.const 0)) { stM4 with mem := m1 } .normal
                { stM4 with mem := Function.update m1 (nb + 8 * id) 0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * id, 0, Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1]),
                Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m2 := Function.update m1 (nb + 8 * id) 0
            have hs3 : Runs w p ω (.store (.bin .add (.reg 6) (.const 1)) (.const 0)) { stM4 with mem := m2 } .normal
                { stM4 with mem := Function.update m2 (nb + 8 * id + 1) 0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * id + 1, 0, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1]))
                (Expr.eval_const (by omega)) (by omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m3 := Function.update m2 (nb + 8 * id + 1) 0
            have hs4 : Runs w p ω (.store (.bin .add (.reg 6) (.const 2)) (.const 0)) { stM4 with mem := m3 } .normal
                { stM4 with mem := Function.update m3 (nb + 8 * id + 2) 0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * id + 2, 0, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1]))
                (Expr.eval_const (by omega)) (by omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m4 := Function.update m3 (nb + 8 * id + 2) 0
            have hs5 : Runs w p ω (.store (.bin .add (.reg 6) (.const 3)) (.const 0)) { stM4 with mem := m4 } .normal
                { stM4 with mem := Function.update m4 (nb + 8 * id + 3) 0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * id + 3, 0, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1]))
                (Expr.eval_const (by omega)) (by omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m5 := Function.update m4 (nb + 8 * id + 3) 0
            have hs6 : Runs w p ω (.store (.bin .add (.reg 6) (.const 4)) (.const 0)) { stM4 with mem := m5 } .normal
                { stM4 with mem := Function.update m5 (nb + 8 * id + 4) 0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * id + 4, 0, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1]))
                (Expr.eval_const (by omega)) (by omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m6 := Function.update m5 (nb + 8 * id + 4) 0
            have hs7 : Runs w p ω (.store (.bin .add (.reg 6) (.const 6)) (.const 0)) { stM4 with mem := m6 } .normal
                { stM4 with mem := Function.update m6 (nb + 8 * id + 6) 0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * id + 6, 0, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1]))
                (Expr.eval_const (by omega)) (by omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m7 := Function.update m6 (nb + 8 * id + 6) 0
            have hs8 : Runs w p ω (.store (.bin .add (.reg 6) (.const 7)) (.reg 4)) { stM4 with mem := m7 } .normal
                { stM4 with mem := Function.update m7 (nb + 8 * id + 7) fh0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * id + 7, fh0, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1]))
                (Expr.eval_const (by omega)) (by omega),
                Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1, r4]), rfl, rfl, rfl⟩
            set m8 := Function.update m7 (nb + 8 * id + 7) fh0
            have hf4 : Runs w p ω (.assign 4 (.reg 5)) { stM4 with mem := m8 } .normal
                { stM4 with mem := m8, regs := Function.update stM4.regs 4 id } _ :=
              runs_assign_iff.mpr ⟨id, Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1, r5]), rfl, rfl, rfl⟩
            have hf5 : Runs w p ω (.assign 5 (.reg 8))
                { stM4 with mem := m8, regs := Function.update stM4.regs 4 id } .normal
                { stM4 with mem := m8, regs := Function.update (Function.update stM4.regs 4 id) 5 r.rootId } _ :=
              runs_assign_iff.mpr ⟨r.rootId, Expr.eval_reg_of_eq (by simp [stM4, stM3]), rfl, rfl, rfl⟩
            have hseq := ord_runs_seq_normal hs1 (ord_runs_seq_normal hs2 (ord_runs_seq_normal hs3
              (ord_runs_seq_normal hs4 (ord_runs_seq_normal hs5 (ord_runs_seq_normal hs6
                (ord_runs_seq_normal hs7 (ord_runs_seq_normal hs8 (ord_runs_seq_normal hf4 hf5))))))))
            have hen_disj : ∀ x ≤ cap, ∀ j < 8, en + (s.nodes id).val ≠ nb + 8 * x + j := fun x _ j _ => by
              rw [hnb, hen]; unfold ordENodeBase ordNodesBase; omega
            refine ⟨_, _, hseq, by simp [Expr.size_bin, Expr.size_reg, Expr.size_const],
              by simp [stM4, stM3, stM2, stM1, r0], by simp [stM4, stM3, stM2, stM1, r2],
              by simp [stM4, stM3, stM2, stM1, r3], by simp, by simp, ?_, ?_, ?_⟩
            · intro x hx
              by_cases hxi : x = id
              · rw [hxi]
                have h5 : m8 (nb + 8 * id + 5) = (s.nodes id).val := by
                  dsimp only [m8, m7, m6, m5, m4, m3, m2, m1]
                  repeat rw [Function.update_of_ne (by omega)]
                  rw [Function.update_of_ne (Ne.symm (hen_disj id hid_le 5 (by omega)))]
                  exact hm_idk
                dsimp only [OrdNodeAt, ordNodeAddr]
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · dsimp only [m8, m7, m6, m5, m4, m3, m2]
                  simp [SplayState.nodes_updateNode,
                    Function.update_of_ne (by omega : nb + 8 * id ≠ nb + 8 * id + 7),
                    Function.update_of_ne (by omega : nb + 8 * id ≠ nb + 8 * id + 6),
                    Function.update_of_ne (by omega : nb + 8 * id ≠ nb + 8 * id + 4),
                    Function.update_of_ne (by omega : nb + 8 * id ≠ nb + 8 * id + 3),
                    Function.update_of_ne (by omega : nb + 8 * id ≠ nb + 8 * id + 2),
                    Function.update_of_ne (by omega : nb + 8 * id ≠ nb + 8 * id + 1)]
                · dsimp only [m8, m7, m6, m5, m4, m3]
                  simp [SplayState.nodes_updateNode,
                    Function.update_of_ne (by omega : nb + 8 * id + 1 ≠ nb + 8 * id + 7),
                    Function.update_of_ne (by omega : nb + 8 * id + 1 ≠ nb + 8 * id + 6),
                    Function.update_of_ne (by omega : nb + 8 * id + 1 ≠ nb + 8 * id + 4),
                    Function.update_of_ne (by omega : nb + 8 * id + 1 ≠ nb + 8 * id + 3),
                    Function.update_of_ne (by omega : nb + 8 * id + 1 ≠ nb + 8 * id + 2)]
                · dsimp only [m8, m7, m6, m5, m4]
                  simp [SplayState.nodes_updateNode,
                    Function.update_of_ne (by omega : nb + 8 * id + 2 ≠ nb + 8 * id + 7),
                    Function.update_of_ne (by omega : nb + 8 * id + 2 ≠ nb + 8 * id + 6),
                    Function.update_of_ne (by omega : nb + 8 * id + 2 ≠ nb + 8 * id + 4),
                    Function.update_of_ne (by omega : nb + 8 * id + 2 ≠ nb + 8 * id + 3)]
                · dsimp only [m8, m7, m6, m5]
                  simp [SplayState.nodes_updateNode,
                    Function.update_of_ne (by omega : nb + 8 * id + 3 ≠ nb + 8 * id + 7),
                    Function.update_of_ne (by omega : nb + 8 * id + 3 ≠ nb + 8 * id + 6),
                    Function.update_of_ne (by omega : nb + 8 * id + 3 ≠ nb + 8 * id + 4)]
                · dsimp only [m8, m7, m6]
                  simp [SplayState.nodes_updateNode,
                    Function.update_of_ne (by omega : nb + 8 * id + 4 ≠ nb + 8 * id + 7),
                    Function.update_of_ne (by omega : nb + 8 * id + 4 ≠ nb + 8 * id + 6)]
                · simpa [SplayState.nodes_updateNode] using h5
                · dsimp only [m8, m7]
                  simp [Function.update_of_ne (by omega : nb + 8 * id + 6 ≠ nb + 8 * id + 7)]
                · dsimp only [m8]; simp
              · rw [SplayState.nodes_updateNode_ne _ hxi, Function.update_of_ne hxi]
                have hna := hn0 x hx
                have hsame : ∀ j < 8, m8 (nb + 8 * x + j) = stM.mem (nb + 8 * x + j) := fun j hj => by
                  dsimp only [m8, m7, m6, m5, m4, m3, m2, m1]
                  repeat rw [Function.update_of_ne (by omega)]
                  exact Function.update_of_ne (Ne.symm (hen_disj x hx j hj)) _ _
                refine ⟨by simpa [ordNodeAddr] using (hsame 0 (by omega)).trans (by simpa [ordNodeAddr] using hna.1),
                  (hsame 1 (by omega)).trans hna.2.1,
                  (hsame 2 (by omega)).trans hna.2.2.1,
                  (hsame 3 (by omega)).trans hna.2.2.2.1,
                  (hsame 4 (by omega)).trans hna.2.2.2.2.1,
                  (hsame 5 (by omega)).trans hna.2.2.2.2.2.1,
                  (hsame 6 (by omega)).trans hna.2.2.2.2.2.2.1,
                  (hsame 7 (by omega)).trans hna.2.2.2.2.2.2.2⟩
            · intro k hk
              dsimp only [m8, m7, m6, m5, m4, m3, m2, m1]
              repeat rw [Function.update_of_ne (by rw [hnb, hen]; unfold ordENodeBase ordNodesBase; omega)]
              by_cases hkeq : k = (s.nodes id).val
              · subst hkeq; simp
              · rw [Function.update_of_ne (by omega), Function.update_of_ne hkeq]; exact he0 k hk
            · intro a ha1 ha2
              dsimp only [m8, m7, m6, m5, m4, m3, m2, m1]
              rw [Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha2 ⟨by omega, by omega⟩)]
          obtain ⟨stP, cP, hrunP, hcP, pr0, pr2, pr3, pr4, pr5, hnP, heP, hfrP⟩ := hpeel
          set s1 := s.updateNode id fun nd => { nd with left := 0, right := 0, par := 0, ppar := 0, sz := 0 }
          set nf1 := Function.update nf0 id fh0
          set eN1 := Function.update eN0 (s.nodes id).val 0
          have hmeas : 2 * r.countNodes - rightSpineLen r + 1 ≤
              2 * (AuxTree.node id .leaf r).countNodes - rightSpineLen (.node id .leaf r) := by
            cases r with
            | leaf => simp [AuxTree.countNodes, rightSpineLen]
            | node rid rl rr =>
              have := rightSpineLen_lt_countNodes (t := .node rid rl rr) (by simp)
              simp only [AuxTree.countNodes, rightSpineLen] at this ⊢; omega
          have hs1_ne : ∀ u, u ≠ id → s1.nodes u = s.nodes u := fun u hne => by
            simp [s1, SplayState.nodes_updateNode, hne]
          have hshR1 : FreeTreeShape s1 r :=
            freeTreeShape_agree hshR fun u hu => hs1_ne u (fun h => hid_nR (h ▸ hu))
          have hfc1 : FreeChain id nf1 (id :: fl0) := by
            refine ⟨rfl, hid0, ?_⟩
            have h1 : nf1 id = fh0 := by simp [nf1]
            rw [h1]
            exact freeChain_congr hfc0 fun u hu =>
              Function.update_of_ne (fun (h : u = id) => hdj0 id (by simp [AuxTree.toList]) (h ▸ hu)) _ _
          obtain ⟨stE, cE, fh', fl', s', nf', eN', hrest, er0, er4, hnE, heE, hfrE, hpermE, hndE, hfcE, hrevE, houtE, heNE, hcE⟩ :=
            ih stP s1 nf1 eN1 id (id :: fl0) r (by omega) hnP heP hRnd hshR1
              (fun u hu => hle0 u (by simp [AuxTree.toList, hu]))
              (fun u hu => by
                rw [hs1_ne u (fun h => hid_nR (h ▸ hu))]
                exact hkl0 u (by simp [AuxTree.toList, hu]))
              (fun u hu hmem => by
                rw [List.mem_cons] at hmem
                rcases hmem with rfl | hmem'
                · exact hid_nR hu
                · exact hdj0 u (by simp [AuxTree.toList, hu]) hmem')
              (List.nodup_cons.mpr ⟨hdj0 id (by simp [AuxTree.toList]), hflnd0⟩) hfc1
              pr0 pr2 pr3 pr4 pr5
          refine ⟨stE, _, fh', fl', s', nf', eN',
            ord_runs_loop_true hcond5 hid0
              (ord_runs_seq_normal ha6 (ord_runs_seq_normal ha7
                (ord_runs_cond_false hcond7 (ord_runs_seq_normal ha8 (ord_runs_seq_normal ha9 hrunP)))))
              hrest, er0, er4, hnE, heE,
            fun a ha1 ha2 => (hfrE a ha1 ha2).trans (hfrP a ha1 ha2),
            hpermE.trans (by simpa [AuxTree.toList] using List.perm_middle),
            hndE, hfcE,
            fun u => (hrevE u).trans (by by_cases h : u = id <;> [rw [h]; skip] <;> simp [s1, SplayState.nodes_updateNode, h]),
            ?_, ?_, ?_⟩
          · intro u hu
            have hui : u ≠ id := fun h => hu (by simp [AuxTree.toList, h])
            have hur : u ∉ r.toList := fun h => hu (by simp [AuxTree.toList, h])
            rcases houtE u hur with ⟨h1, h2⟩
            exact ⟨h1.trans (hs1_ne u hui), h2.trans (Function.update_of_ne hui _ _)⟩
          · intro k hk
            rw [heNE k hk]
            have hiff : (∃ u ∈ r.toList, (s1.nodes u).val = k) ↔ (∃ u ∈ r.toList, (s.nodes u).val = k) := by
              constructor <;> rintro ⟨u, hu, heq⟩ <;> refine ⟨u, hu, ?_⟩
              · rwa [hs1_ne u (fun h => hid_nR (h ▸ hu))] at heq
              · rwa [hs1_ne u (fun h => hid_nR (h ▸ hu))]
            by_cases h1 : ∃ u ∈ r.toList, (s.nodes u).val = k
            · have h2 : ∃ u ∈ (AuxTree.node id .leaf r).toList, (s.nodes u).val = k := by
                rcases h1 with ⟨u, hu, heq⟩; exact ⟨u, by simp [AuxTree.toList, hu], heq⟩
              simp [hiff.mpr h1, h2]
            · by_cases h2 : k = (s.nodes id).val
              · subst h2
                have h3 : ∃ u ∈ (AuxTree.node id .leaf r).toList, (s.nodes u).val = (s.nodes id).val :=
                  ⟨id, by simp [AuxTree.toList], rfl⟩
                simp [hiff.not.mpr h1, eN1, h3]
              · have h3 : ¬ ∃ u ∈ (AuxTree.node id .leaf r).toList, (s.nodes u).val = k := by
                  rintro ⟨u, hu, heq⟩
                  simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_cons] at hu
                  rcases hu with rfl | hur
                  · exact h2 heq.symm
                  · exact h1 ⟨u, hur, heq⟩
                simp [hiff.not.mpr h1, eN1, h2, h3]
          · have hmul : (2 * r.countNodes - rightSpineLen r + 1) * ORD_FREE_STEP_COST ≤
                (2 * (AuxTree.node id .leaf r).countNodes - rightSpineLen (.node id .leaf r)) * ORD_FREE_STEP_COST :=
              Nat.mul_le_mul_right ORD_FREE_STEP_COST hmeas
            unfold ORD_FREE_STEP_COST at hcE hmul ⊢
            simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
            omega
        | node lid ll lr =>
          rcases hshL with ⟨hlid0, hlidL, hlidR, hshLL, hshLR⟩
          have hlid_le : lid ≤ cap := (hle0 lid (by simp [AuxTree.toList])).2
          have hid_ne_lid : id ≠ lid := fun h => hid_nL (h ▸ by simp [AuxTree.toList])
          have hcond7 : (Expr.reg 7).eval w stM2 = some lid := Expr.eval_reg_of_eq (by simp [stM2, AuxTree.rootId])
          have hm_lidR : stM.mem (nb + 8 * lid + 1) = lr.rootId := by rw [← hlidR]; exact (hn0 lid hlid_le).2.1
          have ha8 : Runs w p ω (.assign 8 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 7)))) stM2 .normal
              { stM2 with regs := Function.update stM2.regs 8 (nb + 8 * lid) } _ :=
            runs_assign_iff.mpr ⟨nb + 8 * lid, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM2, stM1, r2]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [stM2, AuxTree.rootId])) (by omega)) (by omega),
              rfl, rfl, rfl⟩
          set stM3 : State := { stM2 with regs := Function.update stM2.regs 8 (nb + 8 * lid) }
          have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 8) (.const 1)))) stM3 .normal
              { stM3 with regs := Function.update stM3.regs 9 lr.rootId } _ :=
            runs_assign_iff.mpr ⟨lr.rootId, Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [stM3])) (Expr.eval_const (by omega)) (by omega)) hm_lidR,
              rfl, rfl, rfl⟩
          set stM4 : State := { stM3 with regs := Function.update stM3.regs 9 lr.rootId }
          have hs1 : Runs w p ω (.store (.reg 6) (.reg 9)) stM4 .normal
              { stM4 with mem := Function.update stM.mem (nb + 8 * id) lr.rootId } _ :=
            runs_store_iff.mpr ⟨nb + 8 * id, lr.rootId, Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1]),
              Expr.eval_reg_of_eq (by simp [stM4]), rfl, rfl, rfl⟩
          set m1 := Function.update stM.mem (nb + 8 * id) lr.rootId
          have hs2 : Runs w p ω (.store (.bin .add (.reg 8) (.const 1)) (.reg 5)) { stM4 with mem := m1 } .normal
              { stM4 with mem := Function.update m1 (nb + 8 * lid + 1) id } _ :=
            runs_store_iff.mpr ⟨nb + 8 * lid + 1, id, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stM4, stM3]))
              (Expr.eval_const (by omega)) (by omega), Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, stM1, r5]),
              rfl, rfl, rfl⟩
          set m2 := Function.update m1 (nb + 8 * lid + 1) id
          have ha5 : Runs w p ω (.assign 5 (.reg 7)) { stM4 with mem := m2 } .normal
              { stM4 with mem := m2, regs := Function.update stM4.regs 5 lid } _ :=
            runs_assign_iff.mpr ⟨lid, Expr.eval_reg_of_eq (by simp [stM4, stM3, stM2, AuxTree.rootId]), rfl, rfl, rfl⟩
          have hrot_branch := ord_runs_seq_normal ha8 (ord_runs_seq_normal ha9
            (ord_runs_seq_normal hs1 (ord_runs_seq_normal hs2 ha5)))
          set t1 : AuxTree := .node lid ll (.node id lr r)
          set s1 := (s.setLeft id lr.rootId).setRight lid id
          have ht1_list : t1.toList = (AuxTree.node id (.node lid ll lr) r).toList := by
            simp [t1, AuxTree.toList, List.append_assoc]
          have ht1_cnt : t1.countNodes = (AuxTree.node id (.node lid ll lr) r).countNodes := by
            simp [t1, AuxTree.countNodes]; omega
          have ht1_rsp : rightSpineLen t1 = rightSpineLen (.node id (.node lid ll lr) r) + 1 := by
            cases r with
            | leaf => simp [t1, rightSpineLen]
            | node rid rl rr => simp [t1, rightSpineLen]
          have hmeas : 2 * t1.countNodes - rightSpineLen t1 + 1 =
              2 * (AuxTree.node id (.node lid ll lr) r).countNodes - rightSpineLen (.node id (.node lid ll lr) r) := by
            have := rightSpineLen_lt_countNodes (t := .node id (.node lid ll lr) r) (by simp)
            omega
          have hn1 : OrdNodesAt m2 nb cap s1 nf0 := by
            have hn0a : OrdNodesAt m1 nb cap (s.setLeft id lr.rootId) nf0 := by
              simpa [ordNodeAddr] using hn0.setLeft hid_le (v := lr.rootId)
            exact hn0a.setRight hlid_le (v := id)
          have he1 : ∀ k < 2 * eCap, m2 (en + k) = eN0 k := fun k hk => by
            dsimp only [m2, m1]
            rw [Function.update_of_ne (by rw [hnb, hen]; unfold ordENodeBase ordNodesBase; omega),
                Function.update_of_ne (by rw [hnb, hen]; unfold ordENodeBase ordNodesBase; omega)]
            exact he0 k hk
          have hsh1 : FreeTreeShape s1 t1 := by
            rcases AuxTree.nodup_node_unfold hLnd with ⟨-, hlid_nLL, -, hlid_nLR, -⟩
            refine ⟨hlid0, by simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, Ne.symm hid_ne_lid, hlidL],
              by simp [s1, SplayState.setRight, SplayState.nodes_updateNode, AuxTree.rootId],
              freeTreeShape_agree hshLL fun u hu => by
                have h1 : u ≠ lid := fun h => hlid_nLL (h ▸ hu)
                have h2 : u ≠ id := fun h => hid_nL (by simp [AuxTree.toList, h ▸ hu])
                simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, h1, h2],
              ⟨hid0, by simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, hid_ne_lid],
                by simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, hid_ne_lid, hidR],
                freeTreeShape_agree hshLR fun u hu => by
                  have h1 : u ≠ lid := fun h => hlid_nLR (h ▸ hu)
                  have h2 : u ≠ id := fun h => hid_nL (by simp [AuxTree.toList, h ▸ hu])
                  simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, h1, h2],
                freeTreeShape_agree hshR fun u hu => by
                  have h1 : u ≠ lid := fun h => hLR lid (by simp [AuxTree.toList]) (h ▸ hu)
                  have h2 : u ≠ id := fun h => hid_nR (h ▸ hu)
                  simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, h1, h2]⟩⟩
          have hval1 : ∀ u, (s1.nodes u).val = (s.nodes u).val := fun u => by
            by_cases h1 : u = lid
            · rw [h1]; simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, Ne.symm hid_ne_lid]
            · by_cases h2 : u = id
              · rw [h2]; simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, hid_ne_lid]
              · simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, h1, h2]
          obtain ⟨stE, cE, fh', fl', s', nf', eN', hrest, er0, er4, hnE, heE, hfrE, hpermE, hndE, hfcE, hrevE, houtE, heNE, hcE⟩ :=
            ih { stM4 with mem := m2, regs := Function.update stM4.regs 5 lid } s1 nf0 eN0 fh0 fl0 t1
              (by omega) hn1 he1 (ht1_list ▸ hnd0) hsh1
              (fun u hu => hle0 u (ht1_list ▸ hu))
              (fun u hu => by rw [hval1]; exact hkl0 u (ht1_list ▸ hu))
              (fun u hu => hdj0 u (ht1_list ▸ hu)) hflnd0 hfc0
              (by simp [stM4, stM3, stM2, stM1, r0]) (by simp [stM4, stM3, stM2, stM1, r2])
              (by simp [stM4, stM3, stM2, stM1, r3]) (by simp [stM4, stM3, stM2, stM1, r4])
              (by simp [t1, AuxTree.rootId])
          refine ⟨stE, _, fh', fl', s', nf', eN',
            ord_runs_loop_true hcond5 hid0
              (ord_runs_seq_normal ha6 (ord_runs_seq_normal ha7
                (ord_runs_cond_true hcond7 hlid0 hrot_branch)))
              hrest, er0, er4, hnE, heE,
            fun a ha1 ha2 => (hfrE a ha1 ha2).trans (by
              dsimp only [m2, m1]
              rw [Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha1 ⟨by omega, by omega⟩)]),
            ht1_list ▸ hpermE, hndE, hfcE,
            fun u => (hrevE u).trans (by
              by_cases h1 : u = lid
              · rw [h1]; simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, Ne.symm hid_ne_lid]
              · by_cases h2 : u = id
                · rw [h2]; simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, hid_ne_lid]
                · simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, h1, h2]),
            fun u hu => by
              rcases houtE u (ht1_list ▸ hu) with ⟨h1, h2⟩
              have hne1 : u ≠ lid := fun h => hu (by simp [AuxTree.toList, h])
              have hne2 : u ≠ id := fun h => hu (by simp [AuxTree.toList, h])
              exact ⟨h1.trans (by simp [s1, SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, hne1, hne2]), h2⟩,
            fun k hk => by rw [heNE k hk]; simp [ht1_list, hval1], ?_⟩
          have hmul : (2 * t1.countNodes - rightSpineLen t1 + 1) * ORD_FREE_STEP_COST =
              (2 * (AuxTree.node id (.node lid ll lr) r).countNodes - rightSpineLen (.node id (.node lid ll lr) r)) * ORD_FREE_STEP_COST :=
            congrArg (· * ORD_FREE_STEP_COST) hmeas
          unfold ORD_FREE_STEP_COST at hcE hmul ⊢
          simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
          omega
  set st0 : State := startState [b, r] mem pos
  have ha2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 0) (.const 4)))) st0 .normal
      { st0 with regs := Function.update st0.regs 2 nb } _ :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) hnb_hdr, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 2 nb }
  have ha3 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 3)))) st1 .normal
      { st1 with regs := Function.update st1.regs 3 en } _ :=
    runs_assign_iff.mpr ⟨en, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) hen_hdr, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 3 en }
  have ha4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 6)))) st2 .normal
      { st2 with regs := Function.update st2.regs 4 fh } _ :=
    runs_assign_iff.mpr ⟨fh, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) hfh_hdr, rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 4 fh }
  have ha5 : Runs w p ω (.assign 5 (.reg 1)) st3 .normal
      { st3 with regs := Function.update st3.regs 5 r } _ :=
    runs_assign_iff.mpr ⟨r, Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState]), rfl, rfl, rfl⟩
  set st4 : State := { st3 with regs := Function.update st3.regs 5 r }
  obtain ⟨stE, cE, fh', fl', sp', nf', eN', hrunL, er0, er4, hnE, heE, hfrE, hpermE, hndE, hfcE, hrevE, houtE, heNE, hcE⟩ :=
    hloop (2 * t.countNodes - rightSpineLen t) st4 st nf eNode fh fl t (le_refl _)
      hnodes hen_at hnd hshape hmem_le hkey_lt hdisj_fl hfl_nd hfc
      (by simp [st4, st3, st2, st1, st0, startState]) (by simp [st4, st3, st2, st1])
      (by simp [st4, st3, st2]) (by simp [st4, st3]) (by simp [st4, hr])
  have hst6 : Runs w p ω (.store (.bin .add (.reg 0) (.const 6)) (.reg 4)) stE .normal
      { stE with mem := Function.update stE.mem (b + 6) fh' } _ :=
    runs_store_iff.mpr ⟨b + 6, fh', Expr.eval_add (Expr.eval_reg_of_eq er0) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq er4, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.const 0)) { stE with mem := Function.update stE.mem (b + 6) fh' }
      (.returned 0) { stE with mem := Function.update stE.mem (b + 6) fh' } _ :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hfull := ord_runs_seq_normal ha2 (ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4
    (ord_runs_seq_normal ha5 (ord_runs_seq_normal hrunL (ord_runs_seq_normal hst6 hret)))))
  have h6_not_nd : ¬ InOrdNodes nb cap (b + 6) := fun h => by
    unfold InOrdNodes at h; rw [hnb] at h; unfold ordNodesBase at h; omega
  have hnE' : OrdNodesAt (Function.update stE.mem (b + 6) fh') nb cap sp' nf' :=
    hnE.congr fun a ha => Function.update_of_ne (fun (h : a = b + 6) => h6_not_nd (h ▸ ha)) _ _
  refine ⟨.returned 0, _, _, hfull, ⟨fh', fl', sp', nf', eN', by simp, hnE',
    fun k hk => by dsimp only; rw [Function.update_of_ne (by rw [hen]; unfold ordENodeBase; omega)]; exact heE k hk,
    fun a ha1 ha2 ha6 => by dsimp only; rw [Function.update_of_ne ha6]; exact hfrE a ha1 ha2,
    hpermE, hndE, hfcE, hrevE, houtE, heNE⟩, ?_⟩
  have h2t : (2 * t.countNodes - rightSpineLen t) * ORD_FREE_STEP_COST ≤
      ORD_FREE_PER_NODE * t.countNodes := by
    have h1 := Nat.mul_le_mul_right ORD_FREE_STEP_COST (Nat.sub_le (2 * t.countNodes) (rightSpineLen t))
    have h2 : 2 * t.countNodes * ORD_FREE_STEP_COST = ORD_FREE_PER_NODE * t.countNodes := by
      unfold ORD_FREE_STEP_COST ORD_FREE_PER_NODE; ring
    omega
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
  omega

end MinCostFlow.SparseCore.Program
