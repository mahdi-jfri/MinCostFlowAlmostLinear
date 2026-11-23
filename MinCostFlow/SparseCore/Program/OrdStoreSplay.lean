module

public import MinCostFlow.SparseCore.Program.OrdStoreLayout
public import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Zero-scratch Word-RAM splay rotation for the order store

This file defines `ordRotateBody`, `ordSplayStepBody`, `ordSplayBody`, and `ordSplayRootBody`
operating on 8-word node records (`OrdNodesAt`) with zero heap scratch, and proves
`ordRotateBody_runs` (matching `SplayState.rotate ordPayload` in at most `ORD_ROTATE_COST` steps).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-! ### Node-pool predicate and tree bounds -/

private theorem ord_parentIn_rootId {t : AuxTree} (p₀ : ℕ) : t.parentIn t.rootId p₀ = p₀ := by
  cases t <;> simp [AuxTree.rootId, AuxTree.parentIn]

/-- All node records `0 .. cap` at `nb` match `st` and `nf`, with mark `0`. -/
def OrdNodesAt (mem : ℕ → ℕ) (nb cap : ℕ) (st : SplayState ℕ Unit Unit) (nf : ℕ → ℕ) : Prop :=
  ∀ x ≤ cap, OrdNodeAt mem nb x (st.nodes x) (nf x)

/-- Cells of node records `0 .. cap` at `nb`. -/
def InOrdNodes (nb cap a : ℕ) : Prop := nb ≤ a ∧ a < nb + 8 * (cap + 1)

/-- `t` is a valid clean splay tree inside `st` with all node IDs and size bounded by `cap`, and
node `0` equal to `ordNullNode`. -/
structure OrdTreeOk (cap : ℕ) (st : SplayState ℕ Unit Unit) (t : AuxTree) : Prop where
  null_node : st.nodes 0 = ordNullNode
  clean : ∀ u, (st.nodes u).rev = false
  inv : TreeInv ordPayload st t
  mem_le : ∀ u ∈ t.toList, u ≤ cap
  count_le : t.countNodes ≤ cap

theorem OrdTreeOk.ptrs_le {cap x : ℕ} {st : SplayState ℕ Unit Unit} {t : AuxTree}
    (h : OrdTreeOk cap st t) (hx : x ∈ t.toList) :
    x ≤ cap ∧ (st.nodes x).left ≤ cap ∧ (st.nodes x).right ≤ cap ∧
      (st.nodes x).par ≤ cap ∧ (st.nodes x).sz ≤ cap := by
  have hsub := SplayState.SubtreeInv_findSubtree h.inv.nodup h.inv.sub hx
  rcases AuxTree.findSubtree_root_of_mem hx with ⟨l, r, hfind⟩
  rw [hfind] at hsub
  rcases hsub with ⟨-, hxl, hxr, hxpar, -, hxsz, -, -, -⟩
  refine ⟨h.mem_le x hx, ?_, ?_, ?_, ?_⟩
  · rw [hxl]
    cases l with
    | leaf => exact Nat.zero_le _
    | node lid ll lr =>
      exact h.mem_le lid (AuxTree.findSubtree_subset (by rw [hfind]; simp [AuxTree.toList]))
  · rw [hxr]
    cases r with
    | leaf => exact Nat.zero_le _
    | node rid rl rr =>
      exact h.mem_le rid (AuxTree.findSubtree_subset (by rw [hfind]; simp [AuxTree.toList]))
  · rw [hxpar]
    by_cases hxr' : x = t.rootId
    · rw [hxr', ord_parentIn_rootId]; exact Nat.zero_le _
    · exact h.mem_le _ (AuxTree.parentIn_mem_and_depth (p₀ := 0) h.inv.nodup hx hxr').1
  · rw [hxsz, ← hfind]
    have hnd_sub := AuxTree.findSubtree_nodup h.inv.nodup (subId := x)
    have hlen_le := hnd_sub.length_le_of_subset fun u hu => AuxTree.findSubtree_subset hu
    rw [AuxTree.length_toList, AuxTree.length_toList] at hlen_le
    exact le_trans hlen_le h.count_le

theorem OrdTreeOk.par_mem {cap x : ℕ} {st : SplayState ℕ Unit Unit} {t : AuxTree}
    (h : OrdTreeOk cap st t) (hx : x ∈ t.toList) (hp : (st.nodes x).par ≠ 0) :
    (st.nodes x).par ∈ t.toList := by
  have hpar := SplayState.SubtreeInv_par_eq_parentIn h.inv.nodup h.inv.sub hx
  have hxr : x ≠ t.rootId := by
    intro heq; rw [hpar, heq, ord_parentIn_rootId] at hp; exact hp rfl
  rw [hpar]
  exact (AuxTree.parentIn_mem_and_depth (p₀ := 0) h.inv.nodup hx hxr).1

theorem OrdTreeOk.left_mem {cap x : ℕ} {st : SplayState ℕ Unit Unit} {t : AuxTree}
    (h : OrdTreeOk cap st t) (hx : x ∈ t.toList) (hl : (st.nodes x).left ≠ 0) :
    (st.nodes x).left ∈ t.toList := by
  have hsub := SplayState.SubtreeInv_findSubtree h.inv.nodup h.inv.sub hx
  rcases AuxTree.findSubtree_root_of_mem hx with ⟨l, r, hfind⟩
  rw [hfind] at hsub
  rcases hsub with ⟨-, hxl, -, -, -, -, -, -, -⟩
  rw [hxl] at hl ⊢
  cases l with
  | leaf => exact absurd rfl hl
  | node lid ll lr =>
    simp only [AuxTree.rootId]
    exact AuxTree.findSubtree_subset (by rw [hfind]; simp [AuxTree.toList])

theorem OrdTreeOk.right_mem {cap x : ℕ} {st : SplayState ℕ Unit Unit} {t : AuxTree}
    (h : OrdTreeOk cap st t) (hx : x ∈ t.toList) (hr : (st.nodes x).right ≠ 0) :
    (st.nodes x).right ∈ t.toList := by
  have hsub := SplayState.SubtreeInv_findSubtree h.inv.nodup h.inv.sub hx
  rcases AuxTree.findSubtree_root_of_mem hx with ⟨l, r, hfind⟩
  rw [hfind] at hsub
  rcases hsub with ⟨-, -, hxr, -, -, -, -, -, -⟩
  rw [hxr] at hr ⊢
  cases r with
  | leaf => exact absurd rfl hr
  | node rid rl rr =>
    simp only [AuxTree.rootId]
    exact AuxTree.findSubtree_subset (by rw [hfind]; simp [AuxTree.toList])

theorem OrdTreeOk.rotate {cap x : ℕ} {st : SplayState ℕ Unit Unit} {t : AuxTree}
    (h : OrdTreeOk cap st t) (hx : x ∈ t.toList) :
    OrdTreeOk cap (SplayState.rotate ordPayload st x) (t.rotateAt x) := by
  by_cases hxr : x = t.rootId
  · have hp0 : (st.nodes x).par = 0 := by
      rw [SplayState.SubtreeInv_par_eq_parentIn h.inv.nodup h.inv.sub hx, hxr, ord_parentIn_rootId]
    have hrot : SplayState.rotate ordPayload st x = st := by simp [SplayState.rotate, hp0]
    have htr : t.rotateAt x = t := by
      cases t with
      | leaf => simp [AuxTree.toList] at hx
      | node id l r => simp only [AuxTree.rootId] at hxr; subst hxr; simp
    rw [hrot, htr]; exact h
  · have hclean_path : ∀ u ∈ t.pathTo x, (st.nodes u).rev = false ∧ (st.nodes u).tag = () :=
      fun u _ => ⟨h.clean u, rfl⟩
    obtain ⟨ht', hperm, -, -, hout, -⟩ := SplayState.rotate_preserves ordPayload_laws h.inv hx hxr hclean_path
    have h0_nmem : 0 ∉ t.toList := fun h0 => SplayState.SubtreeInv_nonZero h.inv.sub h0 rfl
    refine
      { null_node := (hout 0 h0_nmem).trans h.null_node
        clean := rotate_preserves_clean h.clean x
        inv := ht'
        mem_le := fun u hu => h.mem_le u (hperm.mem_iff.mp hu)
        count_le := by
          rw [← AuxTree.length_toList, hperm.length_eq, AuxTree.length_toList]
          exact h.count_le }

theorem OrdInv.ordTreeOk {ord : ℕ → List End} {S : OrdStoreState} (h : OrdInv ord S)
    {v : ℕ} (hv : v < S.vCap) :
    OrdTreeOk S.nextNode S.splay (S.trees v) where
  null_node := h.null_node
  clean := h.clean
  inv := h.tree_inv v hv
  mem_le u hu := (h.live_le_nextNode hv hu).2
  count_le := by
    have h1 : (S.trees v).countNodes ≤ sumCountNodes S :=
      Finset.single_le_sum (f := fun u => (S.trees u).countNodes)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hv)
    have h2 := h.sumCountNodes_add_free
    omega

/-! ### `OrdNodesAt` field updates -/

theorem OrdNodesAt.congr {mem mem' : ℕ → ℕ} {nb cap : ℕ} {st : SplayState ℕ Unit Unit}
    {nf : ℕ → ℕ} (h : OrdNodesAt mem nb cap st nf)
    (hag : ∀ a, InOrdNodes nb cap a → mem' a = mem a) :
    OrdNodesAt mem' nb cap st nf := fun x hx =>
  (h x hx).congr fun i hi => hag _ ⟨by unfold ordNodeAddr; omega, by unfold ordNodeAddr; omega⟩

theorem OrdNodesAt.updateField {mem : ℕ → ℕ} {nb cap x off val : ℕ}
    {st : SplayState ℕ Unit Unit} {nf : ℕ → ℕ}
    {f : SplayNode ℕ Unit Unit → SplayNode ℕ Unit Unit}
    (h : OrdNodesAt mem nb cap st nf) (hx : x ≤ cap) (hoff : off < 8)
    (hnd : OrdNodeAt (Function.update mem (ordNodeAddr nb x + off) val) nb x (f (st.nodes x)) (nf x)) :
    OrdNodesAt (Function.update mem (ordNodeAddr nb x + off) val) nb cap (st.updateNode x f) nf := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simpa using hnd
  · rw [SplayState.nodes_updateNode_ne _ hyx]
    exact (h y hy).congr fun i hi => Function.update_of_ne (fun heq =>
      hyx (ordNodeAddr_disjoint hi hoff heq).1) _ _

theorem OrdNodesAt.setLeft {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState ℕ Unit Unit}
    {nf : ℕ → ℕ} (h : OrdNodesAt mem nb cap st nf) (hx : x ≤ cap) :
    OrdNodesAt (Function.update mem (ordNodeAddr nb x + 0) v) nb cap (st.setLeft x v) nf := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h x hx
  refine h.updateField hx (by decide) ⟨by simp,
    by rw [Function.update_of_ne (by omega)]; exact h1,
    by rw [Function.update_of_ne (by omega)]; exact h2,
    by rw [Function.update_of_ne (by omega)]; exact h3,
    by rw [Function.update_of_ne (by omega)]; exact h4,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdNodesAt.setRight {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState ℕ Unit Unit}
    {nf : ℕ → ℕ} (h : OrdNodesAt mem nb cap st nf) (hx : x ≤ cap) :
    OrdNodesAt (Function.update mem (ordNodeAddr nb x + 1) v) nb cap (st.setRight x v) nf := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h x hx
  refine h.updateField hx (by decide) ⟨
    by rw [Function.update_of_ne (by omega)]; exact h0, by simp,
    by rw [Function.update_of_ne (by omega)]; exact h2,
    by rw [Function.update_of_ne (by omega)]; exact h3,
    by rw [Function.update_of_ne (by omega)]; exact h4,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdNodesAt.setPar {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState ℕ Unit Unit}
    {nf : ℕ → ℕ} (h : OrdNodesAt mem nb cap st nf) (hx : x ≤ cap) :
    OrdNodesAt (Function.update mem (ordNodeAddr nb x + 2) v) nb cap (st.setPar x v) nf := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h x hx
  refine h.updateField hx (by decide) ⟨
    by rw [Function.update_of_ne (by omega)]; exact h0,
    by rw [Function.update_of_ne (by omega)]; exact h1, by simp,
    by rw [Function.update_of_ne (by omega)]; exact h3,
    by rw [Function.update_of_ne (by omega)]; exact h4,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdNodesAt.setPpar {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState ℕ Unit Unit}
    {nf : ℕ → ℕ} (h : OrdNodesAt mem nb cap st nf) (hx : x ≤ cap) :
    OrdNodesAt (Function.update mem (ordNodeAddr nb x + 3) v) nb cap (st.setPpar x v) nf := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h x hx
  refine h.updateField hx (by decide) ⟨
    by rw [Function.update_of_ne (by omega)]; exact h0,
    by rw [Function.update_of_ne (by omega)]; exact h1,
    by rw [Function.update_of_ne (by omega)]; exact h2, by simp,
    by rw [Function.update_of_ne (by omega)]; exact h4,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdNodesAt.setSz {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState ℕ Unit Unit}
    {nf : ℕ → ℕ} (h : OrdNodesAt mem nb cap st nf) (hx : x ≤ cap) :
    OrdNodesAt (Function.update mem (ordNodeAddr nb x + 4) v) nb cap
      (st.updateNode x fun nd => { nd with sz := v }) nf := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h x hx
  refine h.updateField hx (by decide) ⟨
    by rw [Function.update_of_ne (by omega)]; exact h0,
    by rw [Function.update_of_ne (by omega)]; exact h1,
    by rw [Function.update_of_ne (by omega)]; exact h2,
    by rw [Function.update_of_ne (by omega)]; exact h3, by simp,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem pull_ordPayload_eq {x : ℕ} {st : SplayState ℕ Unit Unit}
    (h0 : st.nodes 0 = ordNullNode) (hx0 : x ≠ 0) :
    SplayState.pull ordPayload st x =
      st.updateNode x fun cur =>
        { cur with sz := 1 + (st.nodes (st.nodes x).left).sz + (st.nodes (st.nodes x).right).sz } := by
  unfold SplayState.pull
  simp only [hx0, ↓reduceIte]
  have hL : (if (st.nodes x).left = 0 then 0 else (st.nodes (st.nodes x).left).sz) =
      (st.nodes (st.nodes x).left).sz := by
    split_ifs with h1
    · rw [h1, h0]; rfl
    · rfl
  have hR : (if (st.nodes x).right = 0 then 0 else (st.nodes (st.nodes x).right).sz) =
      (st.nodes (st.nodes x).right).sz := by
    split_ifs with h1
    · rw [h1, h0]; rfl
    · rfl
  rw [hL, hR]

private theorem nodes_setLeft_sz (st : SplayState ℕ Unit Unit) (a b u : ℕ) :
    ((st.setLeft a b).nodes u).sz = (st.nodes u).sz := by
  by_cases h : u = a <;> simp [SplayState.setLeft, SplayState.nodes_updateNode, h]

private theorem nodes_setRight_sz (st : SplayState ℕ Unit Unit) (a b u : ℕ) :
    ((st.setRight a b).nodes u).sz = (st.nodes u).sz := by
  by_cases h : u = a <;> simp [SplayState.setRight, SplayState.nodes_updateNode, h]

private theorem nodes_setPar_sz (st : SplayState ℕ Unit Unit) (a b u : ℕ) :
    ((st.setPar a b).nodes u).sz = (st.nodes u).sz := by
  by_cases h : u = a <;> simp [SplayState.setPar, SplayState.nodes_updateNode, h]

private theorem nodes_setPpar_sz (st : SplayState ℕ Unit Unit) (a b u : ℕ) :
    ((st.setPpar a b).nodes u).sz = (st.nodes u).sz := by
  by_cases h : u = a <;> simp [SplayState.setPpar, SplayState.nodes_updateNode, h]

private theorem nodes_setPar_lr (st : SplayState ℕ Unit Unit) (a b u : ℕ) :
    ((st.setPar a b).nodes u).left = (st.nodes u).left ∧
    ((st.setPar a b).nodes u).right = (st.nodes u).right := by
  by_cases h : u = a <;> simp [SplayState.setPar, SplayState.nodes_updateNode, h]

private theorem nodes_setPpar_lr (st : SplayState ℕ Unit Unit) (a b u : ℕ) :
    ((st.setPpar a b).nodes u).left = (st.nodes u).left ∧
    ((st.setPpar a b).nodes u).right = (st.nodes u).right := by
  by_cases h : u = a <;> simp [SplayState.setPpar, SplayState.nodes_updateNode, h]

private theorem nodes_setLeft_ne (st : SplayState ℕ Unit Unit) {a u : ℕ} (b : ℕ) (h : u ≠ a) :
    (st.setLeft a b).nodes u = st.nodes u := by
  simp [SplayState.setLeft, SplayState.nodes_updateNode, h]

private theorem nodes_setRight_ne (st : SplayState ℕ Unit Unit) {a u : ℕ} (b : ℕ) (h : u ≠ a) :
    (st.setRight a b).nodes u = st.nodes u := by
  simp [SplayState.setRight, SplayState.nodes_updateNode, h]

private theorem nodes_setPar_ne (st : SplayState ℕ Unit Unit) {a u : ℕ} (b : ℕ) (h : u ≠ a) :
    (st.setPar a b).nodes u = st.nodes u := by
  simp [SplayState.setPar, SplayState.nodes_updateNode, h]

private theorem nodes_setPpar_ne (st : SplayState ℕ Unit Unit) {a u : ℕ} (b : ℕ) (h : u ≠ a) :
    (st.setPpar a b).nodes u = st.nodes u := by
  simp [SplayState.setPpar, SplayState.nodes_updateNode, h]

/-! ### Machine splay procedures -/

/-- Record address of node in register `rx`, with `nb` in register `0`. -/
abbrev ordRec (rx : ℕ) : Expr :=
  .bin .add (.reg 0) (.bin .mul (.const 8) (.reg rx))

/-- `ordRotate` on `[nb, x]`: single splay rotation moving `x` up one level, updating `left`,
`right`, `par`, `ppar`, and exact `sz`. Zero heap scratch. -/
def ordRotateBody : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 2 (ordRec 1) ;;
     .assign 3 (.load (.bin .add (.reg 2) (.const 2))) ;;
     .cond (.bin .eq (.reg 3) (.const 0)) (.ret (.const 0))
       (.assign 4 (ordRec 3) ;;
        .assign 5 (.load (.bin .add (.reg 4) (.const 2))) ;;
        .assign 6 (.load (.bin .add (.reg 4) (.const 3))) ;;
        .assign 7 (.bin .eq (.reg 1) (.load (.reg 4))) ;;
        .cond (.reg 7)
          (.assign 8 (.load (.bin .add (.reg 2) (.const 1))) ;;
           .store (.bin .add (.reg 2) (.const 1)) (.reg 3) ;;
           .store (.reg 4) (.reg 8))
          (.assign 8 (.load (.reg 2)) ;;
           .store (.reg 2) (.reg 3) ;;
           .store (.bin .add (.reg 4) (.const 1)) (.reg 8)) ;;
        .cond (.reg 8)
          (.store (.bin .add (ordRec 8) (.const 2)) (.reg 3)) .nop ;;
        .store (.bin .add (.reg 4) (.const 2)) (.reg 1) ;;
        .store (.bin .add (.reg 2) (.const 2)) (.reg 5) ;;
        .store (.bin .add (.reg 2) (.const 3)) (.reg 6) ;;
        .store (.bin .add (.reg 4) (.const 3)) (.const 0) ;;
        .cond (.reg 5)
          (.assign 9 (ordRec 5) ;;
           .cond (.bin .eq (.reg 3) (.load (.reg 9)))
             (.store (.reg 9) (.reg 1))
             (.store (.bin .add (.reg 9) (.const 1)) (.reg 1)))
          .nop ;;
        .assign 10 (.load (.reg 4)) ;;
        .assign 11 (.load (.bin .add (.reg 4) (.const 1))) ;;
        .assign 12 (.load (.bin .add (ordRec 10) (.const 4))) ;;
        .assign 13 (.load (.bin .add (ordRec 11) (.const 4))) ;;
        .store (.bin .add (.reg 4) (.const 4))
          (.bin .add (.bin .add (.const 1) (.reg 12)) (.reg 13)) ;;
        .assign 10 (.load (.reg 2)) ;;
        .assign 11 (.load (.bin .add (.reg 2) (.const 1))) ;;
        .assign 12 (.load (.bin .add (ordRec 10) (.const 4))) ;;
        .assign 13 (.load (.bin .add (ordRec 11) (.const 4))) ;;
        .store (.bin .add (.reg 2) (.const 4))
          (.bin .add (.bin .add (.const 1) (.reg 12)) (.reg 13)) ;;
        .ret (.const 0)))

theorem ordRotateBody_noRand : ordRotateBody.NoRand := by
  simp [ordRotateBody, ordRec, Stmt.NoRand]

def ORD_ROTATE_COST : ℕ := 260

/-! ### Run theorem for `ordRotateBody` -/

theorem ordRotateBody_runs {w nb cap x pos : ℕ} {p : Program} (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState ℕ Unit Unit} {nf : ℕ → ℕ} {t : AuxTree}
    (hnodes : OrdNodesAt mem nb cap st nf) (hok : OrdTreeOk cap st t)
    (hx : x ∈ t.toList) (hw : nb + 8 * (cap + 1) < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω ordRotateBody (startState [nb, x] mem pos) o st' c ∧
      (OrdNodesAt st'.mem nb cap (SplayState.rotate ordPayload st x) nf ∧
        ∀ a, ¬ InOrdNodes nb cap a → st'.mem a = mem a) ∧
      0 + c ≤ ORD_ROTATE_COST := by
  have hx0 : x ≠ 0 := SplayState.SubtreeInv_nonZero hok.inv.sub hx
  obtain ⟨hxc, hxlc, hxrc, hpc, hxsz⟩ := hok.ptrs_le hx
  set pa := (st.nodes x).par with hpa
  have hm_x2 : mem (nb + 8 * x + 2) = pa := (hnodes x hxc).2.2.1
  unfold ordRotateBody
  rw [startState]
  wram_step
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm_x2]
  wram_step
  · have hp0 : pa = 0 := hcond
    wram_step
    · refine ⟨?_, fun _ _ => rfl⟩
      simpa [SplayState.rotate, hx0, ← hpa, hp0] using hnodes
    · unfold ORD_ROTATE_COST; wram_cost
  have hp0 : pa ≠ 0 := hcond
  have hp_mem : pa ∈ t.toList := hok.par_mem hx hp0
  obtain ⟨-, hplc, hprc, hgc, hpsz⟩ := hok.ptrs_le hp_mem
  set g := (st.nodes pa).par with hg
  set pp := (st.nodes pa).ppar with hpp
  set isLeft := (x == (st.nodes pa).left) with hisL
  set b := if isLeft then (st.nodes x).right else (st.nodes x).left with hb
  have hbc : b ≤ cap := by dsimp only [b]; split_ifs <;> assumption
  have hne_xp : x ≠ pa := by
    intro heq
    have hpar := SplayState.SubtreeInv_par_eq_parentIn hok.inv.nodup hok.inv.sub hx
    rw [← hpa] at hpar
    have hxr : x ≠ t.rootId := by intro h; rw [h, ord_parentIn_rootId] at hpar; exact hp0 hpar
    have hdep := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hok.inv.nodup hx hxr).2.1
    rw [← hpar, ← heq] at hdep; omega
  have hne_xg : x ≠ g := by
    intro heq
    have hparx := SplayState.SubtreeInv_par_eq_parentIn hok.inv.nodup hok.inv.sub hx
    rw [← hpa] at hparx
    have hxr : x ≠ t.rootId := by intro h; rw [h, ord_parentIn_rootId] at hparx; exact hp0 hparx
    have hdepx := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hok.inv.nodup hx hxr).2.1
    have hparp := SplayState.SubtreeInv_par_eq_parentIn hok.inv.nodup hok.inv.sub hp_mem
    rw [← hg] at hparp
    by_cases hpr : pa = t.rootId
    · rw [hpr, ord_parentIn_rootId] at hparp; rw [hparp] at heq; exact hx0 heq
    · have hdepp := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hok.inv.nodup hp_mem hpr).2.1
      rw [← hparp, ← heq] at hdepp; rw [← hparx] at hdepx; omega
  have hne_pg : pa ≠ g := by
    intro heq
    have hparp := SplayState.SubtreeInv_par_eq_parentIn hok.inv.nodup hok.inv.sub hp_mem
    rw [← hg] at hparp
    by_cases hpr : pa = t.rootId
    · rw [hpr, ord_parentIn_rootId] at hparp; rw [hparp] at heq; exact hp0 heq
    · have hdepp := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hok.inv.nodup hp_mem hpr).2.1
      rw [← hparp, ← heq] at hdepp; omega
  have hm_p0 : mem (nb + 8 * pa) = (st.nodes pa).left := (hnodes pa hpc).1
  have hm_p2 : mem (nb + 8 * pa + 2) = g := (hnodes pa hpc).2.2.1
  have hm_p3 : mem (nb + 8 * pa + 3) = pp := (hnodes pa hpc).2.2.2.1
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm_p2]
  wram_step; try dsimp only
  rw [hm_p3]
  wram_step; try dsimp only
  rw [hm_p0]
  -- Define model intermediate states st1..st8 (opaque variables to prevent whnf blowup)
  obtain ⟨st1, hst1⟩ : ∃ s, s = (if isLeft then st.setRight x pa else st.setLeft x pa) := ⟨_, rfl⟩
  obtain ⟨st2, hst2⟩ : ∃ s, s = (if isLeft then st1.setLeft pa b else st1.setRight pa b) := ⟨_, rfl⟩
  obtain ⟨st3, hst3⟩ : ∃ s, s = (if b = 0 then st2 else st2.setPar b pa) := ⟨_, rfl⟩
  obtain ⟨st4, hst4⟩ : ∃ s, s = st3.setPar pa x := ⟨_, rfl⟩
  obtain ⟨st5, hst5⟩ : ∃ s, s = st4.setPar x g := ⟨_, rfl⟩
  obtain ⟨st6, hst6⟩ : ∃ s, s = st5.setPpar x pp := ⟨_, rfl⟩
  obtain ⟨st7, hst7⟩ : ∃ s, s = st6.setPpar pa 0 := ⟨_, rfl⟩
  obtain ⟨st8, hst8⟩ : ∃ s, s = (if g = 0 then st7 else if pa == (st7.nodes g).left then st7.setLeft g x else st7.setRight g x) := ⟨_, rfl⟩
  have hst8_0 : st8.nodes 0 = ordNullNode := by
    have h1 : st1.nodes 0 = ordNullNode := by
      rw [hst1]; split_ifs
      · rw [nodes_setRight_ne _ _ (Ne.symm hx0)]; exact hok.null_node
      · rw [nodes_setLeft_ne _ _ (Ne.symm hx0)]; exact hok.null_node
    have h2 : st2.nodes 0 = ordNullNode := by
      rw [hst2]; split_ifs
      · rw [nodes_setLeft_ne _ _ (Ne.symm hp0)]; exact h1
      · rw [nodes_setRight_ne _ _ (Ne.symm hp0)]; exact h1
    have h3 : st3.nodes 0 = ordNullNode := by
      rw [hst3]; split_ifs with hb0; exact h2; rw [nodes_setPar_ne _ _ (Ne.symm hb0)]; exact h2
    have h7 : st7.nodes 0 = ordNullNode := by
      rw [hst7, hst6, hst5, hst4, nodes_setPpar_ne _ _ (Ne.symm hp0), nodes_setPpar_ne _ _ (Ne.symm hx0),
          nodes_setPar_ne _ _ (Ne.symm hx0), nodes_setPar_ne _ _ (Ne.symm hp0)]; exact h3
    rw [hst8]; split_ifs with hg0
    · exact h7
    · rw [nodes_setLeft_ne _ _ (Ne.symm hg0)]; exact h7
    · rw [nodes_setRight_ne _ _ (Ne.symm hg0)]; exact h7
  have hst8_lr : ∀ u, u ≠ g →
      (st8.nodes u).left = (st2.nodes u).left ∧ (st8.nodes u).right = (st2.nodes u).right := by
    intro u hug
    have h3 : (st3.nodes u).left = (st2.nodes u).left ∧ (st3.nodes u).right = (st2.nodes u).right := by
      rw [hst3]; split_ifs; exact ⟨rfl, rfl⟩; exact nodes_setPar_lr st2 b pa u
    have h7 : (st7.nodes u).left = (st2.nodes u).left ∧ (st7.nodes u).right = (st2.nodes u).right := by
      rw [hst7, hst6, hst5, hst4, (nodes_setPpar_lr _ _ _ u).1, (nodes_setPpar_lr _ _ _ u).2,
          (nodes_setPpar_lr _ _ _ u).1, (nodes_setPpar_lr _ _ _ u).2,
          (nodes_setPar_lr _ _ _ u).1, (nodes_setPar_lr _ _ _ u).2,
          (nodes_setPar_lr _ _ _ u).1, (nodes_setPar_lr _ _ _ u).2]; exact h3
    rw [hst8]; split_ifs
    · exact h7
    · rw [nodes_setLeft_ne _ _ hug]; exact h7
    · rw [nodes_setRight_ne _ _ hug]; exact h7
  have hsz_st8 : ∀ u, (st8.nodes u).sz = (st.nodes u).sz := by
    intro u
    have h1 : (st1.nodes u).sz = (st.nodes u).sz := by
      rw [hst1]; split_ifs <;> [exact nodes_setRight_sz _ _ _ u; exact nodes_setLeft_sz _ _ _ u]
    have h2 : (st2.nodes u).sz = (st.nodes u).sz := by
      rw [hst2]; split_ifs <;> [rw [nodes_setLeft_sz, h1]; rw [nodes_setRight_sz, h1]]
    have h3 : (st3.nodes u).sz = (st.nodes u).sz := by
      rw [hst3]; split_ifs <;> [exact h2; rw [nodes_setPar_sz, h2]]
    have h7 : (st7.nodes u).sz = (st.nodes u).sz := by
      rw [hst7, hst6, hst5, hst4, nodes_setPpar_sz, nodes_setPpar_sz, nodes_setPar_sz, nodes_setPar_sz, h3]
    rw [hst8]; split_ifs; exact h7; rw [nodes_setLeft_sz, h7]; rw [nodes_setRight_sz, h7]
  have hmem_le : ∀ u, (u = 0 ∨ u ∈ t.toList) → u ≤ cap ∧ (st.nodes u).sz ≤ cap := by
    rintro u (rfl | hu)
    · rw [hok.null_node]; exact ⟨Nat.zero_le _, by simp [ordNullNode]⟩
    · exact ⟨(hok.ptrs_le hu).1, (hok.ptrs_le hu).2.2.2.2⟩
  have hb_in : b = 0 ∨ b ∈ t.toList := by
    dsimp only [b]; split_ifs
    · by_cases h : (st.nodes x).right = 0; exact Or.inl h; exact Or.inr (hok.right_mem hx h)
    · by_cases h : (st.nodes x).left = 0; exact Or.inl h; exact Or.inr (hok.left_mem hx h)
  have hpl_in : (st8.nodes pa).left = 0 ∨ (st8.nodes pa).left ∈ t.toList := by
    rw [(hst8_lr pa hne_pg).1, hst2, hst1]
    have h0 : (st.nodes pa).left = 0 ∨ (st.nodes pa).left ∈ t.toList := by
      by_cases h : (st.nodes pa).left = 0; exact Or.inl h; exact Or.inr (hok.left_mem hp_mem h)
    split_ifs
    · simp [SplayState.setLeft, SplayState.nodes_updateNode, hb_in]
    · simp [SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode, Ne.symm hne_xp, h0]
  have hpr_in : (st8.nodes pa).right = 0 ∨ (st8.nodes pa).right ∈ t.toList := by
    rw [(hst8_lr pa hne_pg).2, hst2, hst1]
    have h0 : (st.nodes pa).right = 0 ∨ (st.nodes pa).right ∈ t.toList := by
      by_cases h : (st.nodes pa).right = 0; exact Or.inl h; exact Or.inr (hok.right_mem hp_mem h)
    split_ifs
    · simp [SplayState.setLeft, SplayState.setRight, SplayState.nodes_updateNode, Ne.symm hne_xp, h0]
    · simp [SplayState.setRight, SplayState.nodes_updateNode, hb_in]
  have hxl8_in : (st8.nodes x).left = 0 ∨ (st8.nodes x).left ∈ t.toList := by
    rw [(hst8_lr x hne_xg).1, hst2, hst1]
    have h0 : (st.nodes x).left = 0 ∨ (st.nodes x).left ∈ t.toList := by
      by_cases h : (st.nodes x).left = 0; exact Or.inl h; exact Or.inr (hok.left_mem hx h)
    split_ifs
    · rw [nodes_setLeft_ne _ _ hne_xp]; simp [SplayState.setRight, SplayState.nodes_updateNode, h0]
    · rw [nodes_setRight_ne _ _ hne_xp]; simp [SplayState.setLeft, SplayState.nodes_updateNode, hp_mem]
  have hxr8_in : (st8.nodes x).right = 0 ∨ (st8.nodes x).right ∈ t.toList := by
    rw [(hst8_lr x hne_xg).2, hst2, hst1]
    have h0 : (st.nodes x).right = 0 ∨ (st.nodes x).right ∈ t.toList := by
      by_cases h : (st.nodes x).right = 0; exact Or.inl h; exact Or.inr (hok.right_mem hx h)
    split_ifs
    · rw [nodes_setLeft_ne _ _ hne_xp]; simp [SplayState.setRight, SplayState.nodes_updateNode, hp_mem]
    · rw [nodes_setRight_ne _ _ hne_xp]; simp [SplayState.setLeft, SplayState.nodes_updateNode, h0]
  have hst8_pl : (st8.nodes pa).left ≤ cap ∧ (st8.nodes pa).right ≤ cap :=
    ⟨(hmem_le _ hpl_in).1, (hmem_le _ hpr_in).1⟩
  have hst8_xl : (st8.nodes x).left ≤ cap ∧ (st8.nodes x).right ≤ cap :=
    ⟨(hmem_le _ hxl8_in).1, (hmem_le _ hxr8_in).1⟩
  have hpl_sz : (st8.nodes (st8.nodes pa).left).sz ≤ cap := by rw [hsz_st8]; exact (hmem_le _ hpl_in).2
  have hpr_sz : (st8.nodes (st8.nodes pa).right).sz ≤ cap := by rw [hsz_st8]; exact (hmem_le _ hpr_in).2
  obtain ⟨st9, hst9⟩ : ∃ s, s = SplayState.pull ordPayload st8 pa := ⟨_, rfl⟩
  have hrot_eq : SplayState.rotate ordPayload st x = SplayState.pull ordPayload st9 x := by
    unfold SplayState.rotate
    simp only [hx0, ↓reduceIte, ← hpa, hp0]
    rw [hst9, hst8, hst7, hst6, hst5, hst4, hst3, hst2, hst1]
  -- Continuation from `st2`
  have hafter2 : ∀ (stM : State),
      OrdNodesAt stM.mem nb cap st2 nf →
      (∀ a, ¬ InOrdNodes nb cap a → stM.mem a = mem a) →
      stM.regs 0 = nb → stM.regs 1 = x → stM.regs 2 = nb + 8 * x →
      stM.regs 3 = pa → stM.regs 4 = nb + 8 * pa → stM.regs 5 = g →
      stM.regs 6 = pp → stM.regs 8 = b →
      ∃ o st' c, Runs w p ω
        (.cond (.reg 8) (.store (.bin .add (ordRec 8) (.const 2)) (.reg 3)) .nop ;;
         .store (.bin .add (.reg 4) (.const 2)) (.reg 1) ;;
         .store (.bin .add (.reg 2) (.const 2)) (.reg 5) ;;
         .store (.bin .add (.reg 2) (.const 3)) (.reg 6) ;;
         .store (.bin .add (.reg 4) (.const 3)) (.const 0) ;;
         .cond (.reg 5)
           (.assign 9 (ordRec 5) ;;
            .cond (.bin .eq (.reg 3) (.load (.reg 9)))
              (.store (.reg 9) (.reg 1))
              (.store (.bin .add (.reg 9) (.const 1)) (.reg 1)))
           .nop ;;
         .assign 10 (.load (.reg 4)) ;;
         .assign 11 (.load (.bin .add (.reg 4) (.const 1))) ;;
         .assign 12 (.load (.bin .add (ordRec 10) (.const 4))) ;;
         .assign 13 (.load (.bin .add (ordRec 11) (.const 4))) ;;
         .store (.bin .add (.reg 4) (.const 4))
           (.bin .add (.bin .add (.const 1) (.reg 12)) (.reg 13)) ;;
         .assign 10 (.load (.reg 2)) ;;
         .assign 11 (.load (.bin .add (.reg 2) (.const 1))) ;;
         .assign 12 (.load (.bin .add (ordRec 10) (.const 4))) ;;
         .assign 13 (.load (.bin .add (ordRec 11) (.const 4))) ;;
         .store (.bin .add (.reg 2) (.const 4))
           (.bin .add (.bin .add (.const 1) (.reg 12)) (.reg 13)) ;;
         .ret (.const 0)) stM o st' c ∧
        (OrdNodesAt st'.mem nb cap (SplayState.rotate ordPayload st x) nf ∧
          ∀ a, ¬ InOrdNodes nb cap a → st'.mem a = mem a) ∧
        85 + c ≤ ORD_ROTATE_COST := by
    intro stM hn2 hfr2 r0 r1 r2 r3 r4 r5 r6 r8
    -- Continuation from `st8` (the two pulls and ret)
    have htail : ∀ (stE : State),
        OrdNodesAt stE.mem nb cap st8 nf →
        (∀ a, ¬ InOrdNodes nb cap a → stE.mem a = mem a) →
        stE.regs 0 = nb → stE.regs 1 = x → stE.regs 2 = nb + 8 * x →
        stE.regs 3 = pa → stE.regs 4 = nb + 8 * pa →
        ∃ o st' c, Runs w p ω
          (.assign 10 (.load (.reg 4)) ;;
           .assign 11 (.load (.bin .add (.reg 4) (.const 1))) ;;
           .assign 12 (.load (.bin .add (ordRec 10) (.const 4))) ;;
           .assign 13 (.load (.bin .add (ordRec 11) (.const 4))) ;;
           .store (.bin .add (.reg 4) (.const 4))
             (.bin .add (.bin .add (.const 1) (.reg 12)) (.reg 13)) ;;
           .assign 10 (.load (.reg 2)) ;;
           .assign 11 (.load (.bin .add (.reg 2) (.const 1))) ;;
           .assign 12 (.load (.bin .add (ordRec 10) (.const 4))) ;;
           .assign 13 (.load (.bin .add (ordRec 11) (.const 4))) ;;
           .store (.bin .add (.reg 2) (.const 4))
             (.bin .add (.bin .add (.const 1) (.reg 12)) (.reg 13)) ;;
           .ret (.const 0)) stE o st' c ∧
          (OrdNodesAt st'.mem nb cap (SplayState.rotate ordPayload st x) nf ∧
            ∀ a, ¬ InOrdNodes nb cap a → st'.mem a = mem a) ∧
          165 + c ≤ ORD_ROTATE_COST := by
      intro stE hn8 hfr8 e0 e1 e2 e3 e4
      have hm_pl : stE.mem (nb + 8 * pa) = (st8.nodes pa).left := (hn8 pa hpc).1
      have hm_pr : stE.mem (nb + 8 * pa + 1) = (st8.nodes pa).right := (hn8 pa hpc).2.1
      have hm_plsz : stE.mem (nb + 8 * (st8.nodes pa).left + 4) = (st8.nodes (st8.nodes pa).left).sz :=
        (hn8 _ hst8_pl.1).2.2.2.2.1
      have hm_prsz : stE.mem (nb + 8 * (st8.nodes pa).right + 4) = (st8.nodes (st8.nodes pa).right).sz :=
        (hn8 _ hst8_pl.2).2.2.2.2.1
      refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_reg_of_eq e4) hm_pl) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * pa) (by simp [e4]))
        (Expr.eval_const (by omega)) (by omega)) hm_pr) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
        (Expr.eval_reg_of_eq (v := nb) (by simp [e0]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := (st8.nodes pa).left) (by simp)) (by omega))
        (by omega)) (Expr.eval_const (by omega)) (by omega)) hm_plsz) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
        (Expr.eval_reg_of_eq (v := nb) (by simp [e0]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := (st8.nodes pa).right) (by simp)) (by omega))
        (by omega)) (Expr.eval_const (by omega)) (by omega)) hm_prsz) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      have hn9 : OrdNodesAt (Function.update stE.mem (nb + 8 * pa + 4)
          (1 + (st8.nodes (st8.nodes pa).left).sz + (st8.nodes (st8.nodes pa).right).sz)) nb cap st9 nf := by
        rw [hst9, pull_ordPayload_eq hst8_0 hp0]; exact hn8.setSz hpc
      have hfr9 : ∀ a, ¬ InOrdNodes nb cap a →
          Function.update stE.mem (nb + 8 * pa + 4)
            (1 + (st8.nodes (st8.nodes pa).left).sz + (st8.nodes (st8.nodes pa).right).sz) a = mem a := fun a ha => by
        rw [Function.update_of_ne (fun heq => ha ⟨by omega, by omega⟩)]; exact hfr8 a ha
      have hst9_0 : st9.nodes 0 = ordNullNode := by
        rw [hst9, pull_ordPayload_eq hst8_0 hp0, SplayState.nodes_updateNode_ne _ (Ne.symm hp0)]; exact hst8_0
      have hst9_xl : (st9.nodes x).left = (st8.nodes x).left ∧ (st9.nodes x).right = (st8.nodes x).right := by
        rw [hst9, pull_ordPayload_eq hst8_0 hp0, SplayState.nodes_updateNode_ne _ hne_xp]; exact ⟨rfl, rfl⟩
      have hsz9_le : ∀ u, (u = 0 ∨ u ∈ t.toList) → (st9.nodes u).sz ≤ 2 * cap + 1 := by
        intro u hu
        rw [hst9, pull_ordPayload_eq hst8_0 hp0, SplayState.nodes_updateNode]
        split_ifs
        · dsimp only; omega
        · rw [hsz_st8]; have := (hmem_le u hu).2; omega
      have hxl_sz : (st9.nodes (st9.nodes x).left).sz ≤ 2 * cap + 1 := hsz9_le _ (hst9_xl.1 ▸ hxl8_in)
      have hxr_sz : (st9.nodes (st9.nodes x).right).sz ≤ 2 * cap + 1 := hsz9_le _ (hst9_xl.2 ▸ hxr8_in)
      set m9 := Function.update stE.mem (nb + 8 * pa + 4)
          (1 + (st8.nodes (st8.nodes pa).left).sz + (st8.nodes (st8.nodes pa).right).sz)
      have hm9_xl : m9 (nb + 8 * x) = (st9.nodes x).left := (hn9 x hxc).1
      have hm9_xr : m9 (nb + 8 * x + 1) = (st9.nodes x).right := (hn9 x hxc).2.1
      have hm9_xlsz : m9 (nb + 8 * (st9.nodes x).left + 4) = (st9.nodes (st9.nodes x).left).sz :=
        (hn9 _ (hst9_xl.1 ▸ hst8_xl.1)).2.2.2.2.1
      have hm9_xrsz : m9 (nb + 8 * (st9.nodes x).right + 4) = (st9.nodes (st9.nodes x).right).sz :=
        (hn9 _ (hst9_xl.2 ▸ hst8_xl.2)).2.2.2.2.1
      refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := nb + 8 * x) (by simp [e2])) hm9_xl) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * x) (by simp [e2]))
        (Expr.eval_const (by omega)) (by omega)) hm9_xr) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
        (Expr.eval_reg_of_eq (v := nb) (by simp [e0]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := (st9.nodes x).left) (by simp)) (by omega))
        (by omega)) (Expr.eval_const (by omega)) (by omega)) hm9_xlsz) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
        (Expr.eval_reg_of_eq (v := nb) (by simp [e0]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := (st9.nodes x).right) (by simp)) (by omega))
        (by omega)) (Expr.eval_const (by omega)) (by omega)) hm9_xrsz) ?_
      refine runs_seq_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * x) (by simp [e2])) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_add (Expr.eval_add (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (v := (st9.nodes (st9.nodes x).left).sz) (by simp)) (by omega))
          (Expr.eval_reg_of_eq (v := (st9.nodes (st9.nodes x).right).sz) (by simp)) (by omega)) ?_
      wram_step
      · rw [hrot_eq, pull_ordPayload_eq hst9_0 hx0]
        refine ⟨hn9.setSz hxc, fun a ha => ?_⟩
        dsimp only
        rw [Function.update_of_ne (fun heq => ha ⟨by omega, by omega⟩)]
        exact hfr9 a ha
      · unfold ORD_ROTATE_COST; wram_cost
    -- Continuation from `st3` through `st7` and `st8`
    have hafter3 : ∀ (stM3 : State),
        OrdNodesAt stM3.mem nb cap st3 nf →
        (∀ a, ¬ InOrdNodes nb cap a → stM3.mem a = mem a) →
        stM3.regs 0 = nb → stM3.regs 1 = x → stM3.regs 2 = nb + 8 * x →
        stM3.regs 3 = pa → stM3.regs 4 = nb + 8 * pa → stM3.regs 5 = g → stM3.regs 6 = pp →
        ∃ o st' c, Runs w p ω
          (.store (.bin .add (.reg 4) (.const 2)) (.reg 1) ;;
           .store (.bin .add (.reg 2) (.const 2)) (.reg 5) ;;
           .store (.bin .add (.reg 2) (.const 3)) (.reg 6) ;;
           .store (.bin .add (.reg 4) (.const 3)) (.const 0) ;;
           .cond (.reg 5)
             (.assign 9 (ordRec 5) ;;
              .cond (.bin .eq (.reg 3) (.load (.reg 9)))
                (.store (.reg 9) (.reg 1))
                (.store (.bin .add (.reg 9) (.const 1)) (.reg 1)))
             .nop ;;
           .assign 10 (.load (.reg 4)) ;;
           .assign 11 (.load (.bin .add (.reg 4) (.const 1))) ;;
           .assign 12 (.load (.bin .add (ordRec 10) (.const 4))) ;;
           .assign 13 (.load (.bin .add (ordRec 11) (.const 4))) ;;
           .store (.bin .add (.reg 4) (.const 4))
             (.bin .add (.bin .add (.const 1) (.reg 12)) (.reg 13)) ;;
           .assign 10 (.load (.reg 2)) ;;
           .assign 11 (.load (.bin .add (.reg 2) (.const 1))) ;;
           .assign 12 (.load (.bin .add (ordRec 10) (.const 4))) ;;
           .assign 13 (.load (.bin .add (ordRec 11) (.const 4))) ;;
           .store (.bin .add (.reg 2) (.const 4))
             (.bin .add (.bin .add (.const 1) (.reg 12)) (.reg 13)) ;;
           .ret (.const 0)) stM3 o st' c ∧
          (OrdNodesAt st'.mem nb cap (SplayState.rotate ordPayload st x) nf ∧
            ∀ a, ¬ InOrdNodes nb cap a → st'.mem a = mem a) ∧
          105 + c ≤ ORD_ROTATE_COST := by
      intro stM3 hn3 hfr3 m0 m1 m2 m3 m4 m5 m6
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      set m7 := Function.update (Function.update (Function.update (Function.update stM3.mem
        (nb + 8 * pa + 2) x) (nb + 8 * x + 2) g) (nb + 8 * x + 3) pp) (nb + 8 * pa + 3) 0
      have hn7 : OrdNodesAt m7 nb cap st7 nf := by
        rw [hst7, hst6, hst5, hst4]; exact (((hn3.setPar hpc).setPar hxc).setPpar hxc).setPpar hpc
      have hfr7 : ∀ a, ¬ InOrdNodes nb cap a → m7 a = mem a := fun a ha => by
        dsimp only [m7]
        rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
            Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
            Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
            Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
        exact hfr3 a ha
      refine runs_seq_cond_le (Expr.eval_reg_of_eq m5) (fun hg0 => ?_) (fun hg0 => ?_)
      · refine runs_seq_assoc_le ?_
        wram_step; try dsimp only
        have hm7_g0 : m7 (nb + 8 * g) = (st7.nodes g).left := (hn7 g hgc).1
        have hgl_eq : (Expr.bin .eq (.reg 3) (.load (.reg 9))).eval w
            { mem := m7, regs := Function.update stM3.regs 9 (nb + 8 * g), pos := stM3.pos } =
            some (if pa = (st7.nodes g).left then 1 else 0) := by
          refine Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [m3]))
            (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hm7_g0) (by omega)
        refine runs_seq_cond_le hgl_eq (fun hgl => ?_) (fun hgl => ?_)
        · have hpeq : pa = (st7.nodes g).left := by by_contra h; simp [h] at hgl
          have hst8_eq : st8 = st7.setLeft g x := by simp [hst8, hg0, hpeq]
          refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
          have hn8' : OrdNodesAt (Function.update m7 (nb + 8 * g) x) nb cap st8 nf := by
            rw [hst8_eq]; simpa [ordNodeAddr] using hn7.setLeft hgc
          refine (fun ⟨o, st', c, hr, hq, hc⟩ => ⟨o, st', c, hr, hq, by simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩)
            (htail _ hn8'
              (fun a ha => by dsimp only; rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]; exact hfr7 a ha)
              (by simp [m0]) (by simp [m1]) (by simp [m2]) (by simp [m3]) (by simp [m4]))
        · have hpne : pa ≠ (st7.nodes g).left := by intro h; simp [h] at hgl
          have hst8_eq : st8 = st7.setRight g x := by simp [hst8, hg0, hpne]
          refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
          have hn8' : OrdNodesAt (Function.update m7 (nb + 8 * g + 1) x) nb cap st8 nf := by
            rw [hst8_eq]; exact hn7.setRight hgc
          refine (fun ⟨o, st', c, hr, hq, hc⟩ => ⟨o, st', c, hr, hq, by simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩)
            (htail _ hn8'
              (fun a ha => by dsimp only; rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]; exact hfr7 a ha)
              (by simp [m0]) (by simp [m1]) (by simp [m2]) (by simp [m3]) (by simp [m4]))
      · refine runs_seq_nop_le ?_
        have hst8_eq : st8 = st7 := by simp [hst8, hg0]
        have hn8' : OrdNodesAt m7 nb cap st8 nf := by rw [hst8_eq]; exact hn7
        have ⟨o, st', c, hr, hq, hc⟩ := htail { stM3 with mem := m7 } hn8' hfr7 m0 m1 m2 m3 m4
        exact ⟨o, st', c, hr, hq, by simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩
    -- Execute `if b ≠ 0 then b.par := pa`
    refine runs_seq_cond_le (Expr.eval_reg_of_eq r8) (fun hb0 => ?_) (fun hb0 => ?_)
    · refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      have hst3_eq : st3 = st2.setPar b pa := by simp [hst3, hb0]
      have hn3' : OrdNodesAt (Function.update stM.mem (nb + 8 * b + 2) pa) nb cap st3 nf := by
        rw [hst3_eq]; exact hn2.setPar hbc
      have ⟨o, st', c, hr, hq, hc⟩ := hafter3 { stM with mem := Function.update stM.mem (nb + 8 * b + 2) pa } hn3'
        (fun a ha => by dsimp only; rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]; exact hfr2 a ha)
        r0 r1 r2 r3 r4 r5 r6
      exact ⟨o, st', c, hr, hq, by simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at *; omega⟩
    · refine runs_seq_nop_le ?_
      have hst3_eq : st3 = st2 := by simp [hst3, hb0]
      have hn3' : OrdNodesAt stM.mem nb cap st3 nf := by rw [hst3_eq]; exact hn2
      have ⟨o, st', c, hr, hq, hc⟩ := hafter3 stM hn3' hfr2 r0 r1 r2 r3 r4 r5 r6
      exact ⟨o, st', c, hr, hq, by simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at *; omega⟩
  -- Execute the first `if isLeft` branch
  refine runs_seq_cond_le (Expr.eval_reg_of_eq (v := if x = (st.nodes pa).left then 1 else 0) (by simp)) (fun hl => ?_) (fun hl => ?_)
  · have hisL_t : isLeft = true := by
      dsimp only [isLeft]; rw [beq_iff_eq]; by_contra h; simp [h] at hl
    have hb_eq : b = (st.nodes x).right := by simp [b, hisL_t]
    have hst1_eq : st1 = st.setRight x pa := by simp [hst1, hisL_t]
    have hst2_eq : st2 = st1.setLeft pa b := by simp [hst2, hisL_t]
    have hm_xr : mem (nb + 8 * x + 1) = (st.nodes x).right := (hnodes x hxc).2.1
    refine runs_seq_assoc_le ?_
    wram_step; try dsimp only
    rw [hm_xr, ← hb_eq]
    refine runs_seq_assoc_le ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * x) (by simp)) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (v := pa) (by simp)) ?_
    refine runs_seq_store_le (Expr.eval_reg_of_eq (v := nb + 8 * pa) (by simp)) (Expr.eval_reg_of_eq (v := b) (by simp)) ?_
    have hn1 : OrdNodesAt (Function.update mem (nb + 8 * x + 1) pa) nb cap st1 nf := hst1_eq ▸ hnodes.setRight hxc
    have hn2 : OrdNodesAt (Function.update (Function.update mem (nb + 8 * x + 1) pa) (nb + 8 * pa) b) nb cap st2 nf :=
      hst2_eq ▸ (by simpa [ordNodeAddr] using hn1.setLeft hpc)
    have hfr2 : ∀ a, ¬ InOrdNodes nb cap a → Function.update (Function.update mem (nb + 8 * x + 1) pa) (nb + 8 * pa) b a = mem a := fun a ha => by
      rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩), Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
    refine (fun ⟨o, st', c, hr, hq, hc⟩ => ⟨o, st', c, hr, hq, by simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩)
      (hafter2 _ hn2 hfr2 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
  · have hisL_f : isLeft = false := by
      dsimp only [isLeft]; rw [beq_eq_false_iff_ne]; intro h; simp [h] at hl
    have hb_eq : b = (st.nodes x).left := by simp [b, hisL_f]
    have hst1_eq : st1 = st.setLeft x pa := by simp [hst1, hisL_f]
    have hst2_eq : st2 = st1.setRight pa b := by simp [hst2, hisL_f]
    have hm_xl : mem (nb + 8 * x) = (st.nodes x).left := (hnodes x hxc).1
    refine runs_seq_assoc_le ?_
    wram_step; try dsimp only
    rw [hm_xl, ← hb_eq]
    refine runs_seq_assoc_le ?_
    refine runs_seq_store_le (Expr.eval_reg_of_eq (v := nb + 8 * x) (by simp)) (Expr.eval_reg_of_eq (v := pa) (by simp)) ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * pa) (by simp)) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (v := b) (by simp)) ?_
    have hn1 : OrdNodesAt (Function.update mem (nb + 8 * x) pa) nb cap st1 nf := hst1_eq ▸ (by simpa [ordNodeAddr] using hnodes.setLeft hxc)
    have hn2 : OrdNodesAt (Function.update (Function.update mem (nb + 8 * x) pa) (nb + 8 * pa + 1) b) nb cap st2 nf := hst2_eq ▸ hn1.setRight hpc
    have hfr2 : ∀ a, ¬ InOrdNodes nb cap a → Function.update (Function.update mem (nb + 8 * x) pa) (nb + 8 * pa + 1) b a = mem a := fun a ha => by
      rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩), Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
    refine (fun ⟨o, st', c, hr, hq, hc⟩ => ⟨o, st', c, hr, hq, by simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩)
      (hafter2 _ hn2 hfr2 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))

end MinCostFlow.SparseCore.Program
