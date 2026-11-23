module

public import MinCostFlow.SparseCore.Program.OrdStoreCapContract
public import MinCostFlow.LinkCut.SplayOps
import Mathlib.Tactic

/-!
# Splay-sequence model for the order store

This file instantiates `MinCostFlow.LinkCut.LctPayload` with the trivial key-carrying payload
`ordPayload : LctPayload ℕ Unit Unit` (where each node stores an `endKey` in `val`, no lazy tags,
and no reversals) and defines the mathematical state `OrdStoreState`, its invariant `OrdInv`,
and the Sleator–Tarjan potential `ordPhi`.

Because every node has `rev = false` and `tag = ()`, `SplayState.pushPath` is the identity,
`evalPairs` equals the structural in-order list `AuxTree.toList` paired with node keys, and
`SplayState.splay_preserves_and_phi` directly yields the amortized splay bound. We prove the
pure model lemmas for splaying, leftmost/rightmost walks, splitting/detaching, joining, and
building left-leaning spines.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-! ### Trivial key payload -/

/-- Payload carrying an `endKey : ℕ` at each node with unit summary and unit lazy tag. -/
def ordPayload : LctPayload ℕ Unit Unit where
  empty := ()
  single _ _ := ()
  combine _ _ := ()
  revVal v := v
  revSum _ := ()
  idTag := ()
  isIdTag _ := true
  compTag _ _ := ()
  actVal _ v := v
  actSum _ _ := ()
  revTag _ := ()

theorem ordPayload_laws : ordPayload.Laws where
  combine_empty_left _ := rfl
  combine_empty_right _ := rfl
  combine_assoc _ _ _ := rfl
  revVal_revVal _ := rfl
  revSum_revSum _ := rfl
  revTag_revTag _ := rfl
  revSum_empty := rfl
  revSum_single _ _ := rfl
  revSum_combine _ _ := rfl
  actVal_id _ := rfl
  actSum_id _ := rfl
  actVal_comp _ _ _ := rfl
  actSum_comp _ _ _ := rfl
  compTag_id_left _ := rfl
  compTag_id_right _ := rfl
  compTag_assoc _ _ _ := rfl
  actSum_empty _ := rfl
  actSum_single _ _ _ := rfl
  actSum_combine _ _ _ := rfl
  revTag_id := rfl
  revTag_comp _ _ := rfl
  revVal_actVal _ _ := rfl
  revSum_actSum _ _ := rfl
  isIdTag_id := rfl
  isIdTag_eq _ _ := rfl

/-- The all-zero null node record for `ordPayload`. -/
def ordNullNode : SplayNode ℕ Unit Unit :=
  ⟨0, 0, 0, 0, 0, 0, (), (), false⟩

/-! ### Clean-tree specializations of `SplayState` -/

theorem treeSize_zero_eq_countNodes (t : AuxTree) :
    t.treeSize (fun _ => 0) = t.countNodes := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
    simp only [AuxTree.treeSize, AuxTree.countNodes, ihl, ihr]
    omega

theorem rank_zero_eq_log_countNodes (t : AuxTree) :
    t.rank (fun _ => 0) = Nat.log 2 t.countNodes := by
  rw [AuxTree.rank, treeSize_zero_eq_countNodes]

theorem rank_zero_le_ordStoreLog {t : AuxTree} {eCap : ℕ} (h : t.countNodes ≤ 2 * eCap) :
    t.rank (fun _ => 0) ≤ ordStoreLog eCap := by
  rw [rank_zero_eq_log_countNodes, ordStoreLog]
  have h1 : t.countNodes ≤ (eCap + 2) * 2 := by omega
  calc Nat.log 2 t.countNodes
      ≤ Nat.log 2 ((eCap + 2) * 2) := Nat.log_mono_right h1
    _ = Nat.log 2 (eCap + 2) + 1 := Nat.log_mul_base (by decide) (by omega)

theorem treePhi_zero_le_mul_ordStoreLog {t : AuxTree} {eCap : ℕ} (h : t.countNodes ≤ 2 * eCap) :
    t.treePhi (fun _ => 0) ≤ t.countNodes * ordStoreLog eCap := by
  have h1 := AuxTree.treePhi_le (fun _ => 0) t
  rw [treeSize_zero_eq_countNodes] at h1
  have hlog : Nat.log 2 (t.countNodes + 2) ≤ ordStoreLog eCap := by
    rw [ordStoreLog]
    calc Nat.log 2 (t.countNodes + 2)
        ≤ Nat.log 2 ((eCap + 2) * 2) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 (eCap + 2) + 1 := Nat.log_mul_base (by decide) (by omega)
  exact le_trans h1 (Nat.mul_le_mul_left _ hlog)

theorem pushDown_ordPayload_of_clean {st : SplayState ℕ Unit Unit} {x : ℕ}
    (hrev : (st.nodes x).rev = false) :
    SplayState.pushDown ordPayload st x = st := by
  unfold SplayState.pushDown SplayState.pushDownTag SplayState.pushDownRev
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, hrev, ordPayload]

theorem pushPath_ordPayload_of_clean {st : SplayState ℕ Unit Unit}
    (hclean : ∀ u, (st.nodes u).rev = false) :
    ∀ fuel x, SplayState.pushPath ordPayload st fuel x = st
  | 0, _ => rfl
  | fuel + 1, x => by
    unfold SplayState.pushPath
    by_cases hx : x = 0
    · simp [hx]
    · simp only [hx, ↓reduceIte]
      by_cases hp : (st.nodes x).par = 0
      · simp only [hp, ↓reduceIte]
        exact pushDown_ordPayload_of_clean (hclean x)
      · simp only [hp, ↓reduceIte, pushPath_ordPayload_of_clean hclean fuel _]
        exact pushDown_ordPayload_of_clean (hclean x)

theorem splay_ordPayload_eq_splayLoop {st : SplayState ℕ Unit Unit}
    (hclean : ∀ u, (st.nodes u).rev = false) (fuel x : ℕ) :
    SplayState.splay ordPayload st fuel x = SplayState.splayLoop ordPayload st fuel x := by
  unfold SplayState.splay
  by_cases hx : x = 0
  · cases fuel <;> simp [hx, SplayState.splayLoop]
  · simp [hx, pushPath_ordPayload_of_clean hclean]

theorem evalPairs_ordPayload_of_clean {st : SplayState ℕ Unit Unit} {t : AuxTree}
    (hclean : ∀ u ∈ t.toList, (st.nodes u).rev = false) :
    SplayState.evalPairs ordPayload st t false () =
      t.toList.map fun u => (u, (st.nodes u).val) := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
    have hid : (st.nodes id).rev = false := hclean id (by simp [AuxTree.toList])
    have hl : ∀ u ∈ l.toList, (st.nodes u).rev = false :=
      fun u hu => hclean u (by simp [AuxTree.toList, hu])
    have hr : ∀ u ∈ r.toList, (st.nodes u).rev = false :=
      fun u hu => hclean u (by simp [AuxTree.toList, hu])
    have h1 : ordPayload.compTag () (st.nodes id).tag = () := rfl
    have h2 : ordPayload.actVal () (st.nodes id).val = (st.nodes id).val := rfl
    simp only [SplayState.evalPairs, AuxTree.toList, hid, Bool.false_xor, Bool.false_eq_true,
      ↓reduceIte, List.map_append, List.map_cons, List.map_nil, h1, h2]
    rw [ihl hl, ihr hr]

theorem rotate_preserves_clean {st : SplayState ℕ Unit Unit}
    (hclean : ∀ u, (st.nodes u).rev = false) (x : ℕ) :
    ∀ u, ((SplayState.rotate ordPayload st x).nodes u).rev = false := by
  have hpull : ∀ (s : SplayState ℕ Unit Unit) (y : ℕ),
      (∀ z, (s.nodes z).rev = false) → ∀ z, ((SplayState.pull ordPayload s y).nodes z).rev = false := by
    intro s y hs z
    unfold SplayState.pull
    by_cases hy : y = 0
    · simp [hy, hs]
    · simp only [hy, ↓reduceIte, SplayState.nodes_updateNode]
      split_ifs <;> exact hs _
  have hsetL : ∀ (s : SplayState ℕ Unit Unit) (y v : ℕ),
      (∀ z, (s.nodes z).rev = false) → ∀ z, ((s.setLeft y v).nodes z).rev = false := by
    intro s y v hs z; simp [SplayState.setLeft, SplayState.nodes_updateNode]; split_ifs <;> exact hs _
  have hsetR : ∀ (s : SplayState ℕ Unit Unit) (y v : ℕ),
      (∀ z, (s.nodes z).rev = false) → ∀ z, ((s.setRight y v).nodes z).rev = false := by
    intro s y v hs z; simp [SplayState.setRight, SplayState.nodes_updateNode]; split_ifs <;> exact hs _
  have hsetP : ∀ (s : SplayState ℕ Unit Unit) (y v : ℕ),
      (∀ z, (s.nodes z).rev = false) → ∀ z, ((s.setPar y v).nodes z).rev = false := by
    intro s y v hs z; simp [SplayState.setPar, SplayState.nodes_updateNode]; split_ifs <;> exact hs _
  have hsetPP : ∀ (s : SplayState ℕ Unit Unit) (y v : ℕ),
      (∀ z, (s.nodes z).rev = false) → ∀ z, ((s.setPpar y v).nodes z).rev = false := by
    intro s y v hs z; simp [SplayState.setPpar, SplayState.nodes_updateNode]; split_ifs <;> exact hs _
  intro u
  unfold SplayState.rotate
  by_cases hx0 : x = 0
  · simp [hx0, hclean]
  simp only [hx0, ↓reduceIte]
  by_cases hp0 : (st.nodes x).par = 0
  · simp [hp0, hclean]
  simp only [hp0, ↓reduceIte]
  set p := (st.nodes x).par
  set g := (st.nodes p).par
  set pp := (st.nodes p).ppar
  set isLeft := (x == (st.nodes p).left)
  set b := if isLeft then (st.nodes x).right else (st.nodes x).left
  set st1 := if isLeft then st.setRight x p else st.setLeft x p
  set st2 := if isLeft then st1.setLeft p b else st1.setRight p b
  set st3 := if b = 0 then st2 else st2.setPar b p
  set st4 := st3.setPar p x
  set st5 := st4.setPar x g
  set st6 := st5.setPpar x pp
  set st7 := st6.setPpar p 0
  set st8 := if g = 0 then st7 else if p == (st7.nodes g).left then st7.setLeft g x else st7.setRight g x
  have h1 : ∀ z, (st1.nodes z).rev = false := by
    intro z; dsimp only [st1]; split_ifs <;> [exact hsetR _ _ _ hclean z; exact hsetL _ _ _ hclean z]
  have h2 : ∀ z, (st2.nodes z).rev = false := by
    intro z; dsimp only [st2]; split_ifs <;> [exact hsetL _ _ _ h1 z; exact hsetR _ _ _ h1 z]
  have h3 : ∀ z, (st3.nodes z).rev = false := by
    intro z; dsimp only [st3]; split_ifs <;> [exact h2 z; exact hsetP _ _ _ h2 z]
  have h4 : ∀ z, (st4.nodes z).rev = false := hsetP st3 p x h3
  have h5 : ∀ z, (st5.nodes z).rev = false := hsetP st4 x g h4
  have h6 : ∀ z, (st6.nodes z).rev = false := hsetPP st5 x pp h5
  have h7 : ∀ z, (st7.nodes z).rev = false := hsetPP st6 p 0 h6
  have h8 : ∀ z, (st8.nodes z).rev = false := by
    intro z; dsimp only [st8]; split_ifs
    · exact h7 z
    · exact hsetL st7 g x h7 z
    · exact hsetR st7 g x h7 z
  exact hpull _ x (hpull st8 p h8) u

theorem splayStep_preserves_clean {st : SplayState ℕ Unit Unit}
    (hclean : ∀ u, (st.nodes u).rev = false) (x : ℕ) :
    ∀ u, ((SplayState.splayStep ordPayload st x).nodes u).rev = false := by
  unfold SplayState.splayStep
  dsimp only
  split_ifs
  · exact hclean
  · exact hclean
  · exact rotate_preserves_clean hclean x
  · exact rotate_preserves_clean (rotate_preserves_clean hclean _) x
  · exact rotate_preserves_clean (rotate_preserves_clean hclean x) x

theorem splayLoop_preserves_clean :
    ∀ fuel {st : SplayState ℕ Unit Unit} (_ : ∀ u, (st.nodes u).rev = false) (x : ℕ),
      ∀ u, ((SplayState.splayLoop ordPayload st fuel x).nodes u).rev = false
  | 0, _, hclean, _, u => hclean u
  | fuel + 1, st, hclean, x, u => by
    unfold SplayState.splayLoop
    split_ifs
    · exact hclean u
    · exact hclean u
    · exact splayLoop_preserves_clean fuel (splayStep_preserves_clean hclean x) x u

theorem depthOf_lt_countNodes {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) :
    t.depthOf x < t.countNodes := by
  induction t with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
    simp only [AuxTree.depthOf, AuxTree.countNodes]
    by_cases h : x = id
    · simp [h]
    · simp only [h, ↓reduceIte]
      by_cases hl : x ∈ l.toList
      · simp only [hl, ↓reduceIte]
        have := ihl hl
        omega
      · have hr : x ∈ r.toList := by
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
          rcases hx with (h1 | rfl) | h2
          · exact absurd h1 hl
          · exact absurd rfl h
          · exact h2
        simp only [hl, hr, ↓reduceIte]
        have := ihr hr
        omega

/-- Clean specialization of `SplayState.splay_preserves_and_phi` for `ordPayload`. -/
theorem ord_splay_spec {st : SplayState ℕ Unit Unit} {t : AuxTree} {fuel x : ℕ}
    (ht : TreeInv ordPayload st t) (hclean : ∀ u, (st.nodes u).rev = false)
    (hx : x ∈ t.toList) (hfuel : t.depthOf x < fuel) :
    ∃ t',
      let st' := SplayState.splayLoop ordPayload st fuel x
      TreeInv ordPayload st' t' ∧
      t' ≠ .leaf ∧
      t'.rootId = x ∧
      t'.toList = t.toList ∧
      (∀ u, (st'.nodes u).rev = false) ∧
      (∀ u ∈ t.toList, (st'.nodes u).val = (st.nodes u).val) ∧
      (st'.nodes x).ppar = (st.nodes t.rootId).ppar ∧
      (∀ u ∉ t.toList, st'.nodes u = st.nodes u) ∧
      t'.countNodes = t.countNodes ∧
      t'.treePhi (fun _ => 0) + t.depthOf x / 2 ≤
        t.treePhi (fun _ => 0) + 3 * t'.rank (fun _ => 0) := by
  have hsp := SplayState.splay_preserves_and_phi ordPayload_laws ht hx hfuel
  rw [splay_ordPayload_eq_splayLoop hclean] at hsp
  rcases hsp with ⟨t', ht', hne, hroot, hperm, hev, hpp, -, -, hout, hphi⟩
  have hclean' := splayLoop_preserves_clean fuel hclean x
  have hev' : t'.toList.map (fun u => (u, ((SplayState.splayLoop ordPayload st fuel x).nodes u).val)) =
      t.toList.map (fun u => (u, (st.nodes u).val)) := by
    rw [← evalPairs_ordPayload_of_clean (fun u _ => hclean' u),
        ← evalPairs_ordPayload_of_clean (fun u _ => hclean u)]
    exact hev
  have htoList : t'.toList = t.toList := by
    have := congrArg (List.map Prod.fst) hev'
    simpa [List.map_map, Function.comp_def] using this
  have hval : ∀ u ∈ t.toList,
      ((SplayState.splayLoop ordPayload st fuel x).nodes u).val = (st.nodes u).val := by
    intro u hu
    have hmem : (u, ((SplayState.splayLoop ordPayload st fuel x).nodes u).val) ∈
        t.toList.map (fun w => (w, (st.nodes w).val)) := by
      rw [← hev']
      exact List.mem_map.mpr ⟨u, htoList ▸ hu, rfl⟩
    rcases List.mem_map.mp hmem with ⟨w, -, hw⟩
    injection hw with hwu hwv
    subst hwu
    exact hwv.symm
  obtain ⟨hsz, hph⟩ := hphi (fun _ => 0)
  rw [treeSize_zero_eq_countNodes, treeSize_zero_eq_countNodes] at hsz
  exact ⟨t', ht', hne, hroot, htoList, hclean', hval, hpp, hout, hsz, by omega⟩

/-! ### Leftmost and rightmost nodes of an `AuxTree` -/

/-- Leftmost node ID of a non-leaf `AuxTree`, or `0` for `leaf`. -/
def leftmostId : AuxTree → ℕ
  | .leaf => 0
  | .node id .leaf _ => id
  | .node _ l _ => leftmostId l

/-- Rightmost node ID of a non-leaf `AuxTree`, or `0` for `leaf`. -/
def rightmostId : AuxTree → ℕ
  | .leaf => 0
  | .node id _ .leaf => id
  | .node _ _ r => rightmostId r

theorem leftmostId_mem {t : AuxTree} (ht : t ≠ .leaf) : leftmostId t ∈ t.toList := by
  induction t with
  | leaf => exact absurd rfl ht
  | node id l r ihl _ =>
    cases l with
    | leaf => simp [leftmostId, AuxTree.toList]
    | node lid ll lr =>
      have h := ihl (by simp)
      change leftmostId (.node lid ll lr) ∈ (AuxTree.node lid ll lr).toList ++ [id] ++ r.toList
      exact List.mem_append_left _ (List.mem_append_left _ h)

theorem rightmostId_mem {t : AuxTree} (ht : t ≠ .leaf) : rightmostId t ∈ t.toList := by
  induction t with
  | leaf => exact absurd rfl ht
  | node id l r _ ihr =>
    cases r with
    | leaf => simp [rightmostId, AuxTree.toList]
    | node rid rl rr =>
      have h := ihr (by simp)
      change rightmostId (.node rid rl rr) ∈ l.toList ++ [id] ++ (AuxTree.node rid rl rr).toList
      exact List.mem_append_right _ h

theorem toList_head_eq_leftmostId {t : AuxTree} (ht : t ≠ .leaf) :
    t.toList.head? = some (leftmostId t) := by
  induction t with
  | leaf => exact absurd rfl ht
  | node id l r ihl _ =>
    cases l with
    | leaf => simp [leftmostId, AuxTree.toList]
    | node lid ll lr =>
      have hlne : AuxTree.node lid ll lr ≠ .leaf := by simp
      have hlen : (AuxTree.node lid ll lr).toList ≠ [] := by
        intro h; have := AuxTree.rootId_mem hlne; rw [h] at this; exact List.not_mem_nil this
      change ((AuxTree.node lid ll lr).toList ++ [id] ++ r.toList).head? =
        some (leftmostId (.node lid ll lr))
      rw [List.append_assoc, List.head?_append_of_ne_nil _ hlen]
      exact ihl hlne

theorem toList_getLast_eq_rightmostId {t : AuxTree} (ht : t ≠ .leaf) :
    t.toList.getLast? = some (rightmostId t) := by
  induction t with
  | leaf => exact absurd rfl ht
  | node id l r _ ihr =>
    cases r with
    | leaf => simp [rightmostId, AuxTree.toList]
    | node rid rl rr =>
      have hrne : AuxTree.node rid rl rr ≠ .leaf := by simp
      have hlen : (AuxTree.node rid rl rr).toList ≠ [] := by
        intro h; have := AuxTree.rootId_mem hrne; rw [h] at this; exact List.not_mem_nil this
      change ((l.toList ++ [id]) ++ (AuxTree.node rid rl rr).toList).getLast? =
        some (rightmostId (.node rid rl rr))
      rw [List.getLast?_append_of_ne_nil _ hlen]
      exact ihr hrne

theorem rightmost_splay_right_leaf {t : AuxTree} (hnd : t.toList.Nodup) (ht : t ≠ .leaf)
    (hroot : t.rootId = rightmostId t) :
    ∃ l, t = .node (rightmostId t) l .leaf := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r =>
    simp only [AuxTree.rootId] at hroot
    cases r with
    | leaf => exact ⟨l, by simp [rightmostId]⟩
    | node rid rl rr =>
      exfalso
      have hrm : rightmostId (AuxTree.node id l (.node rid rl rr)) ∈
          (AuxTree.node rid rl rr).toList := by
        simp only [rightmostId]
        exact rightmostId_mem (by simp)
      rw [← hroot] at hrm
      exact (AuxTree.nodup_node_unfold hnd).2.2.2.1 hrm

theorem leftmost_splay_left_leaf {t : AuxTree} (hnd : t.toList.Nodup) (ht : t ≠ .leaf)
    (hroot : t.rootId = leftmostId t) :
    ∃ r, t = .node (leftmostId t) .leaf r := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r =>
    simp only [AuxTree.rootId] at hroot
    cases l with
    | leaf => exact ⟨r, by simp [leftmostId]⟩
    | node lid ll lr =>
      exfalso
      have hlm : leftmostId (AuxTree.node id (.node lid ll lr) r) ∈
          (AuxTree.node lid ll lr).toList := by
        simp only [leftmostId]
        exact leftmostId_mem (by simp)
      rw [← hroot] at hlm
      exact (AuxTree.nodup_node_unfold hnd).2.1 hlm

/-- Depth of `leftmostId t` equals the length of the left spine (number of left edges from root). -/
def leftSpineLen : AuxTree → ℕ
  | .leaf => 0
  | .node _ .leaf _ => 0
  | .node _ l _ => leftSpineLen l + 1

/-- Depth of `rightmostId t` equals the length of the right spine. -/
def rightSpineLen : AuxTree → ℕ
  | .leaf => 0
  | .node _ _ .leaf => 0
  | .node _ _ r => rightSpineLen r + 1

theorem depthOf_leftmostId {t : AuxTree} (hnd : t.toList.Nodup) (ht : t ≠ .leaf) :
    t.depthOf (leftmostId t) = leftSpineLen t := by
  induction t with
  | leaf => exact absurd rfl ht
  | node id l r ihl _ =>
    rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hid_nl, -, -, -⟩
    cases l with
    | leaf => simp [leftmostId, leftSpineLen, AuxTree.depthOf]
    | node lid ll lr =>
      have hmem : leftmostId (.node lid ll lr) ∈ (AuxTree.node lid ll lr).toList :=
        leftmostId_mem (by simp)
      have hne : leftmostId (.node lid ll lr) ≠ id := fun h => hid_nl (h ▸ hmem)
      change (AuxTree.node id (.node lid ll lr) r).depthOf (leftmostId (.node lid ll lr)) =
        leftSpineLen (.node lid ll lr) + 1
      rw [AuxTree.depthOf]
      simp only [hne, hmem, ↓reduceIte]
      rw [ihl hl_nd (by simp)]

theorem depthOf_rightmostId {t : AuxTree} (hnd : t.toList.Nodup) (ht : t ≠ .leaf) :
    t.depthOf (rightmostId t) = rightSpineLen t := by
  induction t with
  | leaf => exact absurd rfl ht
  | node id l r _ ihr =>
    rcases AuxTree.nodup_node_unfold hnd with ⟨-, -, hr_nd, hid_nr, hdisj⟩
    cases r with
    | leaf => simp [rightmostId, rightSpineLen, AuxTree.depthOf]
    | node rid rl rr =>
      have hmem : rightmostId (.node rid rl rr) ∈ (AuxTree.node rid rl rr).toList :=
        rightmostId_mem (by simp)
      have hne : rightmostId (.node rid rl rr) ≠ id := fun h => hid_nr (h ▸ hmem)
      have hnl : rightmostId (.node rid rl rr) ∉ l.toList :=
        fun hl => hdisj _ hl hmem
      change (AuxTree.node id l (.node rid rl rr)).depthOf (rightmostId (.node rid rl rr)) =
        rightSpineLen (.node rid rl rr) + 1
      rw [AuxTree.depthOf]
      simp only [hne, hnl, hmem, ↓reduceIte]
      rw [ihr hr_nd (by simp)]

/-! ### Detach, Join, and Spine Construction -/

/-- Detaching the left and right subtrees of a root node preserves `TreeInv` on both and drops
potential. -/
theorem detach_root_treeInv {st : SplayState ℕ Unit Unit} {id : ℕ} {l r : AuxTree}
    (ht : TreeInv ordPayload st (.node id l r)) :
    let st₁ := if l.rootId = 0 then st else st.setPar l.rootId 0
    let st₂ := if r.rootId = 0 then st₁ else st₁.setPar r.rootId 0
    TreeInv ordPayload st₂ l ∧ TreeInv ordPayload st₂ r ∧
      l.treePhi (fun _ => 0) + r.treePhi (fun _ => 0) ≤ (AuxTree.node id l r).treePhi (fun _ => 0) := by
  rcases AuxTree.nodup_node_unfold ht.nodup with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj⟩
  rcases ht.sub with ⟨_, _, _, _, _, _, _, hsub_l, hsub_r⟩
  dsimp only
  have hl_par : ∀ st' : SplayState ℕ Unit Unit,
      (∀ u ∈ l.toList, u ≠ l.rootId → st'.nodes u = st.nodes u) →
      (l ≠ .leaf → st'.nodes l.rootId = { (st.nodes l.rootId) with par := 0 }) →
      SubtreeInv ordPayload st' 0 l := by
    intro st' hoth hrt
    cases l with
    | leaf => trivial
    | node lid ll lr =>
      have hne : AuxTree.node lid ll lr ≠ .leaf := by simp
      rcases hsub_l with ⟨hlid, hll, hlr, -, -, hlsz, -, hsub_ll, hsub_lr⟩
      have hnd_l := AuxTree.nodup_node_unfold hl_nd
      have hrt' := hrt hne
      simp only [AuxTree.rootId] at hrt'
      refine ⟨hlid, ?_, ?_, ?_, fun h => absurd rfl h, ?_, rfl, ?_, ?_⟩
      · simpa [hrt'] using hll
      · simpa [hrt'] using hlr
      · simp [hrt']
      · simpa [hrt'] using hlsz
      · exact SplayState.SubtreeInv_agree hsub_ll fun u hu =>
          (hoth u (by simp [AuxTree.toList, hu]) (fun heq => by
            simp only [AuxTree.rootId] at heq; exact hnd_l.2.1 (heq ▸ hu))).symm
      · exact SplayState.SubtreeInv_agree hsub_lr fun u hu =>
          (hoth u (by simp [AuxTree.toList, hu]) (fun heq => by
            simp only [AuxTree.rootId] at heq; exact hnd_l.2.2.2.1 (heq ▸ hu))).symm
  have hr_par : ∀ st' : SplayState ℕ Unit Unit,
      (∀ u ∈ r.toList, u ≠ r.rootId → st'.nodes u = st.nodes u) →
      (r ≠ .leaf → st'.nodes r.rootId = { (st.nodes r.rootId) with par := 0 }) →
      SubtreeInv ordPayload st' 0 r := by
    intro st' hoth hrt
    cases r with
    | leaf => trivial
    | node rid rl rr =>
      have hne : AuxTree.node rid rl rr ≠ .leaf := by simp
      rcases hsub_r with ⟨hrid, hrl, hrr, -, -, hrsz, -, hsub_rl, hsub_rr⟩
      have hnd_r := AuxTree.nodup_node_unfold hr_nd
      have hrt' := hrt hne
      simp only [AuxTree.rootId] at hrt'
      refine ⟨hrid, ?_, ?_, ?_, fun h => absurd rfl h, ?_, rfl, ?_, ?_⟩
      · simpa [hrt'] using hrl
      · simpa [hrt'] using hrr
      · simp [hrt']
      · simpa [hrt'] using hrsz
      · exact SplayState.SubtreeInv_agree hsub_rl fun u hu =>
          (hoth u (by simp [AuxTree.toList, hu]) (fun heq => by
            simp only [AuxTree.rootId] at heq; exact hnd_r.2.1 (heq ▸ hu))).symm
      · exact SplayState.SubtreeInv_agree hsub_rr fun u hu =>
          (hoth u (by simp [AuxTree.toList, hu]) (fun heq => by
            simp only [AuxTree.rootId] at heq; exact hnd_r.2.2.2.1 (heq ▸ hu))).symm
  have hlr_ne : l ≠ .leaf → r ≠ .leaf → l.rootId ≠ r.rootId := fun hl hr heq =>
    hdisj l.rootId (AuxTree.rootId_mem hl) (heq ▸ AuxTree.rootId_mem hr)
  have hl_nz : l ≠ .leaf → l.rootId ≠ 0 := fun hl =>
    SplayState.SubtreeInv_nonZero hsub_l (AuxTree.rootId_mem hl)
  have hr_nz : r ≠ .leaf → r.rootId ≠ 0 := fun hr =>
    SplayState.SubtreeInv_nonZero hsub_r (AuxTree.rootId_mem hr)
  refine ⟨⟨hl_nd, hl_par _ ?_ ?_⟩, ⟨hr_nd, hr_par _ ?_ ?_⟩, ?_⟩
  · intro u hu hne
    have hur : u ≠ r.rootId := by
      intro heq
      cases r with
      | leaf => exact SplayState.SubtreeInv_nonZero hsub_l hu heq
      | node rid rl rr => exact hdisj u hu (heq ▸ AuxTree.rootId_mem (by simp))
    split_ifs <;> simp [SplayState.setPar, SplayState.nodes_updateNode, hne, hur]
  · intro hl
    have hnz := hl_nz hl
    have hne : l.rootId ≠ r.rootId := by
      cases r with
      | leaf => exact hnz
      | node rid rl rr => exact hlr_ne hl (by simp)
    split_ifs <;> simp [SplayState.setPar, SplayState.nodes_updateNode, hnz, hne]
  · intro u hu hne
    have hul : u ≠ l.rootId := by
      intro heq
      cases l with
      | leaf => exact SplayState.SubtreeInv_nonZero hsub_r hu heq
      | node lid ll lr => exact hdisj u (heq ▸ AuxTree.rootId_mem (by simp)) hu
    split_ifs <;> simp [SplayState.setPar, SplayState.nodes_updateNode, hne, hul]
  · intro hr
    have hnz := hr_nz hr
    have hne : r.rootId ≠ l.rootId := by
      cases l with
      | leaf => exact hnz
      | node lid ll lr => exact (hlr_ne (by simp) hr).symm
    simp only [hnz, ↓reduceIte, SplayState.setPar, SplayState.nodes_updateNode]
    split_ifs <;> simp [hne]
  · simp only [AuxTree.treePhi]; omega

/-- Attaching a disjoint tree `t₂` as the right child of a root `x` whose right child is `.leaf`
yields a valid `TreeInv` on `.node x l t₂` with `toList = (node x l leaf).toList ++ t₂.toList`
and potential increase bounded by `ordStoreLog eCap`. -/
theorem join_right_leaf_treeInv {st : SplayState ℕ Unit Unit} {x owner eCap : ℕ}
    {l t₂ : AuxTree}
    (ht₁ : TreeInv ordPayload st (.node x l .leaf))
    (ht₂ : TreeInv ordPayload st t₂)
    (hdisj : ∀ u ∈ (AuxTree.node x l .leaf).toList, u ∉ t₂.toList)
    (hsz_bound : (AuxTree.node x l .leaf).countNodes + t₂.countNodes ≤ 2 * eCap) :
    let st1 := st.updateNode x fun nd =>
      { nd with right := t₂.rootId, sz := nd.sz + t₂.countNodes, ppar := owner }
    let st2 := if t₂.rootId = 0 then st1 else st1.updateNode t₂.rootId fun nd =>
      { nd with par := x, ppar := 0 }
    TreeInv ordPayload st2 (.node x l t₂) ∧
      (AuxTree.node x l t₂).toList = (AuxTree.node x l .leaf).toList ++ t₂.toList ∧
      (st2.nodes x).ppar = owner ∧
      (AuxTree.node x l t₂).treePhi (fun _ => 0) ≤
        (AuxTree.node x l .leaf).treePhi (fun _ => 0) + t₂.treePhi (fun _ => 0) +
          ordStoreLog eCap := by
  dsimp only
  rcases AuxTree.nodup_node_unfold ht₁.nodup with ⟨hl_nd, hx_nl, -, -, -⟩
  rcases ht₁.sub with ⟨hx_nz, hxl, -, hxpar, -, hxsz, -, hsub_l, -⟩
  have hnd : (AuxTree.node x l t₂).toList.Nodup := by
    rw [AuxTree.toList, List.nodup_append, List.nodup_append]
    refine ⟨⟨hl_nd, List.nodup_singleton x, fun a ha b hb => ?_⟩, ht₂.nodup, fun a ha b hb heq => ?_⟩
    · simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hx_nl ha
    · subst heq
      have ha' : a ∈ (AuxTree.node x l .leaf).toList := by simpa [AuxTree.toList] using ha
      exact hdisj a ha' hb
  have hx_ne_r2 : x ≠ t₂.rootId := by
    cases t₂ with
    | leaf => exact hx_nz
    | node rid rl rr =>
      intro heq; exact hdisj x (by simp [AuxTree.toList]) (heq ▸ AuxTree.rootId_mem (by simp))
  have hl_ne_r2 : ∀ u ∈ l.toList, u ≠ t₂.rootId := by
    intro u hu heq
    cases t₂ with
    | leaf => exact SplayState.SubtreeInv_nonZero hsub_l hu heq
    | node rid rl rr =>
      exact hdisj u (by simp [AuxTree.toList, hu]) (heq ▸ AuxTree.rootId_mem (by simp))
  have hx_ne_t2 : ∀ u ∈ t₂.toList, u ≠ x := fun u hu heq =>
    hdisj x (by simp [AuxTree.toList]) (heq ▸ hu)
  have hsub2 : SplayState.SubtreeInv ordPayload
      (if t₂.rootId = 0 then
        st.updateNode x (fun nd => { nd with right := t₂.rootId, sz := nd.sz + t₂.countNodes, ppar := owner })
      else
        (st.updateNode x (fun nd => { nd with right := t₂.rootId, sz := nd.sz + t₂.countNodes, ppar := owner })).updateNode
          t₂.rootId (fun nd => { nd with par := x, ppar := 0 })) x t₂ := by
    cases t₂ with
    | leaf => trivial
    | node rid rl rr =>
      rcases ht₂.sub with ⟨hrid, hrl, hrr, -, -, hrsz, -, hsub_rl, hsub_rr⟩
      rcases AuxTree.nodup_node_unfold ht₂.nodup with ⟨-, hrid_nrl, -, hrid_nrr, -⟩
      simp only [AuxTree.rootId] at hx_ne_r2
      simp only [AuxTree.rootId, hrid, ↓reduceIte]
      refine ⟨hrid, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
      · simp [SplayState.nodes_updateNode, hx_ne_r2.symm, hrl]
      · simp [SplayState.nodes_updateNode, hx_ne_r2.symm, hrr]
      · simp [SplayState.nodes_updateNode]
      · intro _; simp [SplayState.nodes_updateNode]
      · simp [SplayState.nodes_updateNode, hx_ne_r2.symm, hrsz]
      · exact SplayState.SubtreeInv_agree hsub_rl fun u hu => by
          have h1 : u ≠ rid := fun h => hrid_nrl (h ▸ hu)
          have h2 : u ≠ x := hx_ne_t2 u (by simp [AuxTree.toList, hu])
          simp [SplayState.nodes_updateNode, h1, h2]
      · exact SplayState.SubtreeInv_agree hsub_rr fun u hu => by
          have h1 : u ≠ rid := fun h => hrid_nrr (h ▸ hu)
          have h2 : u ≠ x := hx_ne_t2 u (by simp [AuxTree.toList, hu])
          simp [SplayState.nodes_updateNode, h1, h2]
  have hsub_l' : SplayState.SubtreeInv ordPayload
      (if t₂.rootId = 0 then
        st.updateNode x (fun nd => { nd with right := t₂.rootId, sz := nd.sz + t₂.countNodes, ppar := owner })
      else
        (st.updateNode x (fun nd => { nd with right := t₂.rootId, sz := nd.sz + t₂.countNodes, ppar := owner })).updateNode
          t₂.rootId (fun nd => { nd with par := x, ppar := 0 })) x l :=
    SplayState.SubtreeInv_agree hsub_l fun u hu => by
      have h1 : u ≠ x := fun h => hx_nl (h ▸ hu)
      have h2 : u ≠ t₂.rootId := hl_ne_r2 u hu
      split_ifs <;> simp [SplayState.nodes_updateNode, h1, h2]
  refine ⟨⟨hnd, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨hx_nz, ?_, ?_, ?_, fun h => absurd rfl h, ?_, rfl, hsub_l', hsub2⟩
    · split_ifs <;> simp [SplayState.nodes_updateNode, hx_ne_r2, hxl]
    · split_ifs <;> simp [SplayState.nodes_updateNode, hx_ne_r2]
    · split_ifs <;> simp [SplayState.nodes_updateNode, hx_ne_r2, hxpar]
    · have hcnt : (AuxTree.node x l t₂).countNodes =
          (AuxTree.node x l .leaf).countNodes + t₂.countNodes := by
        simp [AuxTree.countNodes]
      rw [hcnt, ← hxsz]
      split_ifs <;> simp [SplayState.nodes_updateNode, hx_ne_r2]
  · simp [AuxTree.toList]
  · split_ifs <;> simp [SplayState.nodes_updateNode, hx_ne_r2]
  · have hrk : (AuxTree.node x l t₂).rank (fun _ => 0) ≤ ordStoreLog eCap := by
      apply rank_zero_le_ordStoreLog
      simp only [AuxTree.countNodes] at hsz_bound ⊢
      omega
    simp only [AuxTree.treePhi]
    omega

/-- Left-leaning spine `AuxTree` built from a list of node IDs `[u₀, u₁, ..., u_{k-1}]`. -/
def leftSpine : List ℕ → AuxTree
  | [] => .leaf
  | u :: us => leftSpineGo (.node u .leaf .leaf) us
where
  leftSpineGo (acc : AuxTree) : List ℕ → AuxTree
    | [] => acc
    | u :: us => leftSpineGo (.node u acc .leaf) us

theorem leftSpineGo_toList (acc : AuxTree) (us : List ℕ) :
    (leftSpine.leftSpineGo acc us).toList = acc.toList ++ us := by
  induction us generalizing acc with
  | nil => simp [leftSpine.leftSpineGo]
  | cons u us ih =>
    simp only [leftSpine.leftSpineGo, ih, AuxTree.toList, List.append_nil, List.append_assoc,
      List.singleton_append]

theorem leftSpine_toList (us : List ℕ) : (leftSpine us).toList = us := by
  cases us with
  | nil => rfl
  | cons u us =>
    simp [leftSpine, leftSpineGo_toList, AuxTree.toList]

theorem leftSpine_countNodes (us : List ℕ) : (leftSpine us).countNodes = us.length := by
  rw [← AuxTree.length_toList, leftSpine_toList]


end MinCostFlow.SparseCore.Program
