module

public import MinCostFlow.SparseCore.Program.TourCutLinkExec
import Mathlib.Tactic

/-!
# Forest link operation (`link`, Op 2)

Verifies Op `2` (`link [b, e, dropRoot, heap]`) of `tourContract`: links open edge
`e` between two distinct forest components, erases `dropRoot` from `rf.R`, unmarks both ends of `e`,
splices the two Euler-tour splay trees via `tourLinkSpliceBody`, reads the surviving root via
`rootTagOf`, and rotates its first end to the front in `O(tourLog eCap)` amortized time with `2`
words of heap headroom.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Op 2 (`link`) verification -/

/-- Op 2 (`link [b, e, dropRoot, heap]`): verified amortized run theorem. -/
theorem tourOp_link_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b e dropRoot heap pos u v : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) {lsProc : ℕ}
    (hls : p.procs[lsProc]? = some (tourLinkSpliceBody C.splay.splay C.detachLeft C.detachRight C.join))
    (ω : ℕ → Bool) {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (he_lt : e < eCap) (he : e ∉ s.rf.F.E)
    (hxu : (e, true) ∈ s.ord u) (hyv : (e, false) ∈ s.ord v)
    (hnc : ¬ s.rf.F.Connected (ordSrc s.ord (e, true)) (ordSrc s.ord (e, false)))
    (hdrop : dropRoot = s.rf.root (ordSrc s.ord (e, true)) ∨ dropRoot = s.rf.root (ordSrc s.ord (e, false)))
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 2 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpLinkBody lsProc C.rootTagOf C.setValNode C.rotateFront)
        (startState [b, e, dropRoot, heap] mem pos) o st' c ∧
      o.value = heap ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b (tourLink s e dropRoot) x' st'.mem ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 2 mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_CUTLINK_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  have hord_le := h.fixed_le_heap hfoot
  have hhdr := h.header
  have huSrc : ordSrc s.ord (e, true) = u := h.valid.compat.ordSrc_eq hxu
  have hvSrc : ordSrc s.ord (e, false) = v := h.valid.compat.ordSrc_eq hyv
  rw [huSrc, hvSrc] at hnc hdrop
  set ru := s.rf.root u
  set rv := s.rf.root v
  set keepRoot := if dropRoot = ru then rv else ru
  set F' := addForestEdge s.rf.F e u v
  set s'Abs := tourLink s e dropRoot
  have hs'_F : s'Abs.rf.F = F' := by simp [s'Abs, tourLink, F', huSrc, hvSrc]
  have hvalid' : TourValid vCap eCap s'Abs := tourValid_link h.valid he hxu hyv hnc hdrop
  obtain ⟨_, hruR, hruLt, _, hnx_pos, hnx_le, hnx_key, tx, rest1, hctx, hpermx, htx_map, hnx_tx⟩ :=
    h.mem_compTree_of_active hxu
  obtain ⟨_, hrvR, hrvLt, _, hny_pos, hny_le, hny_key, ty, _, hcty, _, hty_map, hny_ty⟩ :=
    h.mem_compTree_of_active hyv
  have hru_ne_rv : ru ≠ rv := fun heq => by
    have h1 := (h.valid.root_spec (h.valid.compat.vert u (List.ne_nil_of_mem hxu))).2
    have h2 : s.rf.F.Connected ru v := heq ▸ connected_symm (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hyv))).2
    exact hnc (connected_trans h1 h2)
  have htx_ne_ty : tx ≠ ty := fun heq => by
    subst heq
    have h1 : (e, false) ∈ fullTour s.ord s.rf.F h.valid.compat.forest ru := by
      rw [← htx_map]; exact List.mem_map.mpr ⟨_, hny_ty, by rw [hny_key, endOfKey_endKey']⟩
    obtain ⟨w', hw', hcw'⟩ := ((fullTour_spec h.valid.compat ru).2 _).mp h1
    have hvw : w' = v := h.valid.compat.unique w' v _ hw' hyv; subst w'
    exact hru_ne_rv (h.valid.root_eq_of_mem (h.valid.compat.vert v (List.ne_nil_of_mem hyv)) hruR (connected_symm hcw')).symm
  have hty_in_rest1 : ty ∈ rest1 := by
    have hty_mem : ty ∈ x.trees := by
      have hft_ne : fullTour s.ord s.rf.F h.valid.compat.forest rv ≠ [] := by
        rw [← hty_map]; exact mt List.map_eq_nil_iff.mp (List.ne_nil_of_mem hny_ty)
      obtain ⟨ty', hcty', hty'_mem, _⟩ := h.comp_some rv hrvR hft_ne
      exact (Option.some.inj (hcty.symm.trans hcty')) ▸ hty'_mem
    exact (List.mem_cons.mp (hpermx.mem_iff.mp hty_mem)).resolve_left htx_ne_ty.symm
  set rest := rest1.erase ty
  have hperm : x.trees.Perm (tx :: ty :: rest) :=
    hpermx.trans (List.Perm.cons tx (List.perm_cons_erase hty_in_rest1))
  have hkx_eq : endKey (e, true) = 2 * e := rfl
  have hky_eq : endKey (e, false) = 2 * e + 1 := rfl
  rw [hkx_eq] at hnx_pos hnx_le hnx_key hnx_tx
  rw [hky_eq] at hny_pos hny_le hny_key hny_ty
  set nx := x.nodeOf (2 * e)
  set ny := x.nodeOf (2 * e + 1)
  have hnx_ne_ny : nx ≠ ny := fun heq => by
    have := congrArg x.keyOf heq; rw [hnx_key, hny_key] at this; omega
  have hnx_cap : nx ≤ x.numNodes := hnx_le
  have hny_cap : ny ≤ x.numNodes := hny_le
  have hord_ru_ne : s.ord ru ≠ [] := mt (fullTour_eq_nil_iff h.valid.compat ru).mpr
    (by rw [← htx_map]; exact mt List.map_eq_nil_iff.mp (List.ne_nil_of_mem hnx_tx))
  have hord_rv_ne : s.ord rv ≠ [] := mt (fullTour_eq_nil_iff h.valid.compat rv).mpr
    (by rw [← hty_map]; exact mt List.map_eq_nil_iff.mp (List.ne_nil_of_mem hny_ty))
  have hdrop_ne_keep : dropRoot ≠ keepRoot := by
    rcases hdrop with rfl | rfl
    · simpa [keepRoot] using hru_ne_rv
    · simp [keepRoot, hru_ne_rv.symm]
  have hdropR : dropRoot ∈ s.rf.R := by rcases hdrop with rfl | rfl <;> assumption
  have hkeepR : keepRoot ∈ s.rf.R := by
    rcases hdrop with rfl | rfl
    · simpa [keepRoot] using hrvR
    · simpa [keepRoot, hru_ne_rv.symm] using hruR
  have hdropLt : dropRoot < vCap := by rcases hdrop with rfl | rfl <;> assumption
  have hkeepLt : keepRoot < vCap := by
    rcases hdrop with rfl | rfl
    · simpa [keepRoot] using hrvLt
    · simpa [keepRoot, hru_ne_rv.symm] using hruLt
  have hord_drop_ne : s.ord dropRoot ≠ [] := by rcases hdrop with rfl | rfl <;> assumption
  have hord_keep_ne : s.ord keepRoot ≠ [] := by
    rcases hdrop with rfl | rfl
    · simpa [keepRoot] using hord_rv_ne
    · simpa [keepRoot, hru_ne_rv.symm] using hord_ru_ne
  obtain ⟨aD, haD⟩ : ∃ aD, (s.ord dropRoot).head? = some aD :=
    Option.isSome_iff_exists.mp (by cases ho : s.ord dropRoot <;> simp_all)
  obtain ⟨aK, haK⟩ : ∃ aK, (s.ord keepRoot).head? = some aK :=
    Option.isSome_iff_exists.mp (by cases ho : s.ord keepRoot <;> simp_all)
  have haD_mem : aD ∈ s.ord dropRoot := List.mem_of_head? haD
  have haK_mem : aK ∈ s.ord keepRoot := List.mem_of_head? haK
  obtain ⟨_, _, _, _, hfeD_pos, hfeD_le, hfeD_key, tD, _, hctD, _, _, hfeD_tD⟩ := h.mem_compTree_of_active haD_mem
  obtain ⟨_, _, _, _, hfeK_pos, hfeK_le, hfeK_key, tK, _, hctK, _, _, hfeK_tK⟩ := h.mem_compTree_of_active haK_mem
  set feD := x.nodeOf (endKey aD)
  set feK := x.nodeOf (endKey aK)
  have hfeD_cap : feD ≤ x.numNodes := hfeD_le
  have hfeK_cap : feK ≤ x.numNodes := hfeK_le
  have hfeD_ne_feK : feD ≠ feK := fun heq => by
    have haeq : aD = aK := by
      have := congrArg (fun id => endOfKey (x.keyOf id)) heq
      simpa [hfeD_key, hfeK_key, endOfKey_endKey'] using this
    exact hdrop_ne_keep (h.valid.compat.unique dropRoot keepRoot aD haD_mem (haeq ▸ haK_mem))
  have hfeD_first : mem (firstEndBase b + dropRoot) = feD := by rw [h.firstEnd_mem dropRoot hdropLt, haD]
  have hfeK_first : mem (firstEndBase b + keepRoot) = feK := by rw [h.firstEnd_mem keepRoot hkeepLt, haK]
  -- Update `isRoot[dropRoot] := 0`, run Steps 1..6
  set mem1 := Function.update mem (isRootBase b vCap + dropRoot) 0
  have hnodes1 : tourLayout.NodesAt mem1 (nodesBase b vCap eCap) x.numNodes x.st :=
    NodesAt.congr tourLayout h.nodesAt fun a ha =>
      Function.update_of_ne (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [isRootBase, nodesBase] at this ⊢; omega) _ _
  have hzero1 : ZeroFrom mem1 heap := fun a ha => by
    dsimp only [mem1]; rw [Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
    exact hzero a ha
  have hheap1 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 mem1 :=
    ⟨(h.heapOk (sp := 2) hfoot hzero hroom hwide).rec_le, hroom, hzero1, hwide⟩
  have hf_perm := (h.forestInv.perm hperm).1
  have hfeD_mem_pair : feD ∈ tx.toList ∨ feD ∈ ty.toList := by
    have hrD : s.rf.root dropRoot = dropRoot := h.valid.root_eq_of_mem (h.valid.roots_sub hdropR) hdropR (connected_refl _ _)
    rw [hrD] at hctD
    rcases hdrop with rfl | rfl
    · left; rw [← Option.some.inj (hctD.symm.trans hctx)]; exact hfeD_tD
    · right; rw [← Option.some.inj (hctD.symm.trans hcty)]; exact hfeD_tD
  set opD := if (x.st.nodes feD).val.isOpen then 1 else 0
  set mkD := if (x.st.nodes feD).val.isMarked then 1 else 0
  have hmem1_opD : mem1 (nodesBase b vCap eCap + 17 * feD + 9) = opD := nodesAt_isOpen hnodes1 hfeD_cap
  have hmem1_mkD : mem1 (nodesBase b vCap eCap + 17 * feD + 10) = mkD := nodesAt_isMarked hnodes1 hfeD_cap
  have hstep1 : ∃ tx₁ ty₁ s₁ o₁ st₁ c₁,
      Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
        (startState [nodesBase b vCap eCap, feD, opD, mkD, 0, 2 * eCap + 2, heap] mem1 pos) o₁ st₁ c₁ ∧
      tourLayout.NodesAt st₁.mem (nodesBase b vCap eCap) x.numNodes s₁ ∧
      TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes heap mem1 st₁.mem ∧
      TourForestInv x.numNodes s₁ (tx₁ :: ty₁ :: rest) ∧ TourValsOk w x.numNodes s₁ ∧
      tx₁.toList = tx.toList ∧ ty₁.toList = ty.toList ∧
      (s₁.nodes feD).val = ⟨0 < opD, 0 < mkD, 0⟩ ∧
      (∀ id ≤ x.numNodes, id ≠ feD → (s₁.nodes id).val = (x.st.nodes id).val) ∧
      c₁ + TOUR_PHI_MULT * forestPhi (tx₁ :: ty₁ :: rest) ≤
        TOUR_PHI_MULT * forestPhi (tx :: ty :: rest) + TOUR_FIND_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) := by
    rcases hfeD_mem_pair with hD_tx | hD_ty
    · obtain ⟨tx₁, s₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, _, _, hlist₁, hvalD₁, hvalne₁, _, hcost₁⟩ :=
        tourSetValNodeBody_runs (isOpen := opD) (isMarked := mkD) (rootTag := 0)
          (fuel := 2 * eCap + 2) (pos := pos) C ω hnodes1 hf_perm (h.valsOk hw)
          hD_tx (by omega) (by have := h.numNodes_le; omega) (by omega) hheap1
      exact ⟨tx₁, ty, s₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hlist₁, rfl, hvalD₁, hvalne₁, hcost₁⟩
    · have hf_sw := (hf_perm.perm (List.Perm.swap ty tx rest)).1
      obtain ⟨ty₁, s₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, _, _, hlist₁, hvalD₁, hvalne₁, _, hcost₁⟩ :=
        tourSetValNodeBody_runs (isOpen := opD) (isMarked := mkD) (rootTag := 0)
          (fuel := 2 * eCap + 2) (pos := pos) C ω hnodes1 hf_sw (h.valsOk hw)
          hD_ty (by omega) (by have := h.numNodes_le; omega) (by omega) hheap1
      have hinv₁' := (hinv₁.perm (List.Perm.swap tx ty₁ rest)).1
      rw [forestPhi_perm (List.Perm.swap tx ty₁ rest), forestPhi_perm (List.Perm.swap tx ty rest)] at hcost₁
      exact ⟨tx, ty₁, s₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁', hvals₁, rfl, hlist₁, hvalD₁, hvalne₁, hcost₁⟩
  obtain ⟨tx₁, ty₁, s₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, htx1_list, hty1_list, hvalD₁, hvalne₁, hcost₁⟩ := hstep1
  set rtX := (s₁.nodes nx).val.rootTag
  have hrtX_mem : st₁.mem (nodesBase b vCap eCap + 17 * nx + 11) = rtX := nodesAt_rootTag hn₁ hnx_cap
  have hnx_tx1 : nx ∈ tx₁.toList := by rw [htx1_list]; exact hnx_tx
  obtain ⟨tx₂, s₂, o₂, st₂, c₂, hrun₂, hn₂, hfr₂, hinv₂, hvals₂, _, _, htx2_list, hvalX₂, hvalne₂, _, hcost₂⟩ :=
    tourSetValNodeBody_runs (isOpen := 0) (isMarked := 0) (rootTag := rtX)
      (fuel := 2 * eCap + 2) (pos := st₁.pos) C ω hn₁ hinv₁ hvals₁ hnx_tx1 (hvals₁.2 nx hnx_cap)
      (by have := h.numNodes_le; omega) (by omega) ⟨hheap1.rec_le, hroom, hfr₁.1, hwide⟩
  set rtY := (s₂.nodes ny).val.rootTag
  have hrtY_mem : st₂.mem (nodesBase b vCap eCap + 17 * ny + 11) = rtY := nodesAt_rootTag hn₂ hny_cap
  have hny_ty1 : ny ∈ ty₁.toList := by rw [hty1_list]; exact hny_ty
  obtain ⟨ty₂, s₃, o₃, st₃, c₃, hrun₃, hn₃, hfr₃, hinv₃, hvals₃, _, _, hty2_list, hvalY₃, hvalne₃, _, hcost₃⟩ :=
    tourSetValNodeBody_runs (isOpen := 0) (isMarked := 0) (rootTag := rtY)
      (fuel := 2 * eCap + 2) (pos := st₂.pos) C ω hn₂ (hinv₂.perm (List.Perm.swap ty₁ tx₂ rest)).1 hvals₂ hny_ty1
      (hvals₂.2 ny hny_cap) (by have := h.numNodes_le; omega) (by omega) ⟨hheap1.rec_le, hroom, hfr₂.1, hwide⟩
  have hnx_tx2 : nx ∈ tx₂.toList := by rw [htx2_list]; exact hnx_tx1
  have hny_ty2 : ny ∈ ty₂.toList := by rw [hty2_list]; exact hny_ty1
  obtain ⟨tm, Px, Qx, Py, Qy, s₄, o₄, st₄, c₄, hrun₄, _, hn₄, hfr₄, hinv₄, hvals₄, _,
    htx2_eq, hty2_eq, htm_list, hval₄, hcost₄⟩ :=
    tourLinkSpliceBody_runs (fuel := 2 * eCap + 2) (pos := st₃.pos) C.toTourSplayOpsProcs ω
      hn₃ (hinv₃.perm (List.Perm.swap tx₂ ty₂ rest)).1 hvals₃ hnx_tx2 hny_ty2 (by have := h.numNodes_le; omega) (by omega)
      ⟨hheap1.rec_le, hroom, hfr₃.1, hwide⟩
  -- Relate `tm` to `fullTour s.ord F' _ keepRoot` via `fullTour_link`
  have hvalid'_F : OrdForestCompat s.ord F' := hs'_F ▸ hvalid'.compat
  have htx_rot_u : ((Px.map (fun id => endOfKey (x.keyOf id))) ++ (e, true) ::
      (Qx.map (fun id => endOfKey (x.keyOf id)))).IsRotated (fullTour s.ord s.rf.F h.valid.compat.forest u) := by
    have h1 : tx.toList.map (fun id => endOfKey (x.keyOf id)) =
        Px.map (fun id => endOfKey (x.keyOf id)) ++ (e, true) :: Qx.map (fun id => endOfKey (x.keyOf id)) := by
      rw [← htx1_list, ← htx2_list, htx2_eq]; simp [List.map_append, hnx_key, tour_endOfKey_two_mul]
    rw [← h1, htx_map]
    exact fullTour_isRotated_of_connected h.valid.compat
      (connected_symm (h.valid.root_spec (h.valid.compat.vert u (List.ne_nil_of_mem hxu))).2)
  have hty_rot_v : ((Py.map (fun id => endOfKey (x.keyOf id))) ++ (e, false) ::
      (Qy.map (fun id => endOfKey (x.keyOf id)))).IsRotated (fullTour s.ord s.rf.F h.valid.compat.forest v) := by
    have h1 : ty.toList.map (fun id => endOfKey (x.keyOf id)) =
        Py.map (fun id => endOfKey (x.keyOf id)) ++ (e, false) :: Qy.map (fun id => endOfKey (x.keyOf id)) := by
      rw [← hty1_list, ← hty2_list, hty2_eq]; simp [List.map_append, hny_key, endOfKey_two_mul_add1]
    rw [← h1, hty_map]
    exact fullTour_isRotated_of_connected h.valid.compat
      (connected_symm (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hyv))).2)
  have htm_rot_u : (tm.toList.map (fun id => endOfKey (x.keyOf id))).IsRotated
      (fullTour s.ord F' hvalid'_F.forest u) := by
    have h1 : tm.toList.map (fun id => endOfKey (x.keyOf id)) =
        Px.map (fun id => endOfKey (x.keyOf id)) ++ (e, true) ::
          Qy.map (fun id => endOfKey (x.keyOf id)) ++ Py.map (fun id => endOfKey (x.keyOf id)) ++
          (e, false) :: Qx.map (fun id => endOfKey (x.keyOf id)) := by
      rw [htm_list]; simp [List.map_append, hnx_key, hny_key, tour_endOfKey_two_mul, endOfKey_two_mul_add1]
    rw [h1]; exact fullTour_link h.valid.compat he hxu hyv hnc htx_rot_u hty_rot_v
  have hconn_u_keep : F'.Connected u keepRoot := by
    rw [connected_addForestEdge_iff he]
    rcases hdrop with rfl | rfl
    · simp only [keepRoot, ↓reduceIte]
      exact Or.inr (Or.inl ⟨connected_refl _ u, (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hyv))).2⟩)
    · simp only [keepRoot, hru_ne_rv.symm, ↓reduceIte]
      exact Or.inl (h.valid.root_spec (h.valid.compat.vert u (List.ne_nil_of_mem hxu))).2
  have htm_rot_keep : (tm.toList.map (fun id => endOfKey (x.keyOf id))).IsRotated
      (fullTour s.ord F' hvalid'_F.forest keepRoot) :=
    htm_rot_u.trans (fullTour_isRotated_of_connected hvalid'_F hconn_u_keep)
  have htm_mem_iff : ∀ z, z ∈ tm.toList ↔ z ∈ tx.toList ∨ z ∈ ty.toList := by
    intro z
    clear * - htm_list htx1_list htx2_list htx2_eq hty1_list hty2_list hty2_eq
    rw [htm_list, ← htx1_list, ← htx2_list, htx2_eq, ← hty1_list, ← hty2_list, hty2_eq]
    simp only [List.mem_append, List.mem_cons]
    tauto
  have hnx_tm : nx ∈ tm.toList := (htm_mem_iff nx).mpr (Or.inl hnx_tx)
  have hfeK_tm : feK ∈ tm.toList := by
    have hrK : s.rf.root keepRoot = keepRoot := h.valid.root_eq_of_mem (h.valid.roots_sub hkeepR) hkeepR (connected_refl _ _)
    rw [hrK] at hctK
    apply (htm_mem_iff feK).mpr
    rcases hdrop with rfl | rfl
    · simp only [keepRoot, ↓reduceIte] at hctK
      right; rw [← Option.some.inj (hctK.symm.trans hcty)]; exact hfeK_tK
    · simp only [keepRoot, hru_ne_rv.symm, ↓reduceIte] at hctK
      left; rw [← Option.some.inj (hctK.symm.trans hctx)]; exact hfeK_tK
  have hs4_rt : ∀ id ≤ x.numNodes, (s₄.nodes id).val.rootTag = if id = feD then 0 else (x.st.nodes id).val.rootTag := by
    intro id hid; rw [hval₄ id hid]
    by_cases hy : id = ny
    · subst id; rw [hvalY₃]; dsimp only [rtY]; rw [hvalne₂ ny hny_cap hnx_ne_ny.symm]
      by_cases hD : ny = feD
      · rw [hD, hvalD₁]; simp
      · rw [hvalne₁ ny hny_cap hD]; simp [hD]
    · rw [hvalne₃ id hid hy]
      by_cases hx : id = nx
      · subst id; rw [hvalX₂]; dsimp only [rtX]
        by_cases hD : nx = feD
        · rw [hD, hvalD₁]; simp
        · rw [hvalne₁ nx hnx_cap hD]; simp [hD]
      · rw [hvalne₂ id hid hx]
        by_cases hD : id = feD
        · rw [hD, hvalD₁]; simp
        · rw [hvalne₁ id hid hD]; simp [hD]
  -- Steps 5 & 6: rootTagOf(nx) -> keepRoot + 1, rotateFront(feK) -> t'
  obtain ⟨tm₁, s₅, o₅, st₅, c₅, hrun₅, hv₅, hn₅, hfr₅, hinv₅, hvals₅, _, _, hlist₅, hval₅, _, hcost₅⟩ :=
    tourRootTagOfBody_runs (fuel := 2 * eCap + 2) (pos := st₄.pos) C ω hn₄ hinv₄ hvals₄ hnx_tm
      (by have := h.numNodes_le; omega) (by omega) ⟨hheap1.rec_le, hroom, hfr₄.1, hwide⟩
  have ho₅_eq : o₅.value = keepRoot + 1 := by
    rw [hv₅]
    refine foldr_max_eq_of_unique_pos hfeK_tm ?_ ?_
    · rw [hs4_rt feK hfeK_cap, ite_eq_right_iff.mpr (fun h => absurd h hfeD_ne_feK.symm),
        h.val_active feK hfeK_pos hfeK_le ⟨keepRoot, by rw [hfeK_key, endOfKey_endKey']; exact haK_mem⟩,
        hfeK_key, endOfKey_endKey', tourRootTagVal_eq_succ h.valid hkeepR haK]
    · intro id hid_tm hid_neK
      have hid_in : 1 ≤ id ∧ id ≤ x.numNodes := (h.nodes_exact id).mp (by
        rcases (htm_mem_iff id).mp hid_tm with htxm | htym
        · exact List.mem_flatMap.mpr ⟨tx, hperm.mem_iff.mpr (by simp), htxm⟩
        · exact List.mem_flatMap.mpr ⟨ty, hperm.mem_iff.mpr (by simp), htym⟩)
      rw [hs4_rt id (by have := h.numNodes_le; omega)]
      split_ifs with hidD
      · rfl
      · have hid_act : ∃ w', endOfKey (x.keyOf id) ∈ s.ord w' ∧ (s.rf.F.Connected ru w' ∨ s.rf.F.Connected rv w') := by
          rcases (htm_mem_iff id).mp hid_tm with htxm | htym
          · have h1 : endOfKey (x.keyOf id) ∈ fullTour s.ord s.rf.F h.valid.compat.forest ru := by
              rw [← htx_map]; exact List.mem_map_of_mem htxm
            obtain ⟨w', hw', hc⟩ := ((fullTour_spec h.valid.compat ru).2 _).mp h1
            exact ⟨w', hw', Or.inl hc⟩
          · have h1 : endOfKey (x.keyOf id) ∈ fullTour s.ord s.rf.F h.valid.compat.forest rv := by
              rw [← hty_map]; exact List.mem_map_of_mem htym
            obtain ⟨w', hw', hc⟩ := ((fullTour_spec h.valid.compat rv).2 _).mp h1
            exact ⟨w', hw', Or.inr hc⟩
        obtain ⟨w', hw', hcw'⟩ := hid_act
        rw [h.val_active id hid_in.1 hid_in.2 ⟨w', hw'⟩]
        exact tourRootTagVal_eq_zero fun r' hr' hh => by
          have hwr : w' = r' := h.valid.compat.unique w' r' _ hw' (List.mem_of_head? hh); subst w'
          have hr'_in : r' = ru ∨ r' = rv := by
            rcases hcw' with h1 | h1
            · left; exact (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr' (connected_refl _ _)).symm.trans
                (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hruR (connected_symm h1))
            · right; exact (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr' (connected_refl _ _)).symm.trans
                (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hrvR (connected_symm h1))
          have hr'_dk : r' = dropRoot ∨ r' = keepRoot := by
            rcases hdrop with rfl | rfl <;> rcases hr'_in with rfl | rfl <;> simp [keepRoot, hru_ne_rv.symm]
          rcases hr'_dk with rfl | rfl
          · have hk : x.keyOf id = endKey aD := by rw [← endKey_endOfKey' (x.keyOf id), Option.some.inj (hh.symm.trans haD)]
            exact hidD ((h.keyOf_mem id hid_in.1 hid_in.2).2.2.symm.trans (by rw [hk]))
          · have hk : x.keyOf id = endKey aK := by rw [← endKey_endOfKey' (x.keyOf id), Option.some.inj (hh.symm.trans haK)]
            exact hid_neK ((h.keyOf_mem id hid_in.1 hid_in.2).2.2.symm.trans (by rw [hk]))
  have hfeK_tm1 : feK ∈ tm₁.toList := by rw [hlist₅]; exact hfeK_tm
  obtain ⟨t', s₆, o₆, st₆, c₆, hrun₆, _, hn₆, hfr₆, hinv₆, _, _, hrot₆, hval₆, _, hcost₆⟩ :=
    tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st₅.pos) C.toTourSplayOpsProcs ω
      hn₅ hinv₅ hvals₅ hfeK_tm1 (by have := h.numNodes_le; omega) (by omega) ⟨hheap1.rec_le, hroom, hfr₅.1, hwide⟩
  have ht'_map : t'.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s.ord F' hvalid'_F.forest keepRoot := by
    rw [hrot₆, hlist₅]
    have hnd := htm_rot_keep.perm.nodup_iff.mpr (fullTour_spec hvalid'_F keepRoot).1
    rw [rotateNatList_map_of_nodup' hnd hfeK_tm, hfeK_key, endOfKey_endKey']
    exact rotateToList_fullTour_of_isRotated hvalid'_F haK htm_rot_keep
  -- Verify `TourRepAt` for `s'Abs`
  let ct' := Function.update (Function.update x.compTree dropRoot none) keepRoot (some t')
  set x' : TourConcrete R_ord.τ := { x with st := s₆, trees := t' :: rest, compTree := ct' }
  have hfr15 : TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes heap mem1 st₅.mem :=
    hfr₁.trans (hfr₂.trans (hfr₃.trans (hfr₄.trans hfr₅)))
  have hfr_all : TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes heap mem1 st₆.mem := hfr15.trans hfr₆
  have hpre_eq1 : ∀ a < nodesBase b vCap eCap, st₆.mem a = mem1 a := fun a ha =>
    hfr_all.2 a (by simp only [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase ha)
  have hpre_eq_mem : ∀ a < nodesBase b vCap eCap, a ≠ isRootBase b vCap + dropRoot → st₆.mem a = mem a := fun a ha hne => by
    rw [hpre_eq1 a ha]; dsimp only [mem1]; rw [Function.update_of_ne hne]
  have hord_eq : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → mem a = st₆.mem a := fun a ha => by
    have ha_ge := h.ordFootGe a ha
    rw [hfr_all.2 a (hfoot a (Or.inr ha)) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le ha_ge)]
    dsimp only [mem1]; rw [Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at ha_ge ⊢; omega)]
  have hOrd := hLoc (ordHandleOf b vCap eCap) s.ord x.ordX mem st₆.mem hord_eq
  have hhdr' : TourHeaderAt vCap eCap b x.numNodes st₆.mem := by
    rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hf : ∀ k < 16, st₆.mem (b + k) = mem (b + k) := fun k hk =>
      hpre_eq_mem (b + k) (by simp [nodesBase]; omega) (by simp [isRootBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
      by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
      by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
      by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
      by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
      by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
      by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
      by rw [hf _ (by decide)]; exact h14⟩
  have htx_not_rest : tx ∉ rest := fun hm => by
    have hnd := hf_perm.nodupAll; rw [List.flatMap_cons, List.nodup_append] at hnd
    exact hnd.2.2 nx hnx_tx nx (List.mem_flatMap.mpr ⟨tx, List.mem_cons_of_mem _ hm, hnx_tx⟩) rfl
  have hty_not_rest : ty ∉ rest := fun hm => by
    have hnd := hf_perm.nodupAll; rw [List.flatMap_cons, List.flatMap_cons, List.nodup_append] at hnd
    exact (List.nodup_append.mp hnd.2.1).2.2 ny hny_ty ny (List.mem_flatMap.mpr ⟨ty, hm, hny_ty⟩) rfl
  have hcomp_inj_xy : ∀ r' ∈ s.rf.R, r' ≠ ru → r' ≠ rv → x.compTree r' ≠ some tx ∧ x.compTree r' ≠ some ty := by
    intro r' hr' hneU hneV
    have hchk : ∀ (tr : AuxTree) (r0 : ℕ) (hr0 : r0 ∈ s.rf.R) (id0 : ℕ), id0 ∈ tr.toList →
        tr.toList.map (fun id => endOfKey (x.keyOf id)) = fullTour s.ord s.rf.F h.valid.compat.forest r0 →
        r' ≠ r0 → x.compTree r' ≠ some tr := by
      intro tr r0 hr0 id0 hid0 hmap0 hne0 hcr'
      have hft' : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := by
        intro hnil; have := h.comp_none r' hr' hnil; rw [hcr'] at this; simp at this
      obtain ⟨tr', hctr', _, htr'_map⟩ := h.comp_some r' hr' hft'
      have hteq : tr' = tr := Option.some.inj (hctr'.symm.trans hcr'); subst hteq
      have he1 : endOfKey (x.keyOf id0) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r0 := by
        rw [← hmap0]; exact List.mem_map_of_mem hid0
      have he2 : endOfKey (x.keyOf id0) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
        rw [← htr'_map]; exact List.mem_map_of_mem hid0
      obtain ⟨v1, hv1, hc1⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he1
      obtain ⟨v2, hv2, hc2⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he2
      have hv12 : v1 = v2 := h.valid.compat.unique v1 v2 _ hv1 hv2; subst hv12
      have hvF := h.valid.compat.vert v1 (List.ne_nil_of_mem hv1)
      exact hne0 ((h.valid.root_eq_of_mem hvF hr' (connected_symm hc2)).symm.trans
        (h.valid.root_eq_of_mem hvF hr0 (connected_symm hc1)))
    exact ⟨hchk tx ru hruR nx hnx_tx htx_map hneU, hchk ty rv hrvR ny hny_ty hty_map hneV⟩
  have hft_other_eq : ∀ r' ∈ s.rf.R, r' ≠ ru → r' ≠ rv →
      fullTour s.ord F' hvalid'_F.forest r' = fullTour s.ord s.rf.F h.valid.compat.forest r' := by
    intro r' hr' hneU hneV
    by_cases hnil : s.ord r' = []
    · rw [(fullTour_eq_nil_iff hvalid'_F r').mpr hnil, (fullTour_eq_nil_iff h.valid.compat r').mpr hnil]
    · obtain ⟨a', ha'⟩ : ∃ a', (s.ord r').head? = some a' :=
        Option.isSome_iff_exists.mp (by cases ho : s.ord r' <;> simp_all)
      have hnd1 := (fullTour_spec hvalid'_F r').1
      have hnd2 := (fullTour_spec h.valid.compat r').1
      have hnc_r' : ¬ s.rf.F.Connected r' u ∧ ¬ s.rf.F.Connected r' v :=
        ⟨fun hc => hneU (h.valid.root_eq_of_mem (h.valid.compat.vert u (List.ne_nil_of_mem hxu)) hr' (connected_symm hc)).symm,
         fun hc => hneV (h.valid.root_eq_of_mem (h.valid.compat.vert v (List.ne_nil_of_mem hyv)) hr' (connected_symm hc)).symm⟩
      have ha'_in1 : a' ∈ fullTour s.ord F' hvalid'_F.forest r' :=
        ((fullTour_spec hvalid'_F r').2 a').mpr ⟨r', List.mem_of_head? ha', connected_refl F' r'⟩
      have ha'_in2 : a' ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' :=
        ((fullTour_spec h.valid.compat r').2 a').mpr ⟨r', List.mem_of_head? ha', connected_refl _ r'⟩
      have hrot_eq : (fullTour s.ord F' hvalid'_F.forest r').IsRotated
          (fullTour s.ord s.rf.F h.valid.compat.forest r') :=
        isRotated_of_cycNext_eq hnd1 hnd2 ha'_in1 ha'_in2
          (fun z hz => by
            obtain ⟨w', hzw', hcw'⟩ := ((fullTour_spec hvalid'_F r').2 z).mp hz
            have hcwF : s.rf.F.Connected r' w' := by
              rw [connected_addForestEdge_iff he] at hcw'
              rcases hcw' with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
              · exact h1
              · exact absurd h1 hnc_r'.1
              · exact absurd h1 hnc_r'.2
            have hzne : z.1 ≠ e := fun hez => by
              have hcases : z = (e, true) ∨ z = (e, false) := by
                obtain ⟨f, b⟩ := z; change f = e at hez; subst f; cases b <;> simp
              rcases hcases with rfl | rfl
              · exact hnc_r'.1 ((h.valid.compat.unique w' u _ hzw' hxu) ▸ hcwF)
              · exact hnc_r'.2 ((h.valid.compat.unique w' v _ hzw' hyv) ▸ hcwF)
            refine (fullTour_cycNext hvalid'_F r' z hz).trans ?_
            simp only [eulerSucc, F', addForestEdge, Finset.mem_insert, hzne, false_or]
            split_ifs with hzF
            · obtain ⟨f, b⟩ := z; cases b <;> simp [MGraph.dst, Function.update_of_ne hzne]
            · rfl)
          (fullTour_cycNext h.valid.compat r')
      have hrot_back := tour_rotateToList_eq_of_isRotated hnd2 hrot_eq (fullTour_head? h.valid.compat r' ha')
      have hrot_self := tour_rotateToList_eq_of_isRotated hnd1 (List.IsRotated.refl _) (fullTour_head? hvalid'_F r' ha')
      exact hrot_self.symm.trans hrot_back
  have ht'_mem_iff : ∀ z, z ∈ t'.toList ↔ z ∈ tx.toList ∨ z ∈ ty.toList := fun z => by
    rw [hrot₆, hlist₅, (rotateNatList_perm hfeK_tm).mem_iff, htm_mem_iff]
  have hrep' : TourRepAt R_ord vCap eCap b s'Abs x' st₆.mem :=
    { valid := hvalid'
      ordRep := hOrd.1 h.ordRep
      ordFootGe := h.ordFootGe
      header := hhdr'
      numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => by
        rw [hpre_eq_mem _ (by simp [nodeOfEndBase, nodesBase]; omega) (by simp [nodeOfEndBase, isRootBase]; omega)]
        exact h.nodeOf_mem k hk
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun id h1 h2 => by
        dsimp only [x'] at h2; have hle := h.numNodes_le
        rw [hpre_eq_mem _ (by simp [keyOfNodeBase, nodesBase]; omega) (by simp [keyOfNodeBase, isRootBase]; omega)]
        exact h.keyOf_mem id h1 h2
      firstEnd_mem := fun w' hw' => by
        rw [hpre_eq_mem _ (by simp [firstEndBase, nodesBase]; omega) (by simp [firstEndBase, isRootBase]; omega)]
        exact h.firstEnd_mem w' hw'
      isRoot_mem := fun w' hw' => by
        rw [hpre_eq1 _ (by simp [isRootBase, nodesBase]; omega)]; dsimp only [mem1]
        by_cases hwd : w' = dropRoot
        · subst w'; simp [s'Abs, tourLink]
        · rw [Function.update_of_ne (by omega), h.isRoot_mem w' hw']
          simp [s'Abs, tourLink, hwd]
      active_end := fun w' hw' z hz => by
        have hz_lt : endKey z < 2 * eCap := by
          have := h.valid.ordWithin.2.2 w' z hz; simp only [endKey]; cases z.2 <;> simp <;> omega
        rw [hpre_eq_mem _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, isRootBase]; omega)]
        exact h.active_end w' hw' z hz
      inactive_owner := fun k hk hno => by
        rw [hpre_eq_mem _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, isRootBase]; omega)]
        exact h.inactive_owner k hk hno
      slot_bij := h.slot_bij
      slotOf_mem := fun v hv => by
        rw [hpre_eq_mem _ (by simp [slotOfVertBase, nodesBase]; omega) (by simp [slotOfVertBase, isRootBase]; omega)]
        exact h.slotOf_mem v hv
      vertOf_mem := fun sl hsl => by
        rw [hpre_eq_mem _ (by simp [vertOfSlotBase, nodesBase]; omega) (by simp [vertOfSlotBase, isRootBase]; omega)]
        exact h.vertOf_mem sl hsl
      markArr_zero := fun k hk => by
        rw [hpre_eq_mem _ (by simp [markArrBase, nodesBase]; omega) (by simp [markArrBase, isRootBase]; omega)]
        exact h.markArr_zero k hk
      nodesAt := hn₆
      forestInv := hinv₆
      nodes_exact := fun id => by
        have h1 : id ∈ (t' :: rest).flatMap AuxTree.toList ↔ id ∈ (tx :: ty :: rest).flatMap AuxTree.toList := by
          simp only [List.flatMap_cons, List.mem_append, ht'_mem_iff, or_assoc]
        have h2 : id ∈ (tx :: ty :: rest).flatMap AuxTree.toList ↔ id ∈ x.trees.flatMap AuxTree.toList := by
          simp only [List.mem_flatMap]
          exact ⟨fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mpr ha, hu⟩,
            fun ⟨a, ha, hu⟩ => ⟨a, hperm.mem_iff.mp ha, hu⟩⟩
        exact h1.trans (h2.trans (h.nodes_exact id))
      comp_none := fun r' hr' hnil => by
        have hrd : r' ≠ dropRoot := (Finset.mem_erase.mp hr').1
        have hr'R : r' ∈ s.rf.R := Finset.mem_of_mem_erase hr'
        have hrk : r' ≠ keepRoot := fun heq => by
          subst r'; exact hord_keep_ne ((fullTour_eq_nil_iff hvalid'.compat keepRoot).mp hnil)
        have hneU : r' ≠ ru := by rcases hdrop with rfl | rfl <;> simp [keepRoot, hru_ne_rv.symm] at hrk <;> assumption
        have hneV : r' ≠ rv := by rcases hdrop with rfl | rfl <;> simp [keepRoot, hru_ne_rv.symm] at hrk <;> assumption
        simp only [x', ct', Function.update_of_ne hrk, Function.update_of_ne hrd]
        have hft_c : fullTour s'Abs.ord s'Abs.rf.F hvalid'.compat.forest r' = fullTour s.ord F' hvalid'_F.forest r' := by
          congr 1
        rw [hft_c, hft_other_eq r' hr'R hneU hneV] at hnil
        exact h.comp_none r' hr'R hnil
      comp_some := fun r' hr' hne_ft => by
        have hrd : r' ≠ dropRoot := (Finset.mem_erase.mp hr').1
        have hr'R : r' ∈ s.rf.R := Finset.mem_of_mem_erase hr'
        have hft_c : fullTour s'Abs.ord s'Abs.rf.F hvalid'.compat.forest r' = fullTour s.ord F' hvalid'_F.forest r' := by congr 1
        rw [hft_c] at hne_ft ⊢
        by_cases hrk : r' = keepRoot
        · subst r'
          exact ⟨t', by simp [x', ct'], by simp [x'], ht'_map⟩
        · have hneU : r' ≠ ru := by rcases hdrop with rfl | rfl <;> simp [keepRoot, hru_ne_rv.symm] at hrk <;> assumption
          have hneV : r' ≠ rv := by rcases hdrop with rfl | rfl <;> simp [keepRoot, hru_ne_rv.symm] at hrk <;> assumption
          rw [hft_other_eq r' hr'R hneU hneV] at hne_ft ⊢
          obtain ⟨tr', hctr', htr'_mem, htr'_map⟩ := h.comp_some r' hr'R hne_ft
          have ⟨hntx, hnty⟩ := hcomp_inj_xy r' hr'R hneU hneV
          have htr'_rest : tr' ∈ rest :=
            (List.mem_cons.mp ((List.mem_cons.mp (hperm.mem_iff.mp htr'_mem)).resolve_left
              (fun heq => hntx (heq ▸ hctr')))).resolve_left (fun heq => hnty (heq ▸ hctr'))
          exact ⟨tr', by simp [x', ct', Function.update_of_ne hrk, Function.update_of_ne hrd, hctr'],
            by simp [x', htr'_rest], htr'_map⟩
      tree_class := fun tr htr => by
        simp only [x', List.mem_cons] at htr
        rcases htr with rfl | hrest
        · exact Or.inl ⟨keepRoot, Finset.mem_erase.mpr ⟨hdrop_ne_keep.symm, hkeepR⟩, by simp [x', ct']⟩
        · have htr_mem : tr ∈ x.trees := hperm.mem_iff.mpr (by simp [hrest])
          rcases h.tree_class tr htr_mem with ⟨r', hr', hcr'⟩ | hsing
          · have hneU : r' ≠ ru := fun heq => by
              subst heq; exact htx_not_rest ((Option.some.inj (hcr'.symm.trans hctx)) ▸ hrest)
            have hneV : r' ≠ rv := fun heq => by
              subst heq; exact hty_not_rest ((Option.some.inj (hcr'.symm.trans hcty)) ▸ hrest)
            have hrd : r' ≠ dropRoot := by rcases hdrop with rfl | rfl <;> assumption
            have hrk : r' ≠ keepRoot := by rcases hdrop with rfl | rfl <;> simp [keepRoot, hru_ne_rv.symm, hneU, hneV]
            exact Or.inl ⟨r', Finset.mem_erase.mpr ⟨hrd, hr'⟩,
              by simp [x', ct', Function.update_of_ne hrk, Function.update_of_ne hrd, hcr']⟩
          · exact Or.inr hsing
      inactive_single := fun id h1 h2 hno => by
        have hmem := h.inactive_single id h1 h2 hno
        have hne_tx : AuxTree.node id .leaf .leaf ≠ tx := fun heq => by
          have he' : endOfKey (x.keyOf id) ∈ fullTour s.ord s.rf.F h.valid.compat.forest ru := by
            rw [← htx_map, ← heq]; simp [AuxTree.toList]
          obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he'
          exact hno w' hw'
        have hne_ty : AuxTree.node id .leaf .leaf ≠ ty := fun heq => by
          have he' : endOfKey (x.keyOf id) ∈ fullTour s.ord s.rf.F h.valid.compat.forest rv := by
            rw [← hty_map, ← heq]; simp [AuxTree.toList]
          obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he'
          exact hno w' hw'
        have hrest : AuxTree.node id .leaf .leaf ∈ rest :=
          (List.mem_cons.mp ((List.mem_cons.mp (hperm.mem_iff.mp hmem)).resolve_left hne_tx)).resolve_left hne_ty
        simp [x', hrest]
      val_active := fun id h1 h2 hact => by
        dsimp only [x'] at h2 ⊢
        have hid_cap : id ≤ x.numNodes := h2
        rw [hval₆ id hid_cap, hval₅ id hid_cap]
        have hrt_target : (if id = feD then 0 else (x.st.nodes id).val.rootTag) =
            tourRootTagVal s'Abs (endOfKey (x.keyOf id)) := by
          by_cases hidD : id = feD
          · subst id; simp only [↓reduceIte, hfeD_key, endOfKey_endKey']
            exact (tourRootTagVal_eq_zero (s := s'Abs) fun r' hr' hh =>
              (Finset.mem_erase.mp hr').1
                (h.valid.compat.unique r' dropRoot aD (List.mem_of_head? hh) haD_mem)).symm
          · simp only [hidD, ↓reduceIte]
            rw [h.val_active id h1 h2 hact]
            have hne_aD : endOfKey (x.keyOf id) ≠ aD := fun heq => by
              have hk : x.keyOf id = endKey aD := by rw [← endKey_endOfKey' (x.keyOf id), heq]
              exact hidD ((h.keyOf_mem id h1 h2).2.2.symm.trans (by rw [hk]))
            by_cases hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
            · obtain ⟨r', hr'R, hr'h⟩ := hex
              have hrd : r' ≠ dropRoot := fun heq => by subst heq; exact hne_aD (Option.some.inj (hr'h.symm.trans haD))
              rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
                tourRootTagVal_eq_succ hvalid' (Finset.mem_erase.mpr ⟨hrd, hr'R⟩) hr'h]
            · push Not at hex
              rw [tourRootTagVal_eq_zero hex, tourRootTagVal_eq_zero]
              intro r' hr' hh; exact hex r' (Finset.mem_of_mem_erase hr') hh
        have hrt_id : (s₄.nodes id).val.rootTag = tourRootTagVal s'Abs (endOfKey (x.keyOf id)) :=
          (hs4_rt id hid_cap).trans hrt_target
        rw [hval₄ id hid_cap]
        by_cases hiy : id = ny
        · subst id
          have hrt_ny : rtY = tourRootTagVal s'Abs (endOfKey (x.keyOf ny)) := by
            have := hrt_id; rw [hval₄ ny hny_cap, hvalY₃] at this; exact this
          rw [hvalY₃, hrt_ny, hny_key, endOfKey_two_mul_add1, hs'_F]
          simp [s'Abs, tourLink, F', addForestEdge]
        · rw [hvalne₃ id hid_cap hiy]
          by_cases hix : id = nx
          · subst id
            have hrt_nx : rtX = tourRootTagVal s'Abs (endOfKey (x.keyOf nx)) := by
              have := hrt_id; rw [hval₄ nx hnx_cap, hvalne₃ nx hnx_cap hnx_ne_ny, hvalX₂] at this; exact this
            rw [hvalX₂, hrt_nx, hnx_key, tour_endOfKey_two_mul, hs'_F]
            simp [s'Abs, tourLink, F', addForestEdge]
          · rw [hvalne₂ id hid_cap hix]
            have hzne : (endOfKey (x.keyOf id)).1 ≠ e := fun heq => by
              have hcases : endOfKey (x.keyOf id) = (e, true) ∨ endOfKey (x.keyOf id) = (e, false) := by
                cases hb : (endOfKey (x.keyOf id)).2
                · right; exact Prod.ext heq hb
                · left; exact Prod.ext heq hb
              rcases hcases with hc | hc
              · have hk : x.keyOf id = 2 * e := by rw [← endKey_endOfKey' (x.keyOf id), hc]; rfl
                exact hix ((h.keyOf_mem id h1 h2).2.2.symm.trans (by rw [hk]))
              · have hk : x.keyOf id = 2 * e + 1 := by rw [← endKey_endOfKey' (x.keyOf id), hc]; rfl
                exact hiy ((h.keyOf_mem id h1 h2).2.2.symm.trans (by rw [hk]))
            by_cases hiD : id = feD
            · subst id; rw [hvalD₁]
              have hvo := h.val_active feD hfeD_pos hfeD_le hact
              have hop : decide (0 < opD) = (x.st.nodes feD).val.isOpen :=
                (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
              have hmk : decide (0 < mkD) = (x.st.nodes feD).val.isMarked :=
                (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
              rw [hvo] at hop hmk
              have hrt0 : tourRootTagVal s'Abs (endOfKey (x.keyOf feD)) = 0 := by rw [← hrt_target]; simp
              rw [hop, hmk, hrt0, hs'_F]
              simp [s'Abs, tourLink, F', addForestEdge, hzne]
            · rw [hvalne₁ id hid_cap hiD, h.val_active id h1 h2 hact, hs'_F]
              have hrt_eq : (x.st.nodes id).val.rootTag = tourRootTagVal s'Abs (endOfKey (x.keyOf id)) := by
                rw [← hrt_target]; simp [hiD]
              rw [h.val_active id h1 h2 hact] at hrt_eq; dsimp only at hrt_eq; rw [hrt_eq]
              simp [s'Abs, tourLink, F', addForestEdge, hzne]
      val_inactive_rt := fun id h1 h2 hno => by
        dsimp only [x'] at h2 ⊢
        have hid_cap : id ≤ x.numNodes := h2
        rw [hval₆ id hid_cap, hval₅ id hid_cap, hs4_rt id hid_cap]
        split_ifs
        · rfl
        · exact h.val_inactive_rt id h1 h2 hno
      val_unused_rt := fun id hid hcond => by
        dsimp only [x'] at hcond
        rw [hval₆ id hid, hval₅ id hid, hs4_rt id hid]
        split_ifs
        · rfl
        · exact h.val_unused_rt id hid hcond }
  have hst5_feK : st₅.mem (firstEndBase b + keepRoot) = feK := by
    rw [hfr15.2 _ (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase (by simp [firstEndBase, nodesBase]; omega))]
    dsimp only [mem1]; rw [Function.update_of_ne (by simp [firstEndBase, isRootBase]; omega)]
    exact hfeK_first
  obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody⟩ := tourOpLinkBody_exec C hls ω hord_le hroom hwide
    he_lt hdropLt hkeepLt
    (by simpa [nodeAddr, tourLayout_stride] using hheap1.addr_lt hfeD_cap)
    (by simpa [nodeAddr, tourLayout_stride] using hheap1.addr_lt hnx_cap)
    (by simpa [nodeAddr, tourLayout_stride] using hheap1.addr_lt hny_cap)
    hhdr.2.2.2.2.2.2.1 (h.nodeOf_mem (2 * e) (by omega)).1 (h.nodeOf_mem (2 * e + 1) (by omega)).1
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1 hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    hhdr.2.2.2.2.2.1 hhdr.2.2.2.2.1 hfeD_first hmem1_opD hmem1_mkD
    hrun₁ hrtX_mem hrun₂ hrtY_mem hrun₃ hrun₄ hrun₅ ho₅_eq hst5_feK hrun₆
  have hresp : (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 2 mem heap b x' st₆.mem :=
    ⟨le_refl heap, Nat.le_add_right heap 2, hfr_all.1,
      fun a ha hnf => by
        have hnr : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a := fun hrec =>
          hnf (Or.inl ⟨by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).1; simp [nodesBase] at this; omega, (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).2⟩)
        rw [hfr_all.2 a ha hnr]; dsimp only [mem1]
        rw [Function.update_of_ne (fun heq => hnf (Or.inl ⟨by simp [isRootBase] at heq ⊢; omega, by simp [isRootBase, ordHandleOf, tourFixedSize] at heq ⊢; omega⟩))],
      fun a ha => Or.inl ha⟩
  refine ⟨.returned heap, st_fin, c_fin, hbody, rfl, x', hmem_fin ▸ hrep', hmem_fin ▸ hresp, ?_⟩
  have hlog := tourLog_of_le h.numNodes_le
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  rw [forestPhi_perm (List.Perm.swap tx₂ ty₂ rest), forestPhi_perm (List.Perm.swap tx₂ ty₁ rest)] at hcost₃
  have hmul_c : (4 * TOUR_FIND_AMORT + TOUR_LINKSPLICE_AMORT + TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) ≤
      (4 * TOUR_FIND_AMORT + TOUR_LINKSPLICE_AMORT + TOUR_SEQ_AMORT) * (2 * tourLog eCap) :=
    Nat.mul_le_mul_left _ hlog
  dsimp only [tourRep, tourPhi, x']
  rw [hmem_fin, ← hOrd.2, forestPhi_perm hperm]
  simp only [TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_SEQ_AMORT,
    TOUR_LINKSPLICE_AMORT, TOUR_CUTLINK_MUL] at hcost₁ hcost₂ hcost₃ hcost₄ hcost₅ hcost₆ hmul_c hcfin ⊢
  omega

end MinCostFlow.SparseCore.Program
