module

public import MinCostFlow.LSF.Program.BatchBFS
import Mathlib.Tactic.Linarith

/-!
# Graph, `FAncAt`, and HLD-Climb Lemmas for `addOrigRoot` (`BatchAddRootMath`)

Proves the pure structural and representation lemmas used by `BatchAddRoot` (root closure via `T_H`)
and `BatchOps` (vertex splits):

* `lsfRep_of_R_orig_eq`: `(LSFRep h).rep` depends on `S.R₀_base` only through `S.R_orig` and
  `LSFStructInv S`.
* `fancAt_after_splitCompBFS`: lifts `FAncAt` and `splitCompBFSContract.post` to `FAncAt` on the
  post-split forest, yielding the component-size drop inequalities needed by `phi_drop_addRoot_cut`
  and `phi_drop_split`.
* `auxAt_thParent_isParent`: relates the stored `thParent` array of `AuxAt` to the exact parent
  relation and upward closure in `(S.TH, S.r₀)`.
* `addOrigRoot_single_step`: when `z ∈ S.T₀.V \ S.R_orig` has its `T_H`-parent in `S.R_orig`,
  adding `z` to `S.R₀_base` adds only `z` to `S.R_orig`, deletes the unique `π`-minimum edge `cutE`
  on `S.T₀.forestPath z (S.origVert rC)`, and partitions `rC`'s component in `S.RF.F` into the two
  components of `cutE`'s endpoints separating `rC` and `z`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Transferring `LSFRep` when `R_orig` agrees -/

/-- `(LSFRep h).rep` depends on `R₀_base` only through `R_orig` and `LSFStructInv`. -/
lemma lsfRep_of_R_orig_eq {h b : ℕ} {S₁ S₂ : LSFState} {x : LSFConcrete} {mem : ℕ → ℕ}
    (hrep : (LSFRep h).rep b S₁ x mem)
    (hInv2 : LSFStructInv S₂)
    (hG₀ : S₂.G₀ = S₁.G₀) (hk : S₂.k = S₁.k)
    (hT₀ : S₂.T₀ = S₁.T₀) (hr₀ : S₂.r₀ = S₁.r₀) (hπ : S₂.π = S₁.π)
    (hG : S₂.G = S₁.G) (hTcur : S₂.T_cur = S₁.T_cur) (hR0i : S₂.R₀_init = S₁.R₀_init)
    (hiso : S₂.isolatedVerts = S₁.isolatedVerts) (horig : S₂.origVert = S₁.origVert)
    (hwstr : S₂.wstr = S₁.wstr) (hW : S₂.W_init = S₁.W_init)
    (_hnum : S₂.numUpdates = S₁.numUpdates)
    (hRorig : S₂.R_orig = S₁.R_orig) :
    (LSFRep h).rep b S₂ x mem := by
  have hR : S₂.R = S₁.R := by simp only [LSFState.R, hRorig, hiso]
  have hRF : S₂.RF = S₁.RF := by
    simp only [LSFState.RF, hTcur, hT₀, hr₀, hRorig, hπ, hR]
  have hTH : S₂.TH = S₁.TH := by simp only [LSFState.TH, hT₀, hr₀]
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hkeq, _, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvlt, helt, hhdr, hdgG, hT, hdgF, hFAnc, hWblk, hwstrAt, hAux⟩
  have hhdr2 : lsfHeaderAt mem b S₂ x := by
    simpa only [lsfHeaderAt, hR, hr₀] using hhdr
  have hAux2 : AuxAt mem (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 x.tM S₂
      x.tOrigList x.vList x.t0Parent x.t0ParentTreeIdx x.t0Depth x.thParent x.upV x.upMinIdx := by
    simpa only [AuxAt, hT₀, hr₀, hπ, hTH, hG, horig] using hAux
  refine ⟨hxH, hh1, hLin, hLw, hkn, hk.trans hkeq, hInv2,
    hG₀ ▸ hn0, hG₀ ▸ hm0, hT₀ ▸ htM, hnv, hme, htn, hn1, hT₀ ▸ hvlt, hG₀ ▸ helt,
    hhdr2, hG ▸ hdgG, hG ▸ hTcur ▸ hT₀ ▸ hπ ▸ hT, hRF ▸ hdgF, hRF ▸ hFAnc,
    hW ▸ hT₀ ▸ hr₀ ▸ hR0i ▸ hπ ▸ hWblk, hG ▸ hwstr ▸ hwstrAt, hAux2⟩

/-! ## Unified `FAncAt` preservation across `splitCompBFSProc` -/

open Classical in
/-- Given `FAncAt` before a single component split (either from deleting one forest edge or from
splitting a root vertex `v` into `v` and `v'`) and `splitCompBFSContract.post` after running
`splitCompBFSProc` on the post-split forest `F'`, produces updated `(compId', compRoot', compSize')`
satisfying `FAncAt` on `{ F := F', R := insert root2 RF.R }` together with the component-size drop
bounds on `Csmall`. -/
lemma fancAt_after_splitCompBFS
    {w dgFPtr fAncPtr auxPtr vCap eCapF n0 uA uB oldCid root1 root2 newSum : ℕ}
    {mem_pre mem_mid mem' : ℕ → ℕ} {RF : RootedForest} {F' : MGraph}
    {rList : List ℕ} {compId compRoot compSize : ℕ → ℕ} {activeCids : Finset ℕ}
    (hFAnc : FAncAt mem_pre fAncPtr vCap RF rList compId compRoot compSize activeCids)
    (hRF_sep : ∀ r₁ ∈ RF.R, ∀ r₂ ∈ RF.R, r₁ ≠ r₂ → ¬ RF.F.Connected r₁ r₂)
    (hF'_vCap : ∀ v ∈ F'.V, v < vCap)
    (hV_sub : RF.F.V ⊆ F'.V)
    (hR'_sub_V : insert root2 RF.R ⊆ F'.V)
    (hr2_not : root2 ∉ RF.R) (hr2_lt : root2 < vCap)
    (hr2_F' : root2 ∈ F'.V) (hr1_F' : root1 ∈ F'.V)
    (hold_act : oldCid ∈ activeCids) (hr1_eq : compRoot oldCid = root1)
    (_huA : uA ∈ F'.V) (_huB : uB ∈ F'.V) (hnotConn : ¬ F'.Connected uA uB)
    (hpart_V : ∀ v ∈ F'.V,
      (F'.Connected v uA ∨ F'.Connected v uB) ↔
      (v = root2 ∨ (v ∈ RF.F.V ∧ RF.F.Connected v root1)))
    (hother_conn : ∀ v ∈ F'.V, ¬ F'.Connected v uA → ¬ F'.Connected v uB →
      v ∈ RF.F.V ∧ ∀ w ∈ RF.F.V, F'.Connected v w ↔ RF.F.Connected v w)
    (hother_disj : ∀ v ∈ F'.V, ∀ w ∈ F'.V,
      (F'.Connected v uA ∨ F'.Connected v uB) → ¬ F'.Connected w uA → ¬ F'.Connected w uB →
      ¬ F'.Connected v w)
    (hroots_sep : (F'.Connected root1 uA ∧ F'.Connected root2 uB) ∨
      (F'.Connected root1 uB ∧ F'.Connected root2 uA))
    (hmid_hdr : mem_mid (fAncPtr + fOffRCount) = RF.R.card + 1 ∧
      mem_mid (fAncPtr + fOffIsRootPtr) = fIsRootBase fAncPtr ∧
      mem_mid (fAncPtr + fOffRListPtr) = fRListBase fAncPtr vCap ∧
      mem_mid (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap ∧
      mem_mid (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap ∧
      mem_mid (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap)
    (hmid_isRoot : ∀ v < vCap,
      mem_mid (fIsRootBase fAncPtr + v) = if v = root2 then 1 else mem_pre (fIsRootBase fAncPtr + v))
    (hmid_rList : (∀ i < rList.length,
      mem_mid (fRListBase fAncPtr vCap + i) = mem_pre (fRListBase fAncPtr vCap + i)) ∧
      mem_mid (fRListBase fAncPtr vCap + rList.length) = root2)
    (hmid_compId : ∀ v < vCap,
      mem_mid (fCompIdBase fAncPtr vCap + v) =
        if v = root2 then oldCid else mem_pre (fCompIdBase fAncPtr vCap + v))
    (hmid_compRoot : ∀ c < vCap,
      mem_mid (fCompRootBase fAncPtr vCap + c) = mem_pre (fCompRootBase fAncPtr vCap + c))
    (hmid_compSize : ∀ c < vCap,
      mem_mid (fCompSizeBase fAncPtr vCap + c) = mem_pre (fCompSizeBase fAncPtr vCap + c))
    (hbfs_post : (splitCompBFSContract w F').post
      [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum]
      mem_mid 0 mem')
    (hcs_le_qA : fCompSizeBase fAncPtr vCap + vCap ≤ auxQBufABase auxPtr vCap n0) :
    ∃ (compId' compRoot' compSize' : ℕ → ℕ) (Csmall Cbig : Finset ℕ),
      let RF' : RootedForest := { F := F', R := insert root2 RF.R }
      ((Csmall = (F'.V.filter fun v => F'.Connected v uA) ∧
        Cbig = (F'.V.filter fun v => F'.Connected v uB)) ∨
       (Csmall = (F'.V.filter fun v => F'.Connected v uB) ∧
        Cbig = (F'.V.filter fun v => F'.Connected v uA))) ∧
      Csmall.card ≤ Cbig.card ∧
      FAncAt mem' fAncPtr vCap RF' (rList ++ [root2]) compId' compRoot' compSize'
        (insert root2 activeCids) ∧
      (∀ u ∈ F'.V, compSize' (compId' u) = (F'.V.filter fun v => F'.Connected v u).card) ∧
      (∀ u ∈ F'.V, u ∈ Csmall → compSize' (compId' u) = Csmall.card ∧
        Csmall.card + Cbig.card = (F'.V.filter fun v => F'.Connected v uA ∨ F'.Connected v uB).card) ∧
      (∀ u ∈ F'.V, u ∈ Cbig → compSize' (compId' u) = Cbig.card) ∧
      (∀ u ∈ F'.V, u ∉ Csmall → u ∉ Cbig → u ∈ RF.F.V ∧ compSize' (compId' u) = compSize (compId u)) := by
  rcases hFAnc with ⟨_, _, _, _, _, _, _, hrlen, hrnd, hrmem, _, hrL, hIsRoot_pre,
    hact_sub, hact_spec, hcid_pre⟩
  rcases hbfs_post with ⟨dgFPtr', fAncPtr', auxPtr', vCap', eCapF', n0', uA', uB', oldCid',
    root1', root2', newSum', hargs_eq, _, hframe, Csmall, Cbig, hCpair, hCle,
    hcid_post, hother_post, hcsR2_post, hcsOld_post, hroots_post⟩
  simp only [List.cons.injEq, and_true] at hargs_eq
  rcases hargs_eq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  set CA := F'.V.filter fun v => F'.Connected v uA
  set CB := F'.V.filter fun v => F'.Connected v uB
  have hCA_disj_CB : Disjoint CA CB := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact hnotConn (connected_trans (connected_symm (Finset.mem_filter.mp hvA).2)
      (Finset.mem_filter.mp hvB).2)
  have hCs_disj_Cb : Disjoint Csmall Cbig := by
    rcases hCpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hCA_disj_CB
    · exact hCA_disj_CB.symm
  have hCs_union : Csmall ∪ Cbig = F'.V.filter fun v => F'.Connected v uA ∨ F'.Connected v uB := by
    ext v
    rcases hCpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [CA, CB, Finset.mem_union, Finset.mem_filter] <;> tauto
  have hCs_card_sum : Csmall.card + Cbig.card =
      (F'.V.filter fun v => F'.Connected v uA ∨ F'.Connected v uB).card := by
    rw [← Finset.card_union_of_disjoint hCs_disj_Cb, hCs_union]
  have hCs_conn : ∀ x ∈ Csmall, ∀ y ∈ Csmall, F'.Connected x y := fun x hx y hy => by
    rcases hCpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact connected_trans (Finset.mem_filter.mp hx).2 (connected_symm (Finset.mem_filter.mp hy).2)
  have hCb_conn : ∀ x ∈ Cbig, ∀ y ∈ Cbig, F'.Connected x y := fun x hx y hy => by
    rcases hCpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact connected_trans (Finset.mem_filter.mp hx).2 (connected_symm (Finset.mem_filter.mp hy).2)
  have hCs_filter : ∀ x ∈ Csmall, (F'.V.filter fun v => F'.Connected v x) = Csmall := by
    intro x hx; ext v
    rcases hCpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [CA, CB, Finset.mem_filter] at hx ⊢ <;>
      exact ⟨fun ⟨hv, hvx⟩ => ⟨hv, connected_trans hvx hx.2⟩,
        fun ⟨hv, hvu⟩ => ⟨hv, connected_trans hvu (connected_symm hx.2)⟩⟩
  have hCb_filter : ∀ x ∈ Cbig, (F'.V.filter fun v => F'.Connected v x) = Cbig := by
    intro x hx; ext v
    rcases hCpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [CA, CB, Finset.mem_filter] at hx ⊢ <;>
      exact ⟨fun ⟨hv, hvx⟩ => ⟨hv, connected_trans hvx hx.2⟩,
        fun ⟨hv, hvu⟩ => ⟨hv, connected_trans hvu (connected_symm hx.2)⟩⟩
  have hroots_in_pair : (root1 ∈ Csmall ∧ root2 ∈ Cbig) ∨ (root1 ∈ Cbig ∧ root2 ∈ Csmall) := by
    rcases hCpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hroots_sep with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Finset.mem_filter.mpr ⟨hr1_F', h1⟩, Finset.mem_filter.mpr ⟨hr2_F', h2⟩⟩
    · exact Or.inr ⟨Finset.mem_filter.mpr ⟨hr1_F', h1⟩, Finset.mem_filter.mpr ⟨hr2_F', h2⟩⟩
    · exact Or.inr ⟨Finset.mem_filter.mpr ⟨hr1_F', h1⟩, Finset.mem_filter.mpr ⟨hr2_F', h2⟩⟩
    · exact Or.inl ⟨Finset.mem_filter.mpr ⟨hr1_F', h1⟩, Finset.mem_filter.mpr ⟨hr2_F', h2⟩⟩
  have hCs_pos : 1 ≤ Csmall.card := by
    rcases hroots_in_pair with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Finset.card_pos.mpr ⟨root1, h1⟩
    · exact Finset.card_pos.mpr ⟨root2, h2⟩
  have hCb_pos : 1 ≤ Cbig.card := le_trans hCs_pos hCle
  let compId' : ℕ → ℕ := fun v =>
    if v ∈ Csmall then root2 else if v = root2 then oldCid else compId v
  let compRoot' : ℕ → ℕ := fun c =>
    if c = root2 then (if root2 ∈ Csmall then root2 else root1)
    else if c = oldCid then (if root2 ∈ Csmall then root1 else root2)
    else compRoot c
  let compSize' : ℕ → ℕ := fun c =>
    if c = root2 then Csmall.card
    else if c = oldCid then Cbig.card
    else compSize c
  have hold_ne_r2 : oldCid ≠ root2 := fun h => hr2_not (h ▸ hact_sub hold_act)
  have hact_old := hact_spec oldCid hold_act
  have hr1_R : root1 ∈ RF.R := hr1_eq ▸ hact_old.2.2.1
  have hcid_old_of_conn : ∀ v ∈ RF.F.V, RF.F.Connected v root1 → compId v = oldCid := by
    intro v hv hconn
    obtain ⟨hcv_eq, hcv_act, hcv_conn⟩ := hcid_pre v hv
    rw [hcv_eq] at hcv_act hcv_conn
    have hcr_R : compRoot (compId v) ∈ RF.R := (hact_spec _ hcv_act).2.2.1
    have hcr_eq : compRoot (compId v) = root1 := by
      by_contra hne
      exact hRF_sep _ hcr_R _ hr1_R hne (connected_trans (connected_symm hcv_conn) hconn)
    have h1 := (hact_spec _ hcv_act).2.2.2.1
    rw [hcr_eq] at h1
    exact h1.symm.trans (hr1_eq ▸ hact_old.2.2.2.1)
  have hmem_below_cid : ∀ a < fCompIdBase fAncPtr vCap, mem' a = mem_mid a := by
    intro a ha
    refine hframe a (fun h => Nat.not_lt.mpr h.1 ha) (fun h => ?_)
    have hcid_le_cs : fCompIdBase fAncPtr vCap ≤ fCompSizeBase fAncPtr vCap + vCap := by
      dsimp [fCompSizeBase, fCompRootBase, fCompIdBase]; omega
    exact Nat.not_le.mpr (lt_of_lt_of_le ha (le_trans hcid_le_cs hcs_le_qA)) h.1
  have hcid'_mem : ∀ v ∈ F'.V, mem' (fCompIdBase fAncPtr vCap + v) = compId' v := by
    intro v hv
    have hvlt := hF'_vCap v hv
    rw [hcid_post v hvlt, hmid_compId v hvlt]
    dsimp only [compId']
    by_cases hvs : v ∈ Csmall
    · simp only [hvs, ↓reduceIte]
    · simp only [hvs, ↓reduceIte]
      by_cases hvr2 : v = root2
      · simp only [hvr2, ↓reduceIte]
      · simp only [hvr2, ↓reduceIte]
        have hv_pre : v ∈ RF.F.V := by
          by_cases hvb : v ∈ Cbig
          · have hmemU : v ∈ Csmall ∪ Cbig := Finset.mem_union_right _ hvb
            rw [hCs_union, Finset.mem_filter] at hmemU
            rcases (hpart_V v hv).mp hmemU.2 with rfl | ⟨h1, _⟩
            · exact absurd rfl hvr2
            · exact h1
          · have hnotU : v ∉ Csmall ∪ Cbig := by simp [hvs, hvb]
            rw [hCs_union, Finset.mem_filter] at hnotU
            have hna : ¬ F'.Connected v uA := fun h => hnotU ⟨hv, Or.inl h⟩
            have hnb : ¬ F'.Connected v uB := fun h => hnotU ⟨hv, Or.inr h⟩
            exact (hother_conn v hv hna hnb).1
        exact (hcid_pre v hv_pre).1
  have hcid'_Cbig : ∀ v ∈ Cbig, compId' v = oldCid := by
    intro v hv
    have hv_notS : v ∉ Csmall := Finset.disjoint_right.mp hCs_disj_Cb hv
    dsimp only [compId']
    simp only [hv_notS, ↓reduceIte]
    by_cases hvr2 : v = root2
    · simp only [hvr2, ↓reduceIte]
    · simp only [hvr2, ↓reduceIte]
      have hmemU : v ∈ Csmall ∪ Cbig := Finset.mem_union_right _ hv
      rw [hCs_union, Finset.mem_filter] at hmemU
      rcases (hpart_V v hmemU.1).mp hmemU.2 with rfl | ⟨hv_pre, hconn⟩
      · exact absurd rfl hvr2
      · exact hcid_old_of_conn v hv_pre hconn
  have hcid'_other : ∀ v ∈ F'.V, v ∉ Csmall → v ∉ Cbig →
      v ∈ RF.F.V ∧ compId' v = compId v ∧ compId v ≠ oldCid ∧ compId v ≠ root2 := by
    intro v hv hvS hvB
    have hnotU : v ∉ Csmall ∪ Cbig := by simp [hvS, hvB]
    rw [hCs_union, Finset.mem_filter] at hnotU
    have hna : ¬ F'.Connected v uA := fun h => hnotU ⟨hv, Or.inl h⟩
    have hnb : ¬ F'.Connected v uB := fun h => hnotU ⟨hv, Or.inr h⟩
    have hv_pre := (hother_conn v hv hna hnb).1
    have hvr2 : v ≠ root2 := by
      intro h; subst h
      rcases hroots_in_pair with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact hvB h2
      · exact hvS h2
    have hcid_eq : compId' v = compId v := by dsimp only [compId']; simp [hvS, hvr2]
    have hne_old : compId v ≠ oldCid := by
      intro hEq
      obtain ⟨hc_eq, _, hc_conn⟩ := hcid_pre v hv_pre
      rw [hc_eq, hEq, hr1_eq] at hc_conn
      have hmemU : F'.Connected v uA ∨ F'.Connected v uB :=
        (hpart_V v hv).mpr (Or.inr ⟨hv_pre, hc_conn⟩)
      exact hmemU.elim hna hnb
    have hne_r2 : compId v ≠ root2 := by
      intro hEq
      obtain ⟨hc_eq, hc_act, _⟩ := hcid_pre v hv_pre
      rw [hc_eq, hEq] at hc_act
      exact hr2_not (hact_sub hc_act)
    exact ⟨hv_pre, hcid_eq, hne_old, hne_r2⟩
  have hcr_r2_in : compRoot' root2 ∈ Csmall := by
    dsimp only [compRoot']
    simp only [↓reduceIte]
    split_ifs with h
    · exact h
    · exact hroots_in_pair.resolve_right (fun hp => h hp.2) |>.1
  have hcr_old_in : compRoot' oldCid ∈ Cbig := by
    dsimp only [compRoot']
    simp only [hold_ne_r2, ↓reduceIte]
    split_ifs with h
    · exact hroots_in_pair.resolve_left (fun hp => Finset.disjoint_left.mp hCs_disj_Cb h hp.2) |>.1
    · exact hroots_in_pair.resolve_right (fun hp => h hp.2) |>.2
  have hcr_r2_mem : mem' (fCompRootBase fAncPtr vCap + root2) = compRoot' root2 ∧
      mem' (fCompRootBase fAncPtr vCap + oldCid) = compRoot' oldCid := by
    dsimp only [compRoot']
    simp only [hold_ne_r2, ↓reduceIte]
    rcases hroots_post with ⟨hr2S, h1, h2⟩ | ⟨hr2nS, h1, h2⟩
    · simp only [hr2S, ↓reduceIte]; exact ⟨h1, h2⟩
    · simp only [hr2nS, ↓reduceIte]; exact ⟨h1, h2⟩
  have hrlen' : (rList ++ [root2]).length = (insert root2 RF.R).card := by
    rw [List.length_append, List.length_singleton, hrlen, Finset.card_insert_of_notMem hr2_not]
  have hrlen'_le : (rList ++ [root2]).length ≤ vCap := by
    rw [hrlen']
    have hsub_rng : insert root2 RF.R ⊆ Finset.range vCap :=
      fun x hx => Finset.mem_range.mpr (hF'_vCap x (hR'_sub_V hx))
    exact (Finset.card_le_card hsub_rng).trans_eq (Finset.card_range vCap)
  have hRF'_FAnc : FAncAt mem' fAncPtr vCap { F := F', R := insert root2 RF.R }
      (rList ++ [root2]) compId' compRoot' compSize' (insert root2 activeCids) := by
    have hhd : ∀ off < fAncHdrSize, mem' (fAncPtr + off) = mem_mid (fAncPtr + off) := fun off hoff =>
      hmem_below_cid _ (by
        dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize] at hoff ⊢; omega)
    refine ⟨(hhd _ (by decide)).trans (hmid_hdr.1.trans (Finset.card_insert_of_notMem hr2_not).symm),
      (hhd _ (by decide)).trans hmid_hdr.2.1,
      (hhd _ (by decide)).trans hmid_hdr.2.2.1,
      (hhd _ (by decide)).trans hmid_hdr.2.2.2.1,
      (hhd _ (by decide)).trans hmid_hdr.2.2.2.2.1,
      (hhd _ (by decide)).trans hmid_hdr.2.2.2.2.2,
      hF'_vCap, hrlen',
      List.nodup_append.mpr ⟨hrnd, List.nodup_singleton _, fun x hx y hy hxy =>
        hr2_not ((hrmem x).mp hx |> fun h => (List.mem_singleton.mp hy ▸ hxy) ▸ h)⟩,
      fun r => by simp [hrmem, Finset.mem_insert, or_comm],
      hrlen'_le, ?_, ?_,
      Finset.insert_subset_insert root2 hact_sub, ?_, ?_⟩
    · intro i hi
      have hi_lt_vCap : i < vCap := lt_of_lt_of_le hi hrlen'_le
      rw [hmem_below_cid _ (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega)]
      by_cases hil : i < rList.length
      · rw [List.getElem_append_left hil, hmid_rList.1 i hil, hrL i hil]
      · have hieq : i = rList.length := by rw [List.length_append, List.length_singleton] at hi; omega
        subst hieq
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        exact hmid_rList.2
    · intro v hv
      rw [hmem_below_cid _ (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega), hmid_isRoot v hv]
      by_cases hvr2 : v = root2
      · subst hvr2; simp
      · simp only [hvr2, ↓reduceIte, hIsRoot_pre v hv, Finset.mem_insert, false_or]
    · intro c hc
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc_old
      · refine ⟨hr2_lt, hcr_r2_mem.1, ?_, ?_, hcsR2_post.trans (by dsimp [compSize']; simp),
          by dsimp [compSize']; simp [hCs_pos], ?_⟩
        · dsimp only [compRoot']; simp only [↓reduceIte]
          split_ifs <;> simp [hr1_R]
        · dsimp only [compId']; simp [hcr_r2_in]
        · dsimp only [compSize']; simp only [↓reduceIte]
          exact (congrArg Finset.card (hCs_filter _ hcr_r2_in)).symm
      · by_cases hco : c = oldCid
        · subst hco
          refine ⟨hact_old.1, hcr_r2_mem.2, ?_, ?_,
            hcsOld_post.trans (by dsimp [compSize']; simp [hold_ne_r2]),
            by dsimp [compSize']; simp [hold_ne_r2, hCb_pos], ?_⟩
          · dsimp only [compRoot']; simp only [hold_ne_r2, ↓reduceIte]
            split_ifs <;> simp [hr1_R]
          · exact hcid'_Cbig _ hcr_old_in
          · dsimp only [compSize']; simp only [hold_ne_r2, ↓reduceIte]
            exact (congrArg Finset.card (hCb_filter _ hcr_old_in)).symm
        · have hc_ne_r2 : c ≠ root2 := fun h => hr2_not (h ▸ hact_sub hc_old)
          obtain ⟨hclt, hcr_pre, hcrR, hcr_cid, hcs_pre, hcs1, hcs_card⟩ := hact_spec c hc_old
          have hcr'_eq : compRoot' c = compRoot c := by dsimp [compRoot']; simp [hc_ne_r2, hco]
          have hcs'_eq : compSize' c = compSize c := by dsimp [compSize']; simp [hc_ne_r2, hco]
          have hcr_F' : compRoot c ∈ F'.V := hR'_sub_V (Finset.mem_insert_of_mem hcrR)
          have hcr_not_conn : ¬ RF.F.Connected (compRoot c) root1 := fun hconn => by
            have hne_r : compRoot c ≠ root1 := fun heq =>
              hco (hcr_cid.symm.trans (heq ▸ hr1_eq ▸ hact_old.2.2.2.1))
            exact hRF_sep _ hcrR _ hr1_R hne_r hconn
          have hcr_ne_r2 : compRoot c ≠ root2 := fun h => hr2_not (h ▸ hcrR)
          have hcr_not_uAB : ¬ F'.Connected (compRoot c) uA ∧ ¬ F'.Connected (compRoot c) uB := by
            have hnot : ¬ (F'.Connected (compRoot c) uA ∨ F'.Connected (compRoot c) uB) := by
              rw [hpart_V _ hcr_F']
              rintro (h1 | ⟨_, h2⟩)
              · exact hcr_ne_r2 h1
              · exact hcr_not_conn h2
            exact ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
          have hcr_notS : compRoot c ∉ Csmall := by
            rcases hCpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact fun h => hcr_not_uAB.1 (Finset.mem_filter.mp h).2
            · exact fun h => hcr_not_uAB.2 (Finset.mem_filter.mp h).2
          have hcomp_eq : (F'.V.filter fun u => F'.Connected u (compRoot c)) =
              (RF.F.V.filter fun u => RF.F.Connected u (compRoot c)) := by
            ext u
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨huF', hconn'⟩
              have hu_not : ¬ (F'.Connected u uA ∨ F'.Connected u uB) := fun huAB =>
                hother_disj u huF' (compRoot c) hcr_F' huAB hcr_not_uAB.1 hcr_not_uAB.2 hconn'
              obtain ⟨hu_pre, hiff⟩ := hother_conn u huF' (fun h => hu_not (Or.inl h)) (fun h => hu_not (Or.inr h))
              have hcr_preV : compRoot c ∈ RF.F.V := (hother_conn _ hcr_F' hcr_not_uAB.1 hcr_not_uAB.2).1
              exact ⟨hu_pre, (hiff _ hcr_preV).mp hconn'⟩
            · rintro ⟨hu_pre, hconn_pre⟩
              have hcr_iff := (hother_conn _ hcr_F' hcr_not_uAB.1 hcr_not_uAB.2).2 u hu_pre
              exact ⟨hV_sub hu_pre, connected_symm (hcr_iff.mpr (connected_symm hconn_pre))⟩
          have hoth := hother_post c hclt hco hc_ne_r2
          refine ⟨hclt, hoth.1.trans ((hmid_compRoot c hclt).trans (hcr_pre.trans hcr'_eq.symm)),
            hcr'_eq ▸ Finset.mem_insert_of_mem hcrR,
            by dsimp only [compRoot', compId']; simp [hc_ne_r2, hco, hcr_notS, hcr_ne_r2, hcr_cid],
            hoth.2.trans ((hmid_compSize c hclt).trans (hcs_pre.trans hcs'_eq.symm)),
            hcs'_eq ▸ hcs1,
            by rw [hcr'_eq, hcs'_eq, hcomp_eq]; exact hcs_card⟩
    · intro v hv
      rw [hcid'_mem v hv]
      by_cases hvS : v ∈ Csmall
      · refine ⟨rfl, ?_, ?_⟩
        · dsimp only [compId']; simp [hvS]
        · dsimp only [compId']; simp only [hvS, ↓reduceIte]
          exact hCs_conn v hvS _ hcr_r2_in
      · by_cases hvB : v ∈ Cbig
        · have hc_eq := hcid'_Cbig v hvB
          rw [hc_eq]
          exact ⟨rfl, Finset.mem_insert_of_mem hold_act, hCb_conn v hvB _ hcr_old_in⟩
        · obtain ⟨hv_pre, hc_eq, hne_old, hne_r2⟩ := hcid'_other v hv hvS hvB
          rw [hc_eq]
          obtain ⟨hpre_eq, hpre_act, hpre_conn⟩ := hcid_pre v hv_pre
          rw [hpre_eq] at hpre_act hpre_conn
          have hnotU : v ∉ Csmall ∪ Cbig := by simp [hvS, hvB]
          rw [hCs_union, Finset.mem_filter] at hnotU
          have hna : ¬ F'.Connected v uA := fun h => hnotU ⟨hv, Or.inl h⟩
          have hnb : ¬ F'.Connected v uB := fun h => hnotU ⟨hv, Or.inr h⟩
          have hcrR := (hact_spec _ hpre_act).2.2.1
          have hcrF' : compRoot (compId v) ∈ F'.V := hR'_sub_V (Finset.mem_insert_of_mem hcrR)
          have hcr_ne_r2 : compRoot (compId v) ≠ root2 := fun h => hr2_not (h ▸ hcrR)
          have hcr_not_r1 : ¬ RF.F.Connected (compRoot (compId v)) root1 := fun hconn => by
            have hne_r : compRoot (compId v) ≠ root1 := fun heq =>
              hne_old ((hact_spec _ hpre_act).2.2.2.1.symm.trans (heq ▸ hr1_eq ▸ hact_old.2.2.2.1))
            exact hRF_sep _ hcrR _ hr1_R hne_r hconn
          have hcr_notU : ¬ (F'.Connected (compRoot (compId v)) uA ∨ F'.Connected (compRoot (compId v)) uB) := by
            rw [hpart_V _ hcrF']
            rintro (h1 | ⟨_, h2⟩)
            · exact hcr_ne_r2 h1
            · exact hcr_not_r1 h2
          have hcr_preV : compRoot (compId v) ∈ RF.F.V :=
            (hother_conn _ hcrF' (fun h => hcr_notU (Or.inl h)) (fun h => hcr_notU (Or.inr h))).1
          refine ⟨rfl, Finset.mem_insert_of_mem hpre_act, ?_⟩
          dsimp only [compRoot']
          simp only [hne_r2, hne_old, ↓reduceIte]
          exact ((hother_conn v hv hna hnb).2 _ hcr_preV).mpr hpre_conn
  refine ⟨compId', compRoot', compSize', Csmall, Cbig, hCpair, hCle, hRF'_FAnc, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨_, hc_act, hc_conn⟩ := hRF'_FAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 u hu
    rw [hcid'_mem u hu] at hc_act hc_conn
    have hcard := (hRF'_FAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (compId' u) hc_act).2.2.2.2.2.2
    rw [hcard]
    congr 1; ext v; simp only [Finset.mem_filter]
    exact ⟨fun ⟨hv, hvc⟩ => ⟨hv, connected_trans hvc (connected_symm hc_conn)⟩,
      fun ⟨hv, hvu⟩ => ⟨hv, connected_trans hvu hc_conn⟩⟩
  · intro u _ huS
    refine ⟨?_, hCs_card_sum⟩
    dsimp only [compId', compSize']; simp [huS]
  · intro u _ huB
    rw [hcid'_Cbig u huB]
    dsimp only [compSize']; simp [hold_ne_r2]
  · intro u hu huS huB
    obtain ⟨hu_pre, hc_eq, hne_old, hne_r2⟩ := hcid'_other u hu huS huB
    refine ⟨hu_pre, ?_⟩
    rw [hc_eq]
    dsimp only [compSize']; simp [hne_r2, hne_old]

/-! ## HLD parent characterization from `AuxAt` -/

/-- From the `AuxAt` edge and depth equations for `thParent`, `vList[thParent i]!` is the exact
parent of `vList[i]` in `(S.TH, S.r₀)`, so the ancestors of `vList[i]` in `S.TH` are `vList[i]`
together with the ancestors of `vList[thParent i]!`. -/
lemma auxAt_thParent_isParent {T₀ : MGraph} {r₀ n0 i : ℕ} {vList : List ℕ}
    {thParent : ℕ → ℕ}
    (hT₀ : IsRootedTree T₀ r₀)
    (hvLen : vList.length = n0) (hvMem : ∀ v, v ∈ vList ↔ v ∈ T₀.V)
    (hi : i < n0) (hp_lt : thParent i < n0)
    (hdep : ((hldAuxTree T₀ r₀).forestPath (vList[i]'(by omega)) r₀).length =
      ((hldAuxTree T₀ r₀).forestPath (vList[thParent i]!) r₀).length + 1)
    (hedge : ∃ e ∈ (hldAuxTree T₀ r₀).E,
      ((hldAuxTree T₀ r₀).tail e = vList[i]'(by omega) ∧
        (hldAuxTree T₀ r₀).head e = vList[thParent i]!) ∨
      ((hldAuxTree T₀ r₀).tail e = vList[thParent i]! ∧
        (hldAuxTree T₀ r₀).head e = vList[i]'(by omega))) :
    let TH := hldAuxTree T₀ r₀
    let u := vList[i]'(by omega)
    let p := vList[thParent i]'(by omega)
    IsAncestor TH r₀ p u ∧
    (∀ w, IsAncestor TH r₀ w u ↔ w = u ∨ IsAncestor TH r₀ w p) := by
  intro TH u p
  have hTH : IsRootedTree TH r₀ := hldAuxTree_isRootedTree hT₀
  have hp_get : vList[thParent i]! = p := getElem!_pos vList (thParent i) (by omega)
  rw [hp_get] at hdep hedge
  have hpV : p ∈ TH.V := (hvMem p).mp (List.getElem_mem _)
  have huV : u ∈ TH.V := (hvMem u).mp (List.getElem_mem _)
  obtain ⟨e, heE, hfh⟩ := hedge
  have hstep : ∃ dir : Bool, TH.src (e, dir) = u ∧ TH.dst (e, dir) = p := by
    rcases hfh with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact ⟨true, by dsimp [TH, MGraph.src]; exact ht, by dsimp [TH, MGraph.dst]; exact hh⟩
    · exact ⟨false, by dsimp [TH, MGraph.src]; exact hh, by dsimp [TH, MGraph.dst]; exact ht⟩
  obtain ⟨dir, hsrc, hdst⟩ := hstep
  have hPp := forestPath_isPath hTH.isForest (hTH.connected hpV hTH.2)
  have hu_not_on : u ∉ TH.walkVertices p (TH.forestPath p r₀) := by
    intro hmem
    have hanc_up : IsAncestor TH r₀ u p := hmem
    have hle := isAncestor_depth_le hTH hpV hanc_up
    dsimp [depth, TH] at hle
    change ((hldAuxTree T₀ r₀).forestPath u r₀).length =
      ((hldAuxTree T₀ r₀).forestPath p r₀).length + 1 at hdep
    omega
  let Q := (e, dir) :: TH.forestPath p r₀
  have hQ_walk : TH.IsWalk u r₀ Q := .cons heE hsrc (hdst.symm ▸ hPp.1)
  have hQ_wv : TH.walkVertices u Q = u :: TH.walkVertices p (TH.forestPath p r₀) := by
    simp [Q, MGraph.walkVertices, hdst]
  have hQ_path : TH.IsPath u r₀ Q :=
    ⟨hQ_walk, by rw [hQ_wv]; exact List.nodup_cons.mpr ⟨hu_not_on, hPp.2⟩⟩
  have hfp_eq : TH.forestPath u r₀ = Q := forestPath_eq_of_isPath hTH.isForest hQ_path
  refine ⟨?_, fun w => ?_⟩
  · show p ∈ TH.walkVertices u (TH.forestPath u r₀)
    rw [hfp_eq, hQ_wv]
    exact List.mem_cons_of_mem _ (isAncestor_refl TH r₀ p)
  · show w ∈ TH.walkVertices u (TH.forestPath u r₀) ↔ w = u ∨ w ∈ TH.walkVertices p (TH.forestPath p r₀)
    rw [hfp_eq, hQ_wv, List.mem_cons]

/-! ## Single-root insertion in `S.RF.F` -/

private lemma isWalk_mem_endpoints_walkVertices {F : MGraph} {s t : ℕ} {W : List (ℕ × Bool)}
    (hW : F.IsWalk s t W) :
    ∀ y ∈ W, F.tail y.1 ∈ F.walkVertices s W ∧ F.head y.1 ∈ F.walkVertices s W := by
  induction hW with
  | nil _ => intro _ hy; cases hy
  | cons _ hsrc _ ih =>
    rename_i u_v v_v x_v P_v
    intro y hy
    rw [MGraph.walkVertices, List.map_cons]
    rcases List.mem_cons.mp hy with rfl | hyt
    · rcases y with ⟨e', dir'⟩
      cases dir'
      · dsimp [MGraph.src, MGraph.dst] at hsrc ⊢
        exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, by rw [hsrc]; exact List.mem_cons_self⟩
      · dsimp [MGraph.src, MGraph.dst] at hsrc ⊢
        exact ⟨by rw [hsrc]; exact List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
    · have := ih y hyt
      exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

/-- Deleting one edge `e` from a forest `F` disconnects `F.tail e` and `F.head e`, partitions
the component of `F.tail e` into the components of `F.tail e` and `F.head e` in `F'`, and leaves
all other components untouched. -/
private lemma forest_delete_edge_components {F : MGraph} (hF : F.IsForest) {e : ℕ} (he : e ∈ F.E) :
    let F' := F.applyUpdate (.delete e)
    let a := F.tail e
    let b := F.head e
    F'.V = F.V ∧ F'.E = F.E.erase e ∧
    ¬ F'.Connected a b ∧
    (∀ v ∈ F.V, (F'.Connected v a ∨ F'.Connected v b) ↔ F.Connected v a) ∧
    (∀ v ∈ F.V, ¬ F'.Connected v a → ¬ F'.Connected v b →
      ∀ w ∈ F.V, F'.Connected v w ↔ F.Connected v w) ∧
    (∀ v ∈ F.V, ∀ w ∈ F.V, (F'.Connected v a ∨ F'.Connected v b) →
      ¬ F'.Connected w a → ¬ F'.Connected w b → ¬ F'.Connected v w) := by
  intro F' a b
  have hF'_eq : F' = { F with E := F.E \ {e} } := by
    dsimp only [F', MGraph.applyUpdate]
    congr 1; ext x; simp [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]; tauto
  have hsubF : F.IsSubgraph F' := ⟨Finset.Subset.refl _, Finset.erase_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩
  have hab : F.Connected a b := ⟨[(e, true)], .cons he rfl (.nil b)⟩
  have hne_ab : a ≠ b := by
    intro hEq
    have hcy : F.IsWalk a a [(e, true)] := .cons he rfl (show F.IsWalk b a [] from hEq ▸ .nil a)
    exact hF.2 [(e, true)] ⟨by simp, by simp, a, hcy⟩
  have hfp_ab : F.forestPath a b = [(e, true)] := by
    have hP : F.IsPath a b [(e, true)] :=
      ⟨.cons he rfl (.nil b), by simp [MGraph.walkVertices, MGraph.dst]; exact hne_ab⟩
    exact forestPath_eq_of_isPath hF hP
  have hnot_ab : ¬ F'.Connected a b := by
    rw [hF'_eq, connected_sdiff_iff_disjoint hF hab, hfp_ab]
    simp [walkEdges]
  have hpart : ∀ v ∈ F.V, (F'.Connected v a ∨ F'.Connected v b) ↔ F.Connected v a := by
    intro v _
    constructor
    · rintro (hva | hvb)
      · exact ⟨_, (isWalk_of_subgraph hsubF hva.choose_spec).1⟩
      · have hvbF : F.Connected v b := ⟨_, (isWalk_of_subgraph hsubF hvb.choose_spec).1⟩
        exact connected_trans hvbF (connected_symm hab)
    · intro hva
      by_cases he_on : e ∈ walkEdges (F.forestPath v a)
      · right
        have hvb : F.Connected v b := connected_trans hva hab
        rw [hF'_eq, connected_sdiff_iff_disjoint hF hvb, Finset.disjoint_singleton_right]
        intro he_vb
        have hPa := forestPath_isPath hF hva
        have hPb := forestPath_isPath hF hvb
        have hb_on_Pa : b ∈ F.walkVertices v (F.forestPath v a) := by
          obtain ⟨x, hxP, hxEq⟩ := List.mem_map.mp (List.mem_toFinset.mp he_on)
          have h1 := (isWalk_mem_endpoints_walkVertices hPa.1 x hxP).2
          rwa [hxEq] at h1
        have hsplit := forestPath_mem_walkVertices_split hF hva hb_on_Pa
        have hfp_ba : F.forestPath b a = [(e, false)] :=
          forestPath_eq_of_isPath hF
            ⟨.cons he rfl (.nil a), by simp [MGraph.walkVertices, MGraph.dst]; exact hne_ab.symm⟩
        have ha_in_Pb : a ∈ F.walkVertices v (F.forestPath v b) := by
          obtain ⟨x, hxP, hxEq⟩ := List.mem_map.mp (List.mem_toFinset.mp he_vb)
          have h1 := (isWalk_mem_endpoints_walkVertices hPb.1 x hxP).1
          rwa [hxEq] at h1
        have hnd := hPa.2
        rw [hsplit.1, hfp_ba, walkVertices_append] at hnd
        simp only [List.map_cons, List.map_nil, MGraph.dst, List.nodup_append] at hnd
        exact hnd.2.2 a ha_in_Pb a List.mem_cons_self rfl
      · left
        rw [hF'_eq, connected_sdiff_iff_disjoint hF hva, Finset.disjoint_singleton_right]
        exact he_on
  have hother : ∀ v ∈ F.V, ¬ F'.Connected v a → ¬ F'.Connected v b →
      ∀ w ∈ F.V, F'.Connected v w ↔ F.Connected v w := by
    intro v hv hna hnb w _
    have hnot_va : ¬ F.Connected v a := fun h => ((hpart v hv).mpr h).elim hna hnb
    constructor
    · intro hvw'
      exact ⟨_, (isWalk_of_subgraph hsubF hvw'.choose_spec).1⟩
    · intro hvw
      rw [hF'_eq, connected_sdiff_iff_disjoint hF hvw, Finset.disjoint_singleton_right]
      intro he_on
      have hP := forestPath_isPath hF hvw
      exact hnot_va (connected_trans hvw (connected_symm (isWalk_mem_walkEdges_connected hP.1 he_on).1))
  have hdisj : ∀ v ∈ F.V, ∀ w ∈ F.V, (F'.Connected v a ∨ F'.Connected v b) →
      ¬ F'.Connected w a → ¬ F'.Connected w b → ¬ F'.Connected v w := by
    intro v _ w _ hvAB hna hnb hvw
    rcases hvAB with hva | hvb
    · exact hna (connected_trans (connected_symm hvw) hva)
    · exact hnb (connected_trans (connected_symm hvw) hvb)
  exact ⟨rfl, rfl, hnot_ab, hpart, hother, hdisj⟩

open Classical in
/-- Single-step mathematical correctness of inserting `z ∈ S.T₀.V \ S.R_orig` whose `T_H`-parent `p`
is already in `S.R_orig`. Proves that `S' = { S with R₀_base := insert z S.R₀_base }` adds only `z`
to `S.R_orig`, deletes the unique edge `cutE = minEdgeOn S.π (walkEdges (S.T₀.forestPath z (S.origVert rC)))`
from `S.RF.F`, and splits `rC`'s component into the two components of `cutE`'s endpoints. -/
lemma addOrigRoot_single_step {S : LSFState} (I : LSFStructInv S)
    {z p rC : ℕ} (hzT : z ∈ S.T₀.V) (hz_not : z ∉ S.R_orig) (hpR : p ∈ S.R_orig)
    (hanc_iff : ∀ w, IsAncestor S.TH S.r₀ w z ↔ w = z ∨ IsAncestor S.TH S.r₀ w p)
    (hrC : rC ∈ S.R) (hconn_zrC : S.RF.F.Connected z rC) :
    let S' : LSFState := { S with R₀_base := insert z S.R₀_base }
    let rOrig := S.origVert rC
    let cutE := minEdgeOn S.π (walkEdges (S.T₀.forestPath z rOrig))
    S'.R_orig = insert z S.R_orig ∧
    z ∉ S.R ∧
    S'.R = insert z S.R ∧
    LSFStructInv S' ∧
    rOrig ∈ S.R_orig ∧
    z ≠ rOrig ∧
    (IsAncestor S.T₀ S.r₀ rOrig z ∨ IsAncestor S.T₀ S.r₀ z rOrig) ∧
    cutE ∈ S.RF.F.E ∧
    S'.RF.F = S.RF.F.applyUpdate (.delete cutE) ∧
    S.RF.F.tail cutE ∈ S'.RF.F.V ∧ S.RF.F.head cutE ∈ S'.RF.F.V ∧
    ¬ S'.RF.F.Connected (S.RF.F.tail cutE) (S.RF.F.head cutE) ∧
    (∀ v ∈ S'.RF.F.V,
      (S'.RF.F.Connected v (S.RF.F.tail cutE) ∨ S'.RF.F.Connected v (S.RF.F.head cutE)) ↔
      (v = z ∨ (v ∈ S.RF.F.V ∧ S.RF.F.Connected v rC))) ∧
    (∀ v ∈ S'.RF.F.V, ¬ S'.RF.F.Connected v (S.RF.F.tail cutE) →
      ¬ S'.RF.F.Connected v (S.RF.F.head cutE) →
      v ∈ S.RF.F.V ∧ ∀ w ∈ S.RF.F.V, S'.RF.F.Connected v w ↔ S.RF.F.Connected v w) ∧
    (∀ v ∈ S'.RF.F.V, ∀ w ∈ S'.RF.F.V,
      (S'.RF.F.Connected v (S.RF.F.tail cutE) ∨ S'.RF.F.Connected v (S.RF.F.head cutE)) →
      ¬ S'.RF.F.Connected w (S.RF.F.tail cutE) → ¬ S'.RF.F.Connected w (S.RF.F.head cutE) →
      ¬ S'.RF.F.Connected v w) ∧
    ((S'.RF.F.Connected rC (S.RF.F.tail cutE) ∧ S'.RF.F.Connected z (S.RF.F.head cutE)) ∨
     (S'.RF.F.Connected rC (S.RF.F.head cutE) ∧ S'.RF.F.Connected z (S.RF.F.tail cutE))) := by
  intro S' rOrig cutE
  have hTH : IsRootedTree S.TH S.r₀ := hldAuxTree_isRootedTree I.hT₀
  have hRorig' : S'.R_orig = insert z S.R_orig := by
    ext w
    rw [Finset.mem_insert]
    change w ∈ upClosure S.TH S.r₀ (insert z S.R₀_base) ↔ w = z ∨ w ∈ S.R_orig
    rw [mem_upClosure_iff]
    constructor
    · rintro ⟨u, hu, hwu⟩
      rw [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · rcases (hanc_iff w).mp hwu with rfl | hwp
        · exact Or.inl rfl
        · exact Or.inr (upClosure_isUpwardClosed hTH I.hR₀_sub hpR hwp)
      · exact Or.inr (mem_upClosure_iff.mpr ⟨u, hu, hwu⟩)
    · rintro (h | hw)
      · rw [h]; exact ⟨z, Finset.mem_insert_self _ _, isAncestor_refl S.TH S.r₀ z⟩
      · obtain ⟨u, hu, hwu⟩ := mem_upClosure_iff.mp hw
        exact ⟨u, Finset.mem_insert_of_mem hu, hwu⟩
  have hz_not_R : z ∉ S.R := by
    rw [LSFState.R, Finset.mem_union]
    rintro (h1 | h2)
    · exact hz_not h1
    · exact Finset.disjoint_left.mp I.hdisj_iso hzT h2
  have hR' : S'.R = insert z S.R := by
    simp only [LSFState.R, hRorig', Finset.insert_union]; rfl
  have I' : LSFStructInv S' := (I.addOrigRoot_inv hzT).1
  have hrOrig_eq : rOrig = (rootedForestGivenRoots S.T₀ S.r₀ S.R_orig S.π).root z :=
    I.origVert_root_eq hzT hrC hconn_zrC
  have hRS := forestGivenRoots_isRootedSpanningForest I.hT₀ I.R_orig_bf ⟨S.r₀, I.r₀_mem_R_orig⟩ S.π
  have hroot_spec := rootedForest_root_spec hRS hzT
  rw [← hrOrig_eq] at hroot_spec
  have hrOrig_R : rOrig ∈ S.R_orig := hroot_spec.1
  have hconn_orig : (forestGivenRoots S.T₀ S.r₀ S.R_orig S.π).Connected z rOrig := hroot_spec.2
  have hz_ne_rOrig : z ≠ rOrig := fun h => hz_not (h ▸ hrOrig_R)
  have hrOrig_T : rOrig ∈ S.T₀.V := I.R_orig_sub hrOrig_R
  have hRorig'_bf : IsBranchFree S.T₀ S.r₀ (insert z S.R_orig) := hRorig' ▸ I'.R_orig_bf
  -- Ancestor trichotomy between `z` and `rOrig` via branch-freeness of `insert z S.R_orig`
  have hanc_or : IsAncestor S.T₀ S.r₀ rOrig z ∨ IsAncestor S.T₀ S.r₀ z rOrig := by
    set l := lca S.T₀ S.r₀ z rOrig
    have hl_R' : l ∈ insert z S.R_orig :=
      hRorig'_bf.2 z (Finset.mem_insert_self _ _) rOrig (Finset.mem_insert_of_mem hrOrig_R)
    rw [Finset.mem_insert] at hl_R'
    rcases hl_R' with hlz | hlR
    · right
      exact hlz ▸ lca_isAncestor_right I.hT₀ hzT hrOrig_T
    · left
      have hl_on : l ∈ S.T₀.walkVertices z (S.T₀.forestPath z rOrig) :=
        lca_mem_forestPath I.hT₀ hzT hrOrig_T
      have hdisj := (connected_sdiff_iff_disjoint I.hT₀.isForest (I.hT₀.connected hzT hrOrig_T)).mp hconn_orig
      have hsplit := forestPath_mem_walkVertices_split I.hT₀.isForest (I.hT₀.connected hzT hrOrig_T) hl_on
      have hconn_lr : (forestGivenRoots S.T₀ S.r₀ S.R_orig S.π).Connected l rOrig := by
        rw [forestGivenRoots, connected_sdiff_iff_disjoint I.hT₀.isForest (I.hT₀.connected (I.R_orig_sub hlR) hrOrig_T)]
        have hsub_e : walkEdges (S.T₀.forestPath l rOrig) ⊆ walkEdges (S.T₀.forestPath z rOrig) := by
          rw [hsplit.1, walkEdges_append]; exact Finset.subset_union_right
        exact Finset.disjoint_of_subset_left hsub_e hdisj
      have hl_eq : l = rOrig := by
        by_contra hne
        exact forestGivenRoots_not_connected_roots I.hT₀ I.R_orig_bf ⟨S.r₀, I.r₀_mem_R_orig⟩ S.π
          hlR hrOrig_R hne hconn_lr
      exact hl_eq ▸ lca_isAncestor_left I.hT₀ hzT hrOrig_T
  -- Prove `deletedEdges S.T₀ S.r₀ (insert z S.R_orig) S.π = insert cutE (deletedEdges S.T₀ S.r₀ S.R_orig S.π)`
  have hno_mid_root : ∀ w ∈ insert z S.R_orig,
      w ∈ S.T₀.walkVertices z (S.T₀.forestPath z rOrig) → w = z ∨ w = rOrig := by
    intro w hwR' hw_on
    rw [Finset.mem_insert] at hwR'
    rcases hwR' with rfl | hwR
    · exact Or.inl rfl
    · right
      have hdisj := (connected_sdiff_iff_disjoint I.hT₀.isForest (I.hT₀.connected hzT hrOrig_T)).mp hconn_orig
      have hsplit := forestPath_mem_walkVertices_split I.hT₀.isForest (I.hT₀.connected hzT hrOrig_T) hw_on
      have hconn_wr : (forestGivenRoots S.T₀ S.r₀ S.R_orig S.π).Connected w rOrig := by
        rw [forestGivenRoots, connected_sdiff_iff_disjoint I.hT₀.isForest (I.hT₀.connected (I.R_orig_sub hwR) hrOrig_T)]
        have hsub_e : walkEdges (S.T₀.forestPath w rOrig) ⊆ walkEdges (S.T₀.forestPath z rOrig) := by
          rw [hsplit.1, walkEdges_append]; exact Finset.subset_union_right
        exact Finset.disjoint_of_subset_left hsub_e hdisj
      by_contra hne
      exact forestGivenRoots_not_connected_roots I.hT₀ I.R_orig_bf ⟨S.r₀, I.r₀_mem_R_orig⟩ S.π
        hwR hrOrig_R hne hconn_wr
  have hcut_in_del' : cutE ∈ deletedEdges S.T₀ S.r₀ (insert z S.R_orig) S.π := by
    have hR'ne : (insert z S.R_orig).Nonempty := ⟨z, Finset.mem_insert_self _ _⟩
    unfold deletedEdges
    rw [ite_eq_left hR'ne, Finset.mem_image]
    rcases hanc_or with hrz | hzr
    · have hz_ne_top : z ≠ topRoot S.T₀ S.r₀ (insert z S.R_orig) := by
        intro hEq
        have hanc_zr : IsAncestor S.T₀ S.r₀ z rOrig := by
          rw [hEq]; exact topRoot_isAncestor I.hT₀ hRorig'_bf hR'ne (Finset.mem_insert_of_mem hrOrig_R)
        exact hz_ne_rOrig (isAncestor_antisymm I.hT₀ hzT hrOrig_T hanc_zr hrz)
      have hz_er : z ∈ (insert z S.R_orig).erase (topRoot S.T₀ S.r₀ (insert z S.R_orig)) :=
        Finset.mem_erase.mpr ⟨hz_ne_top, Finset.mem_insert_self _ _⟩
      obtain ⟨hpR', hp_ne, hanc_pz, hmax⟩ := rootParent_spec I.hT₀ hRorig'_bf hR'ne hz_er
      have hr_anc_p : IsAncestor S.T₀ S.r₀ rOrig (rootParent S.T₀ S.r₀ (insert z S.R_orig) z) :=
        hmax rOrig (Finset.mem_insert_of_mem hrOrig_R) hz_ne_rOrig.symm hrz
      have hp_on : rootParent S.T₀ S.r₀ (insert z S.R_orig) z ∈ S.T₀.walkVertices z (S.T₀.forestPath z rOrig) :=
        (mem_walkVertices_ancestorPath_iff I.hT₀ hzT hrz).mpr ⟨hr_anc_p, hanc_pz⟩
      have hp_eq : rootParent S.T₀ S.r₀ (insert z S.R_orig) z = rOrig :=
        (hno_mid_root _ hpR' hp_on).resolve_left hp_ne
      exact ⟨z, hz_er, by unfold deletedEdge; rw [hp_eq]⟩
    · have hr_ne_top : rOrig ≠ topRoot S.T₀ S.r₀ (insert z S.R_orig) := by
        intro hEq
        have hanc_rz : IsAncestor S.T₀ S.r₀ rOrig z := by
          rw [hEq]; exact topRoot_isAncestor I.hT₀ hRorig'_bf hR'ne (Finset.mem_insert_self _ _)
        exact hz_ne_rOrig.symm (isAncestor_antisymm I.hT₀ hrOrig_T hzT hanc_rz hzr)
      have hr_er : rOrig ∈ (insert z S.R_orig).erase (topRoot S.T₀ S.r₀ (insert z S.R_orig)) :=
        Finset.mem_erase.mpr ⟨hr_ne_top, Finset.mem_insert_of_mem hrOrig_R⟩
      obtain ⟨hpR', hp_ne, hanc_pr, hmax⟩ := rootParent_spec I.hT₀ hRorig'_bf hR'ne hr_er
      have hz_anc_p : IsAncestor S.T₀ S.r₀ z (rootParent S.T₀ S.r₀ (insert z S.R_orig) rOrig) :=
        hmax z (Finset.mem_insert_self _ _) hz_ne_rOrig hzr
      have hp_on_rz : rootParent S.T₀ S.r₀ (insert z S.R_orig) rOrig ∈
          S.T₀.walkVertices rOrig (S.T₀.forestPath rOrig z) :=
        (mem_walkVertices_ancestorPath_iff I.hT₀ hrOrig_T hzr).mpr ⟨hz_anc_p, hanc_pr⟩
      have hp_on_zr : rootParent S.T₀ S.r₀ (insert z S.R_orig) rOrig ∈
          S.T₀.walkVertices z (S.T₀.forestPath z rOrig) := by
        have hP := forestPath_isPath I.hT₀.isForest (I.hT₀.connected hrOrig_T hzT)
        rw [forestPath_rev I.hT₀.isForest (I.hT₀.connected hrOrig_T hzT),
          walkVertices_walkRev hP.1, List.mem_reverse]
        exact hp_on_rz
      have hp_eq : rootParent S.T₀ S.r₀ (insert z S.R_orig) rOrig = z :=
        (hno_mid_root _ hpR' hp_on_zr).resolve_right hp_ne
      refine ⟨rOrig, hr_er, ?_⟩
      unfold deletedEdge
      rw [hp_eq]
      congr 1
      rw [forestPath_rev I.hT₀.isForest (I.hT₀.connected hrOrig_T hzT), walkEdges_walkRev]
  have hwalk_ne : (walkEdges (S.T₀.forestPath z rOrig)).Nonempty := by
    have hP := forestPath_isPath I.hT₀.isForest (I.hT₀.connected hzT hrOrig_T)
    have hne_nil : S.T₀.forestPath z rOrig ≠ [] := by
      intro h; rw [h] at hP
      have hw := hP.1
      generalize h1 : (rOrig : ℕ) = y at hw
      cases hw; exact hz_ne_rOrig h1.symm
    obtain ⟨a, tl, hEq⟩ := List.exists_cons_of_ne_nil hne_nil
    exact ⟨a.1, by rw [hEq, walkEdges_cons]; exact Finset.mem_insert_self _ _⟩
  have hcut_in_walk : cutE ∈ walkEdges (S.T₀.forestPath z rOrig) := minEdgeOn_mem hwalk_ne
  have hcut_in_T₀ : cutE ∈ S.T₀.E := walkEdges_forestPath_sub_edges I.hT₀.isForest hcut_in_walk
  have hcut_not_del : cutE ∉ deletedEdges S.T₀ S.r₀ S.R_orig S.π := by
    have hdisj := (connected_sdiff_iff_disjoint I.hT₀.isForest (I.hT₀.connected hzT hrOrig_T)).mp hconn_orig
    exact Finset.disjoint_left.mp hdisj hcut_in_walk
  have hcut_mem : cutE ∈ S.RF.F.E := Finset.mem_sdiff.mpr ⟨hcut_in_T₀, hcut_not_del⟩
  have hdel'_eq : deletedEdges S.T₀ S.r₀ (insert z S.R_orig) S.π =
      insert cutE (deletedEdges S.T₀ S.r₀ S.R_orig S.π) := by
    have hmono := deletedEdges_mono I.hT₀ I.R_orig_bf hRorig'_bf ⟨S.r₀, I.r₀_mem_R_orig⟩
      (Finset.subset_insert z S.R_orig) S.π I.hord
    have hsub : insert cutE (deletedEdges S.T₀ S.r₀ S.R_orig S.π) ⊆
        deletedEdges S.T₀ S.r₀ (insert z S.R_orig) S.π :=
      Finset.insert_subset_iff.mpr ⟨hcut_in_del', hmono⟩
    have hc1 := deletedEdges_card I.hT₀ I.R_orig_bf ⟨S.r₀, I.r₀_mem_R_orig⟩ S.π
    have hc2 := deletedEdges_card I.hT₀ hRorig'_bf ⟨z, Finset.mem_insert_self _ _⟩ S.π
    have hc3 := Finset.card_insert_of_notMem hz_not
    have hc4 := Finset.card_insert_of_notMem hcut_not_del
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hF'_eq : S'.RF.F = S.RF.F.applyUpdate (.delete cutE) := by
    have hE_eq : S'.RF.F.E = (S.RF.F.applyUpdate (.delete cutE)).E := by
      change S.T₀.E \ deletedEdges S.T₀ S.r₀ S'.R_orig S.π =
        (S.T₀.E \ deletedEdges S.T₀ S.r₀ S.R_orig S.π).erase cutE
      rw [hRorig', hdel'_eq, Finset.sdiff_insert]
    have hmk : ∀ (A B : MGraph), A.V = B.V → A.E = B.E → A.tail = B.tail → A.head = B.head → A = B := by
      rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ rfl rfl rfl rfl; rfl
    exact hmk _ _ rfl hE_eq rfl rfl
  have hF_forest : S.RF.F.IsForest := I.to_RF_spanning.1
  have hF_del := forest_delete_edge_components hF_forest hcut_mem
  rw [← hF'_eq] at hF_del
  obtain ⟨hV'_eq, _, hnot_ab, hpart_a, hother_a, hdisj_a⟩ := hF_del
  have hcut_on_F : cutE ∈ walkEdges (S.RF.F.forestPath z rC) := by
    have hP := forestPath_isPath hF_forest hconn_zrC
    have hW_T₀ : S.T₀.IsWalk z rOrig (S.RF.F.forestPath z rC) := by
      have hproj := proj_isWalk (H := S.RF.F) (K := S.T₀) (proj := S.origVert)
        (fun e he => ⟨Finset.sdiff_subset he, I.horig_T e (Finset.sdiff_subset he)⟩) hP.1
      rwa [I.horig_id z hzT] at hproj
    exact mem_walkEdges_forestPath_of_isWalk I.hT₀.isForest hW_T₀ hcut_in_walk
  have ha_conn_rC : S.RF.F.Connected (S.RF.F.tail cutE) rC := by
    have hP := forestPath_isPath hF_forest hconn_zrC
    exact (isWalk_mem_walkEdges_connected hP.1 hcut_on_F).1
  have haV : S.RF.F.tail cutE ∈ S'.RF.F.V := hV'_eq ▸ (hF_forest.1 cutE hcut_mem).1
  have hbV : S.RF.F.head cutE ∈ S'.RF.F.V := hV'_eq ▸ (hF_forest.1 cutE hcut_mem).2
  have hpart_V : ∀ v ∈ S'.RF.F.V,
      (S'.RF.F.Connected v (S.RF.F.tail cutE) ∨ S'.RF.F.Connected v (S.RF.F.head cutE)) ↔
      (v = z ∨ (v ∈ S.RF.F.V ∧ S.RF.F.Connected v rC)) := by
    intro v hv
    have hvF : v ∈ S.RF.F.V := hV'_eq ▸ hv
    rw [hpart_a v hvF]
    constructor
    · intro hva; exact Or.inr ⟨hvF, connected_trans hva ha_conn_rC⟩
    · rintro (rfl | ⟨_, hvr⟩)
      · exact connected_trans hconn_zrC (connected_symm ha_conn_rC)
      · exact connected_trans hvr (connected_symm ha_conn_rC)
  have hroots_sep : (S'.RF.F.Connected rC (S.RF.F.tail cutE) ∧ S'.RF.F.Connected z (S.RF.F.head cutE)) ∨
      (S'.RF.F.Connected rC (S.RF.F.head cutE) ∧ S'.RF.F.Connected z (S.RF.F.tail cutE)) := by
    have hrC_G : rC ∈ S.G.V := I.to_RF_spanning.2.2.1 hrC
    have hrC_V : rC ∈ S'.RF.F.V := hV'_eq ▸ I.RF_V_eq ▸ hrC_G
    have hz_V : z ∈ S'.RF.F.V := hV'_eq ▸ (I.RF_V_eq ▸ I.hGV_eq ▸ Finset.mem_union_left _ hzT)
    have hrC_ab := (hpart_V rC hrC_V).mpr (Or.inr ⟨hV'_eq ▸ hrC_V, connected_refl S.RF.F rC⟩)
    have hz_ab := (hpart_V z hz_V).mpr (Or.inl rfl)
    have hrC_ne_z : rC ≠ z := fun h => hz_not_R (h ▸ hrC)
    have hnot_rCz : ¬ S'.RF.F.Connected rC z := by
      intro hconn
      obtain ⟨r, _, huniq⟩ := I'.to_RF_spanning.2.2.2.1 rC hrC_G
      have h1 : rC = r := huniq rC ⟨by change rC ∈ S'.R; rw [hR']; exact Finset.mem_insert_of_mem hrC,
        connected_refl S'.RF.F rC⟩
      have h2 : z = r := huniq z ⟨by change z ∈ S'.R; rw [hR']; exact Finset.mem_insert_self _ _, hconn⟩
      exact hrC_ne_z (h1.trans h2.symm)
    rcases hrC_ab with h1 | h1 <;> rcases hz_ab with h2 | h2
    · exact absurd (connected_trans h1 (connected_symm h2)) hnot_rCz
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (connected_trans h1 (connected_symm h2)) hnot_rCz
  exact ⟨hRorig', hz_not_R, hR', I', hrOrig_R, hz_ne_rOrig, hanc_or, hcut_mem, hF'_eq,
    haV, hbV, hnot_ab, hpart_V,
    fun v hv hna hnb => ⟨hV'_eq ▸ hv, hother_a v (hV'_eq ▸ hv) hna hnb⟩,
    fun v hv w hw => hdisj_a v (hV'_eq ▸ hv) w (hV'_eq ▸ hw), hroots_sep⟩

end

end MinCostFlow.LSF.Program
