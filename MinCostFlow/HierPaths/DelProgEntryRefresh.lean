module

public import MinCostFlow.HierPaths.DelProgEntryCursors

/-!
# Chaining the Delete cursor passes

Each scan keeps the descriptors and preserves the two work lists. This lets the entry use
the same lists to refresh pair and support cursors before reporting pruned vertices.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The memory shared by the three cursor passes. -/
def DelCursorMem (x : HierConcrete) (b h wb cb : ℕ) (lost cs : List ℕ)
    (mem0 : ℕ → ℕ) (s : State) : Prop :=
  s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
    ListAt s.mem b x.encode ∧ ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧
    ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j

private theorem delCursorMem_update {x y : HierConcrete} {b h wb cb : ℕ}
    {lost cs : List ℕ} {mem0 : ℕ → ℕ} {s t : State}
    (hs : DelCursorMem x b h wb cb lost cs mem0 s)
    (hbL : b + x.encode.length ≤ wb) (hbC : b + x.encode.length ≤ cb)
    (he : y.encode.length = x.encode.length)
    (ht : t.regs 0 = b ∧ DelWorkRegs t.regs h wb cb lost.length cs.length ∧
      ListAt t.mem b y.encode ∧ ∀ j, (j < b ∨ b + x.encode.length ≤ j) → t.mem j = s.mem j) :
    DelCursorMem y b h wb cb lost cs mem0 t := by
  obtain ⟨h0, hR, hB, hf⟩ := ht
  refine ⟨h0, hR, hB, listAt_congr (fun j _ => ?_) hs.2.2.2.1,
    listAt_congr (fun j _ => ?_) hs.2.2.2.2.1, ?_⟩
  · exact (hf (wb + j) (Or.inr (by omega))).symm
  · exact (hf (cb + j) (Or.inr (by omega))).symm
  · intro j hj
    rw [he] at hj
    exact (hf j hj).trans (hs.2.2.2.2.2 j hj)

/-- Cursor state after the three entry scans. -/
def HierConcrete.delRefreshState (x : HierConcrete) (lost cs : List ℕ) : HierConcrete :=
  let y := (x.refreshPairs cs).refreshOwners lost
  y.refreshWalkVerts (y.walkPassVerts cs)

/-- The three scans preserve the size of the block. -/
theorem HierConcrete.length_encode_delRefreshState (x : HierConcrete) (lost cs : List ℕ) :
    (x.delRefreshState lost cs).encode.length = x.encode.length := by
  unfold delRefreshState
  rw [HierConcrete.length_encode_refreshWalkVerts, HierConcrete.length_encode_refreshOwners,
    HierConcrete.length_encode_refreshPairs]

/-- The costs of the three cursor scans, charging each cursor move as it occurs. -/
def delEntryCursorsCost (x : HierConcrete) (lost cs : List ℕ) : ℕ :=
  let y := x.refreshPairs cs
  let z := y.refreshOwners lost
  rangeCost (delPairPassStepCost x cs) 0 cs.length +
    rangeCost (delOwnerPassStepCost y lost) 0 lost.length +
    rangeCost (delWalkPassStepCost z cs) 0 cs.length +
    18 * cs.length + 9 * lost.length + 50

/-- Run all three cursor scans, leaving the two work lists ready for reporting. -/
theorem delEntryCursors_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b h wb cb : ℕ} {lost cs : List ℕ} {R mem0 : ℕ → ℕ}
    (h0 : R 0 = b) (h70 : R 70 = h) (h71 : R 71 = wb) (h72 : R 72 = lost.length)
    (h73 : R 73 = cb) (h34 : R 34 = cs.length)
    (hbL : b + x.encode.length ≤ wb) (hbC : b + x.encode.length ≤ cb)
    (hwl : wb + lost.length < 2 ^ w) (hwc : cb + cs.length < 2 ^ w)
    (ht : ∀ t ∈ lost, t < x.H.A.C.numTerm) (ho : ∀ t ∈ lost, x.H.A.C.owner t < x.n)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn) (hq : ∀ c ∈ cs, x.H.A.pairOf c < x.H.A.numPairs)
    (hv : ∀ c ∈ cs, ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n)
    (hNp : ∀ q < x.H.A.numPairs, (x.H.A.pairConns q).length + 1 < 2 ^ w)
    (hNs : ∀ v < x.n, (x.H.A.C.supportArray v).length + 1 < 2 ^ w)
    (hP : ∀ q, x.ms.st.pairCur q ≤ (x.H.A.pairConns q).length)
    (hS : ∀ v, x.ms.st.supCur v ≤ (x.H.A.C.supportArray v).length)
    (hIn : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    (hmem : ∀ q < x.H.A.numPairs, ∀ d ∈ x.H.A.pairConns q, d < x.H.A.C.numConn) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧ s.mem = mem0) delEntryCursors
      (normalPost (DelCursorMem (x.delRefreshState lost cs) b h wb cb lost cs mem0))
      (fun _ => delEntryCursorsCost x lost cs) := by
  let y := x.refreshPairs cs
  let z := y.refreshOwners lost
  have ey : y.encode.length = x.encode.length := x.length_encode_refreshPairs cs
  have ez : z.encode.length = y.encode.length := y.length_encode_refreshOwners lost
  obtain ⟨hY, hYL, hYI⟩ := x.refreshPairs_data cs
  obtain ⟨hZ, hZL, hZI⟩ := y.refreshOwners_data lost
  have hyN : y.n = x.n := congrArg (fun t => t.G.n) (x.refreshPairs_other cs).1
  have hzN : z.n = y.n := y.refreshOwners_n lost
  have hYsurv : y.H.A.surv y.ms.st = x.H.A.surv x.ms.st := by
    simp only [StaticArrays.surv, y, hY, hYL]
  have hZsurv : z.H.A.surv z.ms.st = y.H.A.surv y.ms.st := by
    simp only [StaticArrays.surv, z, hZ, hZL]
  have hyI : y.ms.st.inelig = (Finset.range y.H.A.C.numConn).filter fun d =>
      ¬ y.H.A.C.Eligible (y.H.A.surv y.ms.st) d := by
    rw [hYsurv, show y.H = x.H from hY, show y.ms.st.inelig = x.ms.st.inelig from hYI]
    exact hIn
  have hzI : z.ms.st.inelig = (Finset.range z.H.A.C.numConn).filter fun d =>
      ¬ z.H.A.C.Eligible (z.H.A.surv z.ms.st) d := by
    rw [hZsurv, show z.H = y.H from hZ, show z.ms.st.inelig = y.ms.st.inelig from hZI]
    exact hyI
  have hyS : ∀ v, y.ms.st.supCur v ≤ (y.H.A.C.supportArray v).length := by
    rw [show y.H = x.H from hY, show y.ms.st.supCur = x.ms.st.supCur from (x.refreshPairs_other cs).2.1]
    exact hS
  have hzS : ∀ v, z.ms.st.supCur v ≤ (z.H.A.C.supportArray v).length := by
    rw [show z.H = y.H from hZ]
    exact y.refreshOwners_cur_le lost hyS
  let M := fun m => ListAt m b x.encode ∧ ListAt m wb lost ∧ ListAt m cb cs ∧ m = mem0
  let R' := Function.update R 74 cs.length
  have A : Triple w p (fun s => s.regs = R ∧ M s.mem) (.assign 74 (.reg 34))
      (normalPost (DelCursorMem x b h wb cb lost cs mem0)) (fun _ => 2) := by
    refine (triple_assign_exact (M := M) (v := cs.length)
      (fun _ hs _ => Expr.eval_reg_of_eq (hs ▸ h34))).strengthen_post ?_
    intro o s hp
    cases o <;> try contradiction
    obtain ⟨hr, hB, hL, hC, hm⟩ := hp
    refine ⟨by simpa [hr] using h0, ⟨?_, ?_, ?_, ?_, by simp [hr]⟩, hB, hL, hC,
      fun j _ => congrFun hm j⟩
    · simpa [hr] using h70
    · simpa [hr] using h71
    · simpa [hr] using h72
    · simpa [hr] using h73
  have B : Triple w p (DelCursorMem x b h wb cb lost cs mem0)
      (.seq (delReadWorkList 73 74 49 50) delPairPass)
      (normalPost (DelCursorMem y b h wb cb lost cs mem0))
      (fun _ => rangeCost (delPairPassStepCost x cs) 0 cs.length + cs.length * 9 + 13) := by
    intro s ω hs
    have H := delEntryPairs_triple (w := w) (p := p) (R := s.regs) (mem0 := s.mem)
      (b := b) (h := h) (wb := wb) (cb := cb) (lost := lost) (cs := cs)
      x hs.1 hs.2.1 hbC hwc hc hq hNp hP hIn hmem
    obtain ⟨o, t, c, hr, hp, ht'⟩ := H s ω ⟨rfl, hs.2.2.1, hs.2.2.2.2.1, rfl⟩
    cases o <;> try contradiction
    exact ⟨_, t, c, hr, delCursorMem_update hs hbL hbC ey hp, ht'⟩
  have C : Triple w p (DelCursorMem y b h wb cb lost cs mem0)
      (.seq (delReadWorkList 71 72 49 50) delOwnerPass)
      (normalPost (DelCursorMem z b h wb cb lost cs mem0))
      (fun _ => rangeCost (delOwnerPassStepCost y lost) 0 lost.length + lost.length * 9 + 13) := by
    intro s ω hs
    have hl : b + y.encode.length ≤ wb := (congrArg (b + ·) ey).le.trans hbL
    have hcb : b + y.encode.length ≤ cb := (congrArg (b + ·) ey).le.trans hbC
    have H := delEntryOwners_triple (w := w) (p := p) (R := s.regs) (mem0 := s.mem)
      (b := b) (h := h) (wb := wb) (cb := cb) (lost := lost) (cs := cs)
      y hs.1 hs.2.1 hl hwl (by rw [show y.H = x.H from hY]; exact ht)
      (by rw [show y.H = x.H from hY, hyN]; exact ho)
      (by rw [show y.H = x.H from hY, hyN]; exact hNs) hyS hyI
    obtain ⟨o, t, c, hr, hp, ht'⟩ := H s ω ⟨rfl, hs.2.2.1, hs.2.2.2.1, rfl⟩
    cases o <;> try contradiction
    exact ⟨_, t, c, hr, delCursorMem_update hs hl hcb ez hp, ht'⟩
  have D : Triple w p (DelCursorMem z b h wb cb lost cs mem0)
      (.seq (delReadWorkList 73 74 55 56) delWalkPass)
      (normalPost (DelCursorMem (x.delRefreshState lost cs) b h wb cb lost cs mem0))
      (fun _ => rangeCost (delWalkPassStepCost z cs) 0 cs.length + cs.length * 9 + 13) := by
    intro s ω hs
    have hl : b + z.encode.length ≤ wb := (congrArg (b + ·) (ez.trans ey)).le.trans hbL
    have hcb : b + z.encode.length ≤ cb := (congrArg (b + ·) (ez.trans ey)).le.trans hbC
    have hzH : z.H = x.H := hZ.trans hY
    have hn : z.n = x.n := hzN.trans hyN
    have H := delEntryWalks_triple (w := w) (p := p) (R := s.regs) (mem0 := s.mem)
      (b := b) (h := h) (wb := wb) (cb := cb) (lost := lost) (cs := cs)
      z hs.1 hs.2.1 hcb hwc (by rw [hzH]; exact hc) (by rw [hzH, hn]; exact hv)
      (by rw [hzH, hn]; exact hNs) hzS hzI
    obtain ⟨o, t, c, hr, hp, ht'⟩ := H s ω ⟨rfl, hs.2.2.1, hs.2.2.2.2.1, rfl⟩
    cases o <;> try contradiction
    exact ⟨_, t, c, hr, delCursorMem_update hs hl hcb (z.length_encode_refreshWalkVerts _) hp, ht'⟩
  unfold delEntryCursors
  refine (Triple.seq_normal_const A (Triple.seq_normal_const B
    (Triple.seq_normal_const C D))).mono_cost ?_
  intro s hs
  unfold delEntryCursorsCost
  dsimp only [y, z]
  omega

end MinCostFlow.HierPaths

end
