module

public import MinCostFlow.HierPaths.DelProgEntryOutput

/-!
# Chaining the Delete entry through the cursor scans

The first stage produces the lost terminals. The next stage produces the ineligible
connectors. The cursor scans preserve both lists and leave the post-delete cursor state.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The entry through the cursor scans, before reporting the result. -/
def delEntryWork : Stmt := .seq delEntryStart (.seq delEntryConns delEntryCursors)

theorem delEntryWork_noRand : delEntryWork.NoRand := by
  simp [delEntryWork, Stmt.NoRand, delEntryStart_noRand, delEntryConns_noRand, delEntryCursors_noRand]

/-- Address and cursor bounds used by the work-list stages. -/
structure DelEntryWorkBounds (x : HierConcrete) (e h w : ℕ) : Prop where
  deletedWord : x.ms.st.deleted.card + 1 < 2 ^ w
  depthBranchWord : (x.depth - 1) * x.H.A.b < 2 ^ w
  depthWord : x.depth < 2 ^ w
  portsWord : 4 * 2 ^ x.H.A.x < 2 ^ w
  lossSpace : delLostBase h x.n + 2 * 2 ^ x.H.A.x < 2 ^ w
  connSpace : delLostBase h x.n + (x.H.A.newLost x.ms.st e).length +
    ((x.H.A.newLost x.ms.st e).flatMap x.H.A.termConns).length < 2 ^ w
  pairWord : ∀ q < x.H.A.numPairs, (x.H.A.pairConns q).length + 1 < 2 ^ w
  supportWord : ∀ v < x.n, (x.H.A.C.supportArray v).length + 1 < 2 ^ w
  pairCur : ∀ q, x.ms.st.pairCur q ≤ (x.H.A.pairConns q).length
  supCur : ∀ v, x.ms.st.supCur v ≤ (x.H.A.C.supportArray v).length

/-- Cost of marking, handling losses and refreshing the cursors. -/
def delEntryWorkCost (x : HierConcrete) (e : ℕ) : ℕ :=
  let lost := x.H.A.newLost x.ms.st e
  delEntryStartCost x e + (99 * (lost.flatMap x.H.A.termConns).length + 104 * lost.length + 30) +
    delEntryCursorsCost (x.afterDelConns e) lost (x.delWorkConns e) + 2

/-- Only the block and the two work-list intervals can change before the output pass. -/
theorem delEntryWork_triple {w a : ℕ} {p : Program} (x : HierConcrete) {b e h : ℕ}
    {R mem0 : ℕ → ℕ} (h0 : R 0 = b) (h1 : R 1 = e) (h2 : R 2 = h)
    (he : e < x.m) (hnew : e ∉ x.ms.st.deleted)
    (hrel : x.H.Rel a x.ms) (hG : x.ms.abs.G.IsValid)
    (hb : b + x.encode.length ≤ h) (hw : DelEntryWorkBounds x e h w) :
    let lost := x.H.A.newLost x.ms.st e
    let cs := x.delWorkConns e
    let wb := delLostBase h x.n
    let cb := wb + lost.length
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delEntryWork
      (normalPost fun s => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.afterDelCursors e).encode ∧ ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < wb ∨ wb + lost.length ≤ j) → (j < cb ∨ cb + cs.length ≤ j) → s.mem j = mem0 j)
      (fun _ => delEntryWorkCost x e) := by
  dsimp only
  let A := x.H.A
  let y := x.afterDelLoss e
  let z := x.afterDelConns e
  let lost := A.newLost x.ms.st e
  let cs := x.delWorkConns e
  let wb := delLostBase h x.n
  let cb := wb + lost.length
  have hwb : h ≤ wb := by unfold wb delLostBase; omega
  have hB : b + x.encode.length ≤ wb := hb.trans hwb
  have ht : ∀ t ∈ lost, t < A.C.numTerm := by
    intro t ht
    exact ((A.mem_surv).mp ((A.mem_newLost_iff hrel.spec.arrays hrel.inv e t).mp ht).1).1
  have hc : ∀ c ∈ cs, c < A.C.numConn := by
    intro c hc
    have hm := (mem_delCollect.mp hc).1
    obtain ⟨t, ht', htc⟩ := List.mem_flatMap.mp hm
    exact ((hrel.spec.arrays.mem_termConns t (ht t ht') c).mp htc).1
  have hout : cs.length ≤ (lost.flatMap A.termConns).length := delCollect_length_le ..
  have hwl : wb + lost.length < 2 ^ w := by
    have h := hw.connSpace
    change wb + lost.length + (lost.flatMap A.termConns).length < 2 ^ w at h
    omega
  have hwc : cb + cs.length < 2 ^ w := by
    have h := hw.connSpace
    change cb + (lost.flatMap A.termConns).length < 2 ^ w at h
    omega
  have hz : z.encode.length = x.encode.length := by
    unfold z HierConcrete.afterDelConns
    rw [HierConcrete.length_encode_markIneligList]
    exact x.length_encode_afterDelLoss hnew
  let P := fun s : State => s.regs 0 = b ∧ s.regs 70 = h ∧ s.regs 71 = wb ∧
    s.regs 23 = lost.length ∧ ListAt s.mem b y.encode ∧ ListAt s.mem wb lost ∧
    ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
      (j < wb ∨ wb + lost.length ≤ j) → s.mem j = mem0 j
  let Q := fun s : State => s.regs 0 = b ∧ s.regs 70 = h ∧ s.regs 71 = wb ∧
    s.regs 72 = lost.length ∧ s.regs 73 = cb ∧ s.regs 34 = cs.length ∧
    ListAt s.mem b z.encode ∧ ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧
    ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
      (j < wb ∨ wb + lost.length ≤ j) → (j < cb ∨ cb + cs.length ≤ j) → s.mem j = mem0 j
  have Start := delEntryStart_triple (w := w) (p := p) (mem0 := mem0) x h0 h1 h2 he hnew
    hrel.spec.arrays hrel.inv hb hw.deletedWord hw.depthBranchWord hw.depthWord hw.portsWord hw.lossSpace
  have Conns : Triple w p P delEntryConns (normalPost Q)
      (fun _ => 99 * (lost.flatMap x.H.A.termConns).length + 104 * lost.length + 30) := by
    intro s ω hs
    obtain ⟨r0, r70, r71, r23, hblock, hlist, hf⟩ := hs
    have H := delEntryConns_triple (w := w) (p := p) (R := s.regs) (mem0 := s.mem)
      x r0 r70 r71 r23 hnew hB hrel.spec.arrays ht hw.connSpace
    obtain ⟨o, t, c, hr, hp, hcost⟩ := H s ω ⟨rfl, hblock, hlist, rfl⟩
    cases o <;> try contradiction
    obtain ⟨r0', r70', r71', r72', r73', r34', hblock', hlist', hcs, hf'⟩ := hp
    exact ⟨_, t, c, hr, ⟨r0', r70', r71', r72', r73', r34', hblock', hlist', hcs,
      fun j hj hl hcn => (hf' j hj hcn).trans (hf j hj hl)⟩, hcost⟩
  have Cursors : Triple w p Q delEntryCursors
      (normalPost fun s => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.afterDelCursors e).encode ∧ ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < wb ∨ wb + lost.length ≤ j) → (j < cb ∨ cb + cs.length ≤ j) → s.mem j = mem0 j)
      (fun _ => delEntryCursorsCost z lost cs) := by
    intro s ω hs
    obtain ⟨r0, r70, r71, r72, r73, r34, hblock, hlist, hcs, hf⟩ := hs
    have hzL : b + z.encode.length ≤ wb := (congrArg (b + ·) hz).le.trans hB
    have hzC : b + z.encode.length ≤ cb := hzL.trans (Nat.le_add_right ..)
    have H := delEntryCursors_triple (w := w) (p := p) (R := s.regs) (mem0 := s.mem)
      (lost := lost) (cs := cs) z r0 r70 r71 r72 r73 r34 hzL hzC hwl hwc ht
      (fun t ht' => hrel.spec.arrays.fits.1 t (ht t ht')) hc
      (fun c hc' => hrel.spec.arrays.pairOf_lt c (hc c hc'))
      (fun c hc' v hv => MinCostFlow.Spanner.Walk.isWalk_verts_lt hG
        (hrel.spec.arrays.fits.2 c (hc c hc')).2.2 v hv)
      hw.pairWord hw.supportWord hw.pairCur hw.supCur
      (delConnectorPass_inelig x hrel.spec.arrays hrel.inv)
      (fun q _ d hd => (hrel.spec.arrays.mem_pairConns q d hd).1)
    obtain ⟨o, t, c, hr, hp, hcost⟩ := H s ω ⟨rfl, hblock, hlist, hcs, rfl⟩
    cases o <;> try contradiction
    obtain ⟨r0', hregs, hblock', hlist', hcs', hf'⟩ := hp
    have hz' : (z.delRefreshState lost cs).encode.length = x.encode.length :=
      (z.length_encode_delRefreshState lost cs).trans hz
    have heq : z.delRefreshState lost cs = x.afterDelCursors e := x.afterDelCursors_eq e
    rw [hz'] at hf'
    exact ⟨_, t, c, hr, ⟨r0', hregs, heq ▸ hblock', hlist', hcs',
      fun j hj hl hcn => (hf' j hj).trans (hf j hj hl hcn)⟩, hcost⟩
  unfold delEntryWork
  refine (Triple.seq_normal_const Start (Triple.seq_normal_const Conns Cursors)).mono_cost ?_
  intro s _
  let start :=  delEntryStartCost x e
  let conns :=  99 * (lost.flatMap x.H.A.termConns).length + 104 * lost.length + 30
  let C := delEntryCursorsCost z lost cs
  change start + (conns + C + 1) + 1 ≤ start + conns + C + 2
  omega

end MinCostFlow.HierPaths

end
