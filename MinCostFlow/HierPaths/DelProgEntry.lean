module

public import MinCostFlow.HierPaths.DelProgEntryWork

/-!
# The Delete procedure

The entry runs the loss and connector passes, refreshes cursors, reports newly pruned
vertices and clears scratch. The run theorem identifies the encoded state and output.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The deterministic program for operation 0. -/
def hierDeleteEntry : Stmt := .seq delEntryWork (.seq delEntryReports delFinish)

theorem hierDeleteEntry_noRand : hierDeleteEntry.NoRand := by
  simp [hierDeleteEntry, Stmt.NoRand, delEntryWork_noRand, delEntryReports_noRand, delFinish_noRand]

/-- Cost of the whole procedure before converting its event charges to an amortized bound. -/
def hierDeleteEntryCost (x : HierConcrete) (e : ℕ) : ℕ :=
  let lost := x.H.A.newLost x.ms.st e
  let cs := x.delWorkConns e
  delEntryWorkCost x e + delEntryReportsCost (x.afterDelCursors e) lost cs +
    12 * (lost.length + cs.length) + 57

/-- The full Delete run, with explicit bounds for the word arithmetic and scratch intervals. -/
theorem hierDeleteEntry_triple {w a : ℕ} {p : Program} (x : HierConcrete) {b e h : ℕ}
    {R mem0 : ℕ → ℕ} (h0 : R 0 = b) (h1 : R 1 = e) (h2 : R 2 = h)
    (he : e < x.m) (hnew : e ∉ x.ms.st.deleted)
    (hrel : x.H.Rel a x.ms) (hG : x.ms.abs.G.IsValid)
    (hb : b + x.encode.length ≤ h) (hw : DelEntryWorkBounds x e h w)
    (hOutWord : h + 1 + 3 * x.n + 1 < 2 ^ w) (hzero : ZeroFrom mem0 h) :
    let y := HierConcrete.mk x.H (x.H.delete x.ms e)
    let L := (x.afterDelCursors e).delReports (x.H.A.delSupportVisits x.ms.st e)
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      hierDeleteEntry
      (retPost fun u s => u = h + 1 + L.length ∧ ListAt s.mem b y.encode ∧
        SeqAt s.mem h L ∧ L.Nodup ∧ L.toFinset = y.ms.abs.Vhat \ x.ms.abs.Vhat ∧
        ZeroFrom s.mem u ∧
        ∀ j < h, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => hierDeleteEntryCost x e) := by
  dsimp only
  let A := x.H.A
  let lost := A.newLost x.ms.st e
  let cs := x.delWorkConns e
  let wb := delLostBase h x.n
  let cb := wb + lost.length
  let z := x.afterDelCursors e
  let y := HierConcrete.mk x.H (x.H.delete x.ms e)
  let vs := A.delSupportVisits x.ms.st e
  let L := z.delReports vs
  have hwb : h + 1 + 2 * x.n ≤ wb := by unfold wb delLostBase; omega
  have hcb : wb ≤ cb := Nat.le_add_right ..
  have hht : h ≤ wb := by omega
  have hH : z.H = x.H := x.afterDelCursors_H e
  have hAbs : z.ms.abs = (x.markDeleted e).ms.abs := x.afterDelCursors_abs e
  have hV : z.ms.abs.Vhat = x.ms.abs.Vhat := by rw [hAbs]; rfl
  have hN : z.n = x.n := congrArg (fun v => v.G.n) hAbs
  have hG' : z.ms.abs.G = x.ms.abs.G := by rw [hAbs]; rfl
  have hstate : z.afterReports vs = y :=
    x.afterDelReports_eq e hrel.spec.arrays hG hrel.inv hrel.vhat
  have henc : z.encode.length = x.encode.length := by
    let q := x.afterDelConns e
    have hq : q.encode.length = x.encode.length := by
      unfold q HierConcrete.afterDelConns
      rw [HierConcrete.length_encode_markIneligList]
      exact x.length_encode_afterDelLoss hnew
    exact (congrArg (fun t => t.encode.length) (x.afterDelCursors_eq e).symm).trans
      ((q.length_encode_delRefreshState lost cs).trans hq)
  have henc' : y.encode.length = x.encode.length := by
    rw [← hstate]
    exact (z.length_encode_withVhat _).trans henc
  have hvs : lost.map z.H.A.C.owner ++ z.walkPassVerts cs = vs := by
    rw [HierConcrete.walkPassVerts, hH]
    rfl
  have hL := z.delReports_spec (st := x.ms.st) (e := e)
    (by rw [hH, hG']; exact hrel.spec.arrays) (by rwa [hG'])
    (by rw [hH, hG']; exact hrel.inv)
    (by rw [hH]; exact (x.afterDelCursors_tables e hrel.spec.arrays hG hrel.inv).1)
    (by rw [hH, hG', hV]; exact hrel.vhat)
  have hVisits : z.H.A.delSupportVisits x.ms.st e = vs := by rw [hH]
  have hOut : L.Nodup ∧ L.toFinset = y.ms.abs.Vhat \ x.ms.abs.Vhat := by
    dsimp only at hL
    rw [hVisits, hH, hG', hV] at hL
    have hy : y.ms.abs.Vhat = A.C.prunedSet x.ms.abs.G (A.newSurv x.ms.st e) := rfl
    rw [hy]
    exact hL
  have hcap : L.length ≤ x.n := by
    rw [← hN]
    exact z.delReports_length_le (fun v hv => hN.symm ▸
      A.lt_of_mem_touchedVerts hrel.spec.arrays hG hrel.inv e ((A.mem_delSupportVisits x.ms.st e v).mp hv))
  have ht : ∀ t ∈ lost, t < A.C.numTerm := by
    intro t ht
    exact ((A.mem_surv).mp ((A.mem_newLost_iff hrel.spec.arrays hrel.inv e t).mp ht).1).1
  have hc : ∀ c ∈ cs, c < A.C.numConn := by
    intro c hm
    obtain ⟨t, ht', hct⟩ := List.mem_flatMap.mp (mem_delCollect.mp hm).1
    exact ((hrel.spec.arrays.mem_termConns t (ht t ht') c).mp hct).1
  have hwL : wb + lost.length < 2 ^ w := by
    have hp := hw.connSpace
    change wb + lost.length + (lost.flatMap A.termConns).length < 2 ^ w at hp
    omega
  have hwC : cb + cs.length < 2 ^ w := by
    have hp := hw.connSpace
    change cb + (lost.flatMap A.termConns).length < 2 ^ w at hp
    exact lt_of_le_of_lt (Nat.add_le_add_left (delCollect_length_le ..) _) hp
  let Mid := fun s : State => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
    ListAt s.mem b z.encode ∧ ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧
    ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
      (j < wb ∨ wb + lost.length ≤ j) → (j < cb ∨ cb + cs.length ≤ j) → s.mem j = mem0 j
  let Ready := fun s : State => s.regs 0 = b ∧ s.regs 59 = L.length ∧
    DelWorkRegs s.regs h wb cb lost.length cs.length ∧
    ListAt s.mem b y.encode ∧ ListAt s.mem (h + 1) L ∧
    ∀ j, (j < b ∨ b + x.encode.length ≤ j) → (j < h + 1 ∨ h + 1 + L.length ≤ j) →
      (j < wb ∨ wb + lost.length ≤ j) → (j < cb ∨ cb + cs.length ≤ j) → s.mem j = mem0 j
  have Report : Triple w p Mid delEntryReports (normalPost Ready)
      (fun _ => delEntryReportsCost z lost cs) := by
    intro s ω hs
    obtain ⟨r0, hR, hB, hL0, hC0, hf⟩ := hs
    have H := delEntryReports_triple (w := w) (p := p) (R := s.regs) (mem0 := s.mem)
      (lost := lost) (cs := cs) z r0 hR ((congrArg (b + ·) henc).le.trans hb)
      (by rwa [hN]) hcb (by rwa [hN]) hwL hwC
      (by rw [hH]; exact ht) (by rw [hH, hN]; exact fun t ht' => hrel.spec.arrays.fits.1 t (ht t ht'))
      (by rw [hH]; exact hc)
      (by
        rw [hH, hN]
        intro c hc' v hv
        exact MinCostFlow.Spanner.Walk.isWalk_verts_lt hG
          (hrel.spec.arrays.fits.2 c (hc c hc')).2.2 v hv)
    obtain ⟨o, t, c, hr, hp, hcost⟩ := H s ω ⟨rfl, hB, hL0, hC0, rfl⟩
    cases o <;> try contradiction
    obtain ⟨r0', r59, hregs, hblock, hlist, hf'⟩ := hp
    rw [hvs, hstate] at hblock
    rw [hvs] at r59 hlist hf'
    rw [henc] at hf'
    exact ⟨_, t, c, hr, ⟨r0', r59, hregs, hblock, hlist,
      fun j hj ho hl hc => (hf' j hj ho).trans (hf j hj hl hc)⟩, hcost⟩
  let Q := fun u (s : State) => u = h + 1 + L.length ∧ ListAt s.mem b y.encode ∧
    SeqAt s.mem h L ∧ L.Nodup ∧ L.toFinset = y.ms.abs.Vhat \ x.ms.abs.Vhat ∧
    ZeroFrom s.mem u ∧
    ∀ j < h, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j
  have Finish : Triple w p Ready delFinish (retPost Q)
      (fun _ => 12 * (lost.length + cs.length) + 55) := by
    intro s ω hs
    obtain ⟨_, r59, hR, hB, hL, hf⟩ := hs
    have H := delFinish_triple (w := w) (p := p) (R := s.regs) (mem0 := s.mem)
      (b := b) (L := L) (block := y.encode) hR.heap r59 hR.lostBase hR.lostCount
      hR.connBase hR.connCount ((congrArg (b + ·) henc').le.trans hb) (by omega)
      le_rfl hwC (fun j hj hL' hC' =>
        (hf j (Or.inr (by omega)) (Or.inr hj) hL' hC').trans (hzero j (by omega)))
    obtain ⟨o, t, c, hr, hp, hcost⟩ := H s ω ⟨rfl, hB, hL, rfl⟩
    cases o <;> try contradiction
    obtain ⟨hu, hblock, hseq, hz, hf'⟩ := hp
    exact ⟨_, t, c, hr, ⟨hu, hblock, hseq, hOut.1, hOut.2, hz, fun j hj hBlock =>
      (hf' j hj).trans (hf j hBlock (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))⟩, hcost⟩
  have Work := delEntryWork_triple (w := w) (p := p) (mem0 := mem0)
    x h0 h1 h2 he hnew hrel hG hb hw
  unfold hierDeleteEntry
  refine (Triple.seq_normal_const Work (Triple.seq_normal_const Report Finish)).mono_cost ?_
  intro s _
  let W := delEntryWorkCost x e
  let C := delEntryReportsCost z lost cs
  let F := 12 * (lost.length + cs.length)
  change W + (C + (F + 55) + 1) + 1 ≤ W + C + F + 57
  omega

end MinCostFlow.HierPaths

end
