module

public import MinCostFlow.HierPaths.DelProgEntryConns

/-!
# Passing the work lists to the Delete cursor loops

The entry keeps the work-list addresses and lengths in registers 71 through 74.
It copies each list descriptor into the registers of the next scan.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Copy a work-list descriptor into the registers of the next scan. -/
def delReadWorkList (src len dst count : ℕ) : Stmt :=
  .seq (.assign dst (.reg src)) (.assign count (.reg len))

theorem delReadWorkList_noRand (src len dst count : ℕ) :
    (delReadWorkList src len dst count).NoRand := by
  simp [delReadWorkList, Stmt.NoRand]

/-- Copy the list pointer and length without changing memory. -/
theorem delReadWorkList_triple {w : ℕ} {p : Program} {src len dst count base N : ℕ}
    {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop}
    (hbase : R src = base) (hN : R len = N) (hne : len ≠ dst) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) (delReadWorkList src len dst count)
      (normalPost fun s => s.regs = Function.update (Function.update R dst base) count N ∧ M s.mem)
      (fun _ => 5) := by
  exact Triple.seq_normal_const
    (triple_assign_exact fun _ hs _ => Expr.eval_reg_of_eq (hs ▸ hbase))
    (triple_assign_exact fun _ hs _ => Expr.eval_reg_of_eq
      (by rw [hs, Function.update_of_ne hne]; exact hN))

/-- Refresh pair cursors, then owner supports, then supports on the connector walks. -/
def delEntryCursors : Stmt :=
  .seq (.assign 74 (.reg 34))
    (.seq (.seq (delReadWorkList 73 74 49 50) delPairPass)
      (.seq (.seq (delReadWorkList 71 72 49 50) delOwnerPass)
        (.seq (delReadWorkList 73 74 55 56) delWalkPass)))

theorem delEntryCursors_noRand : delEntryCursors.NoRand := by
  simp [delEntryCursors, Stmt.NoRand, delReadWorkList_noRand, delPairPass_noRand,
    delOwnerPass_noRand, delWalkPass_noRand]

/-- Registers that retain the two work-list descriptors across cursor and output scans. -/
structure DelWorkRegs (R : ℕ → ℕ) (h wb cb nl nc : ℕ) : Prop where
  heap : R 70 = h
  lostBase : R 71 = wb
  lostCount : R 72 = nl
  connBase : R 73 = cb
  connCount : R 74 = nc

theorem DelWorkRegs.of_frame {R R' : ℕ → ℕ} {h wb cb nl nc : ℕ}
    (hR : DelWorkRegs R h wb cb nl nc) (hf : ∀ r, 70 ≤ r → R' r = R r) :
    DelWorkRegs R' h wb cb nl nc :=
  ⟨(hf 70 (by decide)).trans hR.heap, (hf 71 (by decide)).trans hR.lostBase,
    (hf 72 (by decide)).trans hR.lostCount, (hf 73 (by decide)).trans hR.connBase,
    (hf 74 (by decide)).trans hR.connCount⟩

private theorem delPairPass_frame : Stmt.WritesBelow 70 delPairPass := by
  simp [delPairPass, forRange, forUp, delRefreshConnPair, delPairRefresh,
    delCursorSetup, delCsrSetup, advanceStmt, pairTestStmt, delCursorStore, Stmt.WritesBelow]

/-- Copy the connector descriptor, then refresh the pair cursors and keep the work registers. -/
theorem delEntryPairs_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b h wb cb : ℕ} {lost cs : List ℕ} {R mem0 : ℕ → ℕ}
    (h0 : R 0 = b) (hR : DelWorkRegs R h wb cb lost.length cs.length)
    (hb : b + x.encode.length ≤ cb) (hw : cb + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hq : ∀ c ∈ cs, x.H.A.pairOf c < x.H.A.numPairs)
    (hN : ∀ q < x.H.A.numPairs, (x.H.A.pairConns q).length + 1 < 2 ^ w)
    (hcur : ∀ q, x.ms.st.pairCur q ≤ (x.H.A.pairConns q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    (hmem : ∀ q < x.H.A.numPairs, ∀ d ∈ x.H.A.pairConns q, d < x.H.A.C.numConn) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem cb cs ∧ s.mem = mem0) (.seq (delReadWorkList 73 74 49 50) delPairPass)
      (normalPost fun s => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.refreshPairs cs).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delPairPassStepCost x cs) 0 cs.length + cs.length * 9 + 13) := by
  let R' := Function.update (Function.update R 49 cb) 50 cs.length
  let M := fun mem => ListAt mem b x.encode ∧ ListAt mem cb cs ∧ mem = mem0
  have H := delReadWorkList_triple (w := w) (p := p) (M := M) (dst := 49) (count := 50)
    hR.connBase hR.connCount (by decide)
  have HT := delPairPass_triple (w := w) (p := p) (mem0 := mem0) (R := R') x
    (by simpa [R'] using h0) (by simp [R']) (by simp [R']) hb hw hc hq hN hcur hinel hmem
  have HF := Triple.regs_frame delPairPass_frame HT R'
  have HF' := (HF.weaken_pre (fun s (hs : s.regs = R' ∧ M s.mem) =>
    ⟨hs, fun r _ => congrFun hs.1 r⟩)).strengthen_post
      (Q' := normalPost fun s => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.refreshPairs cs).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun o s hp => by
        cases o <;> try exact False.elim hp.1
        obtain ⟨⟨h0', hB, hf⟩, hr⟩ := hp
        refine ⟨h0', hR.of_frame (fun r h => ?_), hB, hf⟩
        simpa [R', Function.update_of_ne (show r ≠ 49 by omega),
          Function.update_of_ne (show r ≠ 50 by omega)] using hr r h)
  refine (Triple.seq_normal_const H HF').mono_cost ?_
  intro s _
  omega

private theorem delOwnerPass_frame : Stmt.WritesBelow 70 delOwnerPass := by
  simp [delOwnerPass, forRange, forUp, delRefreshOwner, delSupRefresh,
    delCursorSetup, delCsrSetup, advanceStmt, supTestStmt, delCursorStore, Stmt.WritesBelow]

/-- Copy the lost-terminal descriptor, then refresh the owner support cursors and keep the work registers. -/
theorem delEntryOwners_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b h wb cb : ℕ} {lost cs : List ℕ} {R mem0 : ℕ → ℕ}
    (h0 : R 0 = b) (hR : DelWorkRegs R h wb cb lost.length cs.length)
    (hb : b + x.encode.length ≤ wb) (hw : wb + lost.length < 2 ^ w)
    (hc : ∀ t ∈ lost, t < x.H.A.C.numTerm)
    (hq : ∀ t ∈ lost, x.H.A.C.owner t < x.n)
    (hN : ∀ q < x.n, (x.H.A.C.supportArray q).length + 1 < 2 ^ w)
    (hcur : ∀ q, x.ms.st.supCur q ≤ (x.H.A.C.supportArray q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem wb lost ∧ s.mem = mem0) (.seq (delReadWorkList 71 72 49 50) delOwnerPass)
      (normalPost fun s => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.refreshOwners lost).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delOwnerPassStepCost x lost) 0 lost.length + lost.length * 9 + 13) := by
  let R' := Function.update (Function.update R 49 wb) 50 lost.length
  let M := fun mem => ListAt mem b x.encode ∧ ListAt mem wb lost ∧ mem = mem0
  have H := delReadWorkList_triple (w := w) (p := p) (M := M) (dst := 49) (count := 50)
    hR.lostBase hR.lostCount (by decide)
  have HT := delOwnerPass_triple (w := w) (p := p) (mem0 := mem0) (R := R') x
    (by simpa [R'] using h0) (by simp [R']) (by simp [R']) hb hw hc hq hN hcur hinel
  have HF := Triple.regs_frame delOwnerPass_frame HT R'
  have HF' := (HF.weaken_pre (fun s (hs : s.regs = R' ∧ M s.mem) =>
    ⟨hs, fun r _ => congrFun hs.1 r⟩)).strengthen_post
      (Q' := normalPost fun s => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.refreshOwners lost).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun o s hp => by
        cases o <;> try exact False.elim hp.1
        obtain ⟨⟨h0', hB, hf⟩, hr⟩ := hp
        refine ⟨h0', hR.of_frame (fun r h => ?_), hB, hf⟩
        simpa [R', Function.update_of_ne (show r ≠ 49 by omega),
          Function.update_of_ne (show r ≠ 50 by omega)] using hr r h)
  refine (Triple.seq_normal_const H HF').mono_cost ?_
  intro s _
  omega

private theorem delWalkPass_frame : Stmt.WritesBelow 70 delWalkPass := by
  simp [delWalkPass, forRange, forUp, delConnectorWalkVerts, delWalkVertsLoop, delRefreshWalkVertex, delSupRefresh,
    delCursorSetup, delCsrSetup, advanceStmt, supTestStmt, delCursorStore, Stmt.WritesBelow]

/-- Copy the connector descriptor, then refresh the walk support cursors and keep the work registers. -/
theorem delEntryWalks_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b h wb cb : ℕ} {lost cs : List ℕ} {R mem0 : ℕ → ℕ}
    (h0 : R 0 = b) (hR : DelWorkRegs R h wb cb lost.length cs.length)
    (hb : b + x.encode.length ≤ cb) (hw : cb + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hv : ∀ c ∈ cs, ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n)
    (hN : ∀ q < x.n, (x.H.A.C.supportArray q).length + 1 < 2 ^ w)
    (hcur : ∀ q, x.ms.st.supCur q ≤ (x.H.A.C.supportArray q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem cb cs ∧ s.mem = mem0) (.seq (delReadWorkList 73 74 55 56) delWalkPass)
      (normalPost fun s => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.refreshWalkVerts (x.walkPassVerts cs)).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delWalkPassStepCost x cs) 0 cs.length + cs.length * 9 + 13) := by
  let R' := Function.update (Function.update R 55 cb) 56 cs.length
  let M := fun mem => ListAt mem b x.encode ∧ ListAt mem cb cs ∧ mem = mem0
  have H := delReadWorkList_triple (w := w) (p := p) (M := M) (dst := 55) (count := 56)
    hR.connBase hR.connCount (by decide)
  have HT := delWalkPass_triple (w := w) (p := p) (mem0 := mem0) (R := R') x
    (by simpa [R'] using h0) (by simp [R']) (by simp [R']) hb hw hc hv hN hcur hinel
  have HF := Triple.regs_frame delWalkPass_frame HT R'
  have HF' := (HF.weaken_pre (fun s (hs : s.regs = R' ∧ M s.mem) =>
    ⟨hs, fun r _ => congrFun hs.1 r⟩)).strengthen_post
      (Q' := normalPost fun s => s.regs 0 = b ∧ DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.refreshWalkVerts (x.walkPassVerts cs)).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun o s hp => by
        cases o <;> try exact False.elim hp.1
        obtain ⟨⟨h0', hB, hf⟩, hr⟩ := hp
        refine ⟨h0', hR.of_frame (fun r h => ?_), hB, hf⟩
        simpa [R', Function.update_of_ne (show r ≠ 55 by omega),
          Function.update_of_ne (show r ≠ 56 by omega)] using hr r h)
  refine (Triple.seq_normal_const H HF').mono_cost ?_
  intro s _
  omega

end MinCostFlow.HierPaths

end
