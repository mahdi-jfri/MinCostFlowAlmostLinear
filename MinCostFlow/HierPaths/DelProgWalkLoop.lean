module

public import MinCostFlow.HierPaths.DelProgWalkRefresh

/-!
# Scanning the support cursors of a connector walk

The pass reads the walk's vertex words from section 10 and refreshes each corresponding
support cursor. The vertex words stay intact during the scan.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Scan a walk interval whose section offsets are in registers 52 and 53. -/
def delWalkVertsLoop : Stmt := forRange 48 (.reg 52) (.reg 53) delRefreshWalkVertex

theorem delWalkVertsLoop_noRand : delWalkVertsLoop.NoRand := by
  simp [delWalkVertsLoop, forRange, forUp, Stmt.NoRand, delRefreshWalkVertex_noRand]

/-- Apply the support refresh to the vertices of the walk in the given order. -/
def HierConcrete.refreshWalkVerts (x : HierConcrete) (cs : List ℕ) : HierConcrete :=
  cs.foldl (fun y c => y.refreshSup c) x

theorem HierConcrete.refreshWalkVerts_append_one (x : HierConcrete) (cs : List ℕ) (c : ℕ) :
    x.refreshWalkVerts (cs ++ [c]) = (x.refreshWalkVerts cs).refreshSup c := by
  simp [refreshWalkVerts, List.foldl_append]

theorem HierConcrete.length_encode_refreshSup (x : HierConcrete) (q : ℕ) :
    (x.refreshSup q).encode.length = x.encode.length := by
  show (layoutList (x.refreshSup q).sections).length = (layoutList x.sections).length
  unfold refreshSup
  rw [x.sections_setSupCur]
  exact length_layoutList_set _ (List.length_set ..)

theorem HierConcrete.length_encode_refreshWalkVerts (x : HierConcrete) (cs : List ℕ) :
    (x.refreshWalkVerts cs).encode.length = x.encode.length := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs c ih =>
    rw [x.refreshWalkVerts_append_one, HierConcrete.length_encode_refreshSup, ih]

theorem HierConcrete.refreshWalkVerts_data (x : HierConcrete) (cs : List ℕ) :
    (x.refreshWalkVerts cs).H = x.H ∧ (x.refreshWalkVerts cs).ms.st.loss = x.ms.st.loss ∧
      (x.refreshWalkVerts cs).ms.st.inelig = x.ms.st.inelig := by
  induction cs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | append_singleton cs c ih =>
    rw [x.refreshWalkVerts_append_one]
    exact ih

theorem HierConcrete.refreshWalkVerts_n (x : HierConcrete) (ts : List ℕ) :
    (x.refreshWalkVerts ts).n = x.n := by
  induction ts using List.reverseRecOn with
  | nil => rfl
  | append_singleton ts t ih =>
    rw [x.refreshWalkVerts_append_one]
    exact ih

theorem HierConcrete.refreshWalkVerts_cur_le (x : HierConcrete) (cs : List ℕ)
    (h : ∀ q, x.ms.st.supCur q ≤ (x.H.A.C.supportArray q).length) :
    ∀ q, (x.refreshWalkVerts cs).ms.st.supCur q ≤ (x.H.A.C.supportArray q).length := by
  induction cs using List.reverseRecOn with
  | nil => exact h
  | append_singleton cs c ih =>
    intro q
    rw [x.refreshWalkVerts_append_one]
    let y := x.refreshWalkVerts cs
    change Function.update y.ms.st.supCur c _ q ≤ _
    by_cases hq : q = c
    · subst q
      rw [Function.update_self]
      have he : y.H = x.H := (x.refreshWalkVerts_data cs).1
      exact (advance_le _ (by rw [he]; exact ih _)).trans_eq (by rw [he])
    · rw [Function.update_of_ne hq]
      exact ih q

theorem HierConcrete.refreshWalkVerts_section10 (x : HierConcrete) (vs : List ℕ) :
    (x.refreshWalkVerts vs).sections.getD 10 [] = x.sections.getD 10 [] := by
  induction vs using List.reverseRecOn with
  | nil => rfl
  | append_singleton vs v ih =>
    rw [x.refreshWalkVerts_append_one]
    exact ih

/-- The cursor state after the words before `i` have been scanned. -/
def DelWalkVertsInv (x : HierConcrete) (b lo : ℕ) (vs : List ℕ) (mem0 : ℕ → ℕ)
    (i : ℕ) (s : State) : Prop :=
  s.regs 0 = b ∧ s.regs 48 = i ∧ s.regs 53 = lo + vs.length ∧
  ListAt s.mem b (x.refreshWalkVerts (vs.take (i - lo))).encode ∧
  ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j

/-- Charge each support visit for the entries it actually skips. -/
def delWalkVertsStepCost (x : HierConcrete) (lo : ℕ) (vs : List ℕ) (i : ℕ) : ℕ :=
  let v := vs.getD (i - lo) 0
  let old := (x.refreshWalkVerts (vs.take (i - lo))).ms.st.supCur v
  165 + (advance (x.H.A.supValid (x.H.A.surv x.ms.st) v)
    (x.H.A.C.supportArray v).length old - old + 1) * 280

/-- Read and refresh one vertex, preserving the walk words for subsequent steps. -/
theorem delWalkVertsBody_triple {w : ℕ} {p : Program} (x : HierConcrete) {b lo i : ℕ}
    {vs : List ℕ} {mem0 : ℕ → ℕ} (hb : b + x.encode.length < 2 ^ w)
    (hwords : ∀ k (hk : k < vs.length), ∃ h : lo + k < (x.sections.getD 10 []).length,
      (x.sections.getD 10 [])[lo + k] = vs[k])
    (hv : ∀ v ∈ vs, v < x.n)
    (hN : ∀ v < x.n, (x.H.A.C.supportArray v).length + 1 < 2 ^ w)
    (hcur : ∀ v, x.ms.st.supCur v ≤ (x.H.A.C.supportArray v).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    (hlo : lo ≤ i) (hi : i < lo + vs.length) :
    Triple w p (DelWalkVertsInv x b lo vs mem0 i) delRefreshWalkVertex
      (normalPost fun s => DelWalkVertsInv x b lo vs mem0 (i + 1)
        { s with regs := Function.update s.regs 48 (i + 1) } ∧ s.regs 48 = i)
      (fun _ => delWalkVertsStepCost x lo vs i) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = lo + k := ⟨i - lo, by omega⟩
  have hk : k < vs.length := by omega
  have hsub : lo + k - lo = k := by omega
  have hsub' : lo + k + 1 - lo = k + 1 := by omega
  let v := vs[k]
  let y := x.refreshWalkVerts (vs.take k)
  obtain ⟨hH, hLoss, hIn⟩ := x.refreshWalkVerts_data (vs.take k)
  have hSurv : y.H.A.surv y.ms.st = x.H.A.surv x.ms.st := by
    simp only [StaticArrays.surv, y, hH, hLoss]
  have hlen : y.encode.length = x.encode.length := x.length_encode_refreshWalkVerts _
  have hyb : b + y.encode.length < 2 ^ w := by rwa [hlen]
  have he : y.sections.getD 10 [] = x.sections.getD 10 [] := x.refreshWalkVerts_section10 _
  obtain ⟨hidx, hword⟩ := hwords k hk
  have hidx' : lo + k < (y.sections.getD 10 []).length := by rwa [he]
  have hword' : (y.sections.getD 10 [])[lo + k] = v := by simpa only [he] using hword
  have hyn : (y.H.A.C.supportArray v).length + 1 < 2 ^ w := by
    rw [hH]; exact hN v (hv v (List.getElem_mem hk))
  have hyc : y.ms.st.supCur v ≤ (y.H.A.C.supportArray v).length := by
    rw [hH]; exact x.refreshWalkVerts_cur_le _ hcur v
  have hyI : y.ms.st.inelig = (Finset.range y.H.A.C.numConn).filter fun d =>
      ¬ y.H.A.C.Eligible (y.H.A.surv y.ms.st) d := by
    rw [hIn, hSurv, hH]; exact hinel
  have hnext : x.refreshWalkVerts (vs.take (k + 1)) = y.refreshSup v := by
    rw [List.take_succ_eq_append_getElem hk, x.refreshWalkVerts_append_one]
  intro s ω hs
  simp only [DelWalkVertsInv, hsub] at hs
  obtain ⟨h0, h48, h53, hy, hf⟩ := hs
  have hyv : v < y.n := (x.refreshWalkVerts_n _).symm ▸ hv v (List.getElem_mem hk)
  have H := delRefreshWalkVertex_triple (w := w) (p := p) (mem0 := s.mem)
    y h0 h48 hidx' hword' hyb hyv hyn hyc hyI
  obtain ⟨o, s', d, hrun, ⟨hp, hregs⟩, hd⟩ :=
    Triple.regs_frame delRefreshWalkVertex_writesBelow H s.regs s ω ⟨⟨rfl, hy, rfl⟩, fun _ _ => rfl⟩
  cases o <;> try contradiction
  obtain ⟨h0', _, hblock, hframe⟩ := hp
  refine ⟨_, s', d, hrun, ?_, ?_⟩
  · change DelWalkVertsInv x b lo vs mem0 (lo + k + 1) _ ∧ _
    simp only [DelWalkVertsInv, hsub', hnext]
    refine ⟨⟨by simpa using h0', by simp, ?_, hblock, ?_⟩, (hregs 48 (by decide)).trans h48⟩
    · simpa using (hregs 53 (by decide)).trans h53
    · intro j hj
      exact (hframe j (by simpa only [hlen] using hj)).trans (hf j hj)
  · unfold delWalkVertsStepCost
    rw [hsub, List.getD_eq_getElem _ _ hk]
    dsimp only at hd ⊢
    rw [hSurv, hH] at hd
    exact hd

/-- Scan all vertex words of one connector. A repeated vertex charges no extra cursor moves. -/
theorem delWalkVertsLoop_triple {w : ℕ} {p : Program} (x : HierConcrete) {b lo : ℕ}
    {vs : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h52 : R 52 = lo) (h53 : R 53 = lo + vs.length)
    (hb : b + x.encode.length < 2 ^ w) (hhi : lo + vs.length < 2 ^ w)
    (hwords : ∀ k (hk : k < vs.length), ∃ h : lo + k < (x.sections.getD 10 []).length,
      (x.sections.getD 10 [])[lo + k] = vs[k])
    (hv : ∀ v ∈ vs, v < x.n)
    (hN : ∀ v < x.n, (x.H.A.C.supportArray v).length + 1 < 2 ^ w)
    (hcur : ∀ v, x.ms.st.supCur v ≤ (x.H.A.C.supportArray v).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0) delWalkVertsLoop
      (normalPost fun s => s.regs 0 = b ∧
        ListAt s.mem b (x.refreshWalkVerts vs).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delWalkVertsStepCost x lo vs) lo (lo + vs.length) + vs.length * 9 + 7) := by
  have hone : 1 < 2 ^ w := by have := x.le_length_encode; omega
  have H := Triple.forRange_le (w := w) (p := p) (r := 48) (lo := .reg 52)
    (hi := .reg 53) (Inv := DelWalkVertsInv x b lo vs mem0)
    (delWalkVertsStepCost x lo vs) lo (lo + vs.length) (Nat.le_add_right ..) hone (fun _ => hhi)
    (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
    (fun s hs => ⟨Expr.eval_reg_of_eq (hs.1 ▸ h52), ?_⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ hlo hi => delWalkVertsBody_triple x hb hwords hv hN hcur hinel hlo hi)
  · refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by simp [Expr.size])
    cases o <;> try contradiction
    change DelWalkVertsInv x b lo vs mem0 (lo + vs.length) s at h
    simp only [DelWalkVertsInv, Nat.add_sub_cancel_left, List.take_length] at h
    exact ⟨h.1, h.2.2.2⟩
  · obtain ⟨hr, hblock, hm⟩ := hs
    simp only [DelWalkVertsInv, Nat.sub_self, List.take_zero]
    refine ⟨by simpa [hr] using h0, by simp, by simpa [hr] using h53,
      hblock, fun j _ => congrFun hm j⟩

/-- Read the walk interval of the connector in register 54 and refresh its vertices. -/
def delConnectorWalkVerts : Stmt :=
  .seq (delCsrSetup 10 54 52 53 (readHdr 3)) delWalkVertsLoop

theorem delConnectorWalkVerts_noRand : delConnectorWalkVerts.NoRand := by
  simp [delConnectorWalkVerts, Stmt.NoRand, delCsrSetup_noRand, delWalkVertsLoop_noRand]

theorem delConnectorWalkVerts_writesBelow : Stmt.WritesBelow 54 delConnectorWalkVerts := by
  simp [delConnectorWalkVerts, delCsrSetup, delWalkVertsLoop, forRange, forUp,
    delRefreshWalkVertex, delSupRefresh, delCursorSetup, advanceStmt, supTestStmt,
    delCursorStore, Stmt.WritesBelow]

/-- The register interval for the vertices of a connector's walk. -/
def HierConcrete.walkVertStart (x : HierConcrete) (c : ℕ) : ℕ :=
  delCsrStart x.H.A.C.numConn (fun d => (x.H.A.C.walk d).verts) c

/-- Refresh the stored walk of a connector, using its CSR offsets. -/
theorem delConnectorWalkVerts_triple {w : ℕ} {p : Program} (x : HierConcrete) {b c : ℕ}
    {mem0 R : ℕ → ℕ} (h0 : R 0 = b) (h54 : R 54 = c)
    (hc : c < x.H.A.C.numConn) (hb : b + x.encode.length < 2 ^ w)
    (hv : ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n)
    (hN : ∀ v < x.n, (x.H.A.C.supportArray v).length + 1 < 2 ^ w)
    (hcur : ∀ v, x.ms.st.supCur v ≤ (x.H.A.C.supportArray v).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d) :
    let vs := (x.H.A.C.walk c).verts
    let lo := x.walkVertStart c
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delConnectorWalkVerts
      (normalPost fun s => s.regs 0 = b ∧ ListAt s.mem b (x.refreshWalkVerts vs).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delWalkVertsStepCost x lo vs) lo (lo + vs.length) + vs.length * 9 + 90) := by
  dsimp only
  let lo := x.walkVertStart c
  let f := fun d => (x.H.A.C.walk d).verts
  let vs := f c
  let M := fun mem => ListAt mem b x.encode ∧ mem = mem0
  have hsec : x.sections.getD 10 [] = csrList x.H.A.C.numConn f := rfl
  have hwords : ∀ k (hk : k < vs.length), ∃ h : lo + k < (x.sections.getD 10 []).length,
      (x.sections.getD 10 [])[lo + k] = vs[k] := by
    intro k hk
    have h : lo + k < (x.sections.getD 10 []).length := by
      rw [hsec]
      exact csrList_data_lt f hc hk
    refine ⟨h, ?_⟩
    rw [← List.getD_eq_getElem _ 0 h, hsec]
    change (csrList x.H.A.C.numConn f).getD
      (x.H.A.C.numConn + 1 + ((List.range c).map fun d => (f d).length).sum + k) 0 = _
    rw [csrList_getD_data _ hc hk, List.getD_eq_getElem _ _ hk]
  have hnext : delCsrStart x.H.A.C.numConn f (c + 1) = lo + vs.length := delCsrStart_succ ..
  have hhi : lo + vs.length < 2 ^ w := by
    have hs : lo + vs.length ≤ (x.sections.getD 10 []).length := by
      rw [← hnext, hsec]
      exact delCsrStart_le _ _ hc
    have hpos : 0 < (x.sections.getD 10 []).length := by rw [hsec]; simp [csrList]
    have H := lt_length_of_sec (bs := x.sections) (i := 10)
      (by rw [x.length_sections']; decide)
      (k := (x.sections.getD 10 []).length - 1) (by omega)
    change _ < x.encode.length at H
    omega
  have hsetup := delCsrSetup_triple (w := w) (p := p) (r := 54) (lo := 52) (hi := 53)
    (M := M) (count := readHdr 3) (by decide) hsec hc h0 h54 (by decide) (by decide)
    (fun _ h => h.1) hb (fun s hm hr => by
      simpa [HierConcrete.header] using x.eval_readHdr hb hr hm.1 (k := 3) (by decide))
  unfold delConnectorWalkVerts
  refine (Triple.seq_normal_const hsetup
    (delWalkVertsLoop_triple (lo := lo) (vs := vs) x (by simpa using h0) (by simp [lo, f, HierConcrete.walkVertStart])
      (by simpa using hnext) hb hhi hwords hv hN hcur hinel)).mono_cost ?_
  intro s hs
  simp only [readHdr, readSec, secAddr, Expr.size]
  change _ + (rangeCost (delWalkVertsStepCost x lo vs) lo (lo + vs.length) + vs.length * 9 + 7) + 1 ≤
    rangeCost (delWalkVertsStepCost x lo vs) lo (lo + vs.length) + vs.length * 9 + 90
  omega

end MinCostFlow.HierPaths

end
