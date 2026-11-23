module

public import MinCostFlow.MinRatio.PathTreeContract
public import WordRAM.CopyWords
import MinCostFlow.MinRatio.PathTreeCall
public import MinCostFlow.MinRatio.TreeEdit
public import MinCostFlow.MinRatio.TreeEditDispatch
import MinCostFlow.LinkCut.ForestExposeSpec

/-!
# Retaining the payload of a removed tree edge

The proof of Theorem 5.1 (pages 29–30) maintains flow and detector
accounts in link-cut trees. When an edge leaves the forest, copy its
exposed record to the edge's off-tree storage before cutting it.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Moving a fixed-point edge record preserves all payload fields,
including its orientation. -/
theorem PathEdgeAt.copy {ma mb : ℕ → ℕ} {src dst h L : ℕ} {edge : PathEdgeValue}
    (ha : PathEdgeAt ma src h L (some edge))
    (he : ∀ i < 2 + 4 * L, mb (dst + i) = ma (src + i)) :
    PathEdgeAt mb dst h L (some edge) := by
  obtain ⟨htag, hdir, hg, hl, hf, hd⟩ := ha
  refine ⟨?_, (he 1 (by omega)).trans hdir, hg.congr ?_, hl.congr ?_, hf.congr ?_, hd.congr ?_⟩
  · simpa using (he 0 (by omega)).trans (by simpa using htag)
  · intro i hi
    simpa only [Nat.add_assoc] using he (2 + i) (by omega)
  · intro i hi
    simpa only [Nat.add_assoc] using he (2 + L + i) (by omega)
  · intro i hi
    simpa only [Nat.add_assoc] using he (2 + 2 * L + i) (by omega)
  · intro i hi
    simpa only [Nat.add_assoc] using he (2 + 3 * L + i) (by omega)

/-- Copy the exposed record from register 27 to the off-tree
record address in register 28. Register 29 gives the limb count. -/
@[expose] def treeEditSavePayload (copy : ℕ) : Stmt :=
  .call 30 copy [.reg 27, .reg 28, .bin .add (.const 2) (.bin .mul (.const 4) (.reg 29))]

/-- The copy changes only the off-tree record and takes at most
`68 * L + 53` steps. -/
theorem treeEditSavePayload_runs {w copy h L src dst : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {value : PathEdgeValue}
    (hc : MeetsContract w p copy (copyWordsContract w))
    (h27 : st.regs 27 = src) (h28 : st.regs 28 = dst) (h29 : st.regs 29 = L)
    (hv : PathEdgeAt st.mem src h L (some value))
    (hsep : dst + (2 + 4 * L) ≤ src)
    (hsrc : src + (2 + 4 * L) ≤ 2 ^ w) (hw : 4 < 2 ^ w)
    (hlen : 2 + 4 * L < 2 ^ w) :
    ∃ out cost, Runs w p ω (treeEditSavePayload copy) st .normal out cost ∧
      cost ≤ 68 * L + 53 ∧ PathEdgeAt out.mem dst h L (some value) ∧
      (∀ a, a < dst ∨ dst + (2 + 4 * L) ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 30 → out.regs r = st.regs r) := by
  have h2 : 2 < 2 ^ w := by omega
  have hmul : 4 * L < 2 ^ w := by omega
  have hargs : evalArgs w st [.reg 27, .reg 28,
      .bin .add (.const 2) (.bin .mul (.const 4) (.reg 29))] = some [src, dst, 2 + 4 * L] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h27, h28, h29, h2, hw, hmul, hlen]
  have hwords : ∀ a ∈ [src, dst, 2 + 4 * L], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h <;> subst a <;> omega
  have hpre : (copyWordsContract w).pre [src, dst, 2 + 4 * L] st.mem :=
    ⟨src, dst, _, rfl, by omega, hsrc, by omega, Or.inl hsep⟩
  obtain ⟨out, cost, ret, hr, hp, _, hregs, hcost⟩ :=
    runs_call_of_meetsContract (r := 30) hc hargs hwords hpre ω
  obtain ⟨src', dst', len, hargs', _, hcopy, hframe⟩ := hp
  simp only [List.cons.injEq, and_true] at hargs'
  rcases hargs' with ⟨rfl, rfl, rfl⟩
  simp only [argsSize, Expr.size, copyWordsContract] at hcost
  exact ⟨out, cost, hr, by omega, hv.copy hcopy, hframe, hregs⟩

open LinkCut

/-- Exposing a named edge for its account read keeps the same named
forest and logical payload pairs. The auxiliary trees may change. -/
theorem TreeEditNamedSlots.expose {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ} {e : ℕ}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth) (he : e ∈ G.E) :
    let exposed := lctExpose pathPayload s (slot e)
    ∃ ts, LctInvWith pathPayload exposed ts free depth ∧
      TreeEditNamedSlots exposed ts G slot name ∧
      (forestPairs pathPayload exposed.splay ts).Perm (forestPairs pathPayload s.splay trees) := by
  dsimp only
  obtain ⟨t, ht, hslot⟩ := List.mem_flatMap.mp (hn.forward e he).1
  obtain ⟨ts, _, _, hInv, hPerm, hPar, hPairs, _⟩ :=
    lctExpose_spec pathPayload_laws hi ht hslot
  refine ⟨ts, hInv, ⟨?_, ?_, ?_⟩, hPairs⟩
  · intro f hf
    obtain ⟨ha, hs, hName⟩ := hn.forward f hf
    exact ⟨hPerm.mem_iff.mpr ha, hs, hName⟩
  · intro k hk hs
    exact hn.inverse k (hPerm.mem_iff.mp hk) hs
  · intro f hf
    change ∀ z, inducedSubPar pathPayload (lctExpose pathPayload s (slot e)).splay ts z =
      inducedSubPar pathPayload s.splay trees z at hPar
    simpa only [hPar] using hn.endpoints f hf

/-- Read the deleted name's current tree slot before cutting.
Register 19 holds the slot table base, and register 8 the edge name. -/
@[expose] def treeEditReadPayload (read : ℕ) : Stmt :=
  .call 3 read [.reg 0, .load (.bin .add (.reg 19) (.reg 8)), .reg 27]

/-- The named read exposes the slot, writes its current record at the
saved heap address, and keeps the record address for the off-tree copy. -/
theorem treeEditReadPayload_runs {w L constant init handle slot heap : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (h0 : st.regs 0 = handle) (h27 : st.regs 27 = heap)
    (haddr : st.regs 19 + st.regs 8 < 2 ^ w)
    (hslot : st.mem (st.regs 19 + st.regs 8) = slot)
    (hwords : ∀ a ∈ [handle, slot, heap], a < 2 ^ w)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 4 s [handle, slot, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 4 s.n [handle, slot, heap] < 2 ^ w) :
    let exposed := lctExpose pathPayload s slot
    ∃ out cost ret y,
      Runs w p ω (treeEditReadPayload (op 4)) st .normal out cost ∧ out.regs 3 = ret ∧
      (∀ r, r ≠ 3 → out.regs r = st.regs r) ∧ R.rep handle exposed y out.mem ∧
      PathEdgeAt out.mem heap fmt.limbBits L (exposed.splay.nodes slot).val ∧
      R.Respects (R.foot handle x) heap (allocation 4 s.n [handle, slot, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 7 := by
  dsimp only
  obtain ⟨s', cost, out, y, ret, hrun, hrep', hp, hmem, hcost⟩ :=
    pathTree_runs_call (i := 4) (reg := 3) (st := st) (ω := ω)
      (args := [.reg 0, .load (.bin .add (.reg 19) (.reg 8)), .reg 27])
      (vs := [handle, slot, heap]) himpl
      (by simp [evalArgs, Expr.eval, BinOp.eval, h0, h27, haddr, hslot])
      hwords rfl hrep hpre hfoot hz hroom
  obtain ⟨he, hval⟩ := hp
  change s' = lctExpose pathPayload s slot at he
  subst s'
  exact ⟨{ out with regs := Function.update st.regs 3 ret }, cost, ret, y,
    hrun, by simp, fun r hr => Function.update_of_ne hr _ _, hrep', hval, hmem, hcost⟩

/-- Expose a named tree edge and save its account in off-tree storage. -/
@[expose] def treeEditReadAndSavePayload (read copy : ℕ) : Stmt :=
  treeEditReadPayload read ;; treeEditSavePayload copy

/-- Reading and saving the edge preserves the exposed tree and its
potential through the off-tree write. -/
theorem treeEditReadAndSavePayload_runs {w L constant init handle slot heap dst copy : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h0 : st.regs 0 = handle) (h27 : st.regs 27 = heap)
    (h28 : st.regs 28 = dst) (h29 : st.regs 29 = L)
    (haddr : st.regs 19 + st.regs 8 < 2 ^ w)
    (hslot : st.mem (st.regs 19 + st.regs 8) = slot)
    (hwords : ∀ a ∈ [handle, slot, heap], a < 2 ^ w)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 4 s [handle, slot, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 4 s.n [handle, slot, heap] < 2 ^ w)
    (hval : ((lctExpose pathPayload s slot).splay.nodes slot).val = some value)
    (hsep : dst + (2 + 4 * L) ≤ heap)
    (hsrc : heap + (2 + 4 * L) ≤ 2 ^ w) (hw : 4 < 2 ^ w)
    (hlen : 2 + 4 * L < 2 ^ w)
    (houtside : ∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle x a) :
    let exposed := lctExpose pathPayload s slot
    ∃ out cost ret y,
      Runs w p ω (treeEditReadAndSavePayload (op 4) copy) st .normal out cost ∧
      out.regs 3 = ret ∧
      (∀ r, r ≠ 3 → r ≠ 30 → out.regs r = st.regs r) ∧ R.rep handle exposed y out.mem ∧
      PathEdgeAt out.mem dst fmt.limbBits L (some value) ∧
      (∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle y a) ∧
      R.Respects (fun a => R.foot handle x a ∨ dst ≤ a ∧ a < dst + (2 + 4 * L))
        heap (allocation 4 s.n [handle, slot, heap]) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n +
        R.phi handle x st.mem + (68 * L + 61) := by
  dsimp only
  obtain ⟨mid, c, ret, y, hread, h3, hregs, hRep, hv, hf, hc⟩ :=
    treeEditReadPayload_runs (ω := ω) himpl h0 h27 haddr hslot hwords hpre hrep hfoot hz hroom
  rw [hval] at hv
  obtain ⟨out, d, hsave, hd, hout, hframe, hregs'⟩ :=
    treeEditSavePayload_runs (ω := ω) hcopy ((hregs 27 (by decide)).trans h27)
      ((hregs 28 (by decide)).trans h28) ((hregs 29 (by decide)).trans h29) hv hsep hsrc hw hlen
  have hKeep a (ha : R.foot handle y a) : mid.mem a = out.mem a := by
    symm
    apply hframe
    by_cases hlo : a < dst
    · exact Or.inl hlo
    · right
      by_contra hn
      rcases hf.2.2.2.2 a ha with hOld | ⟨hNew, _⟩
      · exact houtside a (by omega) (by omega) hOld
      · omega
  obtain ⟨hRep', hphi⟩ := himpl.1 handle (lctExpose pathPayload s slot) y mid.mem out.mem hKeep
  refine ⟨out, c + d + 1, ret, y, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hread, hsave, rfl⟩),
    (hregs' 3 (by decide)).trans h3, fun r h3' h30 => (hregs' r h30).trans (hregs r h3'),
    hRep' hRep, hout, ?_, ?_, ?_⟩
  · intro a hlo hhi ha
    rcases hf.2.2.2.2 a ha with hOld | ⟨hNew, _⟩
    · exact houtside a hlo hhi hOld
    · exact (Nat.not_le_of_lt (hhi.trans_le hsep)) hNew
  · refine ⟨hf.1, hf.2.1, ?_, ?_, ?_⟩
    · intro a ha
      rw [hframe a (Or.inr (hsep.trans (hf.1.trans ha)))]
      exact hf.2.2.1 a ha
    · intro a ha hn
      have hwrite : a < dst ∨ dst + (2 + 4 * L) ≤ a := by
        by_cases hlo : a < dst
        · exact Or.inl hlo
        · exact Or.inr (Nat.le_of_not_gt fun hh => hn (Or.inr ⟨by omega, hh⟩))
      rw [hframe a hwrite]
      exact hf.2.2.2.1 a ha (fun hp => hn (Or.inl hp))
    · intro a ha
      exact (hf.2.2.2.2 a ha).imp Or.inl id
  · rw [← hphi]
    omega

/-- Save the heap that will hold the exposed record and resolve
the persistent destination from the edge payload pointer table. -/
@[expose] def treeEditPrepareCutPayload : Stmt :=
  .assign 27 (.reg 3) ;;
  .assign 28 (.load (.bin .add (.reg 22) (.reg 8)))

/-- Preparing a deleted edge's payload addresses takes eight steps
and preserves its resolved endpoints, name and slot-table base. -/
theorem treeEditPrepareCutPayload_runs {w dst : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (haddr : st.regs 22 + st.regs 8 < 2 ^ w)
    (hdst : st.mem (st.regs 22 + st.regs 8) = dst) :
    ∃ out, Runs w p ω treeEditPrepareCutPayload st .normal out 8 ∧
      out.regs 27 = st.regs 3 ∧ out.regs 28 = dst ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 27 → r ≠ 28 → out.regs r = st.regs r) := by
  let mid := { st with regs := Function.update st.regs 27 (st.regs 3) }
  let out := { mid with regs := Function.update mid.regs 28 dst }
  have hsave : Runs w p ω (.assign 27 (.reg 3)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hlookup : Runs w p ω (.assign 28 (.load (.bin .add (.reg 22) (.reg 8))))
      mid .normal out 5 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, haddr, hdst],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 5, hsave, hlookup, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], rfl, ?_⟩
  intro r h27 h28
  simp [out, mid, Function.update_of_ne, h27, h28]

/-- Save the account into the persistent record, then cut its edge. -/
@[expose] def treeEditSaveAndCut (read copy cut : ℕ) : Stmt :=
  treeEditReadAndSavePayload read copy ;; treeEditCut cut

/-- A resolved Cut returns the exposed-and-cut tree and retains the
removed account at its off-tree address. The two tree potentials
telescope across the read and the cut. -/
theorem treeEditSaveAndCut_runs {w L constant init handle slot heap dst copy u v cutSpace : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h0 : st.regs 0 = handle) (h1 : st.regs 1 = u) (h2 : st.regs 2 = v)
    (h27 : st.regs 27 = heap) (h28 : st.regs 28 = dst) (h29 : st.regs 29 = L)
    (haddr : st.regs 19 + st.regs 8 < 2 ^ w)
    (hslot : st.mem (st.regs 19 + st.regs 8) = slot)
    (hwords : ∀ a ∈ [handle, slot, heap], a < 2 ^ w)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 4 s [handle, slot, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 4 s.n [handle, slot, heap] < 2 ^ w)
    (hval : ((lctExpose pathPayload s slot).splay.nodes slot).val = some value)
    (hsep : dst + (2 + 4 * L) ≤ heap)
    (hsrc : heap + (2 + 4 * L) ≤ 2 ^ w) (hw : 4 < 2 ^ w)
    (hlen : 2 + 4 * L < 2 ^ w)
    (houtside : ∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle x a)
    (hcutPre : ∀ ret mem, (pathTreeMachineContract fmt L constant allocation).pre 1
      (lctExpose pathPayload s slot) [handle, u, v, ret] mem)
    (hcutSpace : ∀ ret ≤ heap + allocation 4 s.n [handle, slot, heap],
      allocation 1 s.n [handle, u, v, ret] ≤ cutSpace)
    (hcutRoom : ∀ ret ≤ heap + allocation 4 s.n [handle, slot, heap],
      ret + allocation 1 s.n [handle, u, v, ret] < 2 ^ w) :
    let next := lctCut pathPayload (lctExpose pathPayload s slot) u v
    ∃ out cost ret y,
      Runs w p ω (treeEditSaveAndCut (op 4) copy (op 1)) st .normal out cost ∧
      out.regs 3 = ret ∧
      (∀ r, r ≠ 3 → r ≠ 30 → out.regs r = st.regs r) ∧
      R.rep handle next y out.mem ∧ PathEdgeAt out.mem dst fmt.limbBits L (some value) ∧
      (∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle y a) ∧
      R.Respects (fun a => R.foot handle x a ∨ dst ≤ a ∧ a < dst + (2 + 4 * L))
        heap (allocation 4 s.n [handle, slot, heap] + cutSpace) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ 2 * pathTreeBudget constant L s.n +
        R.phi handle x st.mem + (68 * L + 67) := by
  dsimp only
  obtain ⟨mid, c, ret, y, hr, hret, hregs, hrep', hrecord, hAway, hframe, hcost⟩ :=
    treeEditReadAndSavePayload_runs (ω := ω) himpl hcopy h0 h27 h28 h29 haddr hslot
      hwords hpre hrep hfoot hz hroom hval hsep hsrc hw hlen houtside
  have hroom' := hcutRoom ret hframe.2.1
  have hretWord : ret < 2 ^ w := by omega
  have hhandle := hwords handle (by simp)
  have hargs : ∀ a ∈ [handle, u, v, ret], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h <;> subst a <;> assumption
  have hFootMid a (ha : R.foot handle y a) : a < ret := by
    rcases hframe.2.2.2.2 a ha with (hOld | ⟨_, hNew⟩)
    · rcases hOld with hOld | ⟨_, hDst⟩
      · exact (hfoot a hOld).trans_le hframe.1
      · exact hDst.trans_le (hsep.trans hframe.1)
    · exact hNew
  obtain ⟨out, final, d, z, hcut, hOut, hCutRegs, hTree, hCutFrame, hCutCost⟩ :=
    treeEditCut_runs (ω := ω) himpl
      ⟨(hregs 0 (by decide) (by decide)).trans h0, (hregs 1 (by decide) (by decide)).trans h1,
       (hregs 2 (by decide) (by decide)).trans h2, hret⟩
      hargs hrep' (hcutPre _ _) hFootMid hframe.2.2.1 hroom'
  refine ⟨out, c + d + 1, final, z, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hcut, rfl⟩), hOut,
    fun r h3 h30 => (hCutRegs r h3).trans (hregs r h3 h30), hTree, ?_, ?_, ?_, ?_⟩
  · exact hrecord.congr (fun a hlo hhi =>
      hCutFrame.2.2.2.1 a (by have := hframe.1; omega) (hAway a hlo (by omega)))
  · intro a hlo hhi ha
    rcases hCutFrame.2.2.2.2 a ha with h | ⟨hfresh, _⟩
    · exact hAway a hlo hhi h
    · exact (Nat.not_le_of_lt (hhi.trans_le (hsep.trans hframe.1))) hfresh
  · have hCutLo := hCutFrame.1
    have hCutHi := hCutFrame.2.1
    change final ≤ ret + allocation 1 s.n [handle, u, v, ret] at hCutHi
    have hRoomCut := hcutSpace ret hframe.2.1
    refine ⟨hframe.1.trans hCutLo, by have := hframe.2.1; omega,
      hCutFrame.2.2.1, ?_, ?_⟩
    · intro a ha hOld
      have hMid : ¬ R.foot handle y a := by
        intro hFoot
        rcases hframe.2.2.2.2 a hFoot with h | ⟨hNew, _⟩
        · exact hOld h
        · omega
      exact (hCutFrame.2.2.2.1 a (ha.trans_le hframe.1) hMid).trans
        (hframe.2.2.2.1 a ha hOld)
    · intro a ha
      rcases hCutFrame.2.2.2.2 a ha with h | ⟨hLo, hHi⟩
      · rcases hframe.2.2.2.2 a h with h | ⟨hLo, hHi⟩
        · exact Or.inl h
        · exact Or.inr ⟨hLo, hHi.trans_le hCutLo⟩
      · exact Or.inr ⟨hframe.1.trans hLo, hHi⟩
  · change d + R.phi handle z out.mem ≤ pathTreeBudget constant L s.n + R.phi handle y mid.mem + 5 at hCutCost
    omega

/-- Look up the persistent account and save it before cutting. -/
@[expose] def treeEditPreparedSaveAndCut (read copy cut : ℕ) : Stmt :=
  treeEditPrepareCutPayload ;; treeEditSaveAndCut read copy cut

/-- The complete resolved deletion needs only the edge name,
resolved endpoints, and persistent table bases from the caller. -/
theorem treeEditPreparedSaveAndCut_runs {w L constant init handle slot heap dst copy u v cutSpace : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h0 : st.regs 0 = handle) (h1 : st.regs 1 = u) (h2 : st.regs 2 = v)
    (h3 : st.regs 3 = heap) (h29 : st.regs 29 = L)
    (hpAddr : st.regs 22 + st.regs 8 < 2 ^ w)
    (hpDst : st.mem (st.regs 22 + st.regs 8) = dst)
    (haddr : st.regs 19 + st.regs 8 < 2 ^ w)
    (hslot : st.mem (st.regs 19 + st.regs 8) = slot)
    (hwords : ∀ a ∈ [handle, slot, heap], a < 2 ^ w)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 4 s [handle, slot, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 4 s.n [handle, slot, heap] < 2 ^ w)
    (hval : ((lctExpose pathPayload s slot).splay.nodes slot).val = some value)
    (hsep : dst + (2 + 4 * L) ≤ heap)
    (hsrc : heap + (2 + 4 * L) ≤ 2 ^ w) (hw : 4 < 2 ^ w)
    (hlen : 2 + 4 * L < 2 ^ w)
    (houtside : ∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle x a)
    (hcutPre : ∀ ret mem, (pathTreeMachineContract fmt L constant allocation).pre 1
      (lctExpose pathPayload s slot) [handle, u, v, ret] mem)
    (hcutSpace : ∀ ret ≤ heap + allocation 4 s.n [handle, slot, heap],
      allocation 1 s.n [handle, u, v, ret] ≤ cutSpace)
    (hcutRoom : ∀ ret ≤ heap + allocation 4 s.n [handle, slot, heap],
      ret + allocation 1 s.n [handle, u, v, ret] < 2 ^ w) :
    let next := lctCut pathPayload (lctExpose pathPayload s slot) u v
    ∃ out cost ret y,
      Runs w p ω (treeEditPreparedSaveAndCut (op 4) copy (op 1)) st .normal out cost ∧
      out.regs 3 = ret ∧
      (∀ r, r ≠ 3 → r ≠ 27 → r ≠ 28 → r ≠ 30 → out.regs r = st.regs r) ∧
      R.rep handle next y out.mem ∧ PathEdgeAt out.mem dst fmt.limbBits L (some value) ∧
      (∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle y a) ∧
      R.Respects (fun a => R.foot handle x a ∨ dst ≤ a ∧ a < dst + (2 + 4 * L))
        heap (allocation 4 s.n [handle, slot, heap] + cutSpace) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ 2 * pathTreeBudget constant L s.n +
        R.phi handle x st.mem + (68 * L + 76) := by
  dsimp only
  obtain ⟨mid, hprep, h27, h28, hm, hregs⟩ :=
    treeEditPrepareCutPayload_runs (p := p) (ω := ω) hpAddr hpDst
  have hsave := h27.trans h3
  obtain ⟨out, cost, ret, y, hrun, hret, hstay, htree, hp, hAway, hframe, hc⟩ :=
    treeEditSaveAndCut_runs (ω := ω) himpl hcopy
      ((hregs 0 (by decide) (by decide)).trans h0)
      ((hregs 1 (by decide) (by decide)).trans h1)
      ((hregs 2 (by decide) (by decide)).trans h2) hsave h28
      ((hregs 29 (by decide) (by decide)).trans h29)
      (by rw [hregs 19 (by decide) (by decide), hregs 8 (by decide) (by decide)]; exact haddr)
      (by rw [hm, hregs 19 (by decide) (by decide), hregs 8 (by decide) (by decide)]; exact hslot)
      hwords hu hv (by rwa [hm]) (by rwa [hm]) hfoot (by rwa [hm])
      hroom hval hsep hsrc hw hlen houtside hcutPre hcutSpace hcutRoom
  refine ⟨out, 8 + cost + 1, ret, y, runs_seq_iff.mpr (Or.inr ⟨mid, 8, cost,
    hprep, hrun, rfl⟩), hret, ?_, htree, hp, hAway, by rwa [hm] at hframe, ?_⟩
  · intro r h3' h27' h28' h30
    exact (hstay r h3' h30).trans (hregs r h27' h28')
  · rw [hm] at hc
    omega

open DynSpanner.Program

/-- Packed dispatch with a deletion that saves the removed account. -/
@[expose] def treeEditPayloadDispatch (link read copy cut : ℕ) : Stmt :=
  treeEditDispatchWithBodies (treeEditOrientLink ;; treeEditLink link)
    (treeEditPreparedSaveAndCut read copy cut)

/-- Decode the deletion and resolve its endpoints before calling the
payload-preserving Cut. The packed dispatch costs 49 steps beyond the
resolved deletion. -/
theorem treeEditPayloadDispatch_delete_runs {w link read copy cut base vc ec e addr : ℕ}
    {G : MGraph} {p : Program} {ω : ℕ → Bool} {st : State}
    {Q : State → ℕ → Prop}
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hGraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w)
    {n : ℕ} (hvc : vc ≤ n) (hn : n < 2 ^ w)
    (h6 : st.regs 6 = addr) (hwords : ListAt st.mem addr [0, e]) (haddr : addr + 1 < 2 ^ w)
    (h12 : st.regs 12 = dgETailSlotBase base vc ec)
    (h13 : st.regs 13 = dgEHeadSlotBase base vc ec)
    (h14 : st.regs 14 = dgIntToExtBase base vc)
    (hResolved : ∀ ready, ready.mem = st.mem →
      ready.regs 1 = G.tail e + 1 → ready.regs 2 = G.head e + 1 →
      ready.regs 7 = 0 → ready.regs 8 = e →
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        ready.regs r = st.regs r) →
      ∃ out cost, Runs w p ω (treeEditPreparedSaveAndCut read copy cut) ready .normal out cost ∧ Q out cost) :
    ∃ out cost, Runs w p ω (treeEditPayloadDispatch link read copy cut) st .normal out (cost + 49) ∧
      Q out cost := by
  obtain ⟨decoded, hread, htag, hname, hmem, hreg⟩ :=
    treeEditRead_runs (p := p) (ω := ω) h6 hwords haddr
  obtain ⟨args, hargs, ht, hh, hi, hmem', hreg'⟩ :=
    treeEditGraphArgs_runs (p := p) (ω := ω) (by decide)
      ((hreg 12 (by decide) (by decide)).trans h12)
      ((hreg 13 (by decide) (by decide)).trans h13)
      ((hreg 14 (by decide) (by decide)).trans h14)
  have hargsMem := hmem'.trans hmem
  have hargsName := (hreg' 8 (by decide) (by decide) (by decide)).trans hname
  obtain ⟨ready, hresolve, hu, hv, _, _, hm, hg⟩ :=
    treeEditResolve_runs (p := p) (ω := ω) (by rwa [hargsMem])
      hGraphRoom hvc hn hargsName ht hh hi
  have hr7 := (hg 7 (by decide) (by decide)).trans
    ((hreg' 7 (by decide) (by decide) (by decide)).trans htag)
  have hr8 := (hg 8 (by decide) (by decide)).trans hargsName
  obtain ⟨out, cost, hrun, hq⟩ := hResolved ready (hm.trans hargsMem) hu hv hr7 hr8
    (fun r h1 h2 h7 h8 h9 h10 h11 =>
      (hg r h1 h2).trans ((hreg' r h9 h10 h11).trans (hreg r h7 h8)))
  have hbranch : Runs w p ω
      (treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;;
        treeEditPreparedSaveAndCut read copy cut) decoded .normal out (cost + 37) := by
    exact runs_seq_iff.mpr (Or.inr ⟨args, 8, 27 + cost + 1, hargs,
      runs_seq_iff.mpr (Or.inr ⟨ready, 27, cost, hresolve, hrun, rfl⟩), by omega⟩)
  have hd := treeEditDispatchWithBodies_runs_of_branch (linkBody := treeEditOrientLink ;; treeEditLink link) hread htag
    (by simpa using hbranch)
  exact ⟨out, cost, by simpa [treeEditPayloadDispatch, Nat.add_assoc] using hd, hq⟩

/-- A packed deletion performs the complete payload transfer and Cut,
with one combined frame for the tree and persistent record. -/
theorem treeEditPayloadDispatch_cut_runs {w L constant init handle slot heap dst copy cutSpace link base vc ec e addr : ℕ} {G : MGraph}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h0 : st.regs 0 = handle)
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hGraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w)
    (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (h6 : st.regs 6 = addr) (hrecord : ListAt st.mem addr [0, e]) (haddrWord : addr + 1 < 2 ^ w)
    (h12 : st.regs 12 = dgETailSlotBase base vc ec)
    (h13 : st.regs 13 = dgEHeadSlotBase base vc ec)
    (h14 : st.regs 14 = dgIntToExtBase base vc)
    (h3 : st.regs 3 = heap) (h29 : st.regs 29 = L)
    (hpAddr : st.regs 22 + e < 2 ^ w)
    (hpDst : st.mem (st.regs 22 + e) = dst)
    (haddr : st.regs 19 + e < 2 ^ w)
    (hslot : st.mem (st.regs 19 + e) = slot)
    (hwords : ∀ a ∈ [handle, slot, heap], a < 2 ^ w)
    (hu : G.tail e + 1 < 2 ^ w) (hv : G.head e + 1 < 2 ^ w)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 4 s [handle, slot, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 4 s.n [handle, slot, heap] < 2 ^ w)
    (hval : ((lctExpose pathPayload s slot).splay.nodes slot).val = some value)
    (hsep : dst + (2 + 4 * L) ≤ heap)
    (hsrc : heap + (2 + 4 * L) ≤ 2 ^ w) (hw : 4 < 2 ^ w)
    (hlen : 2 + 4 * L < 2 ^ w)
    (houtside : ∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle x a)
    (hcutPre : ∀ ret mem, (pathTreeMachineContract fmt L constant allocation).pre 1
      (lctExpose pathPayload s slot) [handle, G.tail e + 1, G.head e + 1, ret] mem)
    (hcutSpace : ∀ ret ≤ heap + allocation 4 s.n [handle, slot, heap],
      allocation 1 s.n [handle, G.tail e + 1, G.head e + 1, ret] ≤ cutSpace)
    (hcutRoom : ∀ ret ≤ heap + allocation 4 s.n [handle, slot, heap],
      ret + allocation 1 s.n [handle, G.tail e + 1, G.head e + 1, ret] < 2 ^ w) :
    let next := lctCut pathPayload (lctExpose pathPayload s slot) (G.tail e + 1) (G.head e + 1)
    ∃ out cost ret y,
      Runs w p ω (treeEditPayloadDispatch link (op 4) copy (op 1)) st .normal out cost ∧
      out.regs 3 = ret ∧
      out.regs 7 = 0 ∧ out.regs 8 = e ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 27 → r ≠ 28 → r ≠ 30 → out.regs r = st.regs r) ∧
      R.rep handle next y out.mem ∧ PathEdgeAt out.mem dst fmt.limbBits L (some value) ∧
      (∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle y a) ∧
      R.Respects (fun a => R.foot handle x a ∨ dst ≤ a ∧ a < dst + (2 + 4 * L))
        heap (allocation 4 s.n [handle, slot, heap] + cutSpace) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ 2 * pathTreeBudget constant L s.n +
        R.phi handle x st.mem + (68 * L + 125) := by
  dsimp only
  let Q := fun (out : State) (cost : ℕ) =>
    ∃ ret y, out.regs 3 = ret ∧ out.regs 7 = 0 ∧ out.regs 8 = e ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 27 → r ≠ 28 → r ≠ 30 → out.regs r = st.regs r) ∧
      R.rep handle
        (lctCut pathPayload (lctExpose pathPayload s slot) (G.tail e + 1) (G.head e + 1)) y out.mem ∧
      PathEdgeAt out.mem dst fmt.limbBits L (some value) ∧
      (∀ a, dst ≤ a → a < dst + (2 + 4 * L) → ¬ R.foot handle y a) ∧
      R.Respects (fun a => R.foot handle x a ∨ dst ≤ a ∧ a < dst + (2 + 4 * L))
        heap (allocation 4 s.n [handle, slot, heap] + cutSpace) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ 2 * pathTreeBudget constant L s.n +
        R.phi handle x st.mem + (68 * L + 76)
  obtain ⟨out, c, hr, ret, y, hret, htag, hedge, hregs, htree, hvalue, hAway, hframe, hcost⟩ :=
    treeEditPayloadDispatch_delete_runs (ω := ω) (Q := Q) he hGraphRoom hvc hn h6 hrecord haddrWord
      h12 h13 h14 (by
      intro ready hm h1 h2 h7 h8 hregs
      have keep (r : ℕ) (hr : 12 ≤ r) : ready.regs r = st.regs r :=
        hregs r (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
      have h19 := keep 19 (by decide)
      have h22 := keep 22 (by decide)
      obtain ⟨out, cost, ret, y, hrun, hret, hother, htree, hrecord, hAway, hframe, hcost⟩ :=
        treeEditPreparedSaveAndCut_runs (ω := ω) himpl hcopy
          ((hregs 0 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)).trans h0) h1 h2
          ((hregs 3 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)).trans h3)
          ((keep 29 (by decide)).trans h29)
          (by rwa [h22, h8]) (by rwa [hm, h22, h8])
          (by rwa [h19, h8]) (by rwa [hm, h19, h8]) hwords hu hv
          (by rwa [hm]) (by rwa [hm]) hfoot (by rwa [hm])
          hroom hval hsep hsrc hw hlen houtside hcutPre hcutSpace hcutRoom
      refine ⟨out, cost, hrun, ret, y, hret,
        (hother 7 (by decide) (by decide) (by decide) (by decide)).trans h7,
        (hother 8 (by decide) (by decide) (by decide) (by decide)).trans h8,
        ?_, htree, hrecord, hAway, by rwa [hm] at hframe, by rwa [hm] at hcost⟩
      intro r h1 h2 h3 h7 h8 h9 h10 h11 h27 h28 h30
      exact (hother r h3 h27 h28 h30).trans (hregs r h1 h2 h7 h8 h9 h10 h11))
  exact ⟨out, c + 49, ret, y, hr, hret, htag, hedge, hregs, htree, hvalue, hAway, hframe, by omega⟩

/-- The payload-aware dispatcher binds the new slot only for Link. -/
@[expose] def treeEditPayloadDispatchBound (link read copy cut bind : ℕ) : Stmt :=
  treeEditBindDispatch bind (treeEditPayloadDispatch link read copy cut)

/-- The saved-payload deletion skips Link's slot binding. -/
theorem treeEditPayloadDispatchBound_delete {w link read copy cut bind cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State}
    (hdispatch : Runs w p ω (treeEditPayloadDispatch link read copy cut)
      { st with regs := Function.update st.regs 21 (st.regs 3) } .normal out cost)
    (htag : out.regs 7 = 0) :
    Runs w p ω (treeEditPayloadDispatchBound link read copy cut bind) st .normal out (cost + 7) := by
  have hnop : Runs w p ω .nop out .normal out 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
  exact treeEditBindDispatch_runs hdispatch htag (by simpa using hnop)

end MinCostFlow.MinRatio
