module

public import MinCostFlow.HierPaths.QueryProgEntry

/-!
# Support attachments in GetPath

An attachment reads a support entry, obtains its terminal, and copies the indicated walk
prefix in the requested direction. A terminal entry and a prefix of length zero contribute
no steps.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM Spanner

/-- Read one support entry. Append its attachment to the step buffers and return its terminal.
The arguments are the block, vertex, copy direction, two buffer bases, and current step count.
A direction of one follows the stored walk and a direction of zero reverses the prefix. -/
def attachProc (fEntry fCopy : ℕ) : Stmt :=
  .call 6 fEntry [.reg 0, .reg 1, .const 0] ;;
  .call 7 fEntry [.reg 0, .reg 1, .const 1] ;;
  .cond (.bin .eq (.reg 6) (.const 0)) (.ret (.reg 7)) .nop ;;
  .call 8 fEntry [.reg 0, .reg 1, .const 2] ;;
  .assign 9 (.load (.bin .add (secExpr 2) (.reg 7))) ;;
  .cond (.bin .eq (.reg 8) (.const 0)) (.ret (.reg 9)) .nop ;;
  .assign 10 (.load (.bin .add (secExpr 0) (.const 3))) ;;
  .assign 11 (secExpr 10) ;;
  .assign 12 (secExpr 11) ;;
  .assign 13 (.bin .add (.bin .add (.reg 11) (.bin .add (.reg 10) (.const 1)))
    (.load (.bin .add (.reg 11) (.reg 7)))) ;;
  .assign 14 (.bin .add (.bin .add (.reg 12) (.bin .add (.reg 10) (.const 1)))
    (.load (.bin .add (.reg 12) (.reg 7)))) ;;
  .call 15 fCopy [.reg 13, .reg 14, .reg 8, .reg 2, .reg 3, .reg 4, .reg 5] ;;
  .ret (.reg 9)

/-- The attachment uses only deterministic statements. -/
theorem attachProc_noRand (fEntry fCopy : ℕ) : (attachProc fEntry fCopy).NoRand := by
  simp [attachProc, Stmt.NoRand]

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM Spanner

public section

/-- An occurrence in a support array names a valid connector and a prefix within its walk. -/
theorem support_onWalk_bounds (C : ConnectorSystem) {G : Cited.Graph} (hC : C.FitsGraph G)
    {v c k : ℕ} (he : SupportEntry.onWalk c k ∈ C.supportArray v) :
    c < C.numConn ∧ (C.walk c).verts.length = (C.walk c).edges.length + 1 ∧
      k ≤ (C.walk c).edges.length := by
  rcases C.mem_supportArray.mp he with ⟨t, _, _, heq⟩ | ⟨c', hc, k', hk, heq⟩
  · cases heq
  cases heq
  have hpos := (C.mem_positionsOn.mp hk).1
  have hw := (hC.2 c hc).2.2
  rcases hw.2.2 with ⟨hV, _, _⟩ | ⟨_, hV, _⟩
  · simp [hV] at hpos
  · exact ⟨hc, hV, by omega⟩

/-- The walk prefix available to an attachment, in the direction requested by the caller. -/
@[expose] def attachmentCopy (C : ConnectorSystem) (fwd : Bool) : SupportEntry → Walk
  | .term _ => Walk.empty
  | .onWalk c k => if k = 0 then Walk.empty
    else copyWalk ((C.walk c).verts.take (k + 1)) ((C.walk c).edges.take k) fwd

/-- Number of steps specified by the support entry. -/
@[expose] def attachmentLength : SupportEntry → ℕ
  | .term _ => 0
  | .onWalk _ k => k

/-- The procedure appends exactly the attachment's steps and preserves the other cells. -/
@[expose] def attachContract (X : HierConcrete) (b v outE outY cnt : ℕ) (fwd : Bool) : Contract where
  pre args mem := args = [b, v, if fwd then 1 else 0, outE, outY, cnt] ∧ v < X.n ∧
    X.H.entryAt X.ms.st v ∈ X.H.A.C.supportArray v ∧ ListAt mem b X.encode
  post _ mem r mem' :=
    let e := X.H.entryAt X.ms.st v
    let ss := Walk.steps (attachmentCopy X.H.A.C fwd e)
    r = X.H.A.C.entryTerm e ∧ ListAt mem' (outE + cnt) (ss.map Prod.fst) ∧
      ListAt mem' (outY + cnt) (ss.map Prod.snd) ∧
      ∀ a, CopyOutside outE outY cnt (attachmentLength e) a → mem' a = mem a
  cost _ _ := 60 * attachmentLength (X.H.entryAt X.ms.st v) + 1000

/-- Copying a support prefix gives the attachment walk in either direction. -/
theorem attachmentCopy_eq (C : ConnectorSystem) {G : Cited.Graph} (hC : C.FitsGraph G)
    {v : ℕ} {entry : SupportEntry} (he : entry ∈ C.supportArray v) (fwd : Bool) :
    attachmentCopy C fwd entry = if fwd then (C.supportWalk entry).reverse else C.supportWalk entry := by
  cases entry with
  | term t => cases fwd <;> rfl
  | onWalk c k =>
    by_cases hk : k = 0
    · subst k
      cases fwd <;> simp [attachmentCopy, ConnectorSystem.supportWalk, Walk.prefix_eq,
        ofSteps, Walk.reverse, Walk.empty]
    obtain ⟨_, hV, hlen⟩ := support_onWalk_bounds C hC he
    have h := copyWalk_prefix hV (Nat.pos_of_ne_zero hk) hlen
    cases fwd
    · simpa [ConnectorSystem.supportWalk, attachmentCopy, hk] using h
    · have hr := congrArg Walk.reverse h
      simpa [ConnectorSystem.supportWalk, attachmentCopy, hk, copyWalk, Walk.reverse] using hr

private theorem attachWord_pre {X : HierConcrete} {b v k : ℕ} {mem : ℕ → ℕ}
    (hv : v < X.n) (hk : k < 3) (h : ListAt mem b X.encode) :
    (entryWordContract X b).pre [b, v, k] mem :=
  ⟨v, k, rfl, hv, hk, h⟩

set_option maxHeartbeats 3500000 in
/-- The support attachment procedure meets its buffer and time contract. -/
theorem attachProc_meetsContract {w : ℕ} {p : Program} {f fEntry fCopy : ℕ}
    (hp : p.procs[f]? = some (attachProc fEntry fCopy))
    (hpe : p.procs[fEntry]? = some entryWordProc) (hpc : p.procs[fCopy]? = some copyProc)
    {X : HierConcrete} {b v outE outY cnt cap : ℕ} {fwd : Bool}
    (hC : X.H.A.C.FitsGraph X.ms.abs.G)
    (hblock : b + X.encode.length ≤ outE)
    (hcap : cnt + attachmentLength (X.H.entryAt X.ms.st v) ≤ cap)
    (hbuf : outE + cap ≤ outY) (hwOut : outY + cap < 2 ^ w) :
    MeetsContract w p f (attachContract X b v outE outY cnt fwd) := by
  refine meetsContract_of_runs hp fun args mem pos ω hargs hpre => ?_
  obtain ⟨rfl, hv, hentry, h⟩ := hpre
  have hw : b + X.encode.length < 2 ^ w := by omega
  have hvw := hargs v (by simp)
  have hlen : 25 ≤ X.encode.length := by
    simp [HierConcrete.encode, layoutList, csrList, csrOffsets]
  have hw3 : 3 < 2 ^ w := by omega
  have hEnt := entryWordProc_meetsContract hpe hw
  refine runs_start_le ?_
  unfold attachProc secExpr startState
  wram_step
  · exact attachWord_pre (k := 0) hv (by decide) h
  intro tag m₁ p₁ htag
  obtain ⟨hm₁, htag⟩ := htag
  subst m₁
  have ht := htag v 0 rfl
  subst tag
  wram_step
  · exact attachWord_pre (k := 1) hv (by decide) h
  intro ident m₂ p₂ hid
  obtain ⟨hm₂, hid⟩ := hid
  subst m₂
  have hi := hid v 1 rfl
  subst ident
  cases he : X.H.entryAt X.ms.st v with
  | term t =>
    simp only [HierConcrete.entryWord, he, entryWords, List.getD_cons_zero,
      List.getD_cons_succ]
    wram_step
    · refine runs_seq_ret_le (by eval_expr) ?_ ?_
      · simp [attachContract, he, attachmentCopy, ConnectorSystem.entryTerm,
          Walk.steps, Walk.empty, ListAt, Outcome.value]
      · simp only [attachContract, he, attachmentLength, entryWordContract]
        wram_cost
  | onWalk c k =>
    simp only [HierConcrete.entryWord, he, entryWords, List.getD_cons_zero,
      List.getD_cons_succ]
    have hBounds := support_onWalk_bounds X.H.A.C hC (he ▸ hentry)
    obtain ⟨hc, hV, hk⟩ := hBounds
    wram_step
    wram_step
    wram_step
    · exact attachWord_pre (k := 2) hv (by decide) h
    intro n m₃ p₃ hpos
    obtain ⟨hm₃, hpos⟩ := hpos
    subst m₃
    have hn := hpos v 2 rfl
    rw [HierConcrete.entryWord, he] at hn
    change n = k at hn
    subst n
    obtain ⟨hEnd, hEndEnd⟩ := block_sec h (i := 2) (by decide)
    change ListAt mem _ (tabList X.H.A.C.numConn X.H.A.C.endA) at hEnd
    change _ + (tabList X.H.A.C.numConn X.H.A.C.endA).length ≤ _ at hEndEnd
    rw [length_tabList] at hEndEnd
    generalize hB2 : b + 25 + mem (b + 2) = B2 at hEnd hEndEnd
    have hTerm := listAt_tabList hEnd hc
    have hB2c : b + 25 + mem (b + 2) + c < 2 ^ w := by omega
    wram_step
    simp only [hB2, hTerm]
    wram_step
    · have hk0 : k = 0 := by assumption
      refine runs_seq_ret_le (by eval_expr) ?_ ?_
      · simp [attachContract, he, attachmentCopy, hk0, ConnectorSystem.entryTerm,
          Walk.steps, Walk.empty, ListAt, Outcome.value]
      · simp only [attachContract, he, attachmentLength, entryWordContract]
        wram_cost
    have hk0 : k ≠ 0 := by assumption
    wram_step
    obtain ⟨hL0, hE0⟩ := block_sec h (i := 0) (by decide)
    obtain ⟨hL10, hE10⟩ := block_sec h (i := 10) (by decide)
    obtain ⟨hL11, hE11⟩ := block_sec h (i := 11) (by decide)
    change ListAt mem _ X.header at hL0
    change _ + X.header.length ≤ _ at hE0
    change ListAt mem _ (csrList X.H.A.C.numConn fun i => (X.H.A.C.walk i).verts) at hL10
    change ListAt mem _ (csrList X.H.A.C.numConn fun i => (X.H.A.C.walk i).edges) at hL11
    change _ + (csrList X.H.A.C.numConn fun i => (X.H.A.C.walk i).verts).length ≤ _ at hE10
    change _ + (csrList X.H.A.C.numConn fun i => (X.H.A.C.walk i).edges).length ≤ _ at hE11
    have hlenH : X.header.length = 15 := rfl
    have hN : mem (b + 25 + mem (b + 0) + 3) = X.H.A.C.numConn := hL0 3 (by simp [HierConcrete.header])
    generalize hB10 : b + 25 + mem (b + 10) = B10 at hL10 hE10
    generalize hB11 : b + 25 + mem (b + 11) = B11 at hL11 hE11
    obtain ⟨hVoff, _, hVmem, hVend⟩ := csr_reads hL10 hc
    obtain ⟨hEoff, _, hEmem, hEend⟩ := csr_reads hL11 hc
    let V := ((X.H.A.C.walk c).verts.take (k + 1))
    let Ed := ((X.H.A.C.walk c).edges.take k)
    let va := B10 + (X.H.A.C.numConn + 1) +
      ((List.range c).map fun i => (X.H.A.C.walk i).verts.length).sum
    let ea := B11 + (X.H.A.C.numConn + 1) +
      ((List.range c).map fun i => (X.H.A.C.walk i).edges.length).sum
    have hkv : k + 1 ≤ (X.H.A.C.walk c).verts.length := by omega
    have hlV : V.length = k + 1 := by simp [V, Nat.min_eq_left hkv]
    have hlE : Ed.length = k := by simp [Ed, Nat.min_eq_left hk]
    have hva : va + k + 1 ≤ outE := by dsimp [va]; omega
    have hea : ea + k ≤ outE := by dsimp [ea]; omega
    have hcnt : cnt + k ≤ cap := by simpa only [he, attachmentLength] using hcap
    have hCopy := copyProc_meetsContract (w := w) hpc
      (vA := va) (eA := ea) (V := V) (Ed := Ed)
      (outE := outE) (outY := outY) (cnt := cnt) (fwd := fwd)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    wram_step
    simp only [hN]
    wram_step
    simp only [hB10]
    wram_step
    simp only [hB11]
    wram_step
    simp only [hVoff]
    wram_step
    simp only [hEoff]
    wram_step
    · have hflag : (if fwd then 1 else 0) < 2 ^ w := by split <;> omega
      wram_words
    · change [va, ea, k, if fwd then 1 else 0, outE, outY, cnt] =
        [va, ea, Ed.length, if fwd then 1 else 0, outE, outY, cnt] ∧ _
      refine ⟨by rw [hlE], Or.inr (by omega), hVmem.take _, hEmem.take _, ?_, ?_, by omega⟩
      · intro i hi
        unfold CopyOutside
        constructor <;> left <;> omega
      · intro i hi
        unfold CopyOutside
        constructor <;> left <;> omega
    intro r m₄ p₄ hPost
    obtain ⟨_, hEwrite, hVwrite, hframe⟩ := hPost
    refine runs_ret_le (by eval_expr) ?_ ?_
    · simp only [attachContract, he, attachmentCopy, hk0, ↓reduceIte,
        attachmentLength, ConnectorSystem.entryTerm, Outcome.value]
      exact ⟨trivial, hEwrite, hVwrite, by simpa only [hlE] using hframe⟩
    · simp only [attachContract, he, attachmentLength, copyContract, hlE, entryWordContract]
      wram_cost

end

end MinCostFlow.HierPaths
