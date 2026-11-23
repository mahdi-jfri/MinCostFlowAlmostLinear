module

public import MinCostFlow.HierPaths.DelProgPush

/-!
# Scanning one terminal's incident connectors

The loop visits each word in the interval for one terminal. Its invariant records the set
of connectors already visited and the first-visit order of the new ones.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The concrete state after visiting a list of incident connectors. -/
def HierConcrete.markIneligList (x : HierConcrete) (cs : List ℕ) : HierConcrete :=
  x.withSt { x.ms.st with inelig := x.ms.st.inelig ∪ cs.toFinset }

theorem HierConcrete.markIneligList_nil (x : HierConcrete) :
    x.markIneligList [] = x := by simp [markIneligList, withSt]

theorem HierConcrete.markIneligList_append_one (x : HierConcrete) (cs : List ℕ) (c : ℕ) :
    x.markIneligList (cs ++ [c]) = (x.markIneligList cs).markInelig c := by
  simp only [markIneligList, markInelig, withSt, List.toFinset_append, List.toFinset_cons,
    List.toFinset_nil]
  congr 3
  ext j
  simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
  tauto

theorem HierConcrete.length_encode_markIneligList (x : HierConcrete) (cs : List ℕ) :
    (x.markIneligList cs).encode.length = x.encode.length := by
  induction cs using List.reverseRecOn with
  | nil => rw [x.markIneligList_nil]
  | append_singleton cs c ih =>
    rw [x.markIneligList_append_one, HierConcrete.length_encode_markInelig, ih]

theorem HierConcrete.section7_markIneligList (x : HierConcrete) (cs : List ℕ) :
    (x.markIneligList cs).sections.getD 7 [] = x.sections.getD 7 [] := rfl

/-- Iterate over the incident-list word interval in registers `29` and `30`. -/
def delIncidentLoop : Stmt := forRange 35 (.reg 29) (.reg 30) delConnAt

theorem delIncidentLoop_noRand : delIncidentLoop.NoRand := by
  simp [delIncidentLoop, forRange, forUp, Stmt.NoRand, delConnAt_noRand]

/-- The loop state after processing the first `i - lo` words. -/
def DelIncidentInv (x : HierConcrete) (b base lo : ℕ) (cs L : List ℕ) (mem0 : ℕ → ℕ)
    (i : ℕ) (s : State) : Prop :=
  let visited := cs.take (i - lo)
  let out := L ++ delCollect x.ms.st.inelig visited
  s.regs 35 = i ∧ s.regs 0 = b ∧ s.regs 30 = lo + cs.length ∧ s.regs 33 = base ∧
  s.regs 34 = out.length ∧
  ListAt s.mem b (x.markIneligList visited).encode ∧ ListAt s.mem base out ∧
  ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
    (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j

theorem delCollect_length_le (S : Finset ℕ) (cs : List ℕ) :
    (delCollect S cs).length ≤ cs.length := by
  induction cs generalizing S with
  | nil => simp [delCollect]
  | cons c cs ih =>
    by_cases hc : c ∈ S
    · exact (by simpa [delCollect, hc] using (ih S).trans (Nat.le_succ cs.length))
    · simpa [delCollect, hc] using Nat.succ_le_succ (ih (insert c S))

/-- A single loop iteration reads one connector, marks it, and extends the invariant. -/
theorem delIncidentBody_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base lo i : ℕ} {cs L : List ℕ} {mem0 : ℕ → ℕ}
    (hword : ∀ k (hk : k < cs.length), ∃ h : lo + k < (x.sections.getD 7 []).length,
      (x.sections.getD 7 [])[lo + k] = cs[k])
    (hcs : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hdisj : b + x.encode.length ≤ base) (hw : base + L.length + cs.length < 2 ^ w)
    (hlo : lo ≤ i) (hi : i < lo + cs.length) :
    Triple w p (DelIncidentInv x b base lo cs L mem0 i) delConnAt
      (normalPost fun s => DelIncidentInv x b base lo cs L mem0 (i + 1)
        { s with regs := Function.update s.regs 35 (i + 1) } ∧ s.regs 35 = i)
      (fun _ => 90) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = lo + k := ⟨i - lo, by omega⟩
  have hk : k < cs.length := by omega
  obtain ⟨hwk, hread⟩ := hword k hk
  let c := cs[k]
  let visited := cs.take k
  let out := L ++ delCollect x.ms.st.inelig visited
  let y := x.markIneligList visited
  have hlen : y.encode.length = x.encode.length := x.length_encode_markIneligList _
  have hsub : lo + k - lo = k := by omega
  have hsub' : lo + k + 1 - lo = k + 1 := by omega
  have htake : cs.take (k + 1) = visited ++ [c] := List.take_succ_eq_append_getElem hk
  have hmark : x.markIneligList (cs.take (k + 1)) = y.markInelig c := by
    rw [htake, x.markIneligList_append_one]
  have hout : L ++ delCollect x.ms.st.inelig (cs.take (k + 1)) =
      out ++ delCollect y.ms.st.inelig [c] := by
    rw [htake, delCollect_append, ← List.append_assoc]
    rfl
  have hcnt : out.length ≤ L.length + k := by
    simp only [out, List.length_append]
    have h := (delCollect_length_le x.ms.st.inelig visited).trans (List.length_take_le _ _)
    omega
  have hsec : y.sections.getD 7 [] = x.sections.getD 7 [] := x.section7_markIneligList _
  have hyword : lo + k < (y.sections.getD 7 []).length := by rwa [hsec]
  have hyread : (y.sections.getD 7 [])[lo + k] = c := by simpa only [hsec] using hread
  intro s ω hs
  simp only [DelIncidentInv, hsub] at hs
  obtain ⟨hr, h0, h30, h33, h34, hb, hL, hf⟩ := hs
  have hd : b + y.encode.length ≤ base := by rwa [hlen]
  have hww : base + out.length + 1 < 2 ^ w := by omega
  have H := delConnAt_triple (w := w) (p := p) (mem0 := s.mem) (R := s.regs)
    (L := out) y h0 hr h33 h34 hyword hyread (hcs c (List.getElem_mem hk)) hd hww
  obtain ⟨o, s', d, hrun, hpost, hd'⟩ := H s ω ⟨rfl, hb, hL, rfl⟩
  cases o <;> try contradiction
  obtain ⟨hreg, hblock, hlist, hframe⟩ := hpost
  refine ⟨_, s', d, hrun, ?_, hd'⟩
  change DelIncidentInv x b base lo cs L mem0 (lo + k + 1) _
    ∧ s'.regs 35 = lo + k
  have hnext : out.length ≤ (out ++ delCollect y.ms.st.inelig [c]).length := by simp
  simp only [DelIncidentInv, hsub', hmark, hout]
  refine ⟨⟨by simp, ?_, ?_, ?_, ?_, hblock, hlist, ?_⟩, ?_⟩
  · simpa [hreg] using h0
  · simpa [hreg] using h30
  · simpa [hreg] using h33
  · simp [hreg]
  · intro j hj hscratch
    change j < base + L.length ∨ base + (out ++ delCollect y.ms.st.inelig [c]).length ≤ j at hscratch
    change ∀ j, _ → (j < base + L.length ∨ base + out.length ≤ j) → _ at hf
    have hLle : L.length ≤ out.length := by simp [out]
    have hj' : j < b ∨ b + y.encode.length ≤ j := by rwa [hlen]
    rw [hframe j hj' (by omega)]
    exact hf j hj (by omega)
  · simpa [hreg] using hr

/-- Scan the entire incident list in time linear in its length. -/
theorem delIncidentLoop_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base lo : ℕ} {cs L : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h29 : R 29 = lo) (h30 : R 30 = lo + cs.length)
    (h33 : R 33 = base) (h34 : R 34 = L.length)
    (hword : ∀ k (hk : k < cs.length), ∃ h : lo + k < (x.sections.getD 7 []).length,
      (x.sections.getD 7 [])[lo + k] = cs[k])
    (hcs : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hdisj : b + x.encode.length ≤ base) (hw : base + L.length + cs.length < 2 ^ w)
    (hhi : lo + cs.length < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0) delIncidentLoop
      (normalPost fun s =>
        let out := L ++ delCollect x.ms.st.inelig cs
        s.regs 0 = b ∧ s.regs 33 = base ∧ s.regs 34 = out.length ∧
        ListAt s.mem b (x.markIneligList cs).encode ∧ ListAt s.mem base out ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => 99 * cs.length + 7) := by
  have hone : 1 < 2 ^ w := by have := x.le_length_encode; omega
  have H := Triple.forRange_const (w := w) (p := p) (r := 35) (lo := .reg 29)
    (hi := .reg 30) (body := delConnAt) (Inv := DelIncidentInv x b base lo cs L mem0) 90 lo
    (lo + cs.length) (Nat.le_add_right ..) hone (fun _ => hhi)
    (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0)
    (fun s hs => ⟨Expr.eval_reg_of_eq (hs.1 ▸ h29), ?_⟩)
    (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ hlo hi => delIncidentBody_triple x hword hcs hdisj hw hlo hi)
  · refine (H.strengthen_post fun o s h => ?_).mono_cost fun _ _ => by
      simp [Expr.size, Nat.mul_comm]
    cases o <;> try contradiction
    have hs : lo + cs.length - lo = cs.length := by omega
    change DelIncidentInv x b base lo cs L mem0 (lo + cs.length) s at h
    simp only [DelIncidentInv, hs, List.take_length] at h
    exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · obtain ⟨hr, hb, hL, hm⟩ := hs
    simp only [DelIncidentInv, Nat.sub_self, List.take_zero, delCollect, List.append_nil,
      x.markIneligList_nil]
    refine ⟨by simp, ?_, ?_, ?_, ?_, hb, hL, fun j _ _ => congrFun hm j⟩
    · simpa [hr] using h0
    · simpa [hr] using h30
    · simpa [hr] using h33
    · simpa [hr] using h34

/-- Set up and run the incident scan of the terminal in register `28`. -/
def delTerminalConns : Stmt := .seq delTermSetup delIncidentLoop

theorem delTerminalConns_noRand : delTerminalConns.NoRand := by
  simp [delTerminalConns, delTermSetup, Stmt.NoRand, delCsrSetup_noRand, delIncidentLoop_noRand]

/-- Mark and collect the incident connectors of one newly lost terminal. -/
theorem delTerminalConns_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base t : ℕ} {L : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h28 : R 28 = t) (h33 : R 33 = base) (h34 : R 34 = L.length)
    (ht : t < x.H.A.C.numTerm)
    (hcs : ∀ c ∈ x.H.A.termConns t, c < x.H.A.C.numConn)
    (hdisj : b + x.encode.length ≤ base)
    (hw : base + L.length + (x.H.A.termConns t).length < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0) delTerminalConns
      (normalPost fun s =>
        let cs := x.H.A.termConns t
        let out := L ++ delCollect x.ms.st.inelig cs
        s.regs 0 = b ∧ s.regs 33 = base ∧ s.regs 34 = out.length ∧
        ListAt s.mem b (x.markIneligList cs).encode ∧ ListAt s.mem base out ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => 99 * (x.H.A.termConns t).length + 88) := by
  let lo := delCsrStart x.H.A.C.numTerm x.H.A.termConns t
  let cs := x.H.A.termConns t
  have hb : b + x.encode.length < 2 ^ w := by omega
  have hsec : x.sections.getD 7 [] = csrList x.H.A.C.numTerm x.H.A.termConns := rfl
  have hword : ∀ k (hk : k < cs.length), ∃ h : lo + k < (x.sections.getD 7 []).length,
      (x.sections.getD 7 [])[lo + k] = cs[k] := by
    intro k hk
    have h : lo + k < (x.sections.getD 7 []).length := by
      rw [hsec]
      exact csrList_data_lt x.H.A.termConns ht hk
    refine ⟨h, ?_⟩
    rw [← List.getD_eq_getElem _ _ h, hsec]
    rw [show lo + k = x.H.A.C.numTerm + 1 +
      ((List.range t).map fun i => (x.H.A.termConns i).length).sum + k from rfl]
    rw [csrList_getD_data _ ht hk, List.getD_eq_getElem _ _ hk]
  have hhi : lo + cs.length < 2 ^ w := by
    have hs : lo + cs.length ≤ (x.sections.getD 7 []).length := by
      rw [hsec, show lo + cs.length = delCsrStart x.H.A.C.numTerm x.H.A.termConns (t + 1)
        from (delCsrStart_succ ..).symm]
      exact delCsrStart_le _ _ ht
    have hpos : 0 < (x.sections.getD 7 []).length := by rw [hsec]; simp [csrList]
    have H := lt_length_of_sec (bs := x.sections) (i := 7)
      (by rw [x.length_sections']; norm_num)
      (k := (x.sections.getD 7 []).length - 1) (by omega)
    change _ < x.encode.length at H
    omega
  unfold delTerminalConns
  refine (Triple.seq_normal_const
    (delTermSetup_triple (M := fun mem => ListAt mem b x.encode ∧
      ListAt mem base L ∧ mem = mem0) x h0 h28 ht (fun _ h => h.1) hb)
    (delIncidentLoop_triple (lo := lo) (cs := cs) (L := L) x
      (by simpa using h0) (by simp [lo]) (by simp [lo, cs])
      (by simpa using h33) (by simpa using h34) hword hcs hdisj hw hhi)).mono_cost ?_
  intro s hs
  dsimp only [cs]
  omega

end MinCostFlow.HierPaths

end
