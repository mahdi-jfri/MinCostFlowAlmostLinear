module

public import MinCostFlow.HierPaths.DelProgEntryRefresh

/-!
# Starting the output part of Delete

The vertex output begins one word after the heap pointer. The report scans append to it,
using the descriptors retained across the cursor passes.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Initialize the length and base registers of the vertex output. -/
def delEntryOutputSetup : Stmt :=
  .seq (.assign 58 (.bin .add (.reg 70) (.const 1))) (.assign 59 (.const 0))

theorem delEntryOutputSetup_noRand : delEntryOutputSetup.NoRand := by
  simp [delEntryOutputSetup, Stmt.NoRand]

/-- Initialize the output registers and preserve memory. -/
theorem delEntryOutputSetup_triple {w : ℕ} {p : Program} {h : ℕ}
    {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop} (h70 : R 70 = h) (hw : h + 1 < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) delEntryOutputSetup
      (normalPost fun s => s.regs = Function.update (Function.update R 58 (h + 1)) 59 0 ∧ M s.mem)
      (fun _ => 7) := by
  exact Triple.seq_normal_const
    (triple_assign_exact fun _ hr _ => Expr.eval_add
      (Expr.eval_reg_of_eq (hr ▸ h70)) (Expr.eval_const (by omega)) hw)
    (triple_assign_exact fun _ _ _ => Expr.eval_const (Nat.two_pow_pos _))

/-- Report terminal owners first, then the vertices of the connector walks. -/
def delEntryReports : Stmt :=
  .seq delEntryOutputSetup
    (.seq (.seq (delReadWorkList 71 72 60 61) delOutputOwners)
      (.seq (delReadWorkList 73 74 67 68) delOutputConns))

theorem delEntryReports_noRand : delEntryReports.NoRand := by
  simp [delEntryReports, Stmt.NoRand, delEntryOutputSetup_noRand, delReadWorkList_noRand,
    delOutputOwners_noRand, delOutputConns_noRand]

private theorem delOutputConns_frame : Stmt.WritesBelow 70 delOutputConns := by
  simp [delOutputConns, forRange, forUp, delOutputWalk, delCsrSetup,
    delReportRead, delReportVertex, delReportTest, delCursorSetup, delVhatSet, delVertexPush,
    Stmt.WritesBelow]

/-- The cost of reporting visits, before header write and scratch cleanup. -/
def delEntryReportsCost (x : HierConcrete) (lost cs : List ℕ) : ℕ :=
  let y := x.afterReports (lost.map x.H.A.C.owner)
  lost.length * (delOutputOwnerExpr.size + 176) +
    rangeCost (delOutputConnCost y cs) 0 cs.length + cs.length * 9 + 35

/-- Run both reporting scans and retain the scratch descriptors for cleanup. -/
theorem delEntryReports_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b h wb cb : ℕ} {lost cs : List ℕ} {R mem0 : ℕ → ℕ}
    (h0 : R 0 = b) (hR : DelWorkRegs R h wb cb lost.length cs.length)
    (hb : b + x.encode.length ≤ h) (hwb : h + 1 + 2 * x.n ≤ wb) (hcb : wb ≤ cb)
    (hw : h + 1 + 3 * x.n + 1 < 2 ^ w)
    (hwl : wb + lost.length < 2 ^ w) (hwc : cb + cs.length < 2 ^ w)
    (ht : ∀ t ∈ lost, t < x.H.A.C.numTerm) (ho : ∀ t ∈ lost, x.H.A.C.owner t < x.n)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hv : ∀ c ∈ cs, ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n) :
    let vs := lost.map x.H.A.C.owner ++ x.walkPassVerts cs
    let L := x.delReports vs
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem wb lost ∧ ListAt s.mem cb cs ∧ s.mem = mem0) delEntryReports
      (normalPost fun s => s.regs 0 = b ∧ s.regs 59 = L.length ∧
        DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.afterReports vs).encode ∧ ListAt s.mem (h + 1) L ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < h + 1 ∨ h + 1 + L.length ≤ j) → s.mem j = mem0 j)
      (fun _ => delEntryReportsCost x lost cs) := by
  dsimp only
  let base := h + 1
  let owners := lost.map x.H.A.C.owner
  let walks := x.walkPassVerts cs
  let y := x.afterReports owners
  let L := x.delReports owners
  let L' := x.delReports (owners ++ walks)
  have hy : y.encode.length = x.encode.length := x.length_encode_withVhat _
  have hov : ∀ v ∈ owners, v < x.n := by
    intro v hm
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hm
    exact ho t ht'
  have hcap : L.length ≤ x.n := x.delReports_length_le hov
  have hL' : L' = L ++ y.delReports walks := x.delReports_append owners walks
  have hy' : x.afterReports (owners ++ walks) = y.afterReports walks :=
    x.afterReports_append owners walks
  let M := fun mem => ListAt mem b x.encode ∧ ListAt mem wb lost ∧ ListAt mem cb cs ∧ mem = mem0
  let R' := Function.update (Function.update R 58 base) 59 0
  let R'' := Function.update (Function.update R' 60 wb) 61 lost.length
  have H := delEntryOutputSetup_triple (w := w) (p := p) (M := M) hR.heap (by omega)
  have HR := delReadWorkList_triple (w := w) (p := p) (M := M) (dst := 60) (count := 61)
    (show R' 71 = wb by simpa [R'] using hR.lostBase)
    (show R' 72 = lost.length by simpa [R'] using hR.lostCount) (by decide)
  let Mid := fun s : State => s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = L.length ∧
    DelWorkRegs s.regs h wb cb lost.length cs.length ∧
    ListAt s.mem b y.encode ∧ ListAt s.mem base L ∧ ListAt s.mem cb cs ∧
    ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
      (j < base ∨ base + L.length ≤ j) → s.mem j = mem0 j
  have HO := delOutputOwners_triple (w := w) (p := p) (R := R'') (mem0 := mem0)
    (L := []) (ts := lost) (base := base) (src := wb) x (by simpa [R'', R'] using h0) (by simp [R'', R'])
    (by simp [R'', R']) (by simp [R'']) (by simp [R''])
    (by omega) (by simp only [List.length_nil, Nat.add_zero]; omega)
    (by simp only [List.length_nil, Nat.add_zero]; omega) hwl ht ho
  have HT : Triple w p (fun s => s.regs = R'' ∧ M s.mem) delOutputOwners
      (normalPost Mid) (fun _ => lost.length * (delOutputOwnerExpr.size + 176) + 7) := by
    intro s ω hs
    have hm : ListAt mem0 wb lost := hs.2.2.2.2 ▸ hs.2.2.1
    obtain ⟨o, t, c, hr, hp, hcost⟩ := HO hm s ω
      ⟨hs.1, hs.2.1, (fun _ hh => by simp at hh), hs.2.2.2.2⟩
    cases o <;> try contradiction
    obtain ⟨h0', h58', hl, he, hB, hList, hf⟩ := hp
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hl hList hf
    change ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
      (j < base ∨ base + L.length ≤ j) → t.mem j = mem0 j at hf
    have hsrc : base + L.length ≤ cb := by unfold base; omega
    refine ⟨_, t, c, hr, ⟨h0', h58', hl, hR.of_frame ?_, hB, hList, ?_, hf⟩, hcost⟩
    · intro j hj
      simpa [R'', R', Function.update_of_ne (show j ≠ 58 by omega),
        Function.update_of_ne (show j ≠ 59 by omega), Function.update_of_ne (show j ≠ 60 by omega),
        Function.update_of_ne (show j ≠ 61 by omega)] using he j (by omega)
    · refine listAt_congr (fun j _ => ?_) hs.2.2.2.1
      exact (congrFun hs.2.2.2.2 _).trans
        (hf (cb + j) (Or.inr (by omega)) (Or.inr (hsrc.trans (Nat.le_add_right ..)))).symm
  have End : Triple w p Mid (.seq (delReadWorkList 73 74 67 68) delOutputConns)
      (normalPost fun s => s.regs 0 = b ∧ s.regs 59 = L'.length ∧
        DelWorkRegs s.regs h wb cb lost.length cs.length ∧
        ListAt s.mem b (x.afterReports (owners ++ walks)).encode ∧ ListAt s.mem base L' ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base ∨ base + L'.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delOutputConnCost y cs) 0 cs.length + cs.length * 9 + 13) := by
    intro s ω hs
    obtain ⟨h0', h58', h59', hR', hB, hL, hC, hf⟩ := hs
    let S := Function.update (Function.update s.regs 67 cb) 68 cs.length
    let P := fun mem => ListAt mem b y.encode ∧ ListAt mem base L ∧ ListAt mem cb cs ∧ mem = s.mem
    have Read := delReadWorkList_triple (w := w) (p := p) (M := P) (dst := 67) (count := 68)
      hR'.connBase hR'.connCount (by decide)
    have hb' : b + y.encode.length ≤ base := (congrArg (b + ·) hy).le.trans (by omega)
    have hsep : base + L.length + y.n ≤ cb := by
      change base + L.length + x.n ≤ cb
      omega
    have hfit : base + L.length + 2 * y.n + 1 < 2 ^ w := by
      change base + L.length + 2 * x.n + 1 < 2 ^ w
      omega
    have HC := delOutputConns_triple (w := w) (p := p) (R := S) (mem0 := s.mem)
      (L := L) (cs := cs) (base := base) (src := cb) y (by simpa [S] using h0') (by simpa [S] using h58')
      (by simpa [S] using h59') (by simp [S]) (by simp [S]) hb' hsep hfit hwc hc hv
    have CF := Triple.regs_frame delOutputConns_frame HC S
    have Tail := CF.weaken_pre (fun t (ht : t.regs = S ∧ P t.mem) =>
      ⟨ht, fun j _ => congrFun ht.1 j⟩)
    obtain ⟨o, t, c, hr, hp, hcost⟩ := (Triple.seq_normal_const Read Tail) s ω
      ⟨rfl, hB, hL, hC, rfl⟩
    cases o <;> try exact False.elim hp.1
    obtain ⟨⟨h0'', _, h59'', hB', hList, hf'⟩, hg⟩ := hp
    change ∀ j, (j < b ∨ b + y.encode.length ≤ j) →
      (j < base + L.length ∨ base + (L ++ y.delReports walks).length ≤ j) →
        t.mem j = s.mem j at hf'
    rw [hy, ← hL'] at hf'
    have hle : L.length ≤ L'.length := by rw [hL']; simp
    refine ⟨_, t, c, hr, ?_, ?_⟩
    · exact ⟨h0'', hL'.symm ▸ h59'', hR'.of_frame (fun j hj => by
          simpa [S, Function.update_of_ne (show j ≠ 67 by omega),
            Function.update_of_ne (show j ≠ 68 by omega)] using hg j hj),
        hy'.symm ▸ hB', hL'.symm ▸ hList,
        fun j hj hOut => (hf' j hj (by omega)).trans (hf j hj (by omega))⟩
    · dsimp only at hcost ⊢
      omega
  unfold delEntryReports
  refine (Triple.seq_normal_const H
    (Triple.seq_normal_const (Triple.seq_normal_const HR HT) End)).mono_cost ?_
  intro s _
  unfold delEntryReportsCost
  dsimp only [y, owners]
  omega

end MinCostFlow.HierPaths

end
