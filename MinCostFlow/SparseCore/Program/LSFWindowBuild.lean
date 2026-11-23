module

public import MinCostFlow.SparseCore.Program.LSFWindowBuildEdges
import MinCostFlow.SparseCore.Program.LSFWindowRepackDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Top-Level Canonical Guest Memory Builder Verification (`LSFWindowBuild`)

Proves `buildCanonGuestProc_runs`: calling `buildCanonGuestProc` (index `bBuild + 5` of
`canonBuildProcs`) on a host `DynGraphAt mem g0Ptr vCap0 eCap0 G₀` and `L_in`-limb edge-length
array `lenArr` builds `canonGuestMem G₀ ℓ₀ h L_in P_fp` identically across
`[guestBase, guestBase + 2 ^ w')`, keeps `ZeroFrom st'.mem (guestBase + canonHandlesOut G₀ L_in)`
(hence `ZeroFrom st'.mem (guestBase + 2 ^ w')`), preserves all host memory below `guestBase`, and
runs in `≤ buildCanonGuestCost G₀.n G₀.m L_in` steps (no `vCap` or `eCap` scan).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

private lemma runs_seq_of_runs' {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt}
    {st st₁ : State} {c₁ k T : ℕ} {Q : Outcome → State → Prop}
    (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (h₂ : ∃ o st' c₂, Runs w p ω s₂ st₁ o st' c₂ ∧ Q o st' ∧ (k + c₁ + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h₂ with ⟨o, st', c₂, hr₂, hq, hc₂⟩
  exact ⟨o, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, hr₂, rfl⟩), hq, by omega⟩

set_option maxHeartbeats 600000 in
lemma buildCanonGuestProc_runs {w h bBuild bSort bCopy bFill g0Ptr vCap0 eCap0 lenArr L_in P_fp
    guestBase : ℕ}
    {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hLin1 : 1 ≤ L_in)
    (hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hℓ₀ : ∀ e ∈ G₀.E, Valid mem (lenArr + e * L_in) h L_in ∧
      fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ guestBase)
    (hlen_le : lenArr + eCap0 * L_in ≤ guestBase)
    (hz : ZeroFrom mem guestBase)
    (hsp_lt : guestBase + canonHandlesOut G₀ L_in + max G₀.n G₀.m < 2 ^ w)
    (hpBuild : p.HasAt bBuild (canonBuildProcs bBuild bSort bCopy bFill))
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hFill : MeetsContract w p bFill (memFillContract w)) :
    ∃ body st' c,
      p.procs[bBuild + 5]? = some body ∧
      Runs w p ω body (startState [g0Ptr, lenArr, L_in, guestBase] mem pos) (.returned 0) st' c ∧
      (∀ z < guestBase, st'.mem z = mem z) ∧
      (∀ a, st'.mem (guestBase + a) = canonGuestMem G₀ ℓ₀ h L_in P_fp a) ∧
      ZeroFrom st'.mem (guestBase + canonHandlesOut G₀ L_in) ∧
      c ≤ buildCanonGuestCost G₀.n G₀.m L_in := by
  set vCap := canonVCap G₀
  set eCap := canonECap G₀
  set dstLen := guestBase + canonLenArr G₀
  set scratch := guestBase + canonHandlesOut G₀ L_in
  have hsz_eq : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hsz_c : dynGraphSize (canonVCap G₀) (canonECap G₀) = 4 + 7 * vCap + 9 * eCap := rfl
  have hlen_eq : canonLenArr G₀ = dynGraphSize vCap eCap := rfl
  have hdst_eq : dstLen = guestBase + (4 + 7 * vCap + 9 * eCap) := rfl
  have heCap_mul : (canonECap G₀) * L_in = eCap * L_in := rfl
  have hscr_eq : scratch = guestBase + (4 + 7 * vCap + 9 * eCap) + eCap * L_in := by
    dsimp [scratch, canonHandlesOut, canonLenArr, dynGraphSize]; omega
  have hvL_clen : (canonVList G₀).length = G₀.n := G₀.V.length_sort (· ≤ ·)
  have heL_clen : (canonEList G₀).length = G₀.m := G₀.E.length_sort (· ≤ ·)
  have hsz0_eq : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
  have hcanonH_eq : canonHandlesOut G₀ L_in = dynGraphSize vCap eCap + eCap * L_in := rfl
  have hpPush : p.procs[bBuild + 0]? = some pushHalfEdgeProc :=
    hpBuild.get (i := 0) (by rw [canonBuildProcs_length]; decide)
  have hpMax : p.procs[bBuild + 1]? = some maxCapListProc :=
    hpBuild.get (i := 1) (by rw [canonBuildProcs_length]; decide)
  have hpVerts : p.procs[bBuild + 2]? = some buildCanonVertsProc :=
    hpBuild.get (i := 2) (by rw [canonBuildProcs_length]; decide)
  have hpEdges : p.procs[bBuild + 3]? = some (buildCanonEdgesProc bCopy) :=
    hpBuild.get (i := 3) (by rw [canonBuildProcs_length]; decide)
  have hpInc : p.procs[bBuild + 4]? = some (buildCanonIncProc (bBuild + 0)) :=
    hpBuild.get (i := 4) (by rw [canonBuildProcs_length]; decide)
  have hpTop : p.procs[bBuild + 5]? =
      some (buildCanonGuestProc bSort bCopy bFill (bBuild + 1) (bBuild + 2) (bBuild + 3) (bBuild + 4)) :=
    hpBuild.get (i := 5) (by rw [canonBuildProcs_length]; decide)
  obtain ⟨vL0, hvL0_len, hvL0_nd, hvL0_mem, hvL0_at, _⟩ := hdg0.2.2.2.2.2.2.2.2.1
  obtain ⟨eL0, heL0_len, heL0_nd, heL0_mem, heL0_at, _⟩ := hdg0.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hn_le0 : G₀.n ≤ vCap0 := (dynGraph_card_le hdg0).1
  have hm_le0 : G₀.m ≤ eCap0 := (dynGraph_card_le hdg0).2
  have hn_le : G₀.n ≤ vCap := by
    have hsub : G₀.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (canonVCap_gt hv)
    calc G₀.n = G₀.V.card := rfl
      _ ≤ (Finset.range vCap).card := Finset.card_le_card hsub
      _ = vCap := Finset.card_range vCap
  have hm_le : G₀.m ≤ eCap := by
    have hsub : G₀.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (canonECap_gt he)
    calc G₀.m = G₀.E.card := rfl
      _ ≤ (Finset.range eCap).card := Finset.card_le_card hsub
      _ = eCap := Finset.card_range eCap
  have hLin_lt : L_in < 2 ^ w := by
    have : 1 * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in (canonECap_pos G₀)
    omega
  have hvCap_eq : max 1 (vL0.foldl max 0 + 1) = vCap := by
    rw [foldl_max_eq_finset_sup hvL0_mem, max_eq_right (Nat.succ_pos _)]; rfl
  have heCap_eq : max 1 (eL0.foldl max 0 + 1) = eCap := by
    rw [foldl_max_eq_finset_sup heL0_mem]; rfl
  have hvL0_lt : ∀ x ∈ vL0, x + 1 < 2 ^ w := fun x hx => by
    have := canonVCap_gt ((hvL0_mem x).mp hx); omega
  have heL0_lt : ∀ x ∈ eL0, x + 1 < 2 ^ w := fun x hx => by
    have := canonECap_gt ((heL0_mem x).mp hx); omega
  suffices hmain : ∃ o st' c,
      Runs w p ω (buildCanonGuestProc bSort bCopy bFill (bBuild + 1) (bBuild + 2) (bBuild + 3) (bBuild + 4))
        (startState [g0Ptr, lenArr, L_in, guestBase] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (∀ z < guestBase, st'.mem z = mem z) ∧
        (∀ a, st'.mem (guestBase + a) = canonGuestMem G₀ ℓ₀ h L_in P_fp a) ∧
        ZeroFrom st'.mem scratch) ∧
      0 + c ≤ buildCanonGuestCost G₀.n G₀.m L_in by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2, h3⟩, hc⟩
    exact ⟨_, st', c, hpTop, hrun, h1, h2, h3, by omega⟩
  unfold buildCanonGuestProc startState
  refine runs_seq_assign_flat (v := vCap0)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, dgVCapOff,
      show g0Ptr < 2 ^ w by omega]) hdg0.2.2.2.1) ?_
  refine runs_seq_assign_flat (v := eCap0)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, dgECapOff,
      show 1 < 2 ^ w by omega, show g0Ptr + 1 < 2 ^ w by omega]) hdg0.2.2.2.2.1) ?_
  refine runs_seq_assign_flat (v := G₀.n)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, dgNOff,
      show 2 < 2 ^ w by omega, show g0Ptr + 2 < 2 ^ w by omega]) hdg0.2.2.2.2.2.1) ?_
  refine runs_seq_assign_flat (v := G₀.m)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, dgMOff,
      show 3 < 2 ^ w by omega, show g0Ptr + 3 < 2 ^ w by omega]) hdg0.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_flat (v := dgVListBase g0Ptr vCap0)
    (by simp [Expr.eval, BinOp.eval, dgVListBase, show 4 < 2 ^ w by omega,
      show g0Ptr + 4 < 2 ^ w by omega, show g0Ptr + 4 + vCap0 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := dgEListBase g0Ptr vCap0 eCap0)
    (by simp [Expr.eval, BinOp.eval, dgEListBase, show 4 < 2 ^ w by omega,
      show 7 < 2 ^ w by omega, show g0Ptr + 4 < 2 ^ w by omega, show 7 * vCap0 < 2 ^ w by omega,
      show g0Ptr + 4 + 7 * vCap0 < 2 ^ w by omega, show g0Ptr + 4 + 7 * vCap0 + eCap0 < 2 ^ w by omega]) ?_
  -- Call maxCapListProc for vCap and eCap
  refine runs_seq_call_body_flat hpMax (vs := [dgVListBase g0Ptr vCap0, G₀.n])
    (P_call := fun ret st1 => ret = vCap ∧ st1.mem = mem) (c1_max := 30 * G₀.n + 25)
    (by simp [evalArgs, Expr.eval])
    (by obtain ⟨stM1, cM1, hrunM1, hmM1, hcM1⟩ :=
          maxCapListProc_runs (p := p) (ω := ω) (mem := mem) (pos := pos)
            (arr := dgVListBase g0Ptr vCap0) (L := vL0)
            hw16 (by dsimp [dgVListBase]; omega) hvL0_at hvL0_lt
        rw [hvL0_len, hvCap_eq] at hrunM1; rw [hvL0_len] at hcM1
        exact ⟨vCap, stM1, cM1, hrunM1, ⟨rfl, hmM1⟩, hcM1⟩)
    (fun retM1 stM1 ⟨hretM1, hmM1⟩ => ?_)
  subst hretM1; rw [hmM1]
  refine runs_seq_call_body_flat hpMax (vs := [dgEListBase g0Ptr vCap0 eCap0, G₀.m])
    (P_call := fun ret st1 => ret = eCap ∧ st1.mem = mem) (c1_max := 30 * G₀.m + 25)
    (by simp [evalArgs, Expr.eval])
    (by obtain ⟨stM2, cM2, hrunM2, hmM2, hcM2⟩ :=
          maxCapListProc_runs (p := p) (ω := ω) (mem := mem) (pos := stM1.pos)
            (arr := dgEListBase g0Ptr vCap0 eCap0) (L := eL0)
            hw16 (by dsimp [dgEListBase]; omega) heL0_at heL0_lt
        rw [heL0_len, heCap_eq] at hrunM2; rw [heL0_len] at hcM2
        exact ⟨eCap, stM2, cM2, hrunM2, ⟨rfl, hmM2⟩, hcM2⟩)
    (fun retM2 stM2 ⟨hretM2, hmM2⟩ => ?_)
  subst hretM2; rw [hmM2]
  -- Store 4 header words at guestBase + 0..3
  refine runs_seq_store_flat (x := guestBase + 0) (v := vCap)
    (by simp [Expr.eval, BinOp.eval, dgVCapOff, show guestBase < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_flat (x := guestBase + 1) (v := eCap)
    (by simp [Expr.eval, BinOp.eval, dgECapOff, show 1 < 2 ^ w by omega, show guestBase + 1 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_flat (x := guestBase + 2) (v := G₀.n)
    (by simp [Expr.eval, BinOp.eval, dgNOff, show 2 < 2 ^ w by omega, show guestBase + 2 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_flat (x := guestBase + 3) (v := G₀.m)
    (by simp [Expr.eval, BinOp.eval, dgMOff, show 3 < 2 ^ w by omega, show guestBase + 3 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  set memH := Function.update (Function.update (Function.update (Function.update mem
    (guestBase + 0) vCap) (guestBase + 1) eCap) (guestBase + 2) G₀.n) (guestBase + 3) G₀.m
  refine runs_seq_assign_flat (v := dstLen)
    (by simp [Expr.eval, BinOp.eval, dstLen, canonLenArr, dynGraphSize,
      show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, show 9 < 2 ^ w by omega,
      show guestBase + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
      show guestBase + 4 + 7 * vCap < 2 ^ w by omega, show 9 * eCap < 2 ^ w by omega,
      show guestBase + 4 + 7 * vCap + 9 * eCap < 2 ^ w by omega]; omega) ?_
  have hscr_dst : dstLen + eCap * L_in = scratch := by omega
  refine runs_seq_assign_flat (v := scratch)
    (by simp [Expr.eval, BinOp.eval, show eCap * L_in < 2 ^ w by omega, hscr_dst]; omega) ?_
  refine runs_seq_assign_flat (v := dgVListBase guestBase vCap)
    (by simp [Expr.eval, BinOp.eval, dgVListBase, show 4 < 2 ^ w by omega,
      show guestBase + 4 < 2 ^ w by omega, show guestBase + 4 + vCap < 2 ^ w by omega]) ?_
  -- Copy, sort, zero scratch for vList
  refine runs_seq_call_flat hCopy
    (vs := [dgVListBase guestBase vCap, dgVListBase g0Ptr vCap0, G₀.n])
    (by simp [evalArgs, Expr.eval])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · dsimp [dgVListBase]; omega
        · dsimp [dgVListBase]; omega
        · omega)
    ⟨dgVListBase guestBase vCap, dgVListBase g0Ptr vCap0, G₀.n, rfl,
      by dsimp [dgVListBase]; omega, by dsimp [dgVListBase]; omega,
      Or.inr (by dsimp [dgVListBase]; omega)⟩ ?_
  intro ret1 mem1 pos1 hpost1
  rcases hpost1 with ⟨_, _, _, hEq1, rfl, hcp1, hfr1⟩
  simp only [List.cons.injEq, and_true] at hEq1; rcases hEq1 with ⟨rfl, rfl, rfl⟩
  have hvL_mem1 : ListAt mem1 (dgVListBase guestBase vCap) vL0 := fun i hi => by
    have h1 := hcp1 i (by omega)
    rw [h1]
    dsimp only [memH]
    rw [Function.update_of_ne (by dsimp [dgVListBase]; omega),
        Function.update_of_ne (by dsimp [dgVListBase]; omega),
        Function.update_of_ne (by dsimp [dgVListBase]; omega),
        Function.update_of_ne (by dsimp [dgVListBase]; omega)]
    exact hvL0_at i hi
  have hSortV := mergeSort_meetsContract (w := w) (L := vL0) hpSort hpSort
  refine runs_seq_call_flat hSortV
    (vs := [dgVListBase guestBase vCap, vL0.length, scratch])
    (by simp [evalArgs, Expr.eval, hvL0_len])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · dsimp [dgVListBase]; omega
        · omega
        · omega)
    ⟨dgVListBase guestBase vCap, scratch, rfl, hw16,
      by dsimp [dgVListBase]; omega, by dsimp [scratch]; omega,
      Or.inl (by dsimp [dgVListBase, scratch]; omega), hvL_mem1,
      fun x hx => by have := hvL0_lt x hx; omega⟩ ?_
  intro ret2 mem2 pos2 hpost2
  rcases hpost2 with ⟨_, _, vL_sorted, hEq2, rfl, hpermV, hpairV, hvL_at2, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEq2; rcases hEq2 with ⟨rfl, _, rfl⟩
  have hvL_eq : vL_sorted = canonVList G₀ := eq_finset_sort_of_perm hvL0_nd hvL0_mem hpermV hpairV
  subst hvL_eq
  refine runs_seq_call_flat hFill
    (vs := [scratch, G₀.n, 0])
    (by simp [evalArgs, Expr.eval, show 0 < 2 ^ w by omega])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> omega)
    ⟨scratch, G₀.n, 0, rfl, by omega⟩ ?_
  intro ret3 mem3 pos3 hpost3
  rcases hpost3 with ⟨_, _, _, hEq3, rfl, hfill3, hfr3⟩
  simp only [List.cons.injEq, and_true] at hEq3; rcases hEq3 with ⟨rfl, rfl, rfl⟩
  have hvL_at3 : ListAt mem3 (dgVListBase guestBase vCap) (canonVList G₀) := fun i hi => by
    rw [hfr3 _ (Or.inl (by dsimp [dgVListBase, scratch]; omega))]
    exact hvL_at2 i hi
  -- Call buildCanonVertsProc
  refine runs_seq_call_body_flat hpVerts (vs := [guestBase, vCap, G₀.n])
    (P_call := fun _ stV =>
      (∀ v ∈ G₀.V,
        stV.mem (dgVPresBase guestBase + v) = 1 ∧
        stV.mem (dgVPosBase guestBase vCap + v) = (canonVList G₀).idxOf v ∧
        stV.mem (dgExtToIntBase guestBase vCap + v) = v ∧
        stV.mem (dgIntToExtBase guestBase vCap + v) = v) ∧
      (∀ addr,
        (∀ v ∈ G₀.V, addr ≠ dgVPresBase guestBase + v ∧ addr ≠ dgVPosBase guestBase vCap + v ∧
          addr ≠ dgExtToIntBase guestBase vCap + v ∧ addr ≠ dgIntToExtBase guestBase vCap + v) →
        stV.mem addr = mem3 addr))
    (c1_max := 50 * G₀.n + 80)
    (by simp [evalArgs, Expr.eval])
    (by obtain ⟨stV, cV, hrunV, hvSet, hfrV, hcV⟩ :=
          buildCanonVertsProc_runs (p := p) (ω := ω) (mem := mem3) (pos := pos3)
            hw16 (by omega) hvL_at3
        exact ⟨0, stV, cV, hrunV, ⟨hvSet, hfrV⟩, hcV⟩)
    (fun _ stV ⟨hvSet, hfrV⟩ => ?_)
  -- Copy, sort, zero scratch for eList
  refine runs_seq_assign_flat (v := dgEListBase guestBase vCap eCap)
    (by simp [Expr.eval, BinOp.eval, dgEListBase, show 4 < 2 ^ w by omega,
      show 7 < 2 ^ w by omega, show guestBase + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
      show guestBase + 4 + 7 * vCap < 2 ^ w by omega, show guestBase + 4 + 7 * vCap + eCap < 2 ^ w by omega]) ?_
  have hmem_below_V : ∀ z < guestBase, stV.mem z = mem z := fun z hz' => by
    rw [hfrV z (fun v _ => by dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega),
        hfr3 z (Or.inl (by omega)), hfr2 z (Or.inl (by dsimp [dgVListBase]; omega)) (Or.inl (by omega)),
        hfr1 z (Or.inl (by dsimp [dgVListBase]; omega))]
    dsimp only [memH]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine runs_seq_call_flat hCopy
    (vs := [dgEListBase guestBase vCap eCap, dgEListBase g0Ptr vCap0 eCap0, G₀.m])
    (by simp [evalArgs, Expr.eval])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · dsimp [dgEListBase]; omega
        · dsimp [dgEListBase]; omega
        · omega)
    ⟨dgEListBase guestBase vCap eCap, dgEListBase g0Ptr vCap0 eCap0, G₀.m, rfl,
      by dsimp [dgEListBase]; omega, by dsimp [dgEListBase]; omega,
      Or.inr (by dsimp [dgEListBase]; omega)⟩ ?_
  intro ret4 mem4 pos4 hpost4
  rcases hpost4 with ⟨_, _, _, hEq4, rfl, hcp4, hfr4⟩
  simp only [List.cons.injEq, and_true] at hEq4; rcases hEq4 with ⟨rfl, rfl, rfl⟩
  have heL_mem4 : ListAt mem4 (dgEListBase guestBase vCap eCap) eL0 := fun i hi => by
    rw [hcp4 i (by omega), hmem_below_V _ (by dsimp [dgEListBase]; omega)]
    exact heL0_at i hi
  have hSortE := mergeSort_meetsContract (w := w) (L := eL0) hpSort hpSort
  refine runs_seq_call_flat hSortE
    (vs := [dgEListBase guestBase vCap eCap, eL0.length, scratch])
    (by simp [evalArgs, Expr.eval, heL0_len])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · dsimp [dgEListBase]; omega
        · omega
        · omega)
    ⟨dgEListBase guestBase vCap eCap, scratch, rfl, hw16,
      by dsimp [dgEListBase]; omega, by dsimp [scratch]; omega,
      Or.inl (by dsimp [dgEListBase, scratch]; omega), heL_mem4,
      fun x hx => by have := heL0_lt x hx; omega⟩ ?_
  intro ret5 mem5 pos5 hpost5
  rcases hpost5 with ⟨_, _, eL_sorted, hEq5, rfl, hpermE, hpairE, heL_at5, hfr5⟩
  simp only [List.cons.injEq, and_true] at hEq5; rcases hEq5 with ⟨rfl, _, rfl⟩
  have heL_eq : eL_sorted = canonEList G₀ := eq_finset_sort_of_perm heL0_nd heL0_mem hpermE hpairE
  subst heL_eq
  refine runs_seq_call_flat hFill
    (vs := [scratch, G₀.m, 0])
    (by simp [evalArgs, Expr.eval, show 0 < 2 ^ w by omega])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> omega)
    ⟨scratch, G₀.m, 0, rfl, by omega⟩ ?_
  intro ret6 mem6 pos6 hpost6
  rcases hpost6 with ⟨_, _, _, hEq6, rfl, hfill6, hfr6⟩
  simp only [List.cons.injEq, and_true] at hEq6; rcases hEq6 with ⟨rfl, rfl, rfl⟩
  have hmem6_below : ∀ z < guestBase, mem6 z = mem z := fun z hz' => by
    rw [hfr6 z (Or.inl (by omega)), hfr5 z (Or.inl (by dsimp [dgEListBase]; omega)) (Or.inl (by omega)),
        hfr4 z (Or.inl (by dsimp [dgEListBase]; omega)), hmem_below_V z hz']
  have hdg0_6 : DynGraphAt mem6 g0Ptr vCap0 eCap0 G₀ :=
    hdg0.of_agree fun a _ ha2 => hmem6_below a (by omega)
  have hℓ₀_6 : ∀ e ∈ G₀.E, Valid mem6 (lenArr + e * L_in) h L_in ∧
      fixVal mem6 (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e := fun e he => by
    have he_lt0 := hdg0.2.2.1 e he
    have hmul0 : (e + 1) * L_in ≤ eCap0 * L_in := Nat.mul_le_mul_right L_in (by omega)
    have hadd0 : e * L_in + L_in = (e + 1) * L_in := by ring
    have hag : ∀ t < L_in, mem6 (lenArr + e * L_in + t) = mem (lenArr + e * L_in + t) := fun t ht =>
      hmem6_below _ (by omega)
    exact ⟨fun t ht => by rw [hag t ht]; exact (hℓ₀ e he).1 t ht,
      by unfold fixVal; rw [intVal_congr hag]; exact (hℓ₀ e he).2.1, (hℓ₀ e he).2.2⟩
  have heL_at6 : ListAt mem6 (dgEListBase guestBase vCap eCap) (canonEList G₀) := fun i hi => by
    rw [hfr6 _ (Or.inl (by dsimp [dgEListBase, scratch]; omega))]
    exact heL_at5 i hi
  -- Call buildCanonEdgesProc
  refine runs_seq_call_body_flat hpEdges (vs := [g0Ptr, lenArr, L_in, guestBase, vCap, eCap, G₀.m, dstLen])
    (P_call := fun _ stE =>
      (∀ e ∈ G₀.E,
        stE.mem (dgEPresBase guestBase vCap + e) = 1 ∧
        stE.mem (dgEPosBase guestBase vCap eCap + e) = (canonEList G₀).idxOf e ∧
        stE.mem (dgETailSlotBase guestBase vCap eCap + e) = G₀.tail e ∧
        stE.mem (dgEHeadSlotBase guestBase vCap eCap + e) = G₀.head e ∧
        ∀ t < L_in, stE.mem (dstLen + e * L_in + t) = natLimb (canonLenInt ℓ₀ P_fp e) h t) ∧
      (∀ addr,
        (∀ e ∈ G₀.E,
          addr ≠ dgEPresBase guestBase vCap + e ∧
          addr ≠ dgEPosBase guestBase vCap eCap + e ∧
          addr ≠ dgETailSlotBase guestBase vCap eCap + e ∧
          addr ≠ dgEHeadSlotBase guestBase vCap eCap + e ∧
          (addr < dstLen + e * L_in ∨ dstLen + e * L_in + L_in ≤ addr)) →
        stE.mem addr = mem6 addr))
    (c1_max := G₀.m * (20 * L_in + 100) + 180)
    (by simp [evalArgs, Expr.eval])
    (by obtain ⟨stE, cE, hrunE, heSet, hfrE, hcE⟩ :=
          buildCanonEdgesProc_runs (p := p) (ω := ω) (mem := mem6) (pos := pos6)
            hw16 hLin1 hdg0_6 hℓ₀_6 hg0_le hlen_le (by omega) heL_at6 hCopy
        exact ⟨0, stE, cE, hrunE, ⟨heSet, hfrE⟩, hcE⟩)
    (fun _ stE ⟨heSet, hfrE⟩ => ?_)
  -- Verify stE.mem agrees with canonDGMemBase on [guestBase, guestBase + dynGraphSize vCap eCap)
  have hz6 : ZeroFrom mem6 scratch := fun z hz' => by
    by_cases hlt : z < scratch + G₀.m
    · have := hfill6 (z - scratch) (by omega)
      rwa [show scratch + (z - scratch) = z by omega] at this
    · rw [hfr6 z (Or.inr (by omega)),
          hfr5 z (Or.inr (by dsimp [dgEListBase, scratch]; omega)) (Or.inr (by omega)),
          hfr4 z (Or.inr (by dsimp [dgEListBase, scratch]; omega)),
          hfrV z (fun v hv => by have := canonVCap_gt hv; dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase, scratch]; omega)]
      by_cases hltN : z < scratch + G₀.n
      · have := hfill3 (z - scratch) (by omega)
        rwa [show scratch + (z - scratch) = z by omega] at this
      · rw [hfr3 z (Or.inr (by omega)),
            hfr2 z (Or.inr (by dsimp [dgVListBase, scratch]; omega)) (Or.inr (by omega)),
            hfr1 z (Or.inr (by dsimp [dgVListBase, scratch]; omega))]
        dsimp only [memH]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hz z (by omega)
  have hzE : ZeroFrom stE.mem scratch := fun z hz' => by
    rw [hfrE z fun e he => by
      have := canonECap_gt he
      have hmul : (e + 1) * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in (by omega)
      have hadd : e * L_in + L_in = (e + 1) * L_in := by ring
      dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, scratch, canonHandlesOut, canonLenArr] at hz' ⊢
      omega]
    exact hz6 z hz'
  have hmem6_zero_untouched : ∀ z, guestBase + 4 ≤ z → z < scratch →
      (z < dgVListBase guestBase vCap ∨ dgVListBase guestBase vCap + G₀.n ≤ z) →
      (z < dgEListBase guestBase vCap eCap ∨ dgEListBase guestBase vCap eCap + G₀.m ≤ z) →
      (∀ v ∈ G₀.V, z ≠ dgVPresBase guestBase + v ∧ z ≠ dgVPosBase guestBase vCap + v ∧
        z ≠ dgExtToIntBase guestBase vCap + v ∧ z ≠ dgIntToExtBase guestBase vCap + v) →
      mem6 z = 0 := fun z h1 h2 h3 h4 h5 => by
    rw [hfr6 z (Or.inl h2), hfr5 z (by rcases h4 with h | h <;> [left; right] <;> omega) (Or.inl h2),
        hfr4 z h4, hfrV z h5, hfr3 z (Or.inl h2),
        hfr2 z (by rcases h3 with h | h <;> [left; right] <;> omega) (Or.inl h2), hfr1 z h3]
    dsimp only [memH]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz z (by omega)
  have hbaseE : ∀ a < dynGraphSize vCap eCap, stE.mem (guestBase + a) = canonDGMemBase G₀ a := by
    classical
    intro a ha
    have hhdr := canonDGMemBase_hdr G₀
    have h0_vL : dgVListBase 0 vCap = 4 + vCap := rfl
    have h0_vP : dgVPosBase 0 vCap = 4 + 2 * vCap := rfl
    have h0_e2i : dgExtToIntBase 0 vCap = 4 + 3 * vCap := rfl
    have h0_i2e : dgIntToExtBase 0 vCap = 4 + 4 * vCap := rfl
    have h0_sD : dgSlotDegBase 0 vCap = 4 + 5 * vCap := rfl
    have h0_iH : dgIncHeadBase 0 vCap = 4 + 6 * vCap := rfl
    have h0_ePr : dgEPresBase 0 vCap = 4 + 7 * vCap := rfl
    have h0_eL : dgEListBase 0 vCap eCap = 4 + 7 * vCap + eCap := rfl
    have h0_ePo : dgEPosBase 0 vCap eCap = 4 + 7 * vCap + 2 * eCap := rfl
    have h0_eT : dgETailSlotBase 0 vCap eCap = 4 + 7 * vCap + 3 * eCap := rfl
    have h0_eH : dgEHeadSlotBase 0 vCap eCap = 4 + 7 * vCap + 4 * eCap := rfl
    have h0_hP : dgHePrevBase 0 vCap eCap = 4 + 7 * vCap + 5 * eCap := rfl
    have hstE_unch : ∀ x < dgEPresBase guestBase vCap, stE.mem x = mem6 x := fun x hx =>
      hfrE x fun e _ => by
        dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr] at hx ⊢
        omega
    have hmem6_ltE : ∀ x < dgEListBase guestBase vCap eCap, mem6 x = stV.mem x := fun x hx => by
      rw [hfr6 x (Or.inl (by dsimp [dgEListBase, scratch] at hx ⊢; omega)),
          hfr5 x (Or.inl hx) (Or.inl (by dsimp [dgEListBase, scratch] at hx ⊢; omega)),
          hfr4 x (Or.inl hx)]
    by_cases h0 : a = 0
    · subst h0; rw [hhdr.1, hstE_unch _ (by dsimp [dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgEListBase]; omega),
        hfrV _ (fun _ _ => by dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega),
        hfr3 _ (Or.inl (by omega)), hfr2 _ (Or.inl (by dsimp [dgVListBase]; omega)) (Or.inl (by omega)),
        hfr1 _ (Or.inl (by dsimp [dgVListBase]; omega))]
      simp [memH, vCap]
    by_cases h1 : a = 1
    · subst h1; rw [hhdr.2.1, hstE_unch _ (by dsimp [dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgEListBase]; omega),
        hfrV _ (fun _ _ => by dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega),
        hfr3 _ (Or.inl (by omega)), hfr2 _ (Or.inl (by dsimp [dgVListBase]; omega)) (Or.inl (by omega)),
        hfr1 _ (Or.inl (by dsimp [dgVListBase]; omega))]
      simp [memH, eCap]
    by_cases h2 : a = 2
    · subst h2; rw [hhdr.2.2.1, hstE_unch _ (by dsimp [dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgEListBase]; omega),
        hfrV _ (fun _ _ => by dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega),
        hfr3 _ (Or.inl (by omega)), hfr2 _ (Or.inl (by dsimp [dgVListBase]; omega)) (Or.inl (by omega)),
        hfr1 _ (Or.inl (by dsimp [dgVListBase]; omega))]
      simp [memH]
    by_cases h3 : a = 3
    · subst h3; rw [hhdr.2.2.2, hstE_unch _ (by dsimp [dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgEListBase]; omega),
        hfrV _ (fun _ _ => by dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega),
        hfr3 _ (Or.inl (by omega)), hfr2 _ (Or.inl (by dsimp [dgVListBase]; omega)) (Or.inl (by omega)),
        hfr1 _ (Or.inl (by dsimp [dgVListBase]; omega))]
      simp [memH]
    by_cases h4 : a < dgVListBase 0 vCap
    · set v := a - 4
      have hv_lt : v < vCap := by dsimp [dgVListBase] at h4; omega
      have ha_eq : a = dgVPresBase 0 + v := by dsimp [dgVPresBase]; omega
      rw [ha_eq, canonDGMemBase_vPres hv_lt, show guestBase + (dgVPresBase 0 + v) = dgVPresBase guestBase + v by
          dsimp [dgVPresBase]; omega,
        hstE_unch _ (by dsimp [dgVPresBase, dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgVPresBase, dgEListBase]; omega)]
      by_cases hv : v ∈ G₀.V
      · rw [ite_eq_left hv]; exact (hvSet v hv).1
      · rw [ite_eq_right hv, ← hmem6_ltE _ (by dsimp [dgVPresBase, dgEListBase]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgVPresBase]; omega) (by dsimp [dgVPresBase, scratch]; omega)
          (Or.inl (by dsimp [dgVPresBase, dgVListBase]; omega))
          (Or.inl (by dsimp [dgVPresBase, dgEListBase]; omega))
          (fun u hu => by
            have := canonVCap_gt hu; have hne : v ≠ u := fun hEq => hv (hEq ▸ hu)
            dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h5 : a < dgVPosBase 0 vCap
    · set i := a - dgVListBase 0 vCap
      have hi_lt : i < vCap := by dsimp [dgVListBase, dgVPosBase] at h4 h5; omega
      have ha_eq : a = dgVListBase 0 vCap + i := by dsimp [dgVListBase] at h4 ⊢; omega
      rw [ha_eq, canonDGMemBase_vList hi_lt,
        show guestBase + (dgVListBase 0 vCap + i) = dgVListBase guestBase vCap + i by dsimp [dgVListBase]; omega,
        hstE_unch _ (by dsimp [dgVListBase, dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgVListBase, dgEListBase]; omega)]
      by_cases hi : i < (canonVList G₀).length
      · rw [List.getD_eq_getElem _ _ hi,
            hfrV _ (fun u hu => by have := canonVCap_gt hu; dsimp [dgVListBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)]
        exact hvL_at3 i hi
      · have hlenV : (canonVList G₀).length = G₀.n := G₀.V.length_sort (· ≤ ·)
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
            ← hmem6_ltE _ (by dsimp [dgVListBase, dgEListBase]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgVListBase]; omega) (by dsimp [dgVListBase, scratch]; omega)
          (Or.inr (by omega)) (Or.inl (by dsimp [dgVListBase, dgEListBase]; omega))
          (fun u hu => by have := canonVCap_gt hu; dsimp [dgVListBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h6 : a < dgExtToIntBase 0 vCap
    · set v := a - dgVPosBase 0 vCap
      have hv_lt : v < vCap := by dsimp [dgVPosBase, dgExtToIntBase] at h5 h6; omega
      have ha_eq : a = dgVPosBase 0 vCap + v := by dsimp [dgVPosBase] at h5 ⊢; omega
      rw [ha_eq, canonDGMemBase_vPos hv_lt,
        show guestBase + (dgVPosBase 0 vCap + v) = dgVPosBase guestBase vCap + v by dsimp [dgVPosBase]; omega,
        hstE_unch _ (by dsimp [dgVPosBase, dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgVPosBase, dgEListBase]; omega)]
      by_cases hv : v ∈ G₀.V
      · rw [ite_eq_left hv]; exact (hvSet v hv).2.1
      · rw [ite_eq_right hv, ← hmem6_ltE _ (by dsimp [dgVPosBase, dgEListBase]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgVPosBase]; omega) (by dsimp [dgVPosBase, scratch]; omega)
          (Or.inr (by dsimp [dgVPosBase, dgVListBase]; omega))
          (Or.inl (by dsimp [dgVPosBase, dgEListBase]; omega))
          (fun u hu => by
            have := canonVCap_gt hu; have hne : v ≠ u := fun hEq => hv (hEq ▸ hu)
            dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h7 : a < dgIntToExtBase 0 vCap
    · set v := a - dgExtToIntBase 0 vCap
      have hv_lt : v < vCap := by dsimp [dgExtToIntBase, dgIntToExtBase] at h6 h7; omega
      have ha_eq : a = dgExtToIntBase 0 vCap + v := by dsimp [dgExtToIntBase] at h6 ⊢; omega
      rw [ha_eq, canonDGMemBase_extToInt hv_lt,
        show guestBase + (dgExtToIntBase 0 vCap + v) = dgExtToIntBase guestBase vCap + v by dsimp [dgExtToIntBase]; omega,
        hstE_unch _ (by dsimp [dgExtToIntBase, dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgExtToIntBase, dgEListBase]; omega)]
      by_cases hv : v ∈ G₀.V
      · rw [ite_eq_left hv]; exact (hvSet v hv).2.2.1
      · rw [ite_eq_right hv, ← hmem6_ltE _ (by dsimp [dgExtToIntBase, dgEListBase]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgExtToIntBase]; omega) (by dsimp [dgExtToIntBase, scratch]; omega)
          (Or.inr (by dsimp [dgExtToIntBase, dgVListBase]; omega))
          (Or.inl (by dsimp [dgExtToIntBase, dgEListBase]; omega))
          (fun u hu => by
            have := canonVCap_gt hu; have hne : v ≠ u := fun hEq => hv (hEq ▸ hu)
            dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h8 : a < dgSlotDegBase 0 vCap
    · set v := a - dgIntToExtBase 0 vCap
      have hv_lt : v < vCap := by dsimp [dgIntToExtBase, dgSlotDegBase] at h7 h8; omega
      have ha_eq : a = dgIntToExtBase 0 vCap + v := by dsimp [dgIntToExtBase] at h7 ⊢; omega
      rw [ha_eq, canonDGMemBase_intToExt hv_lt,
        show guestBase + (dgIntToExtBase 0 vCap + v) = dgIntToExtBase guestBase vCap + v by dsimp [dgIntToExtBase]; omega,
        hstE_unch _ (by dsimp [dgIntToExtBase, dgEPresBase]; omega),
        hmem6_ltE _ (by dsimp [dgIntToExtBase, dgEListBase]; omega)]
      by_cases hv : v ∈ G₀.V
      · rw [ite_eq_left hv]; exact (hvSet v hv).2.2.2
      · rw [ite_eq_right hv, ← hmem6_ltE _ (by dsimp [dgIntToExtBase, dgEListBase]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgIntToExtBase]; omega) (by dsimp [dgIntToExtBase, scratch]; omega)
          (Or.inr (by dsimp [dgIntToExtBase, dgVListBase]; omega))
          (Or.inl (by dsimp [dgIntToExtBase, dgEListBase]; omega))
          (fun u hu => by
            have := canonVCap_gt hu; have hne : v ≠ u := fun hEq => hv (hEq ▸ hu)
            dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h9 : a < dgIncHeadBase 0 vCap
    · set s := a - dgSlotDegBase 0 vCap
      have hs_lt : s < vCap := by dsimp [dgSlotDegBase, dgIncHeadBase] at h8 h9; omega
      rw [show a = dgSlotDegBase 0 vCap + s by dsimp [dgSlotDegBase] at h8 ⊢; omega,
          canonDGMemBase_slotDeg hs_lt, hstE_unch _ (by dsimp [dgSlotDegBase, dgEPresBase]; omega)]
      exact hmem6_zero_untouched _ (by dsimp [dgSlotDegBase]; omega) (by dsimp [dgSlotDegBase, scratch]; omega)
        (Or.inr (by dsimp [dgSlotDegBase, dgVListBase]; omega))
        (Or.inl (by dsimp [dgSlotDegBase, dgEListBase]; omega))
        (fun u hu => by have := canonVCap_gt hu; dsimp [dgSlotDegBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h10 : a < dgEPresBase 0 vCap
    · set s := a - dgIncHeadBase 0 vCap
      have hs_lt : s < vCap := by dsimp [dgIncHeadBase, dgEPresBase] at h9 h10; omega
      rw [show a = dgIncHeadBase 0 vCap + s by dsimp [dgIncHeadBase] at h9 ⊢; omega,
          canonDGMemBase_incHead hs_lt, hstE_unch _ (by dsimp [dgIncHeadBase, dgEPresBase]; omega)]
      exact hmem6_zero_untouched _ (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, scratch]; omega)
        (Or.inr (by dsimp [dgIncHeadBase, dgVListBase]; omega))
        (Or.inl (by dsimp [dgIncHeadBase, dgEListBase]; omega))
        (fun u hu => by have := canonVCap_gt hu; dsimp [dgIncHeadBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h11 : a < dgEListBase 0 vCap eCap
    · set e := a - dgEPresBase 0 vCap
      have he_lt : e < eCap := by dsimp [dgEPresBase, dgEListBase] at h10 h11; omega
      rw [show a = dgEPresBase 0 vCap + e by dsimp [dgEPresBase] at h10 ⊢; omega,
          canonDGMemBase_ePres he_lt,
          show guestBase + (dgEPresBase 0 vCap + e) = dgEPresBase guestBase vCap + e by dsimp [dgEPresBase]; omega]
      by_cases he : e ∈ G₀.E
      · rw [ite_eq_left he]; exact (heSet e he).1
      · rw [ite_eq_right he, hfrE _ (fun f hf => by
          have := canonECap_gt hf; have hne : e ≠ f := fun hEq => he (hEq ▸ hf)
          dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgEPresBase]; omega) (by dsimp [dgEPresBase, scratch]; omega)
          (Or.inr (by dsimp [dgEPresBase, dgVListBase]; omega))
          (Or.inl (by dsimp [dgEPresBase, dgEListBase]; omega))
          (fun u hu => by have := canonVCap_gt hu; dsimp [dgEPresBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h12 : a < dgEPosBase 0 vCap eCap
    · set i := a - dgEListBase 0 vCap eCap
      have hi_lt : i < eCap := by dsimp [dgEListBase, dgEPosBase] at h11 h12; omega
      rw [show a = dgEListBase 0 vCap eCap + i by dsimp [dgEListBase] at h11 ⊢; omega,
          canonDGMemBase_eList hi_lt,
          show guestBase + (dgEListBase 0 vCap eCap + i) = dgEListBase guestBase vCap eCap + i by dsimp [dgEListBase]; omega,
          hfrE _ (fun f hf => by
            have := canonECap_gt hf
            dsimp [dgEListBase, dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr]; omega)]
      by_cases hi : i < (canonEList G₀).length
      · rw [List.getD_eq_getElem _ _ hi]; exact heL_at6 i hi
      · have hlenE : (canonEList G₀).length = G₀.m := G₀.E.length_sort (· ≤ ·)
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
        exact hmem6_zero_untouched _ (by dsimp [dgEListBase]; omega) (by dsimp [dgEListBase, scratch]; omega)
          (Or.inr (by dsimp [dgEListBase, dgVListBase]; omega)) (Or.inr (by omega))
          (fun u hu => by have := canonVCap_gt hu; dsimp [dgEListBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h13 : a < dgETailSlotBase 0 vCap eCap
    · set e := a - dgEPosBase 0 vCap eCap
      have he_lt : e < eCap := by dsimp [dgEPosBase, dgETailSlotBase] at h12 h13; omega
      rw [show a = dgEPosBase 0 vCap eCap + e by dsimp [dgEPosBase] at h12 ⊢; omega,
          canonDGMemBase_ePos he_lt,
          show guestBase + (dgEPosBase 0 vCap eCap + e) = dgEPosBase guestBase vCap eCap + e by dsimp [dgEPosBase]; omega]
      by_cases he : e ∈ G₀.E
      · rw [ite_eq_left he]; exact (heSet e he).2.1
      · rw [ite_eq_right he, hfrE _ (fun f hf => by
          have := canonECap_gt hf; have hne : e ≠ f := fun hEq => he (hEq ▸ hf)
          dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgEPosBase]; omega) (by dsimp [dgEPosBase, scratch]; omega)
          (Or.inr (by dsimp [dgEPosBase, dgVListBase]; omega))
          (Or.inr (by dsimp [dgEPosBase, dgEListBase]; omega))
          (fun u hu => by have := canonVCap_gt hu; dsimp [dgEPosBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h14 : a < dgEHeadSlotBase 0 vCap eCap
    · set e := a - dgETailSlotBase 0 vCap eCap
      have he_lt : e < eCap := by dsimp [dgETailSlotBase, dgEHeadSlotBase] at h13 h14; omega
      rw [show a = dgETailSlotBase 0 vCap eCap + e by dsimp [dgETailSlotBase] at h13 ⊢; omega,
          canonDGMemBase_eTailSlot he_lt,
          show guestBase + (dgETailSlotBase 0 vCap eCap + e) = dgETailSlotBase guestBase vCap eCap + e by dsimp [dgETailSlotBase]; omega]
      by_cases he : e ∈ G₀.E
      · rw [ite_eq_left he]; exact (heSet e he).2.2.1
      · rw [ite_eq_right he, hfrE _ (fun f hf => by
          have := canonECap_gt hf; have hne : e ≠ f := fun hEq => he (hEq ▸ hf)
          dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase, scratch]; omega)
          (Or.inr (by dsimp [dgETailSlotBase, dgVListBase]; omega))
          (Or.inr (by dsimp [dgETailSlotBase, dgEListBase]; omega))
          (fun u hu => by have := canonVCap_gt hu; dsimp [dgETailSlotBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    by_cases h15 : a < dgHePrevBase 0 vCap eCap
    · set e := a - dgEHeadSlotBase 0 vCap eCap
      have he_lt : e < eCap := by dsimp [dgEHeadSlotBase, dgHePrevBase] at h14 h15; omega
      rw [show a = dgEHeadSlotBase 0 vCap eCap + e by dsimp [dgEHeadSlotBase] at h14 ⊢; omega,
          canonDGMemBase_eHeadSlot he_lt,
          show guestBase + (dgEHeadSlotBase 0 vCap eCap + e) = dgEHeadSlotBase guestBase vCap eCap + e by dsimp [dgEHeadSlotBase]; omega]
      by_cases he : e ∈ G₀.E
      · rw [ite_eq_left he]; exact (heSet e he).2.2.2.1
      · rw [ite_eq_right he, hfrE _ (fun f hf => by
          have := canonECap_gt hf; have hne : e ≠ f := fun hEq => he (hEq ▸ hf)
          dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr]; omega)]
        exact hmem6_zero_untouched _ (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase, scratch]; omega)
          (Or.inr (by dsimp [dgEHeadSlotBase, dgVListBase]; omega))
          (Or.inr (by dsimp [dgEHeadSlotBase, dgEListBase]; omega))
          (fun u hu => by have := canonVCap_gt hu; dsimp [dgEHeadSlotBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
    · rw [canonDGMemBase_zero_ge_hePrev (Nat.le_of_not_lt h15),
          hfrE _ (fun f hf => by
            have := canonECap_gt hf
            dsimp [dgHePrevBase, dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr] at h15 ⊢
            omega)]
      exact hmem6_zero_untouched _ (by dsimp [dgHePrevBase] at h15; omega) (by dsimp [scratch]; omega)
        (Or.inr (by dsimp [dgHePrevBase, dgVListBase] at h15 ⊢; omega))
        (Or.inr (by dsimp [dgHePrevBase, dgEListBase] at h15 ⊢; omega))
        (fun u hu => by have := canonVCap_gt hu; dsimp [dgHePrevBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase] at h15 ⊢; omega)
  -- Call buildCanonIncProc
  refine runs_seq_call_body_flat hpInc (vs := [guestBase, vCap, eCap, G₀.m])
    (P_call := fun _ stI =>
      (∀ a < dynGraphSize vCap eCap, stI.mem (guestBase + a) = canonDGMem G₀ a) ∧
      (∀ addr, addr < guestBase ∨ guestBase + dynGraphSize vCap eCap ≤ addr →
        stI.mem addr = stE.mem addr))
    (c1_max := 270 * G₀.m + 80)
    (by simp [evalArgs, Expr.eval])
    (by obtain ⟨stI, cI, hrunI, hdgI, hfrI, hcI⟩ :=
          buildCanonIncProc_runs (p := p) (ω := ω) (mem := stE.mem) (pos := stE.pos)
            hG₀ hw16 (by omega) hbaseE hpPush
        exact ⟨0, stI, cI, hrunI, ⟨hdgI, hfrI⟩, hcI⟩)
    (fun _ stI ⟨hdgI, hfrI⟩ => ?_)
  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ⟨rfl, ?_, ?_, ?_⟩ ?_
  · intro z hz'
    rw [hfrI z (Or.inl hz'),
        hfrE z (fun _ _ => by dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen]; omega),
        hmem6_below z hz']
  · intro a
    unfold canonGuestMem
    by_cases h1 : a < canonLenArr G₀
    · rw [ite_eq_left h1]; exact hdgI a h1
    · rw [ite_eq_right h1]
      by_cases h2 : a < canonHandlesOut G₀ L_in
      · rw [ite_eq_left h2]
        dsimp only
        set off := a - canonLenArr G₀
        set e := off / L_in
        set t := off % L_in
        have ht_lt : t < L_in := Nat.mod_lt _ (by omega)
        have hoff_eq : off = e * L_in + t := by
          dsimp only [e, t]; rw [mul_comm, Nat.div_add_mod]
        have ha_eq : guestBase + a = dstLen + e * L_in + t := by
          dsimp only [dstLen]; omega
        rw [hfrI _ (Or.inr (by dsimp [canonLenArr] at h1; omega)), ha_eq]
        by_cases he : e ∈ G₀.E
        · rw [ite_eq_left he]; exact (heSet e he).2.2.2.2 t ht_lt
        · rw [ite_eq_right he, hfrE _ (fun f hf => by
            have := canonECap_gt hf
            have hne : e ≠ f := fun hEq => he (hEq ▸ hf)
            refine ⟨by dsimp [dgEPresBase, dstLen, canonLenArr]; omega,
              by dsimp [dgEPosBase, dstLen, canonLenArr]; omega,
              by dsimp [dgETailSlotBase, dstLen, canonLenArr]; omega,
              by dsimp [dgEHeadSlotBase, dstLen, canonLenArr]; omega, ?_⟩
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · left
              have : (e + 1) * L_in ≤ f * L_in := Nat.mul_le_mul_right L_in hlt
              have : e * L_in + L_in = (e + 1) * L_in := by ring
              omega
            · right
              have : (f + 1) * L_in ≤ e * L_in := Nat.mul_le_mul_right L_in hgt
              have : f * L_in + L_in = (f + 1) * L_in := by ring
              omega)]
          exact hmem6_zero_untouched _ (by dsimp [dstLen, canonLenArr]; omega)
            (by dsimp [scratch]; omega)
            (Or.inr (by dsimp [dstLen, canonLenArr, dgVListBase]; omega))
            (Or.inr (by dsimp [dstLen, canonLenArr, dgEListBase]; omega))
            (fun u hu => by have := canonVCap_gt hu; dsimp [dstLen, canonLenArr, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)
      · rw [ite_eq_right h2, hfrI _ (Or.inr (by dsimp [canonHandlesOut, canonLenArr] at h2 ⊢; omega))]
        exact hzE _ (by dsimp [scratch]; omega)
  · intro z hz'
    rw [hfrI z (Or.inr (by dsimp [scratch, canonHandlesOut, canonLenArr] at hz' ⊢; omega))]
    exact hzE z hz'
  · simp only [buildCanonGuestCost, memCopyContract, mergeSortContract, memFillContract,
      argsSize, Expr.size, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rw [hvL0_len, heL0_len]
    have hmulE : G₀.m * (20 * L_in + 100) = 20 * (G₀.m * L_in) + 100 * G₀.m := by ring
    have h1 : 200 * G₀.n * (Nat.log 2 (G₀.n + 1) + 1) ≤ 250 * G₀.n * (Nat.log 2 (G₀.n + 1) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : 200 * G₀.m * (Nat.log 2 (G₀.m + 1) + 1) ≤ 250 * G₀.m * (Nat.log 2 (G₀.m + 1) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : 20 * (G₀.m * L_in) ≤ 30 * G₀.m * L_in := by
      have : 20 * (G₀.m * L_in) = 20 * G₀.m * L_in := by ring
      rw [this]; exact Nat.mul_le_mul_right L_in (by omega)
    omega

end MinCostFlow.SparseCore.Program
