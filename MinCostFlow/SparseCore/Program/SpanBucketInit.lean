module

public import MinCostFlow.SparseCore.Program.SpanBucketDefs

import WordRAM.Tactic

/-!
# Multi-Bucket Dynamic Spanner Manager: Init and Activate (`SpanBucketInit`)

Proves length, determinism (`Stmt.NoRand`), module unpacking, locality (`bucketSpannerRep_local`),
initialization (`bucketSpannerDS_init`), and operation `0` (`bucketSpannerDS_op0`: lazy first
initialization or branch restart of one bucket slot) for `bucketSpannerDS` (`SpanBucketDefs.lean`).
Operations `1..4` and `bucketSpannerDS_implements` are in `SpanBucket.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## Private helpers -/

private lemma hasAt_append_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt b xs := by
  intro i hi
  have h1 := h i (by rw [List.length_append]; omega)
  rwa [List.getElem_append_left hi] at h1

private lemma hasAt_append_right {p : Program} {b n : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : xs.length = n) : p.HasAt (b + n) ys := by
  intro i hi
  have h1 := h (n + i) (by rw [List.length_append, hlen]; omega)
  rw [Nat.add_assoc]
  rw [List.getElem_append_right (by omega)] at h1
  simpa [hlen] using h1

private lemma noRand_append {xs ys : List Stmt}
    (hx : ∀ s ∈ xs, s.NoRand) (hy : ∀ s ∈ ys, s.NoRand) :
    ∀ s ∈ xs ++ ys, s.NoRand := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact hx s h
  · exact hy s h

private lemma bucketSpanOpsProcs_length (b : ℕ) : (bucketSpanOpsProcs b).length = 6 := rfl

private lemma bucketSpanOpsProcs_noRand (b : ℕ) : ∀ s ∈ bucketSpanOpsProcs b, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

private lemma phaseBase_lt_pow {nCap L w : ℕ} (hL : 1 ≤ L) (hw16 : 16 ≤ 2 ^ w)
    (hn : nCap + 2 < 2 ^ w) : phaseBase nCap L < 2 ^ w := by
  by_cases h1 : nCap ≤ 1
  · rw [phaseBase_of_le_one h1]; omega
  · have hpow : nCap ≤ nCap ^ L := by
      calc nCap = nCap ^ 1 := (pow_one nCap).symm
        _ ≤ nCap ^ L := Nat.pow_le_pow_right (by omega) hL
    have hle : phaseBase nCap L ≤ nCap := (phaseBase_le_iff hL (by omega) (by omega)).mpr hpow
    omega

/-! ## Shared footprint helpers and public module theorems -/

public section

lemma bucket_tbl_end_le_of_foot {L cap tbl h : ℕ} {x : BucketSpannerMeta L cap}
    (hfoot : ∀ a, bucketFoot tbl x a → a < h) (hcap : 1 ≤ cap) :
    tbl + cap ≤ h := by
  have hm : bucketFoot tbl x (tbl + cap - 1) := Or.inl ⟨by omega, by omega⟩
  have := hfoot _ hm
  omega

lemma bucket_slot_lt_of_foot {L cap tbl slot h : ℕ} {x : BucketSpannerMeta L cap}
    (hfoot : ∀ a, bucketFoot tbl x a → a < h) (hslot : slot < cap) :
    tbl + slot < h :=
  hfoot (tbl + slot) (Or.inl ⟨Nat.le_add_right _ _, by omega⟩)

theorem bucketSpannerProcs_length (impl : SparsifyImpl) (b : ℕ) :
    (bucketSpannerProcs impl b).length = 121 + impl.procs.length := by
  unfold bucketSpannerProcs
  simp only [List.length_append, spanParamProcs_length, spanReadoutProcs_length,
    bucketSpanOpsProcs_length, dynSpannerDSProcs_length]
  omega

/-- Every procedure in `bucketSpannerProcs impl b` is deterministic (`Stmt.NoRand`). -/
theorem bucketSpannerProcs_noRand (impl : SparsifyImpl) (b : ℕ) :
    ∀ s ∈ bucketSpannerProcs impl b, s.NoRand := by
  unfold bucketSpannerProcs
  exact noRand_append
    (noRand_append (noRand_append (spanParamProcs_noRand _) spanReadoutProcs_noRand)
      (bucketSpanOpsProcs_noRand _))
    (dynSpannerDSProcs_noRand impl _)

/-- Unpack the four sub-modules from `p.HasAt b (bucketSpannerProcs impl b)`. -/
theorem bucketSpannerProcs_unpack {impl : SparsifyImpl} {p : Program} {b : ℕ}
    (hp : p.HasAt b (bucketSpannerProcs impl b)) :
    p.HasAt (b + bsOffParam) (spanParamProcs (b + bsOffParam)) ∧
    p.HasAt (b + bsOffRead) spanReadoutProcs ∧
    p.HasAt (b + bsOffOps) (bucketSpanOpsProcs b) ∧
    p.HasAt (b + bsOffDyn) (dynSpannerDSProcs impl (b + bsOffDyn)) := by
  have h123 := hasAt_append_left hp
  have hDyn : p.HasAt (b + bsOffDyn) (dynSpannerDSProcs impl (b + bsOffDyn)) :=
    hasAt_append_right hp (by
      simp only [List.length_append, spanParamProcs_length, spanReadoutProcs_length,
        bucketSpanOpsProcs_length, bsOffDyn])
  have h12 := hasAt_append_left h123
  have hOps : p.HasAt (b + bsOffOps) (bucketSpanOpsProcs b) :=
    hasAt_append_right h123 (by
      simp only [List.length_append, spanParamProcs_length, spanReadoutProcs_length, bsOffOps])
  have hParam : p.HasAt (b + bsOffParam) (spanParamProcs (b + bsOffParam)) := by
    simpa [bsOffParam] using hasAt_append_left h12
  have hRead : p.HasAt (b + bsOffRead) spanReadoutProcs :=
    hasAt_append_right h12 (spanParamProcs_length _)
  exact ⟨hParam, hRead, hOps, hDyn⟩

/-- `bucketSpannerRep P cap` is local to `bucketFoot`. -/
theorem bucketSpannerRep_local (P : DSParams) (cap : ℕ) : (bucketSpannerRep P cap).Local := by
  intro tbl S x mem mem' hag
  refine ⟨fun h => ?_, rfl⟩
  obtain ⟨hslots, hdisj⟩ := h
  refine ⟨fun j => ?_, hdisj⟩
  have hj := hslots j
  have hcell : mem (tbl + j.1) = mem' (tbl + j.1) :=
    hag (tbl + j.1) (Or.inl ⟨Nat.le_add_right _ _, by omega⟩)
  cases hS : S j with
  | none =>
    cases hX : x.slots j with
    | none => simp only [hS, hX] at hj ⊢; exact hcell.symm.trans hj
    | some _ => simp only [hS, hX] at hj
  | some s =>
    cases hX : x.slots j with
    | none => simp only [hS, hX] at hj
    | some bm =>
      rcases bm with ⟨b, m⟩
      simp only [hS, hX] at hj ⊢
      obtain ⟨hb, hrep, hnotbl⟩ := hj
      refine ⟨hcell.symm.trans hb, ?_, hnotbl⟩
      exact ((dynSpannerRep_local P) b s m mem mem' fun a ha =>
        hag a (Or.inr ⟨j, b, m, hX, ha⟩)).1 hrep

/-- Initialization clause of `bucketSpannerDS_implements`. -/
theorem bucketSpannerDS_init (P : DSParams) (cap : ℕ) {p : Program} {b : ℕ}
    (hp : p.HasAt b (bucketSpannerProcs P.impl b)) :
    ∀ args mem pos ω, (∀ a ∈ args, a < 2 ^ P.w) → (bucketSpannerDS P cap).initPre args mem →
      ZeroFrom mem (heapArg args) →
      heapArg args + (bucketSpannerDS P cap).initSpace args mem < 2 ^ P.w →
      ∃ body, p.procs[b + bsIdxInit]? = some body ∧ ∃ o st' c,
        Runs P.w p ω body (startState args mem pos) o st' c ∧ ∃ S' x',
          (bucketSpannerRep P cap).rep (heapArg args) S' x' st'.mem ∧
          (bucketSpannerDS P cap).initPost args mem S' st'.mem ∧
          (bucketSpannerRep P cap).Respects (fun _ => False) (heapArg args)
            ((bucketSpannerDS P cap).initSpace args mem) mem o.value (heapArg args) x' st'.mem ∧
          c + (bucketSpannerRep P cap).phi (heapArg args) x' st'.mem ≤
            (bucketSpannerDS P cap).initCost args mem := by
  intro args mem pos ω _ hpre hz hspace
  obtain ⟨-, -, hOps, -⟩ := bucketSpannerProcs_unpack hp
  obtain ⟨h, rfl, hw16⟩ := hpre
  have hheap : heapArg [cap, h] = h := rfl
  rw [hheap] at hz hspace ⊢
  have hbody : p.procs[b + bsIdxInit]? = some bucketSpanInitStmt := by
    have hg := hOps.get (i := 0) (by simp [bucketSpanOpsProcs])
    simpa only [bsIdxInit, bsOffOps, Nat.add_zero, bucketSpanOpsProcs,
      List.getElem_cons_zero] using hg
  refine ⟨bucketSpanInitStmt, hbody, ?_⟩
  dsimp only [bucketSpanInitStmt]
  have hrun : ∃ o st' c, Runs P.w p ω (.ret (.bin .add (.reg 1) (.reg 0)))
      (startState [cap, h] mem pos) o st' c ∧
      (o.value = h + cap ∧ st'.mem = mem) ∧ c ≤ 10 := by
    refine runs_start_le ?_
    refine runs_ret_le (v := h + cap)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
        (Expr.eval_reg_of_eq (v := cap) (by simp [startState])) hspace)
      ⟨rfl, rfl⟩ (by simp [Expr.size])
  obtain ⟨o, st', c, hr, ⟨hov, hmem⟩, hc⟩ := hrun
  refine ⟨o, st', c, hr, fun _ => none, ⟨fun _ => none⟩, ?_, rfl, ?_, ?_⟩
  · refine ⟨fun j => ?_, fun _ _ _ _ _ _ _ h1 => by simp at h1⟩
    simp only [hmem]
    exact hz (h + j.1) (Nat.le_add_right _ _)
  · refine ⟨by omega, by show o.value ≤ h + cap; omega, ?_, fun _ _ _ => hmem ▸ rfl, fun a ha => ?_⟩
    · rw [hmem, hov]; exact fun a ha' => hz a (by omega)
    · rcases ha with ⟨h1, h2⟩ | ⟨_, _, _, h1, _⟩
      · exact Or.inr ⟨h1, by omega⟩
      · simp at h1
  · simpa [bucketSpannerRep, bucketSpannerDS, bucketPhi, bucketSlotBank] using hc

/-- Operation `0` (activate / restart bucket) clause of `bucketSpannerDS_implements`. -/
theorem bucketSpannerDS_op0 (P : DSParams) (cap : ℕ) {p : Program} {b : ℕ}
    (hp : p.HasAt b (bucketSpannerProcs P.impl b)) :
    ∀ tbl S x args mem pos ω, (∀ a ∈ args, a < 2 ^ P.w) → args.head? = some tbl →
      (bucketSpannerRep P cap).rep tbl S x mem → (bucketSpannerDS P cap).pre 0 S args mem →
      (∀ a, (bucketSpannerRep P cap).foot tbl x a → a < heapArg args) →
      ZeroFrom mem (heapArg args) →
      heapArg args + (bucketSpannerDS P cap).space 0 S args mem < 2 ^ P.w →
      ∃ body, p.procs[b + bsIdxOp0 + 0]? = some body ∧ ∃ o st' c,
        Runs P.w p ω body (startState args mem pos) o st' c ∧ ∃ S' x',
          (bucketSpannerRep P cap).rep tbl S' x' st'.mem ∧
          (bucketSpannerDS P cap).post 0 S args mem S' st'.mem ∧
          (bucketSpannerRep P cap).Respects ((bucketSpannerRep P cap).foot tbl x) (heapArg args)
            ((bucketSpannerDS P cap).space 0 S args mem) mem o.value tbl x' st'.mem ∧
          c + (bucketSpannerRep P cap).phi tbl x' st'.mem ≤
            (bucketSpannerDS P cap).cost 0 S args mem +
              (bucketSpannerRep P cap).phi tbl x mem := by
  intro tbl S x args mem pos ω hW hhead hrep hpre hfoot hz hspace
  obtain ⟨hParam, -, hOps, hDyn⟩ := bucketSpannerProcs_unpack hp
  have hImp := dynSpannerDSProcs_implements P hDyn
  obtain ⟨tbl', slot, nV, V_ptr, nE, E_ptr, h, rfl, hslot, hnvW, hInitPre⟩ := hpre
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  have hheap : heapArg [tbl', slot, P.L, P.splitBound, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] = h := rfl
  rw [hheap] at hfoot hz hspace ⊢
  set initArgs := bucketActInitArgs
    [tbl', slot, P.L, P.splitBound, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] with hinitArgs
  set q := phaseBase (nV + P.splitBound) P.L with hq
  have hInitPre' := hInitPre
  obtain ⟨_, _, _, _, _, _, -, -, hL1, -, hpreI⟩ := hInitPre'
  obtain ⟨_, _, _, -, hw16, -⟩ := hpreI
  have hLW : P.L < 2 ^ P.w := hW P.L (by simp)
  have hqW : q < 2 ^ P.w := phaseBase_lt_pow hL1 hw16 hnvW
  have htbl_slot_lt_h : tbl' + slot < h := bucket_slot_lt_of_foot hfoot hslot
  have htbl_cap_le_h : tbl' + cap ≤ h := bucket_tbl_end_le_of_foot hfoot (by omega)
  have hhW : h < 2 ^ P.w := hW h (by simp)
  have hbody : p.procs[b + bsIdxOp0 + 0]? =
      some (bucketSpanActivateStmt (b + bsOffParam + spanParamIdxPhaseBase)
        (b + bsOffDyn + dynSpannerInitOff)) := by
    have hg := hOps.get (i := 1) (by simp [bucketSpanOpsProcs])
    simpa only [bsIdxOp0, bsOffOps, Nat.add_zero, Nat.add_assoc, bucketSpanOpsProcs,
      List.getElem_cons_succ, List.getElem_cons_zero] using hg
  refine ⟨_, hbody, ?_⟩
  have hinitArgs_eq : initArgs = [P.L, q, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] := rfl
  have hinitW : ∀ a ∈ initArgs, a < 2 ^ P.w := by
    intro a ha
    rw [hinitArgs_eq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hLW
    · exact hqW
    · exact hW P.vCap (by simp)
    · exact hW P.eCap (by simp)
    · exact hW a (by simp)
    · exact hW a (by simp)
    · exact hW a (by simp)
    · exact hW a (by simp)
    · exact hhW
  have hheapInit : heapArg initArgs = h := by rw [hinitArgs_eq]; rfl
  have hSpaceInit : (bucketSpannerDS P cap).space 0 S
      [tbl', slot, P.L, P.splitBound, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] mem =
      (dynSpannerDS P).initSpace initArgs mem := by
    simp only [bucketSpannerDS, ← hinitArgs]
  -- The bank of the new slot, paid for by the cost of the initialization.
  set B := DSHist.bank P ⟨initArgsGraph initArgs mem, []⟩ with hB
  have hDSInit : MeetsContract P.w p (b + bsOffDyn + dynSpannerInitOff)
      { pre := fun a m => a = initArgs ∧ m = mem
        post := fun a m ret m' => ∃ s' x',
          (dynSpannerRep P).rep h s' x' m' ∧
          (dynSpannerDS P).initPost a m s' m' ∧
          (dynSpannerRep P).Respects (fun _ => False) h ((dynSpannerDS P).initSpace a m) m ret
            h x' m' ∧
          B ≤ (dynSpannerDS P).initCost a m
        cost := fun a m => (dynSpannerDS P).initCost a m - B } := by
    rintro a m pos' ω' _ ⟨haeq, hmeq⟩
    subst a; subst m
    obtain ⟨bd, hbd, o', st', c', hr', s', x', hrep', hpost', hresp', hc'⟩ :=
      hImp.2.1 initArgs mem pos' ω' hinitW hInitPre
        (by rw [hheapInit]; exact hz) (by rw [hheapInit, ← hSpaceInit]; exact hspace)
    rw [hheapInit] at hrep' hresp'
    have hbank : x'.1.bank P = B := by rw [hrep'.1, hpost'.1]
    have hc'' : c' + x'.1.bank P ≤ (dynSpannerDS P).initCost initArgs mem := hc'
    rw [hbank] at hc''
    exact ⟨bd, hbd, o', st', c', hr', ⟨s', x', hrep', hpost', hresp', by omega⟩,
      by show c' ≤ (dynSpannerDS P).initCost initArgs mem - B; omega⟩
  have hrun : ∃ o st' c,
      Runs P.w p ω (bucketSpanActivateStmt (b + bsOffParam + spanParamIdxPhaseBase)
        (b + bsOffDyn + dynSpannerInitOff))
        (startState [tbl', slot, P.L, P.splitBound, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] mem pos)
        o st' c ∧
      (∃ s' x' mem1,
        (dynSpannerRep P).rep h s' x' mem1 ∧
        (dynSpannerDS P).initPost initArgs mem s' mem1 ∧
        (dynSpannerRep P).Respects (fun _ => False) h
          ((dynSpannerDS P).initSpace initArgs mem) mem o.value h x' mem1 ∧
        st'.mem = Function.update mem1 (tbl' + slot) h ∧
        B ≤ (dynSpannerDS P).initCost initArgs mem) ∧
      c ≤ phaseBaseCost (nV + P.splitBound) P.L + ((dynSpannerDS P).initCost initArgs mem - B) +
        35 := by
    dsimp only [bucketSpanActivateStmt]
    refine runs_start_le ?_
    refine runs_seq_call_le (vs := [nV + P.splitBound, P.L])
      (phaseBase_meetsContract (w := P.w) hParam)
      (evalArgs_cons
        (Expr.eval_add (Expr.eval_reg_of_eq (v := nV) (by simp [startState]))
          (Expr.eval_reg_of_eq (v := P.splitBound) (by simp [startState])) (by omega)) <|
        evalArgs_cons (Expr.eval_reg_of_eq (v := P.L) (by simp [startState])) <| evalArgs_nil _ _)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> omega)
      ⟨rfl, hL1, hw16, hnvW, hLW⟩ ?_
    rintro retQ memQ posQ ⟨hmemQ, hretQ⟩
    subst memQ
    refine runs_seq_call_le (vs := initArgs) hDSInit
      (by
        rw [hinitArgs_eq]
        exact evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [hretQ, hq])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <| evalArgs_nil _ _)
      hinitW ⟨rfl, rfl⟩ ?_
    rintro retH mem1 pos1 ⟨s', x', hrep1, hpost1, hresp1, hBle⟩
    refine runs_seq_store_le (x := tbl' + slot) (v := h)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := tbl') (by simp [startState]))
        (Expr.eval_reg_of_eq (v := slot) (by simp [startState])) (by omega))
      (Expr.eval_reg_of_eq (v := h) (by simp [startState])) ?_
    refine runs_ret_le (v := retH) (Expr.eval_reg_of_eq (by simp))
      ⟨s', x', mem1, hrep1, hpost1, hresp1, rfl, hBle⟩ ?_
    simp only [Expr.size, argsSize_cons, argsSize_nil, phaseBaseContract, startState]
    omega
  obtain ⟨o, st', c, hr, ⟨s', x', mem1, hrep1, hpost1, hresp1, hmem', hBle⟩, hc⟩ := hrun
  have hbank : x'.1.bank P = B := by rw [hrep1.1, hpost1.1]
  obtain ⟨hlo, hhi, hz1, hframe1, hfoot1⟩ := hresp1
  obtain ⟨hs'eq, hcl82⟩ := hpost1
  set idx : Fin cap := ⟨slot, hslot⟩
  set S' : BucketSpannerState cap := S.set idx (some s')
  set x'B : BucketSpannerMeta P.L cap := x.set idx (some (h, x'))
  have hfoot1_ge : ∀ a, metaFoot h x'.2 a → h ≤ a ∧ a < o.value := fun a ha => by
    rcases hfoot1 a ha with hF | hR
    · exact False.elim hF
    · exact hR
  refine ⟨o, st', c, hr, S', x'B, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hslots, hdisj⟩ := hrep
    refine ⟨fun j => ?_, fun j₁ j₂ hne b₁ m₁ b₂ m₂ h₁ h₂ a ha₁ ha₂ => ?_⟩
    · by_cases hj : j = idx
      · subst hj
        simp only [S', x'B, BucketSpannerState.set, BucketSpannerMeta.set, Function.update_self]
        refine ⟨by rw [hmem']; exact Function.update_self _ _ _, ?_, fun a ha => ?_⟩
        · exact ((dynSpannerRep_local P) h s' x' mem1 st'.mem fun a ha => by
            rw [hmem', Function.update_of_ne]
            have := (hfoot1_ge a ha).1
            omega).1 hrep1
        · have := (hfoot1_ge a ha).1
          exact Or.inr (le_trans htbl_cap_le_h this)
      · have hjval : j.1 ≠ slot := fun heq => hj (Fin.ext heq)
        simp only [S', x'B, BucketSpannerState.set, BucketSpannerMeta.set, Function.update_of_ne hj]
        have hprev := hslots j
        have hcell_eq : st'.mem (tbl' + j.1) = mem (tbl' + j.1) := by
          rw [hmem', Function.update_of_ne (by omega)]
          exact hframe1 (tbl' + j.1) (bucket_slot_lt_of_foot hfoot j.2) id
        cases hSj : S j with
        | none =>
          cases hXj : x.slots j with
          | none => simp only [hSj, hXj] at hprev ⊢; exact hcell_eq.trans hprev
          | some _ => simp only [hSj, hXj] at hprev
        | some sj =>
          cases hXj : x.slots j with
          | none => simp only [hSj, hXj] at hprev
          | some bm =>
            rcases bm with ⟨bj, mj⟩
            simp only [hSj, hXj] at hprev ⊢
            obtain ⟨hbj, hrepj, hnotblj⟩ := hprev
            refine ⟨hcell_eq.trans hbj, ?_, hnotblj⟩
            exact ((dynSpannerRep_local P) bj sj mj mem st'.mem fun a ha => by
              have halt : a < h := hfoot a (Or.inr ⟨j, bj, mj, hXj, ha⟩)
              have hne_ts : a ≠ tbl' + slot := by
                rcases hnotblj a ha with h1 | h2 <;> omega
              rw [hmem', Function.update_of_ne hne_ts]
              exact (hframe1 a halt id).symm).1 hrepj
    · by_cases h1i : j₁ = idx
      · subst h1i
        have h2ne : j₂ ≠ idx := hne.symm
        simp only [x'B, BucketSpannerMeta.set, Function.update_self,
          Function.update_of_ne h2ne] at h₁ h₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
        have ha1ge := (hfoot1_ge a ha₁).1
        have ha2lt := hfoot a (Or.inr ⟨j₂, b₂, m₂, h₂, ha₂⟩)
        omega
      · by_cases h2i : j₂ = idx
        · subst h2i
          simp only [x'B, BucketSpannerMeta.set, Function.update_self,
            Function.update_of_ne h1i] at h₁ h₂
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
          have ha2ge := (hfoot1_ge a ha₂).1
          have ha1lt := hfoot a (Or.inr ⟨j₁, b₁, m₁, h₁, ha₁⟩)
          omega
        · simp only [x'B, BucketSpannerMeta.set, Function.update_of_ne h1i,
            Function.update_of_ne h2i] at h₁ h₂
          exact hdisj j₁ j₂ hne b₁ m₁ b₂ m₂ h₁ h₂ a ha₁ ha₂
  · refine ⟨hslot, ?_, ?_⟩
    · simp only [S', idx, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, hs'eq, hinitArgs]
    · simpa only [hs'eq] using hcl82
  · refine ⟨hlo, hhi, ?_, ?_, ?_⟩
    · intro a ha
      rw [hmem', Function.update_of_ne (by omega)]
      exact hz1 a ha
    · intro a ha hnf
      have hne_ts : a ≠ tbl' + slot := fun heq => hnf (Or.inl ⟨by omega, by omega⟩)
      rw [hmem', Function.update_of_ne hne_ts]
      exact hframe1 a ha id
    · intro a ha
      rcases ha with htbl | ⟨j, bj, mj, hj, ham⟩
      · exact Or.inl (Or.inl htbl)
      · by_cases hji : j = idx
        · subst hji
          simp only [x'B, BucketSpannerMeta.set, Function.update_self] at hj
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
          exact Or.inr (hfoot1_ge a ham)
        · simp only [x'B, BucketSpannerMeta.set, Function.update_of_ne hji] at hj
          exact Or.inl (Or.inr ⟨j, bj, mj, hj, ham⟩)
  · -- The potential grows by at most the bank `B` of the new slot.
    have hset : bucketPhi P x'B + bucketSlotBank P (x.slots idx) = bucketPhi P x + B := by
      have := bucketPhi_set P x idx (some (h, x'))
      simp only [bucketSlotBank, hbank] at this
      exact this
    show c + bucketPhi P x'B ≤ phaseBaseCost (nV + P.splitBound) P.L +
      (dynSpannerDS P).initCost initArgs mem + 35 + bucketPhi P x
    omega

end

end MinCostFlow.SparseCore.Program
