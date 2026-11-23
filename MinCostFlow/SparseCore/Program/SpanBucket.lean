module

public import MinCostFlow.SparseCore.Program.SpanBucketInit

import WordRAM.Tactic

/-!
# Multi-Bucket Dynamic Spanner Manager: Update, Readouts, and `Implements` (`SpanBucket`)

Completes the verification of `bucketSpannerDS P cap` (`SpanBucketDefs.lean`, `SpanBucketInit.lean`):

* `bucketSpannerDS_op1`: operation `1` (batch update on one bucket slot), preserving all other
  slots via `dynSpannerRep_local`.
* `bucketSpannerDS_readouts`: operations `2`, `3`, and `4` (`H` pointer, `G` pointer, and
  `piTotal` walk pointer readouts).
* `bucketSpannerDS_implements`: full `DSRep.Implements` for `bucketSpannerProcs P.impl b` against
  `bucketSpannerDS P cap`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## Private helpers -/

private lemma dsUpdatePre_handle_iff {P : DSParams} {s : DSHist} {b₁ b₂ batchPtr W h : ℕ}
    {mem : ℕ → ℕ} :
    DSUpdatePre P s [b₁, batchPtr, W, h] mem ↔ DSUpdatePre P s [b₂, batchPtr, W, h] mem := by
  constructor <;> rintro ⟨_, bp, W', h', heq, rest⟩
  · simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨-, rfl, rfl, rfl⟩
    exact ⟨b₂, batchPtr, W, h, rfl, rest⟩
  · simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨-, rfl, rfl, rfl⟩
    exact ⟨b₁, batchPtr, W, h, rfl, rest⟩

private lemma dsUpdatePost_handle_iff {P : DSParams} {s s' : DSHist} {b₁ b₂ batchPtr W h : ℕ}
    {mem mem' : ℕ → ℕ} :
    DSUpdatePost P s [b₁, batchPtr, W, h] mem s' mem' ↔
      DSUpdatePost P s [b₂, batchPtr, W, h] mem s' mem' := by
  simp only [DSUpdatePost, opBatch, opWords, List.getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

private lemma dsUpdateAmortCost_handle_eq {P : DSParams} {s : DSHist}
    {b₁ b₂ batchPtr W h : ℕ} {mem : ℕ → ℕ} :
    dsUpdateAmortCost P s [b₁, batchPtr, W, h] mem =
      dsUpdateAmortCost P s [b₂, batchPtr, W, h] mem := by
  simp only [dsUpdateAmortCost, opBatch, opWords, List.getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

private lemma dsUpdateOpSpace_handle_eq {P : DSParams} {s : DSHist} {b₁ b₂ batchPtr W h : ℕ}
    {mem : ℕ → ℕ} :
    dsUpdateOpSpace P s [b₁, batchPtr, W, h] mem = dsUpdateOpSpace P s [b₂, batchPtr, W, h] mem := by
  simp only [dsUpdateOpSpace, opBatch, opWords, List.getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]

private lemma foot_self_mem {L vCap eCap b : ℕ} {x : DynSpannerMeta L}
    (hvx : x.vCap = vCap) (hex : x.eCap = eCap) : metaFoot b x b :=
  Or.inl ⟨le_rfl, by rw [hvx, hex]; have := dsFixedSize_pos L vCap eCap; omega⟩

private lemma foot_fixed_lt_of_lt {L vCap eCap b h : ℕ} {x : DynSpannerMeta L}
    (hvx : x.vCap = vCap) (hex : x.eCap = eCap) (hfoot : ∀ a, metaFoot b x a → a < h) :
    b + dsFixedSize L vCap eCap ≤ h := by
  have hpos := dsFixedSize_pos L vCap eCap
  have hm : metaFoot b x (b + dsFixedSize L vCap eCap - 1) :=
    Or.inl ⟨by omega, by rw [hvx, hex]; omega⟩
  have := hfoot _ hm
  omega

/-! ## Operation `1` (update), operations `2..4` (readouts), and `DSRep.Implements` -/

/-- Operation `1` (update bucket) clause of `bucketSpannerDS_implements`. -/
private theorem bucketSpannerDS_op1 (P : DSParams) (cap : ℕ) {p : Program} {b : ℕ}
    (hp : p.HasAt b (bucketSpannerProcs P.impl b)) :
    ∀ tbl S x args mem pos ω, (∀ a ∈ args, a < 2 ^ P.w) → args.head? = some tbl →
      (bucketSpannerRep P cap).rep tbl S x mem → (bucketSpannerDS P cap).pre 1 S args mem →
      (∀ a, (bucketSpannerRep P cap).foot tbl x a → a < heapArg args) →
      ZeroFrom mem (heapArg args) →
      heapArg args + (bucketSpannerDS P cap).space 1 S args mem < 2 ^ P.w →
      ∃ body, p.procs[b + bsIdxOp0 + 1]? = some body ∧ ∃ o st' c,
        Runs P.w p ω body (startState args mem pos) o st' c ∧ ∃ S' x',
          (bucketSpannerRep P cap).rep tbl S' x' st'.mem ∧
          (bucketSpannerDS P cap).post 1 S args mem S' st'.mem ∧
          (bucketSpannerRep P cap).Respects ((bucketSpannerRep P cap).foot tbl x) (heapArg args)
            ((bucketSpannerDS P cap).space 1 S args mem) mem o.value tbl x' st'.mem ∧
          c + (bucketSpannerRep P cap).phi tbl x' st'.mem ≤
            (bucketSpannerDS P cap).cost 1 S args mem +
              (bucketSpannerRep P cap).phi tbl x mem := by
  intro tbl S x args mem pos ω hW hhead hrep hpre hfoot hz hspace
  obtain ⟨-, -, hOps, hDyn⟩ := bucketSpannerProcs_unpack hp
  have hImp := dynSpannerDSProcs_implements P hDyn
  obtain ⟨tbl', slot, batchPtr, W, h, rfl, hslot, s, hSs, hUpdPre⟩ := hpre
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  have hheap : heapArg [tbl', slot, batchPtr, W, h] = h := rfl
  rw [hheap] at hfoot hz hspace ⊢
  set idx : Fin cap := ⟨slot, hslot⟩
  obtain ⟨hslots, hdisj⟩ := hrep
  have hidx_rep := hslots idx
  cases hXi : x.slots idx with
  | none => simp only [hSs, hXi] at hidx_rep
  | some bm =>
    rcases bm with ⟨bslot, mslot⟩
    simp only [hSs, hXi] at hidx_rep
    obtain ⟨hbslot_mem, hrep_slot, hnotbl_slot⟩ := hidx_rep
    have htbl_slot_lt_h : tbl' + slot < h := bucket_slot_lt_of_foot hfoot hslot
    have htbl_cap_le_h : tbl' + cap ≤ h := bucket_tbl_end_le_of_foot hfoot (by omega)
    have hfoot_slot : ∀ a, metaFoot bslot mslot.2 a → a < h := fun a ha =>
      hfoot a (Or.inr ⟨idx, bslot, mslot, hXi, ha⟩)
    have hbslot_lt_h : bslot < h :=
      hfoot_slot bslot (foot_self_mem hrep_slot.2.1.2.2.2.2.2.2.2.1.1 hrep_slot.2.1.2.2.2.2.2.2.2.1.2.1)
    have hhW : h < 2 ^ P.w := hW h (by simp)
    have hSpaceEq : (bucketSpannerDS P cap).space 1 S [tbl', slot, batchPtr, W, h] mem =
        dsUpdateOpSpace P s [bslot, batchPtr, W, h] mem := by
      simp only [bucketSpannerDS, bucketUpdateSpace, List.getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, hslot, ↓reduceDIte]
      change (match S idx with | some s => dsUpdateOpSpace P s [0, batchPtr, W, h] mem | none => 0) = _
      rw [hSs]
      exact dsUpdateOpSpace_handle_eq
    have hCostEq : (bucketSpannerDS P cap).cost 1 S [tbl', slot, batchPtr, W, h] mem =
        dsUpdateAmortCost P s [bslot, batchPtr, W, h] mem + 20 := by
      simp only [bucketSpannerDS, bucketUpdateCost, List.getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, hslot, ↓reduceDIte]
      change (match S idx with
        | some s => dsUpdateAmortCost P s [0, batchPtr, W, h] mem + 20 | none => 0) = _
      rw [hSs]
      dsimp only
      rw [dsUpdateAmortCost_handle_eq (b₂ := bslot)]
    have hDSArgsW : ∀ a ∈ [bslot, batchPtr, W, h], a < 2 ^ P.w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · omega
      · exact hW a (by simp)
      · exact hW a (by simp)
      · exact hhW
    -- The next history and the amortized cost of the update with the bank of `s`.
    set sN : DSHist := ⟨s.G₀, s.Us ++ [(opBatch P s [bslot, batchPtr, W, h] mem).1]⟩ with hsN
    set A := dsUpdateAmortCost P s [bslot, batchPtr, W, h] mem + s.bank P with hA
    have hDSUpd : MeetsContract P.w p (b + bsOffDyn + dynSpannerUpdateOff)
        { pre := fun a m => a = [bslot, batchPtr, W, h] ∧ m = mem
          post := fun a m ret m' => ∃ s' x',
            (dynSpannerRep P).rep bslot s' x' m' ∧
            (dynSpannerDS P).post 0 s a m s' m' ∧
            (dynSpannerRep P).Respects (metaFoot bslot mslot.2) h
              ((dynSpannerDS P).space 0 s a m) m ret bslot x' m' ∧
            sN.bank P ≤ A
          cost := fun a m => A - sN.bank P } := by
      rintro a m pos' ω' _ ⟨haeq, hmeq⟩
      subst a; subst m
      obtain ⟨bd, hbd, o', st', c', hr', s', x', hrep', hpost', hresp', hc'⟩ :=
        hImp.2.2 0 bslot s mslot [bslot, batchPtr, W, h] mem pos' ω' hDSArgsW rfl hrep_slot
          ⟨rfl, dsUpdatePre_handle_iff.mp hUpdPre⟩ hfoot_slot hz
          (by
            change h + dsUpdateOpSpace P s [bslot, batchPtr, W, h] mem < 2 ^ P.w
            rw [← hSpaceEq]; exact hspace)
      have hbank' : x'.1.bank P = sN.bank P := by rw [hrep'.1, hpost'.1]
      have hbank : mslot.1.bank P = s.bank P := by rw [hrep_slot.1]
      have hc'' : c' + x'.1.bank P ≤
          dsUpdateAmortCost P s [bslot, batchPtr, W, h] mem + mslot.1.bank P := hc'
      rw [hbank', hbank] at hc''
      exact ⟨bd, by simpa only [Nat.add_zero] using hbd, o', st', c', hr',
        ⟨s', x', hrep', hpost', hresp', by omega⟩, by show c' ≤ A - sN.bank P; omega⟩
    have hbody : p.procs[b + bsIdxOp0 + 1]? =
        some (bucketSpanUpdateStmt (b + bsOffDyn + dynSpannerUpdateOff)) := by
      have hg := hOps.get (i := 2) (by simp [bucketSpanOpsProcs])
      simpa only [bsIdxOp0, bsOffOps, Nat.add_assoc, bucketSpanOpsProcs,
        List.getElem_cons_succ, List.getElem_cons_zero] using hg
    refine ⟨_, hbody, ?_⟩
    have hrun : ∃ o st' c,
        Runs P.w p ω (bucketSpanUpdateStmt (b + bsOffDyn + dynSpannerUpdateOff))
          (startState [tbl', slot, batchPtr, W, h] mem pos) o st' c ∧
        (∃ s' m',
          (dynSpannerRep P).rep bslot s' m' st'.mem ∧
          DSUpdatePost P s [bslot, batchPtr, W, h] mem s' st'.mem ∧
          (dynSpannerRep P).Respects (metaFoot bslot mslot.2) h
            (dsUpdateOpSpace P s [bslot, batchPtr, W, h] mem) mem o.value bslot m' st'.mem ∧
          sN.bank P ≤ A) ∧
        c ≤ A - sN.bank P + 20 := by
      dsimp only [bucketSpanUpdateStmt]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := bslot)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := tbl') (by simp [startState]))
            (Expr.eval_reg_of_eq (v := slot) (by simp [startState])) (by omega))
          hbslot_mem) ?_
      refine runs_seq_call_le (vs := [bslot, batchPtr, W, h]) hDSUpd
        (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <| evalArgs_nil _ _)
        hDSArgsW ⟨rfl, rfl⟩ ?_
      rintro retH mem1 pos1 ⟨s', m', hrep', hpost', hresp', hAle⟩
      refine runs_ret_le (v := retH) (Expr.eval_reg_of_eq (by simp))
        ⟨s', m', hrep', hpost', hresp', hAle⟩ ?_
      simp only [Expr.size, argsSize_cons, argsSize_nil]
      omega
    obtain ⟨o, st', c, hr, ⟨s', m', hrep', hpost', hresp', hAle⟩, hc⟩ := hrun
    have hbank' : m'.1.bank P = sN.bank P := by rw [hrep'.1, hpost'.1]
    have hbank : mslot.1.bank P = s.bank P := by rw [hrep_slot.1]
    obtain ⟨hlo, hhi, hz', hframe', hfoot'⟩ := hresp'
    set S' : BucketSpannerState cap := S.set idx (some s')
    set x'B : BucketSpannerMeta P.L cap := x.set idx (some (bslot, m'))
    have hnotbl_new : ∀ a, metaFoot bslot m'.2 a → a < tbl' ∨ tbl' + cap ≤ a := fun a ha => by
      rcases hfoot' a ha with hold | hnew
      · exact hnotbl_slot a hold
      · exact Or.inr (le_trans htbl_cap_le_h hnew.1)
    have htbl_unch : ∀ j : Fin cap, st'.mem (tbl' + j.1) = mem (tbl' + j.1) := fun j =>
      hframe' (tbl' + j.1) (bucket_slot_lt_of_foot hfoot j.2) fun hm => by
        rcases hnotbl_slot (tbl' + j.1) hm with h1 | h2 <;> omega
    refine ⟨o, st', c, hr, S', x'B, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun j => ?_, fun j₁ j₂ hne b₁ m₁ b₂ m₂ h₁ h₂ a ha₁ ha₂ => ?_⟩
      · by_cases hj : j = idx
        · subst hj
          simp only [S', x'B, BucketSpannerState.set, BucketSpannerMeta.set, Function.update_self]
          exact ⟨(htbl_unch idx).trans hbslot_mem, hrep', hnotbl_new⟩
        · simp only [S', x'B, BucketSpannerState.set, BucketSpannerMeta.set, Function.update_of_ne hj]
          have hprev := hslots j
          cases hSj : S j with
          | none =>
            cases hXj : x.slots j with
            | none => simp only [hSj, hXj] at hprev ⊢; exact (htbl_unch j).trans hprev
            | some _ => simp only [hSj, hXj] at hprev
          | some sj =>
            cases hXj : x.slots j with
            | none => simp only [hSj, hXj] at hprev
            | some bm =>
              rcases bm with ⟨bj, mj⟩
              simp only [hSj, hXj] at hprev ⊢
              obtain ⟨hbj, hrepj, hnotblj⟩ := hprev
              refine ⟨(htbl_unch j).trans hbj, ?_, hnotblj⟩
              exact ((dynSpannerRep_local P) bj sj mj mem st'.mem fun a ha =>
                (hframe' a (hfoot a (Or.inr ⟨j, bj, mj, hXj, ha⟩))
                  fun hm => hdisj idx j (Ne.symm hj) bslot mslot bj mj hXi hXj a hm ha).symm).1
                hrepj
      · by_cases h1i : j₁ = idx
        · subst h1i
          have h2ne : j₂ ≠ idx := hne.symm
          simp only [x'B, BucketSpannerMeta.set, Function.update_self,
            Function.update_of_ne h2ne] at h₁ h₂
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
          rcases hfoot' a ha₁ with hold | hnew
          · exact hdisj idx j₂ hne bslot mslot b₂ m₂ hXi h₂ a hold ha₂
          · have halt := hfoot a (Or.inr ⟨j₂, b₂, m₂, h₂, ha₂⟩)
            omega
        · by_cases h2i : j₂ = idx
          · subst h2i
            simp only [x'B, BucketSpannerMeta.set, Function.update_self,
              Function.update_of_ne h1i] at h₁ h₂
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
            rcases hfoot' a ha₂ with hold | hnew
            · exact hdisj j₁ idx hne b₁ m₁ bslot mslot h₁ hXi a ha₁ hold
            · have halt := hfoot a (Or.inr ⟨j₁, b₁, m₁, h₁, ha₁⟩)
              omega
          · simp only [x'B, BucketSpannerMeta.set, Function.update_of_ne h1i,
              Function.update_of_ne h2i] at h₁ h₂
            exact hdisj j₁ j₂ hne b₁ m₁ b₂ m₂ h₁ h₂ a ha₁ ha₂
    · refine ⟨hslot, s, s', hSs, ?_, ?_⟩
      · simp only [S', idx, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some]
      · simpa only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
          using dsUpdatePost_handle_iff.mp hpost'
    · refine ⟨hlo, hSpaceEq ▸ hhi, hz', fun a ha hnf =>
        hframe' a ha fun hm => hnf (Or.inr ⟨idx, bslot, mslot, hXi, hm⟩), fun a ha => ?_⟩
      rcases ha with htbl | ⟨j, bj, mj, hj, ham⟩
      · exact Or.inl (Or.inl htbl)
      · by_cases hji : j = idx
        · subst hji
          simp only [x'B, BucketSpannerMeta.set, Function.update_self] at hj
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
          rcases hfoot' a ham with hold | hnew
          · exact Or.inl (Or.inr ⟨idx, bslot, mslot, hXi, hold⟩)
          · exact Or.inr hnew
        · simp only [x'B, BucketSpannerMeta.set, Function.update_of_ne hji] at hj
          exact Or.inl (Or.inr ⟨j, bj, mj, hj, ham⟩)
    · -- The potential changes by the bank of `s'` minus the bank of `s`.
      have hset : bucketPhi P x'B + s.bank P = bucketPhi P x + sN.bank P := by
        have := bucketPhi_set P x idx (some (bslot, m'))
        simp only [bucketSlotBank, hXi, hbank, hbank'] at this
        exact this
      rw [hCostEq]
      show c + bucketPhi P x'B ≤ dsUpdateAmortCost P s [bslot, batchPtr, W, h] mem + 20 +
        bucketPhi P x
      omega

/-- Operations `2`, `3`, and `4` (readouts `H`, `G`, and `piTotal`) of `bucketSpannerDS_implements`. -/
private theorem bucketSpannerDS_readouts (P : DSParams) (cap : ℕ) {p : Program} {b : ℕ}
    (hp : p.HasAt b (bucketSpannerProcs P.impl b)) :
    ∀ i, (i = 2 ∨ i = 3 ∨ i = 4) →
    ∀ tbl S x args mem pos ω, (∀ a ∈ args, a < 2 ^ P.w) → args.head? = some tbl →
      (bucketSpannerRep P cap).rep tbl S x mem → (bucketSpannerDS P cap).pre i S args mem →
      (∀ a, (bucketSpannerRep P cap).foot tbl x a → a < heapArg args) →
      ZeroFrom mem (heapArg args) →
      heapArg args + (bucketSpannerDS P cap).space i S args mem < 2 ^ P.w →
      ∃ body, p.procs[b + bsIdxOp0 + i]? = some body ∧ ∃ o st' c,
        Runs P.w p ω body (startState args mem pos) o st' c ∧ ∃ S' x',
          (bucketSpannerRep P cap).rep tbl S' x' st'.mem ∧
          (bucketSpannerDS P cap).post i S args mem S' st'.mem ∧
          (bucketSpannerRep P cap).Respects ((bucketSpannerRep P cap).foot tbl x) (heapArg args)
            ((bucketSpannerDS P cap).space i S args mem) mem o.value tbl x' st'.mem ∧
          c + (bucketSpannerRep P cap).phi tbl x' st'.mem ≤
            (bucketSpannerDS P cap).cost i S args mem +
              (bucketSpannerRep P cap).phi tbl x mem := by
  intro i hi tbl S x args mem pos ω hW hhead hrep hpre hfoot hz hspace
  obtain ⟨-, hRead, hOps, -⟩ := bucketSpannerProcs_unpack hp
  rcases hi with rfl | rfl | rfl
  · -- Operation 2: read H pointer
    obtain ⟨tbl', slot, h, rfl, hw16, hslot, s, hSs⟩ := hpre
    simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    have hheap : heapArg [tbl', slot, h] = h := rfl
    rw [hheap] at hfoot hz hspace ⊢
    set idx : Fin cap := ⟨slot, hslot⟩
    have hidx := hrep.1 idx
    cases hXi : x.slots idx with
    | none => simp only [hSs, hXi] at hidx
    | some bm =>
      rcases bm with ⟨bslot, mslot⟩
      simp only [hSs, hXi] at hidx
      obtain ⟨hbslot_mem, hrep_slot, _⟩ := hidx
      have hfoot_slot : ∀ a, metaFoot bslot mslot.2 a → a < h := fun a ha =>
        hfoot a (Or.inr ⟨idx, bslot, mslot, hXi, ha⟩)
      have hfix_le : bslot + dsFixedSize P.L P.vCap P.eCap ≤ h :=
        foot_fixed_lt_of_lt hrep_slot.2.1.2.2.2.2.2.2.2.1.1 hrep_slot.2.1.2.2.2.2.2.2.2.1.2.1 hfoot_slot
      have htbl_slot_lt : tbl' + slot < h := bucket_slot_lt_of_foot hfoot hslot
      have hbody : p.procs[b + bsIdxOp0 + 2]? =
          some (bucketSpanReadHStmt (b + bsOffRead + spanReadIdxHPtr)) := by
        have hg := hOps.get (i := 3) (by simp [bucketSpanOpsProcs])
        simpa only [bsIdxOp0, bsOffOps, Nat.add_assoc, bucketSpanOpsProcs,
          List.getElem_cons_succ, List.getElem_cons_zero] using hg
      refine ⟨_, hbody, ?_⟩
      have hrun : ∃ o st' c,
          Runs P.w p ω (bucketSpanReadHStmt (b + bsOffRead + spanReadIdxHPtr))
            (startState [tbl', slot, h] mem pos) o st' c ∧
          (o.value = h + 1 ∧ st'.mem = Function.update mem h (dsHPtr bslot P.vCap P.eCap) ∧
            DynGraphAt mem (dsHPtr bslot P.vCap P.eCap) P.vCap P.eCap (s.state P).H) ∧
          c ≤ 60 := by
        dsimp only [bucketSpanReadHStmt]
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := bslot)
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (v := tbl') (by simp [startState]))
              (Expr.eval_reg_of_eq (v := slot) (by simp [startState])) (by omega))
            hbslot_mem) ?_
        refine runs_seq_call_le (vs := [bslot])
          (spanHPtr_meetsContract (P := P) (b := bslot) (s := s) (x := mslot.2) hRead)
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <| evalArgs_nil _ _)
          (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv; omega)
          ⟨rfl, hw16, hrep_slot.2.1, by omega⟩ ?_
        rintro retP mem1 pos1 ⟨hm1, hretP, hH⟩
        subst mem1; subst hretP
        refine runs_seq_store_le (x := h) (v := dsHPtr bslot P.vCap P.eCap)
          (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_ret_le (v := h + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
            (Expr.eval_const (by omega)) hspace)
          ⟨rfl, rfl, hH⟩ ?_
        simp only [Expr.size, argsSize_cons, argsSize_nil, spanHPtrContract]
        omega
      obtain ⟨o, st', c, hr, ⟨hov, hmem', hH⟩, hc⟩ := hrun
      refine ⟨o, st', c, hr, S, x, ?_, ?_, ?_, by simpa [bucketSpannerRep, bucketSpannerDS] using hc⟩
      · exact ((bucketSpannerRep_local P cap) tbl' S x mem st'.mem fun a ha => by
          rw [hmem', Function.update_of_ne (by have := hfoot a ha; omega)]).1 hrep
      · refine ⟨rfl, hslot, s, hSs, ?_⟩
        rw [hmem', hheap, Function.update_self]
        refine dynGraphAt_of_agree hH fun a ha1 ha2 => ?_
        have hlt_fix : dsHPtr bslot P.vCap P.eCap + dynGraphSize P.vCap P.eCap ≤
            bslot + dsFixedSize P.L P.vCap P.eCap :=
          (stepZero_fixed_lt bslot P.L P.vCap P.eCap).2.2.1.2
        rw [Function.update_of_ne (by omega)]
      · refine ⟨by omega, by show o.value ≤ h + 1; omega,
          fun a ha => by rw [hmem', Function.update_of_ne (by omega)]; exact hz a (by omega),
          fun a ha _ => by rw [hmem', Function.update_of_ne (by omega)],
          fun a ha => Or.inl ha⟩
  · -- Operation 3: read G pointer
    obtain ⟨tbl', slot, h, rfl, hw16, hslot, s, hSs⟩ := hpre
    simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    have hheap : heapArg [tbl', slot, h] = h := rfl
    rw [hheap] at hfoot hz hspace ⊢
    set idx : Fin cap := ⟨slot, hslot⟩
    have hidx := hrep.1 idx
    cases hXi : x.slots idx with
    | none => simp only [hSs, hXi] at hidx
    | some bm =>
      rcases bm with ⟨bslot, mslot⟩
      simp only [hSs, hXi] at hidx
      obtain ⟨hbslot_mem, hrep_slot, _⟩ := hidx
      have hfoot_slot : ∀ a, metaFoot bslot mslot.2 a → a < h := fun a ha =>
        hfoot a (Or.inr ⟨idx, bslot, mslot, hXi, ha⟩)
      have hfix_le : bslot + dsFixedSize P.L P.vCap P.eCap ≤ h :=
        foot_fixed_lt_of_lt hrep_slot.2.1.2.2.2.2.2.2.2.1.1 hrep_slot.2.1.2.2.2.2.2.2.2.1.2.1 hfoot_slot
      have htbl_slot_lt : tbl' + slot < h := bucket_slot_lt_of_foot hfoot hslot
      have hbody : p.procs[b + bsIdxOp0 + 3]? =
          some (bucketSpanReadGStmt (b + bsOffRead + spanReadIdxGPtr)) := by
        have hg := hOps.get (i := 4) (by simp [bucketSpanOpsProcs])
        simpa only [bsIdxOp0, bsOffOps, Nat.add_assoc, bucketSpanOpsProcs,
          List.getElem_cons_succ, List.getElem_cons_zero] using hg
      refine ⟨_, hbody, ?_⟩
      have hrun : ∃ o st' c,
          Runs P.w p ω (bucketSpanReadGStmt (b + bsOffRead + spanReadIdxGPtr))
            (startState [tbl', slot, h] mem pos) o st' c ∧
          (o.value = h + 1 ∧ st'.mem = Function.update mem h (dsGPtr bslot) ∧
            DynGraphAt mem (dsGPtr bslot) P.vCap P.eCap (s.state P).G) ∧
          c ≤ 35 := by
        dsimp only [bucketSpanReadGStmt]
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := bslot)
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (v := tbl') (by simp [startState]))
              (Expr.eval_reg_of_eq (v := slot) (by simp [startState])) (by omega))
            hbslot_mem) ?_
        refine runs_seq_call_le (vs := [bslot])
          (spanGPtr_meetsContract (P := P) (b := bslot) (s := s) (x := mslot.2) hRead)
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <| evalArgs_nil _ _)
          (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv; omega)
          ⟨rfl, hw16, hrep_slot.2.1, by omega⟩ ?_
        rintro retP mem1 pos1 ⟨hm1, hretP, hG⟩
        subst mem1; subst hretP
        refine runs_seq_store_le (x := h) (v := dsGPtr bslot)
          (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_ret_le (v := h + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
            (Expr.eval_const (by omega)) hspace)
          ⟨rfl, rfl, hG⟩ ?_
        simp only [Expr.size, argsSize_cons, argsSize_nil, spanGPtrContract]
        omega
      obtain ⟨o, st', c, hr, ⟨hov, hmem', hG⟩, hc⟩ := hrun
      refine ⟨o, st', c, hr, S, x, ?_, ?_, ?_, by simpa [bucketSpannerRep, bucketSpannerDS] using hc⟩
      · exact ((bucketSpannerRep_local P cap) tbl' S x mem st'.mem fun a ha => by
          rw [hmem', Function.update_of_ne (by have := hfoot a ha; omega)]).1 hrep
      · refine ⟨rfl, hslot, s, hSs, ?_⟩
        rw [hmem', hheap, Function.update_self]
        refine dynGraphAt_of_agree hG fun a ha1 ha2 => ?_
        have hlt_fix : dsGPtr bslot + dynGraphSize P.vCap P.eCap ≤
            bslot + dsFixedSize P.L P.vCap P.eCap :=
          (stepZero_fixed_lt bslot P.L P.vCap P.eCap).2.1.2
        rw [Function.update_of_ne (by omega)]
      · refine ⟨by omega, by show o.value ≤ h + 1; omega,
          fun a ha => by rw [hmem', Function.update_of_ne (by omega)]; exact hz a (by omega),
          fun a ha _ => by rw [hmem', Function.update_of_ne (by omega)],
          fun a ha => Or.inl ha⟩
  · -- Operation 4: read piTotal walk pointer
    obtain ⟨tbl', slot, e, h, rfl, hw16, hslot, s, hSs, heG⟩ := hpre
    simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    have hheap : heapArg [tbl', slot, e, h] = h := rfl
    rw [hheap] at hfoot hz hspace ⊢
    set idx : Fin cap := ⟨slot, hslot⟩
    have hidx := hrep.1 idx
    cases hXi : x.slots idx with
    | none => simp only [hSs, hXi] at hidx
    | some bm =>
      rcases bm with ⟨bslot, mslot⟩
      simp only [hSs, hXi] at hidx
      obtain ⟨hbslot_mem, hrep_slot, _⟩ := hidx
      have hfoot_slot : ∀ a, metaFoot bslot mslot.2 a → a < h := fun a ha =>
        hfoot a (Or.inr ⟨idx, bslot, mslot, hXi, ha⟩)
      have hfix_le : bslot + dsFixedSize P.L P.vCap P.eCap ≤ h :=
        foot_fixed_lt_of_lt hrep_slot.2.1.2.2.2.2.2.2.2.1.1 hrep_slot.2.1.2.2.2.2.2.2.2.1.2.1 hfoot_slot
      have htbl_slot_lt : tbl' + slot < h := bucket_slot_lt_of_foot hfoot hslot
      have hbody : p.procs[b + bsIdxOp0 + 4]? =
          some (bucketSpanReadPiStmt (b + bsOffRead + spanReadIdxPiWalkPtr)) := by
        have hg := hOps.get (i := 5) (by simp [bucketSpanOpsProcs])
        simpa only [bsIdxOp0, bsOffOps, Nat.add_assoc, bucketSpanOpsProcs,
          List.getElem_cons_succ, List.getElem_cons_zero] using hg
      refine ⟨_, hbody, ?_⟩
      have hrun : ∃ o st' c,
          Runs P.w p ω (bucketSpanReadPiStmt (b + bsOffRead + spanReadIdxPiWalkPtr))
            (startState [tbl', slot, e, h] mem pos) o st' c ∧
          (∃ ptr, o.value = h + 1 ∧ st'.mem = Function.update mem h ptr ∧
            MWalkAt mem ptr (piTotal (s.state P) e) ∧
            RangeInHeapFoot mslot.2 ptr (ptr + (mWalkEncode (piTotal (s.state P) e)).length)) ∧
          c ≤ spanPiWalkPtrCost P.L + 30 := by
        dsimp only [bucketSpanReadPiStmt]
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := bslot)
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (v := tbl') (by simp [startState]))
              (Expr.eval_reg_of_eq (v := slot) (by simp [startState])) (by omega))
            hbslot_mem) ?_
        refine runs_seq_call_le (vs := [bslot, e])
          (spanPiWalkPtr_meetsContract (P := P) (b := bslot) (e := e) (s := s) (x := mslot.2) hRead)
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <| evalArgs_nil _ _)
          (fun v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl
            · omega
            · exact hW v (by simp))
          ⟨rfl, hw16, hrep_slot.2.1, heG, by omega,
            fun a ha => lt_trans (hfoot_slot a (Or.inr ha)) (by omega)⟩ ?_
        rintro retP mem1 pos1 ⟨hm1, hMW, hRange⟩
        subst mem1
        refine runs_seq_store_le (x := h) (v := retP)
          (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_ret_le (v := h + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
            (Expr.eval_const (by omega)) hspace)
          ⟨retP, rfl, rfl, hMW, hRange⟩ ?_
        simp only [Expr.size, argsSize_cons, argsSize_nil, spanPiWalkPtrContract]
        omega
      obtain ⟨o, st', c, hr, ⟨ptr, hov, hmem', hMW, hRange⟩, hc⟩ := hrun
      refine ⟨o, st', c, hr, S, x, ?_, ?_, ?_, by simpa [bucketSpannerRep, bucketSpannerDS] using hc⟩
      · exact ((bucketSpannerRep_local P cap) tbl' S x mem st'.mem fun a ha => by
          rw [hmem', Function.update_of_ne (by have := hfoot a ha; omega)]).1 hrep
      · refine ⟨rfl, hslot, s, hSs, ?_⟩
        rw [hmem', hheap, Function.update_self]
        simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
        intro j hj
        have hlt_h : ptr + j < h :=
          hfoot_slot (ptr + j) (Or.inr (hRange (ptr + j) (Nat.le_add_right _ _) (by omega)))
        rw [Function.update_of_ne (by omega)]
        exact hMW j hj
      · refine ⟨by omega, by show o.value ≤ h + 1; omega,
          fun a ha => by rw [hmem', Function.update_of_ne (by omega)]; exact hz a (by omega),
          fun a ha _ => by rw [hmem', Function.update_of_ne (by omega)],
          fun a ha => Or.inl ha⟩

public section

/-- **Multi-bucket dynamic spanner data structure implementation.** Any program containing
`bucketSpannerProcs P.impl b` at index `b` implements `bucketSpannerDS P cap` with representation
`bucketSpannerRep P cap`, initialization at `b + bsIdxInit`, and operations `0..4` at
`b + bsIdxOp0 + i`. -/
theorem bucketSpannerDS_implements (P : DSParams) (cap : ℕ) {p : Program} {b : ℕ}
    (hp : p.HasAt b (bucketSpannerProcs P.impl b)) :
    (bucketSpannerRep P cap).Implements P.w p (b + bsIdxInit) (fun i => b + bsIdxOp0 + i)
      (bucketSpannerDS P cap) := by
  refine ⟨bucketSpannerRep_local P cap, bucketSpannerDS_init P cap hp, ?_⟩
  intro i tbl S x args mem pos ω hW hhead hrep hpre hfoot hz hspace
  match i with
  | 0 => exact bucketSpannerDS_op0 P cap hp tbl S x args mem pos ω hW hhead hrep hpre hfoot hz hspace
  | 1 => exact bucketSpannerDS_op1 P cap hp tbl S x args mem pos ω hW hhead hrep hpre hfoot hz hspace
  | 2 =>
    exact bucketSpannerDS_readouts P cap hp 2 (Or.inl rfl) tbl S x args mem pos ω hW hhead
      hrep hpre hfoot hz hspace
  | 3 =>
    exact bucketSpannerDS_readouts P cap hp 3 (Or.inr (Or.inl rfl)) tbl S x args mem pos ω hW
      hhead hrep hpre hfoot hz hspace
  | 4 =>
    exact bucketSpannerDS_readouts P cap hp 4 (Or.inr (Or.inr rfl)) tbl S x args mem pos ω hW
      hhead hrep hpre hfoot hz hspace
  | _ + 5 => exact False.elim hpre

end

end MinCostFlow.SparseCore.Program
