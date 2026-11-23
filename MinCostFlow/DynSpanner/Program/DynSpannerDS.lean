module

public import MinCostFlow.DynSpanner.Program.DynSpannerDSInit

/-!
# The data structure of Theorem 8.2

`dynSpannerDS_implements` proves that the procedures `dsInitStmt` (the initialization) and
`dsUpdateOpStmt` (operation `0`, a batch of updates) implement the data structure
`dynSpannerDS` of Theorem 8.2 (page 39) with the representation `dynSpannerRep`.

The update clause is `dynSpannerDS_update`. It turns the abstract state and the representation
into the precondition of `dsUpdateOp_meetsContract`, on the list `us = Us.flatten ++ U` of all
updates from time `k₀ = |Us.flatten|`:
* the facts on the history carry over from `Us.flatten` to `us` (`DynSpannerDSPrefix.lean`), and
  `SnapInv` comes from `runInv_all`;
* the state block, the generation word and the footprint come from `DSRepAt`.
Then it reads the post of the batch loop as the new representation (the model state after the
batch is `runState us (k₀ + |U|)` by `update_slice_spec`), the outputs in memory, and the clauses
of Theorem 8.2 for the new history (`theorem82Clauses_of`). For the cost, the bound of the loop is
at most the costs `dsStepAmortCost` of the new steps plus `1410 W + 460` (`dsUpdateLoopCost_le`).
The bank pays for these steps: it grows by the charge of the batch (`dsBankTotal_append`), its
spent part grows by the costs of the new steps (`dsSpent_append`), and it is nonnegative before
and after the batch (`dsSpent_le_bankTotal`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The update clause of `DSRep.Implements` for the data structure of Theorem 8.2. -/
theorem dynSpannerDS_update (P : DSParams) {p : Program} {bs : UpdateLoopBases} {bOp : ℕ}
    (hps : HasUpdateLoopProcs P.impl p bs) (hpOp : p.HasAt bOp (dsOpProcs bs.sz.bAux bs.bUL)) :
    ∀ i b s x args mem pos ω, (∀ a ∈ args, a < 2 ^ P.w) → args.head? = some b →
      (dynSpannerRep P).rep b s x mem → (dynSpannerDS P).pre i s args mem →
      (∀ a, (dynSpannerRep P).foot b x a → a < heapArg args) → ZeroFrom mem (heapArg args) →
      heapArg args + (dynSpannerDS P).space i s args mem < 2 ^ P.w →
      ∃ body, p.procs[bOp + i]? = some body ∧ ∃ o st' c,
        Runs P.w p ω body (startState args mem pos) o st' c ∧ ∃ s' x',
          (dynSpannerRep P).rep b s' x' st'.mem ∧ (dynSpannerDS P).post i s args mem s' st'.mem ∧
          (dynSpannerRep P).Respects ((dynSpannerRep P).foot b x) (heapArg args)
            ((dynSpannerDS P).space i s args mem) mem o.value b x' st'.mem ∧
          c + (dynSpannerRep P).phi b x' st'.mem ≤
            (dynSpannerDS P).cost i s args mem + (dynSpannerRep P).phi b x mem := by
  intro i b s x args mem pos ω hW hhead hrep hpre0 hfootlt hz hspace
  obtain ⟨s0, x⟩ := x
  obtain ⟨rfl, hpre⟩ := hpre0
  obtain ⟨b', batchPtr, W, h, rfl, hw16, hbody, hWeq, hbat, hbatw, hBVU, hdsU, hcaps, hsplit,
    hgenw, hkw, hqw, hWOK⟩ := hpre
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  obtain ⟨hs0, ⟨hL, hVG₀, hGm₀, hE₀, hBVf, hdsf, hsplitf, hState, hRev, hgen⟩, hpst⟩ := hrep
  simp only at hs0
  subst s0
  -- The batch and the list of all updates.
  set U := (opBatch P s [b', batchPtr, W, h] mem).1 with hU
  set lens := (opBatch P s [b', batchPtr, W, h] mem).2 with hlens
  set us := s.flat ++ U with hus
  set k₀ := s.flat.length with hk₀
  have hheap : heapArg [b', batchPtr, W, h] = h := rfl
  rw [hheap] at hfootlt hz hspace ⊢
  have hq1 : 1 ≤ s.q P := le_trans (by norm_num) (two_le_phaseBase _ _)
  have hGeq : (s.state P).G = s.G₀.applyBatch s.flat := by
    have h1 := (snapInv_of_history P hVG₀ hL hq1 hGm₀ hBVf hdsf s.flat.length le_rfl).G_eq
    rw [List.take_length] at h1
    exact h1
  have hBVus : s.G₀.BatchIsValid us :=
    (batchIsValid_append _ _ _).mpr ⟨hBVf, by rw [← hGeq]; exact hBVU⟩
  have hdsus : ∀ u ∈ us, isDelOrSplit u := fun u hu => by
    rcases List.mem_append.mp hu with h1 | h1
    · exact hdsf u h1
    · exact hdsU u h1
  have hslice : ∀ i (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi) := fun i hi => by
    rw [hus, hk₀, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hi
  have hSnap : ∀ t ≤ k₀, SnapInv s.G₀ P.L (s.q P) P.mMax
      (canonicalSparsifyParams P.impl P.mMax).absorbTime (canonicalSparsify P.impl) us t :=
    fun t ht => snapInv_of_history P hVG₀ hL hq1 hGm₀ hBVus hdsus t
      (le_trans ht (by simp [hus, hk₀]))
  have hst0 : runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) us k₀ = s.state P :=
    runState_append s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat U k₀ le_rfl
  have hState' : DynSpannerStateAt P.L P.vCap P.eCap b' mem x
      (runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) us k₀) := hst0 ▸ hState
  have hRev' := revHistoryInv_append U (le_refl k₀) hRev
  have hfixpos := ((stepZero_fixed_lt b' P.L P.vCap P.eCap).1 0 (by decide)).2
  have hfix : b' + dsFixedSize P.L P.vCap P.eCap ≤ h := by
    have hm : metaFoot b' x (b' + dsFixedSize P.L P.vCap P.eCap - 1) :=
      Or.inl ⟨by omega, by rw [hState.1, hState.2.1]; omega⟩
    have := hfootlt _ hm
    omega
  have hfootH : ∀ a, heapFoot x a → a < h := fun a ha => hfootlt a (Or.inr ha)
  have hbatlen : mem batchPtr = U.length := by
    rw [hU]
    exact (decodeBatchBody_length mem _ _ _).symm
  have hspace' : h + (1 + lens.sum) + dsUpdateLoopSpace s.G₀ P.impl P.mMax P.L (s.q P) P.vCap
      P.eCap us U lens k₀ < 2 ^ P.w := by
    have : h + (W + dsUpdateLoopSpace s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap us U lens k₀)
        < 2 ^ P.w := hspace
    omega
  have hgenw' : mem (b' + dsGenOff) + dsUpdateLoopGen s.G₀ P.impl P.L (s.q P) us U.length k₀ <
      2 ^ P.w := lt_of_le_of_lt (Nat.add_le_add_right hgen _) hgenw
  have hbody' : BatchBodyLensAt mem (batchPtr + 1)
      (runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) us k₀).G U lens := by
    rw [hst0]; exact hbody
  obtain ⟨body, hget, o, st', c, hrun, hpost, hcost⟩ :=
    dsUpdateOp_meetsContract (G₀ := s.G₀) (impl := P.impl) (mMax := P.mMax) (w := P.w)
      (L := P.L) (q := s.q P) (vCap := P.vCap) (eCap := P.eCap) (b := b') (k₀ := k₀) (us := us)
      (U := U) (lens := lens) (x₀ := x) hps hpOp _ mem pos ω hW
      ⟨batchPtr, h, by rw [hWeq], hw16, hL, hq1, hVG₀, hGm₀, hE₀, hBVus, hdsus, hslice, hSnap,
        hState', hRev', hfix, hfootH, hz, hspace', hgenw', by simpa [hus, hk₀] using hkw, hqw,
        hWOK, hWeq ▸ hbat,
        hWeq ▸ hbatw, hbatlen, hbody', hcaps⟩
  refine ⟨body, by simpa using hget, o, st', c, hrun, ?_⟩
  obtain ⟨bp2, h2, memC, hargs2, hagC, hBP, hlo, hhi, hgen2⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs2
  obtain ⟨-, rfl, -, rfl⟩ := hargs2
  obtain ⟨uhOutPtr, uhOutWords, dOutPtr, rOutPtr, uhActual, dOut, rOut, x', h0, h1, h2', h3, h4,
    h5, h6, hdLo, hdr, hru, huRet, hBat, hPerm, hApp, hnd, hdfin, hdAt, hrnd, hrfin, hrAt, hzF,
    hx'v, hx'e,
    hfoot', hStateF, hRevF, hframe, hmeta⟩ := hBP
  have hslice_spec := update_slice_spec (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) us U k₀
    hslice
  rw [hst0] at hBat hPerm hApp hdfin hrfin hStateF hslice_spec
  have hflat' : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).flat = us := by simp [DSHist.flat, hus]
  have hstate' : DSHist.state P ⟨s.G₀, s.Us ++ [U]⟩ =
      (update (s.state P) U (canonicalSparsify P.impl)).state := by
    rw [DSHist.state_append, hslice_spec.1]
  have hOutEq : h + (1 + lens.sum) =
      [b', batchPtr, W, h].getD 3 0 + opWords [b', batchPtr, W, h] := by
    simp [opWords, hWeq]
  refine ⟨⟨s.G₀, s.Us ++ [U]⟩, (⟨s.G₀, s.Us ++ [U]⟩, x'), ⟨rfl, ⟨hL, hVG₀, hGm₀, hE₀,
      hflat' ▸ hBVus, hflat' ▸ hdsus,
      hflat' ▸ hsplit, hstate' ▸ hStateF, ?_, ?_⟩, hpst⟩, ⟨rfl, ⟨uhOutPtr, uhOutWords, dOutPtr,
      rOutPtr, uhActual, dOut, rOut,
      hOutEq ▸ h0, hOutEq ▸ h1, hOutEq ▸ h2', hOutEq ▸ h3, hOutEq ▸ h4, hOutEq ▸ h5, hOutEq ▸ h6,
      hBat, hPerm, hApp, hnd, hdfin, hdAt, hrnd, hrfin, hrAt, hOutEq ▸ hdLo, hdr, hru,
      by
        have hsp : h + (W + dsUpdateLoopSpace s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap us
          U lens k₀) < 2 ^ P.w := hspace
        omega⟩, ?_⟩,
    ⟨by omega, by
      show o.value ≤ h + (W + dsUpdateLoopSpace s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap us
        U lens k₀)
      omega, hzF, fun a ha hnf => (hframe a (by omega) hnf).trans (hagC a ha), ?_⟩, ?_⟩
  · have hlen : us.length = k₀ + U.length := by
      rw [hus, hk₀, List.length_append]
    rw [hflat', hlen]
    exact hRevF
  · rw [DSHist.genBound_append]
    exact le_trans hgen2 (Nat.add_le_add_right hgen _)
  · have hfl : (s.Us ++ [U]).flatten = us := by simp [hus, DSHist.flat]
    exact theorem82Clauses_of P hVG₀ hL hGm₀ (hfl ▸ hBVus) (hfl ▸ hdsus) (hfl ▸ hsplit)
  · intro a ha
    by_cases hlt : a < h + (1 + lens.sum)
    · exact Or.inl ((hmeta a hlt).mp ha)
    · refine Or.inr ⟨by omega, ?_⟩
      rcases ha with ⟨_, h2⟩ | hh
      · rw [hx'v, hx'e] at h2; omega
      · exact hfoot' a hh
  · -- The amortized cost: the bank pays for the steps of the batch.
    have hc : c ≤ 30 * (1 + lens.sum) + 25 + dsUpdateOpOverhead +
        dsUpdateLoopCost s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap us U lens k₀ := by
      have h := hcost
      simp only [dsUpdateOpContract] at h
      exact h
    have hloop := dsUpdateLoopCost_le s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap us U lens k₀
    have hold : dsSpent P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ s.flat ≤
        dsBankTotal P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ s.Us :=
      dsSpent_le_bankTotal (nMax := s.G₀.n + P.splitBound) P.impl hVG₀ hL hGm₀ hBVf hdsf
        (Nat.add_le_add_left hsplitf _) hpst
    have hnew : dsSpent P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ us ≤
        dsBankTotal P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ (s.Us ++ [U]) := by
      have hfl : (s.Us ++ [U]).flatten = us := by simp [hus, DSHist.flat]
      have := dsSpent_le_bankTotal (Us := s.Us ++ [U]) (vCap := P.vCap) (eCap := P.eCap)
        (nMax := s.G₀.n + P.splitBound) P.impl hVG₀ hL hGm₀ (hfl ▸ hBVus) (hfl ▸ hdsus)
        (Nat.add_le_add_left (hfl ▸ hsplit) _) hpst
      rw [hfl] at this
      exact this
    have happ := dsBankTotal_append P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀
      s.Us U
    have hsp := dsSpent_append P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ s.flat U
    have hfl' : (s.Us ++ [U]).flatten = s.flat ++ U := by simp [DSHist.flat]
    have hlens : lens.sum ≤ W := by omega
    show c + dsBank P.impl P.mMax P.L (DSHist.q P ⟨s.G₀, s.Us ++ [U]⟩) P.vCap P.eCap
        (s.G₀.n + P.splitBound) s.G₀ (s.Us ++ [U]) ≤
      dsBatchCharge P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀ (s.G₀.applyBatch s.flat)
          U + 1440 * W + 485 + dsUpdateOpOverhead +
        dsBank P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.G₀.n + P.splitBound) s.G₀ s.Us
    have hq' : DSHist.q P ⟨s.G₀, s.Us ++ [U]⟩ = s.q P := rfl
    rw [hq']
    unfold dsBank
    rw [hfl']
    rw [← hus] at hsp ⊢
    rw [← hk₀] at hsp
    have hflat0 : s.G₀.applyBatch s.Us.flatten = s.G₀.applyBatch s.flat := rfl
    rw [hflat0] at happ
    have hflat1 : s.Us.flatten = s.flat := rfl
    rw [hflat1]
    omega

/-- **The data structure of Theorem 8.2 (page 39).** The procedures `dsInitStmt` (at
`bi.bInit + initIdx`) and `dsUpdateOpStmt` (operation `0`, at `bOp`) implement `dynSpannerDS P`
with the representation `dynSpannerRep P`. -/
theorem dynSpannerDS_implements (P : DSParams) {p : Program} {bi : DSInitBases}
    {bs : UpdateLoopBases} {bOp : ℕ} (hpI : HasDSInitProcs P.impl p bi)
    (hps : HasUpdateLoopProcs P.impl p bs) (hpOp : p.HasAt bOp (dsOpProcs bs.sz.bAux bs.bUL)) :
    (dynSpannerRep P).Implements P.w p (bi.bInit + initIdx) (fun i => bOp + i)
      (dynSpannerDS P) :=
  ⟨dynSpannerRep_local P, dynSpannerDS_init P hpI, dynSpannerDS_update P hps hpOp⟩

end

end MinCostFlow.DynSpanner.Program
