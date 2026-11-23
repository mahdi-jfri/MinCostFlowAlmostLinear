module

public import MinCostFlow.SparseCore.Program.RestartLoopDefs
public import WordRAM.Logic
import MinCostFlow.SparseCore.Program.SpanBucket

/-!
# The loop of the restart (`RestartLoop`)

The loop of `restartBranchStmt` runs operation `0` of the bucket spanners on each listed slot,
with the graph that the bundle piece exported for it. The invariant `LoopInv` after `i` rounds
says: the registers other than `12` and `13` are unchanged, register `13` counts the rounds,
register `12` is the heap pointer, which has grown by at most the space of the rounds done; the
table is `spanAfter S6 g (slots.take i)`; its footprint grew only above `h1`; memory below `h1`
outside the old footprint is unchanged; and no round raised the potential by more than its cost
bound. `restartLoop_body` proves one round (`bucketSpannerDS_implements`, operation `0`, with the
precondition from `bucketActivatePre_of_exportAt`), and `restartLoop_triple` the whole loop
(`Triple.forRange_le`).
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

/-- The invariant of the loop after `i` rounds (see the module docstring). `R` gives the registers
at the start, `h1` the heap pointer at the start and `mem1` the memory at the start. -/
@[expose] def LoopInv (P : DSParams) (cap : ℕ) (R : ℕ → ℕ) (spanTbl h1 : ℕ) (S6 : BucketSpannerState cap)
    (x6 : (bucketSpannerRep P cap).τ) (g : ℕ → MGraph) (slots : List ℕ) (mem1 : ℕ → ℕ)
    (i : ℕ) (st : State) : Prop :=
  (∀ r, r ≠ 13 → r ≠ 14 → st.regs r = R r) ∧ st.regs 14 = i ∧
  h1 ≤ st.regs 13 ∧
  st.regs 13 ≤ h1 + ((List.range i).map fun j => spanActivateSpace P (g (slots.getD j 0))).sum ∧
  ZeroFrom st.mem (st.regs 13) ∧
  (∀ a < h1, ¬ (bucketSpannerRep P cap).foot spanTbl x6 a → st.mem a = mem1 a) ∧
  (∀ j < i, specPhi P (spanAfter S6 g (slots.take (j + 1))) ≤
      spanActivateCost P (g (slots.getD j 0)) + specPhi P (spanAfter S6 g (slots.take j))) ∧
  ∃ x6i, (bucketSpannerRep P cap).rep spanTbl (spanAfter S6 g (slots.take i)) x6i st.mem ∧
    ∀ a, (bucketSpannerRep P cap).foot spanTbl x6i a →
      (bucketSpannerRep P cap).foot spanTbl x6 a ∨ (h1 ≤ a ∧ a < st.regs 13)

/-- The cost bound of round `i`: the call and the bound of operation `0`, minus the increase of
the potential. -/
@[expose] noncomputable def loopStepCost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (g : ℕ → MGraph) (slots : List ℕ) (i : ℕ) : ℕ :=
  argsSize restartLoopArgs + 1 +
    (spanActivateCost P (g (slots.getD i 0)) + specPhi P (spanAfter S6 g (slots.take i)) -
      specPhi P (spanAfter S6 g (slots.take (i + 1))))

theorem argsSize_restartLoopArgs :
    argsSize restartLoopArgs = 40 := by
  simp [restartLoopArgs]

/-- The hypotheses of the loop: what the bundle piece and the caller give at its start. -/
structure LoopHyps (P : DSParams) (cap : ℕ) (R : ℕ → ℕ) (spanTbl slotsPtr h h1 : ℕ)
    (S6 : BucketSpannerState cap) (x6 : (bucketSpannerRep P cap).τ) (g : ℕ → MGraph)
    (slots : List ℕ) (mem1 : ℕ → ℕ) : Prop where
  hR2 : R 2 = spanTbl
  hR4 : R 4 = slots.length
  hR5 : R 5 = slotsPtr
  hR6 : R 6 = h
  hR9 : R 9 = P.splitBound
  hR10 : R 10 = P.vCap
  hR11 : R 11 = P.eCap
  hR12 : R 12 = P.L
  hw16 : 16 ≤ 2 ^ P.w
  hL : P.L < 2 ^ P.w
  hSplit : P.splitBound < 2 ^ P.w
  hV : P.vCap < 2 ^ P.w
  hE : P.eCap < 2 ^ P.w
  hlist : ListAt mem1 slotsPtr slots
  hlist_h : slotsPtr + slots.length ≤ h
  hlist_free : ∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length →
    ¬ (bucketSpannerRep P cap).foot spanTbl x6 a
  hh1 : h + 4 * slots.length ≤ h1
  hexp : ∀ i (hi : i < slots.length), ∃ Gb, ExportAt mem1 (h + 4 * i) h1 Gb ∧
    normGraph Gb = g slots[i]
  hok : ∀ s ∈ slots, SpanGraphOK P (g s)
  hact : ∀ s ∈ slots, s < cap
  hrep : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem1
  hfoot : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → a < h
  hz : ZeroFrom mem1 h1
  hspace : h1 + (slots.map fun s => spanActivateSpace P (g s)).sum < 2 ^ P.w

variable {P : DSParams} {cap : ℕ} {p : Program} {bSpan : ℕ} {R : ℕ → ℕ}
  {spanTbl slotsPtr h h1 : ℕ} {S6 : BucketSpannerState cap} {x6 : (bucketSpannerRep P cap).τ}
  {g : ℕ → MGraph} {slots : List ℕ} {mem1 : ℕ → ℕ}

theorem getD_eq_getElem' {slots : List ℕ} {i : ℕ} (hi : i < slots.length) :
    slots.getD i 0 = slots[i] := by
  simp [List.getElem?_eq_getElem hi]

/-- **One round of the loop.** -/
theorem restartLoop_body (hp : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    (H : LoopHyps P cap R spanTbl slotsPtr h h1 S6 x6 g slots mem1) (i : ℕ)
    (hi : i < slots.length) :
    Triple P.w p (LoopInv P cap R spanTbl h1 S6 x6 g slots mem1 i)
      (restartLoopBody (bSpan + bsIdxOp0 + 0))
      (normalPost fun st₁ =>
        LoopInv P cap R spanTbl h1 S6 x6 g slots mem1 (i + 1)
            { st₁ with regs := Function.update st₁.regs 14 (i + 1) } ∧
          st₁.regs 14 = i)
      (fun _ => loopStepCost P S6 g slots i) := by
  intro st ω hInv
  obtain ⟨hregs, h14, hc1, hc2, hzc, hframe, hph, x6i, hrepi, hfooti⟩ := hInv
  have hsl : slots[i] ∈ slots := List.getElem_mem hi
  have hslot : slots[i] < cap := H.hact _ hsl
  have hgetD := getD_eq_getElem' hi
  obtain ⟨Gb, hx1, hGb⟩ := H.hexp i hi
  -- the space of this round fits
  have hsp_le : st.regs 13 + spanActivateSpace P (g slots[i]) ≤
      h1 + ((List.range (i + 1)).map fun j => spanActivateSpace P (g (slots.getD j 0))).sum := by
    rw [sum_range_succ', hgetD]; omega
  have hsp_tot : h1 + ((List.range (i + 1)).map fun j =>
      spanActivateSpace P (g (slots.getD j 0))).sum < 2 ^ P.w := by
    have h1' := sum_range_mono (fun j => spanActivateSpace P (g (slots.getD j 0)))
      (show i + 1 ≤ slots.length by omega)
    rw [sum_range_getD (fun s => spanActivateSpace P (g s))] at h1'
    have := H.hspace
    omega
  have hcW : st.regs 13 + spanActivateSpace P (normGraph Gb) < 2 ^ P.w := by
    rw [hGb]; omega
  have hh1 := H.hh1
  have hfoot := H.hfoot
  -- memory between `h` and `h1` is that of the start
  have hx : ExportAt st.mem (h + 4 * i) h1 Gb :=
    exportAt_congr (fun a ha1 ha2 => hframe a ha2 fun hf => by have := hfoot a hf; omega) hx1
  have hmemslot : st.mem (slotsPtr + i) = slots[i] := by
    have hlh := H.hlist_h
    rw [hframe _ (by omega) (H.hlist_free _ (by omega) (by omega))]
    exact H.hlist i hi
  obtain ⟨hn, hm, -, -, -, -, -, hd4, hV1, hE1, hVend, hEend⟩ := id hx
  have hh1W : h1 < 2 ^ P.w := by omega
  have hcW' : st.regs 13 < 2 ^ P.w := by omega
  have hslotTbl : spanTbl + slots[i] < h :=
    bucket_slot_lt_of_foot (x := x6) (fun a ha => hfoot a ha) hslot
  have hslotW : slots[i] < 2 ^ P.w := by omega
  have hspanW : spanTbl < 2 ^ P.w := by omega
  have hr2 : st.regs 2 = spanTbl := (hregs 2 (by decide) (by decide)).trans H.hR2
  have hr5 : st.regs 5 = slotsPtr := (hregs 5 (by decide) (by decide)).trans H.hR5
  have hr6 : st.regs 6 = h := (hregs 6 (by decide) (by decide)).trans H.hR6
  have hr9 : st.regs 9 = P.splitBound := (hregs 9 (by decide) (by decide)).trans H.hR9
  have hr10 : st.regs 10 = P.vCap := (hregs 10 (by decide) (by decide)).trans H.hR10
  have hr11 : st.regs 11 = P.eCap := (hregs 11 (by decide) (by decide)).trans H.hR11
  have hr12 : st.regs 12 = P.L := (hregs 12 (by decide) (by decide)).trans H.hR12
  have hlh := H.hlist_h
  set vs := activateArgs P st.mem spanTbl slots[i] (h + 4 * i) (st.regs 13) with hvs
  have h4 : (Expr.const 4).eval P.w st = some 4 := Expr.eval_const (by omega)
  have hmul : (Expr.bin .mul (.const 4) (.reg 14)).eval P.w st = some (4 * i) :=
    Expr.eval_mul h4 (Expr.eval_reg_of_eq h14) (by omega)
  have hbase : (Expr.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 14))).eval P.w st =
      some (h + 4 * i) := Expr.eval_add (Expr.eval_reg_of_eq hr6) hmul (by omega)
  have hd : ∀ t, t < 4 → (Expr.bin .add (Expr.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 14)))
      (.const t)).eval P.w st = some (h + 4 * i + t) := fun t ht =>
    Expr.eval_add hbase (Expr.eval_const (k := t) (by omega)) (by omega)
  have hargs : evalArgs P.w st restartLoopArgs = some vs := by
    unfold restartLoopArgs
    rw [hvs]
    unfold activateArgs
    refine evalArgs_cons (Expr.eval_reg_of_eq hr2) <| evalArgs_cons
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr5) (Expr.eval_reg_of_eq h14)
        (by omega)) hmemslot) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr12) <| evalArgs_cons (Expr.eval_reg_of_eq hr9) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr10) <| evalArgs_cons (Expr.eval_reg_of_eq hr11) <|
      evalArgs_cons (Expr.eval_load hbase) <|
      evalArgs_cons (Expr.eval_load (hd 1 (by decide))) <|
      evalArgs_cons (Expr.eval_load (hd 2 (by decide))) <|
      evalArgs_cons (Expr.eval_load (hd 3 (by decide))) <|
      evalArgs_cons (Expr.eval_reg_of_eq rfl) <| evalArgs_nil _ _
  have hwords : ∀ a ∈ vs, a < 2 ^ P.w := by
    intro a ha
    rw [hvs] at ha
    unfold activateArgs at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hspanW | exact hslotW | exact H.hL | exact H.hSplit | exact H.hV | exact H.hE
      | exact hcW' | omega
  have hheap : heapArg vs = st.regs 13 := rfl
  have hpre : (bucketSpannerDS P cap).pre 0 (spanAfter S6 g (slots.take i)) vs st.mem :=
    bucketActivatePre_of_exportAt hx (hGb ▸ H.hok _ hsl) hslot hc1 (by omega) hzc
      (lt_of_le_of_lt (le_refl _) hcW)
  have hspaceOp : heapArg vs + (bucketSpannerDS P cap).space 0 (spanAfter S6 g (slots.take i))
      vs st.mem < 2 ^ P.w := by
    rw [hheap, hvs, bucketActivateSpace_of_exportAt hx]; exact hcW
  obtain ⟨body, hbody, o, st₁, c₁, hrun, S', x', hrep', hpost, hresp, hcost⟩ :=
    (bucketSpannerDS_implements P cap hp).2.2 0 spanTbl _ x6i vs st.mem st.pos ω hwords rfl
      hrepi hpre (fun a ha => by
        rcases hfooti a ha with hf | ⟨_, hf⟩
        · have := hfoot a hf; rw [hheap]; omega
        · rw [hheap]; exact hf) (by rw [hheap]; exact hzc) hspaceOp
  have hcall := (runs_call_iff (w := P.w) (p := p) (ω := ω) (r := 13)
    (f := bSpan + bsIdxOp0 + 0) (args := restartLoopArgs)
    (st := st) (o := .normal)
    (st' := { st₁ with regs := Function.update st.regs 13 o.value })
    (c := argsSize restartLoopArgs + c₁ + 1)).mpr
      ⟨vs, body, o, st₁, c₁, hargs, hbody, hrun, rfl, rfl, rfl⟩
  -- the new table
  obtain ⟨hslot', hS', -⟩ := hpost
  have hS'eq : S' = spanAfter S6 g (slots.take (i + 1)) := by
    rw [hS', spanAfter_take_succ S6 g hi hslot]
    have hG : initArgsGraph (bucketActInitArgs vs) st.mem = g slots[i] := by
      rw [hvs]; unfold activateArgs; rw [initArgsGraph_of_exportAt hx, hGb]
    rw [hG]; rfl
  rw [hS'eq] at hrep'
  obtain ⟨hlo, hhi, hz', hfr, hft⟩ := hresp
  rw [hheap] at hlo hhi hfr hft
  rw [hvs, bucketActivateSpace_of_exportAt hx, hGb] at hhi
  have hphi_i := bucketPhi_eq_specPhi hrepi
  have hphi_i1 := bucketPhi_eq_specPhi hrep'
  have hcostEq : (bucketSpannerDS P cap).cost 0 (spanAfter S6 g (slots.take i)) vs st.mem =
      spanActivateCost P (g slots[i]) := by
    rw [hvs, bucketActivateCost_of_exportAt hx, hGb]
  rw [hcostEq, hphi_i, hphi_i1] at hcost
  refine ⟨.normal, _, _, hcall, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, x', ?_, ?_⟩, ?_⟩, ?_⟩
  · intro r hr13 hr14
    simp only [Function.update_of_ne hr14, Function.update_of_ne hr13]
    exact hregs r hr13 hr14
  · simp
  · simp only [Function.update_of_ne (show (13 : ℕ) ≠ 14 by decide), Function.update_self]
    omega
  · simp only [Function.update_of_ne (show (13 : ℕ) ≠ 14 by decide), Function.update_self]
    omega
  · simp only [Function.update_of_ne (show (13 : ℕ) ≠ 14 by decide), Function.update_self]
    exact hz'
  · intro a ha hnf
    show st₁.mem a = mem1 a
    rw [hfr a (by omega) (fun hf => by
      rcases hfooti a hf with hf' | ⟨hle, _⟩
      · exact hnf hf'
      · omega)]
    exact hframe a ha hnf
  · intro j hj
    rcases Nat.lt_or_ge j i with hji | hji
    · exact hph j hji
    · have hj' : j = i := by omega
      subst hj'
      rw [hgetD]
      omega
  · exact hrep'
  · intro a ha
    simp only [Function.update_of_ne (show (13 : ℕ) ≠ 14 by decide), Function.update_self]
    rcases hft a ha with hf | ⟨hle, hlt⟩
    · rcases hfooti a hf with hf' | ⟨hle', hlt'⟩
      · exact Or.inl hf'
      · exact Or.inr ⟨hle', by omega⟩
    · exact Or.inr ⟨by omega, hlt⟩
  · simp only [Function.update_of_ne (show (14 : ℕ) ≠ 13 by decide)]
    exact h14
  · show argsSize _ + c₁ + 1 ≤ loopStepCost P S6 g slots i
    unfold loopStepCost
    rw [hgetD]
    omega

/-- **The loop.** From the state after the bundle piece (memory `mem1`, registers `R`, heap pointer
`h1` in register `13`), the loop ends in `LoopInv` after all rounds, at cost at most the sum of the
round bounds and the loop overhead. -/
theorem restartLoop_triple (hp : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    (H : LoopHyps P cap R spanTbl slotsPtr h h1 S6 x6 g slots mem1) :
    Triple P.w p (fun st => st.mem = mem1 ∧ (∀ r, r ≠ 14 → st.regs r = R r) ∧ R 13 = h1)
      (forRange 14 (.const 0) (.reg 4)
        (restartLoopBody (bSpan + bsIdxOp0 + 0)))
      (normalPost (LoopInv P cap R spanTbl h1 S6 x6 g slots mem1 slots.length))
      (fun _ => rangeCost (loopStepCost P S6 g slots) 0 slots.length +
        (slots.length - 0) * ((Expr.reg 4).size + 8) +
          ((Expr.const 0).size + (Expr.reg 4).size + 5)) := by
  have hw : 1 < 2 ^ P.w := by have := H.hw16; omega
  have hnW : slots.length < 2 ^ P.w := by
    have := H.hlist_h; have := H.hh1; have := H.hspace; omega
  refine Triple.forRange_le (loopStepCost P S6 g slots) 0 slots.length (Nat.zero_le _) hw
    (fun _ => hnW) ?_ ?_ ?_ ?_
  · rintro st ⟨hmem, hregs, hR13⟩
    refine ⟨Expr.eval_const (by omega), ?_⟩
    refine ⟨?_, by simp, ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), x6, ?_, ?_⟩
    · intro r hr13 hr14
      simp only [Function.update_of_ne hr14]
      exact hregs r hr14
    · simp only [Function.update_of_ne (show (13 : ℕ) ≠ 14 by decide), hregs 13 (by decide)]
      omega
    · simp only [Function.update_of_ne (show (13 : ℕ) ≠ 14 by decide), hregs 13 (by decide)]
      simp [hR13]
    · simp only [Function.update_of_ne (show (13 : ℕ) ≠ 14 by decide), hregs 13 (by decide), hR13]
      rw [hmem]; exact H.hz
    · intro a _ _; show st.mem a = mem1 a; rw [hmem]
    · show (bucketSpannerRep P cap).rep spanTbl (spanAfter S6 g (slots.take 0)) x6 st.mem
      rw [List.take_zero, spanAfter_nil, hmem]; exact H.hrep
    · intro a ha; exact Or.inl ha
  · intro i st _ _ hInv; exact hInv.2.1
  · intro i st _ _ hInv
    exact Expr.eval_reg_of_eq ((hInv.1 4 (by decide) (by decide)).trans H.hR4)
  · intro i _ hi
    exact restartLoop_body hp H i hi

end

end MinCostFlow.SparseCore.Program.Restart
