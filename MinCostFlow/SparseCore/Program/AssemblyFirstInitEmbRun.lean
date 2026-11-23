module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitEmbModel
public import MinCostFlow.SparseCore.Program.EmbRefresh

import MinCostFlow.SparseCore.Program.SpanBucketInit

/-!
# The embedding table at the init: the run (`AssemblyFirstInitEmbRun`)

The piece `asmFirstInitEmbBody` makes the embedding table of the build in two calls: the start
table (`asmFirstInitEmbTblBody`), in which every edge of `G` has the empty walk, and the refresh of
the restart (`embRefreshStmt`), which gives every edge of the graph of a listed slot its walk in
the spanner of that slot. `asmFirstInitEmb_runs` proves the run. With
`asmFirstInit_refresh_emb_eq` (`AssemblyFirstInitEmbModel.lean`), the table then holds the walk
`tr₀.emb e` of every core edge.

The refresh asks that two listed slots give the same walk to a common edge (`SlotWalkAgree`). At
the init, the graphs of distinct slots have no common edge, since they are the bundles of distinct
active pairs (`asmFirstInit_slotWalkAgree`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **The walks of distinct slots agree at the init**: two listed slots that share an edge are the
same slot, since the graph of the slot of an active pair has the edges of its bundle, and distinct
active bundles share no edge. -/
theorem asmFirstInit_slotWalkAgree (P : DSParams) {L : ℕ} {tr : BundleTreeState L}
    {slotCap cap : ℕ} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S6 : BucketSpannerState cap}
    (hMap : SlotMapOK tr slotCap cap slots slotOf)
    (hGE : ∀ q ∈ activePairs tr, slotGE P S6 (slotOf q) = (tr.bun q).edges)
    (hBD : BunDisjointInv tr) : SlotWalkAgree P S6 slots := by
  intro s₁ h₁ s₂ h₂ e he₁ he₂
  obtain ⟨q₁, hq₁, rfl⟩ := hMap.2.2.1 s₁ h₁
  obtain ⟨q₂, hq₂, rfl⟩ := hMap.2.2.1 s₂ h₂
  rw [hGE q₁ hq₁] at he₁
  rw [hGE q₂ hq₂] at he₂
  rw [eq_of_mem_bun_of_mem_bun hBD hq₁ hq₂ he₁ he₂]

/-- **The embedding table**, `[graph, vCap, eCap, spanH, slotsPtr, n, h]`: the start table at `h`
(`fTbl`), then the refresh (`fRef`) of the table at `h` with the spanner table at `spanH` and the
`n` slots at `slotsPtr`. It returns the end of the refresh. -/
def asmFirstInitEmbBody (fTbl fRef : ℕ) : Stmt :=
  .call 7 fTbl [.reg 0, .reg 1, .reg 2, .reg 6] ;;
  .call 8 fRef [.reg 6, .reg 3, .reg 4, .reg 5, .reg 7] ;;
  .ret (.reg 8)

/-- The piece never reads random bits. -/
theorem asmFirstInitEmbBody_noRand (fTbl fRef : ℕ) : (asmFirstInitEmbBody fTbl fRef).NoRand := by
  simp [asmFirstInitEmbBody, Stmt.NoRand]

/-- **The run of the embedding table.** Let `graph` hold the memory form of `G`, let `spanH` hold
the spanner table `S6` with the parameters `P`, and let `slotsPtr` hold the slot list, all below
`h`, with fresh memory from `h`. Let each listed slot hold a spanner whose graph has edges below
`eCap`, and let the walks of the slots agree. Then the piece leaves at `h` the table that the
refresh makes from the start table, in `[h, o)`, keeps memory below `h`, and costs at most the
start table, the refresh and `20`. -/
theorem asmFirstInitEmb_runs {w graph vCap eCap spanH slotsPtr h pos fTbl fRef bCopy bSpan cap
    : ℕ} {p : Program} {ω : ℕ → Bool} (P : DSParams) (hPw : P.w = w)
    (hfT : p.procs[fTbl]? = some asmFirstInitEmbTblBody)
    (hfR : p.procs[fRef]? = some (embRefreshStmt bCopy (bSpan + bsOffRead + spanReadIdxPiWalkPtr)))
    (hcopy : p.HasAt bCopy [copyWords]) (hpS : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    {G : MGraph} {slots : List ℕ} {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap}
    {mem : ℕ → ℕ}
    (hG : DynGraphAt mem graph vCap eCap G) (hgB : graph + dynGraphSize vCap eCap ≤ h)
    (hS6 : (bucketSpannerRep P cap).rep spanH S6 x6 mem)
    (hfoot6 : ∀ a, bucketFoot spanH x6 a → a < h) (hspan_h : spanH < h)
    (hlist : ListAt mem slotsPtr slots) (hlist_h : slotsPtr + slots.length ≤ h)
    (hact : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (hecap : ∀ s ∈ slots, ∀ e ∈ slotGE P S6 s, e < eCap)
    (hagree : SlotWalkAgree P S6 slots)
    (hz : ZeroFrom mem h)
    (hroom : h + 3 + eCap + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) <
      2 ^ w) :
    ∃ o st' c y',
      Runs w p ω (asmFirstInitEmbBody fTbl fRef)
        (startState [graph, vCap, eCap, spanH, slotsPtr, slots.length, h] mem pos) o st' c ∧
      (embRep eCap).rep h ((⟨fun _ => [], G.E⟩ : EmbView).refresh P S6 slots) y' st'.mem ∧
      h + 3 + eCap ≤ o.value ∧
      o.value ≤ h + 3 + eCap + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem a) ∧
      (∀ a, embFoot eCap h y' a → h ≤ a ∧ a < o.value) ∧
      c ≤ 30 * G.m + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) + 80 := by
  subst hPw
  obtain ⟨oT, stT, cT, hrunT, hoT, hrepT, hzT, hkeepT, hfootT, hcT⟩ :=
    asmFirstInitEmbTbl_runs (w := P.w) (p := p) (ω := ω) (pos := pos) hG hgB hz (by omega)
  set h' := h + 3 + eCap with hh'
  have hkeepT' : ∀ a < h, mem a = stT.mem a := fun a ha => (hkeepT a ha).symm
  have hS6T := ((bucketSpannerRep_local P cap) spanH S6 x6 mem stT.mem
    fun a ha => hkeepT' a (hfoot6 a ha)).1 hS6
  have hlistT : ListAt stT.mem slotsPtr slots := fun i hi => by
    rw [hkeepT _ (by omega)]
    exact hlist i hi
  have hw16 : 16 ≤ 2 ^ P.w := by
    have : embRefreshMul ≤ embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    simp only [embRefreshMul] at this hroom ⊢
    omega
  have hargsR : ∀ a ∈ [h, spanH, slotsPtr, slots.length, h'], a < 2 ^ P.w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> omega
  obtain ⟨bodyR, hbR, oR, stR, cR, yR, hrunR, hrepR, hoR1, hoR2, hzR, hkeepR, hfootR, hcR⟩ :=
    (embRefresh_asmBrEmbRefreshDisjAt_of_bucketSpanner P.impl P.w P.L p fRef bCopy bSpan hfR
      hcopy hpS).runs P.mMax P.vCap P.eCap P.splitBound cap eCap h spanH slotsPtr h' slots
      ⟨fun _ => [], G.E⟩ (asmFirstInitEmbConc G.E h eCap) S6 x6 stT.mem stT.pos ω hargsR
      hrepT hS6T hlistT (by omega) hact hecap hagree
      (fun a ha => by have := hfootT a ha; rw [hoT] at this; omega)
      (fun a ha => by have := hfoot6 a ha; omega)
      (fun a ha hb => by have := hfootT a ha; have := hfoot6 a hb; omega)
      (fun a h1 h2 hc => by have := hfootT a hc; omega)
      (by rw [hoT] at hzT; exact hzT) (by omega)
  rw [hfR] at hbR
  cases hbR
  have hPeta : (⟨P.impl, P.mMax, P.w, P.L, P.vCap, P.eCap, P.splitBound⟩ : DSParams) = P := rfl
  simp only [hPeta] at hoR2 hcR
  -- the three steps
  set st0 := startState [graph, vCap, eCap, spanH, slotsPtr, slots.length, h] mem pos
    with hst0
  have hargsT : evalArgs P.w st0 [.reg 0, .reg 1, .reg 2, .reg 6] = some [graph, vCap, eCap, h] := by
    simp [evalArgs, Expr.eval, hst0, startState]
  set s1 : State := { stT with regs := Function.update st0.regs 7 oT.value } with hs1
  have hcallT : Runs P.w p ω (.call 7 fTbl [.reg 0, .reg 1, .reg 2, .reg 6]) st0 .normal s1
      (argsSize [.reg 0, .reg 1, .reg 2, .reg 6] + cT + 1) :=
    runs_call_iff.mpr ⟨_, _, oT, stT, cT, hargsT, hfT, hrunT, rfl, rfl, rfl⟩
  have hargsR' : evalArgs P.w s1 [.reg 6, .reg 3, .reg 4, .reg 5, .reg 7] =
      some [h, spanH, slotsPtr, slots.length, h'] := by
    simp [evalArgs, Expr.eval, hs1, hst0, startState, hoT, hh']
  set s2 : State := { stR with regs := Function.update s1.regs 8 oR.value } with hs2
  have hcallR : Runs P.w p ω (.call 8 fRef [.reg 6, .reg 3, .reg 4, .reg 5, .reg 7]) s1 .normal s2
      (argsSize [.reg 6, .reg 3, .reg 4, .reg 5, .reg 7] + cR + 1) :=
    runs_call_iff.mpr ⟨_, _, oR, stR, cR, hargsR', hfR, hrunR, rfl, rfl, rfl⟩
  have hret : Runs P.w p ω (.ret (.reg 8)) s2 (.returned oR.value) s2 2 :=
    runs_ret_iff.mpr ⟨oR.value, by simp [Expr.eval, hs2], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallR, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallT, t1, rfl⟩)
  refine ⟨_, s2, _, yR, t2, hrepR, hoR1, hoR2, hzR, fun a ha => ?_, fun a ha => ?_, ?_⟩
  · show stR.mem a = mem a
    rw [hkeepR a (by omega) (fun hf => by obtain ⟨h1, -⟩ := hfootT a hf; omega), hkeepT a ha]
  · show h ≤ a ∧ a < oR.value
    rcases hfootR a ha with hf | ⟨hf1, hf2⟩
    · obtain ⟨h1, h2⟩ := hfootT a hf
      rw [hoT] at h2
      omega
    · omega
  · simp only [argsSize, Expr.size] at *
    omega

end

end MinCostFlow.SparseCore.Program
