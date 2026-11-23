module

public import MinCostFlow.SparseCore.Program.EmbRefreshInner
public import MinCostFlow.SparseCore.Program.SpanBucketDefs

import WordRAM.Tactic

/-!
# Embedding-table refresh after a restart (`EmbRefresh`)

Verifies the outer slot loop and complete refresh procedure `embRefreshStmt bCopy bPi`
(`EmbRefreshDefs.lean`), calling `copyWords` at `bCopy` and `spanPiWalkPtrStmt` at `bPi` (either
from `spanReadoutProcs` directly or from `bucketSpannerProcs` at `bSpan + bsOffRead +
spanReadIdxPiWalkPtr`).

Main results:
* `embRefresh_runs`: full Word-RAM correctness, heap allocation, frame, footprint growth, and
  cost bound `embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1)` under the
  preconditions of `AsmBrEmbRefreshAt` plus `SlotWalkAgree P S6 slots` (walk agreement on shared
  edges, needed because `EmbView.refresh` chooses a covering slot with `Classical.choose`).
* `embRefresh_runs_embRefreshSize`: corollary matching `embRefreshSize` (since
  `embRefreshSizeAt ≤ embRefreshSize`).
* `AsmBrEmbRefreshDisjAt` and `embRefresh_asmBrEmbRefreshDisjAt` /
  `embRefresh_asmBrEmbRefreshDisjAt_of_bucketSpanner`: the repaired interface structure
  (adding `SlotWalkAgree` and using `embRefreshSizeAt`) met by `embRefreshStmt`, with non-vacuity
  witness `exists_embRefreshDisjPre`.
* `embRefresh_restart_cost_le`: on `restartSpanState`, the refresh cost and space bound
  `embRefreshMul * (embRefreshSizeAt ... + slots.length + 1)` is at most
  `1200 * singleBundleRestartMachCost ...` (input-free constant, independent of `P.L`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Repaired interface and outer-loop invariant -/

@[expose] public section

/-- **Repaired interface of the embedding-table refresh after a restart** (`AsmBrEmbRefreshAt` with
two minimal fixes: (1) `SlotWalkAgree` so `EmbView.refresh`'s `Classical.choose` is independent of
slot order; (2) `embRefreshSizeAt` so freshly initialized slots pay `O(walkWords)` without an extra
`+ depth` level scan per edge). -/
structure AsmBrEmbRefreshDisjAt (impl : SparsifyImpl) (w depth : ℕ) (p : Program) (f mul : ℕ) :
    Prop where
  runs : ∀ (mMax spV spE splitB cap eCap embH spanH slotsPtr h : ℕ) (slots : List ℕ)
      (v : EmbView) (y : EmbConc) (S6 : BucketSpannerState cap) (x6 : BucketSpannerMeta depth cap)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      let P : DSParams := ⟨impl, mMax, w, depth, spV, spE, splitB⟩
      (∀ a ∈ [embH, spanH, slotsPtr, slots.length, h], a < 2 ^ w) →
      (embRep eCap).rep embH v y mem →
      (bucketSpannerRep P cap).rep spanH S6 x6 mem →
      ListAt mem slotsPtr slots → slotsPtr + slots.length ≤ h →
      (∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome) →
      (∀ s ∈ slots, ∀ e ∈ slotGE P S6 s, e < eCap) →
      SlotWalkAgree P S6 slots →
      (∀ a, embFoot eCap embH y a → a < h) → (∀ a, bucketFoot spanH x6 a → a < h) →
      (∀ a, embFoot eCap embH y a → ¬ bucketFoot spanH x6 a) →
      (∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length → ¬ embFoot eCap embH y a) →
      ZeroFrom mem h →
      h + mul * (embRefreshSizeAt P S6 slots + slots.length + 1) < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c y',
        Runs w p ω body (startState [embH, spanH, slotsPtr, slots.length, h] mem pos) o st' c ∧
        (embRep eCap).rep embH (v.refresh P S6 slots) y' st'.mem ∧
        h ≤ o.value ∧
        o.value ≤ h + mul * (embRefreshSizeAt P S6 slots + slots.length + 1) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ embFoot eCap embH y a → st'.mem a = mem a) ∧
        (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h ≤ a ∧ a < o.value)) ∧
        c ≤ mul * (embRefreshSizeAt P S6 slots + slots.length + 1)

/-- Loop invariant of the outer slot loop after processing the first `k` slots of `slots`. -/
def EmbRefreshOuterInv (P : DSParams) {cap : ℕ} (eCap embH spanH slotsPtr h₀ : ℕ)
    (mem₀ : ℕ → ℕ) (vInit : EmbView) (ptrInit : ℕ → ℕ)
    (S6 : BucketSpannerState cap) (slots : List ℕ) (k : ℕ) (st : State) : Prop :=
  ∃ (curV : EmbView) (curPtr : ℕ → ℕ),
    let hp := h₀ + ((slots.take k).map (slotWalkWords P S6)).sum
    st.regs 0 = embH ∧ st.regs 1 = spanH ∧ st.regs 2 = slotsPtr ∧
    st.regs 3 = slots.length ∧ st.regs 4 = hp ∧ st.regs 5 = embH + 2 ∧
    st.regs 6 = k ∧
    EmbRepAt eCap embH curV curPtr st.mem ∧
    (∀ x < h₀, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → st.mem x = mem₀ x) ∧
    ZeroFrom st.mem hp ∧
    (∀ e ∈ curV.dom,
      (curPtr e = ptrInit e ∧ curV.emb e = vInit.emb e ∧ e ∈ vInit.dom) ∨
      (h₀ ≤ curPtr e ∧ curPtr e + Read.walkWords (curV.emb e) ≤ hp)) ∧
    curV.dom = vInit.dom ∪ slotsGE P S6 (slots.take k) ∧
    (∀ e ∈ slotsGE P S6 (slots.take k),
      ∃ s ∈ slots.take k, e ∈ slotGE P S6 s ∧ curV.emb e = slotWalk P S6 s e) ∧
    (∀ e, e ∉ slotsGE P S6 (slots.take k) → curV.emb e = vInit.emb e)

end

/-! ## Private helper lemmas -/

/-- Flat register-assignment step to avoid nested `{ st with regs := ... }` blowup across
long sequences of setup assignments. -/
private lemma runs_seq_assign_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s₂ : Stmt} {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (h₂ : ∃ o st' c, Runs w p ω s₂ ⟨mem, Function.update regs r v, pos⟩ o st' c ∧ Q o st' ∧
      (k + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.assign r e ;; s₂) ⟨mem, regs, pos⟩ o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h₂ with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + 1 + c + 1,
    runs_seq_iff.mpr (Or.inr ⟨⟨mem, Function.update regs r v, pos⟩, e.size + 1, c,
      runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩),
    hq, by omega⟩

private lemma runs_of_triple_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {P : State → Prop} {Q₁ Q : Outcome → State → Prop} {T₁ : State → ℕ} {st : State} {k T : ℕ}
    (ht : Triple w p P s Q₁ T₁) (hp : P st)
    (hpost : ∀ o st', Q₁ o st' → Q o st') (hc : k + T₁ st ≤ T) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases ht st ω hp with ⟨o, st', c, hr, hq, hcle⟩
  exact ⟨o, st', c, hr, hpost o st' hq, by omega⟩

private lemma slotChange_apply_props {P : DSParams} {cap : ℕ} {S6 : BucketSpannerState cap}
    {s : ℕ} {eL : List ℕ} (heL_mem : ∀ e, e ∈ eL ↔ e ∈ slotGE P S6 s) (v : EmbView) :
    (v.apply (slotChange P S6 s eL)).dom = v.dom ∪ slotGE P S6 s ∧
    (∀ e ∈ slotGE P S6 s, (v.apply (slotChange P S6 s eL)).emb e = slotWalk P S6 s e) ∧
    (∀ e, e ∉ slotGE P S6 s → (v.apply (slotChange P S6 s eL)).emb e = v.emb e) := by
  have hfst : ((slotChange P S6 s eL).map Prod.fst).toFinset = slotGE P S6 s := by
    ext e
    simp only [slotChange, List.map_map, Function.comp_def, List.map_id', List.mem_toFinset, heL_mem]
  have hfold : ∀ (es : List ℕ) (f : Embedding) (e : ℕ),
      ((slotChange P S6 s es).foldl embUpd f) e =
        if e ∈ es then slotWalk P S6 s e else f e := by
    intro es
    induction es with
    | nil => intro f e; simp [slotChange]
    | cons a as ih =>
      intro f e
      simp only [slotChange, List.map_cons, List.foldl_cons, embUpd] at ih ⊢
      rw [ih]
      by_cases hea : e ∈ as
      · simp [hea]
      · by_cases heq : e = a
        · subst heq; simp [hea]
        · simp [hea, heq]
  refine ⟨?_, ?_, ?_⟩
  · unfold EmbView.apply; rw [hfst]
  · intro e he
    show ((slotChange P S6 s eL).foldl embUpd v.emb) e = _
    rw [hfold, ite_eq_left ((heL_mem e).mpr he)]
  · intro e he
    show ((slotChange P S6 s eL).foldl embUpd v.emb) e = _
    rw [hfold, ite_eq_right (fun h => he ((heL_mem e).mp h))]

private lemma slotsGE_take_succ (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) {k : ℕ} (hk : k < slots.length) :
    slotsGE P S6 (slots.take (k + 1)) = slotsGE P S6 (slots.take k) ∪ slotGE P S6 slots[k] := by
  ext e
  simp only [slotsGE, List.take_succ_eq_append_getElem hk, List.toFinset_append,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_biUnion, Finset.mem_union,
    Finset.mem_insert, Finset.notMem_empty, or_false]
  constructor
  · rintro ⟨s, hs | rfl, he⟩
    · exact Or.inl ⟨s, hs, he⟩
    · exact Or.inr he
  · rintro (⟨s, hs, he⟩ | he)
    · exact ⟨s, Or.inl hs, he⟩
    · exact ⟨slots[k], Or.inr rfl, he⟩

private lemma sum_slotWalkWords_le_embRefreshSizeAt (P : DSParams) {cap : ℕ}
    (S6 : BucketSpannerState cap) (slots : List ℕ) :
    (slots.map (slotWalkWords P S6)).sum ≤ embRefreshSizeAt P S6 slots := by
  rw [embRefreshSizeAt_eq_sum]
  induction slots with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (slotWalkWords_le_slotRefreshSizeAt P S6 s) ih

private lemma rangeCost_getElem_eq_map_sum_outer {α : Type*} (l : List α) (f : α → ℕ) :
    rangeCost (fun i => if hi : i < l.length then f (l[i]'hi) else 0) 0 l.length =
      (l.map f).sum := by
  have h : ∀ k (hk : k ≤ l.length),
      rangeCost (fun i => if hi : i < l.length then f (l[i]'hi) else 0) 0 k =
        ((l.take k).map f).sum := by
    intro k
    induction k with
    | zero => intro _; simp [rangeCost]
    | succ m ih =>
      intro hm
      have hmlt : m < l.length := by omega
      have hstep : rangeCost (fun i => if hi : i < l.length then f (l[i]'hi) else 0) 0 (m + 1) =
          rangeCost (fun i => if hi : i < l.length then f (l[i]'hi) else 0) 0 m +
            (if hi : m < l.length then f (l[m]'hi) else 0) := by
        simp only [rangeCost, Nat.sub_zero, List.range'_eq_map_range, List.range_succ,
          List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, Nat.zero_add]
      rw [hstep, ih (by omega), dite_eq_left_of_eq_true (eq_true hmlt),
        List.take_succ_eq_append_getElem hmlt, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
  simpa using h l.length le_rfl

private lemma embFoot_below_parts {eCap embH h₀ : ℕ} {y : EmbConc}
    (hfoot : ∀ a, embFoot eCap embH y a → a < h₀) :
    embH + 2 + eCap ≤ h₀ ∧
    ∀ e ∈ y.view.dom, y.ptr e + Read.walkWords (y.view.emb e) ≤ h₀ := by
  refine ⟨?_, fun e he => ?_⟩
  · have := hfoot (embH + 1 + eCap) (Or.inl ⟨by omega, by omega⟩); omega
  · have := hfoot (y.ptr e + Read.walkWords (y.view.emb e) - 1)
      (Or.inr ⟨e, he, by simp only [Read.walkWords]; omega, by simp only [Read.walkWords]; omega⟩)
    omega

/-! ## Outer slot step and main verification -/

/-- One iteration of `embRefreshSlotBody` refreshes all edges of slot `slots[k]`. -/
private theorem embRefreshSlot_step {P : DSParams} {cap eCap embH spanH slotsPtr h₀ : ℕ}
    {p : Program} {bCopy bRead : ℕ}
    (hcopy : MeetsContract P.w p bCopy (copyWordsContract P.w))
    (hread : p.HasAt bRead spanReadoutProcs)
    {mem₀ : ℕ → ℕ} {vInit : EmbView} {ptrInit : ℕ → ℕ}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap}
    {slots : List ℕ}
    (hS6 : (bucketSpannerRep P cap).rep spanH S6 x6 mem₀)
    (hlist : ListAt mem₀ slotsPtr slots) (hlist_h : slotsPtr + slots.length ≤ h₀)
    (hS6act : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (heCap_all : ∀ s ∈ slots, ∀ e ∈ slotGE P S6 s, e < eCap)
    (htab : embH + 2 + eCap ≤ h₀)
    (hold : ∀ e' ∈ vInit.dom, ptrInit e' + Read.walkWords (vInit.emb e') ≤ h₀)
    (hbFoot : ∀ a, bucketFoot spanH x6 a → a < h₀)
    (hdisjB : ∀ a, embH + 2 ≤ a → a < embH + 2 + eCap → ¬ bucketFoot spanH x6 a)
    (hdisjL : ∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length →
      ¬ (embH + 2 ≤ a ∧ a < embH + 2 + eCap))
    (hw16 : 16 ≤ 2 ^ P.w)
    (hEndLt : h₀ + (slots.map (slotWalkWords P S6)).sum < 2 ^ P.w)
    {k : ℕ} (hk : k < slots.length) :
    Triple P.w p
      (EmbRefreshOuterInv P eCap embH spanH slotsPtr h₀ mem₀ vInit ptrInit S6 slots k)
      (embRefreshSlotBody bCopy (bRead + spanReadIdxPiWalkPtr))
      (normalPost fun st₁ =>
        EmbRefreshOuterInv P eCap embH spanH slotsPtr h₀ mem₀ vInit ptrInit S6 slots (k + 1)
          { st₁ with regs := Function.update st₁.regs 6 (k + 1) } ∧
        st₁.regs 6 = k)
      (fun _ => 142 * slotRefreshSizeAt P S6 (slots[k]'hk)) := by
  intro st ω hInv
  rcases st with ⟨mem, regs, pos⟩
  dsimp only [EmbRefreshOuterInv] at hInv
  obtain ⟨curV, curPtr, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hrep, hfr, hz, hloc,
    hdom, hin, hout⟩ := hInv
  set s := slots[k]'hk with hs_def
  set hp := h₀ + ((slots.take k).map (slotWalkWords P S6)).sum with hhp_def
  have hsMem : s ∈ slots := List.getElem_mem hk
  obtain ⟨hs, hsome⟩ := hS6act s hsMem
  cases hSj : S6 ⟨s, hs⟩ with
  | none => simp [hSj] at hsome
  | some d =>
    have hslot := hS6.1 ⟨s, hs⟩
    rw [hSj] at hslot
    cases hxm : x6.slots ⟨s, hs⟩ with
    | none => simp [hxm] at hslot
    | some bm =>
      rcases bm with ⟨b, m⟩
      rw [hxm] at hslot
      obtain ⟨hmb, ⟨hm1, hdsRep, _⟩, _⟩ := hslot
      have hSt := hdsRep.2.2.2.2.2.2.2.1
      have hGAt : DynGraphAt mem₀ (dsGPtr b) P.vCap P.eCap (d.state P).G :=
        hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      obtain ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩ :=
        hGAt.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hfixH : b + dsFixedSize P.L P.vCap P.eCap ≤ h₀ :=
        slot_fixedSize_le_h hS6 hSj hxm hbFoot
      have hB := embRefresh_fixedBounds (b := b) (L := P.L) (vCap := P.vCap) (eCap := P.eCap)
      have hh₀W : h₀ < 2 ^ P.w := by omega
      have hfixW : b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w := lt_of_le_of_lt hfixH hh₀W
      have hvCapMeta : m.2.vCap = P.vCap := hSt.1
      have heCapMeta : m.2.eCap = P.eCap := hSt.2.1
      have hmem_bucket : ∀ a, bucketFoot spanH x6 a → mem a = mem₀ a := by
        intro a ha
        refine hfr a (hbFoot a ha) ?_
        by_contra hnot
        push Not at hnot
        exact hdisjB a hnot.1 hnot.2 ha
      have hmem_fixed : ∀ a, b ≤ a → a < b + dsFixedSize P.L P.vCap P.eCap → mem a = mem₀ a := by
        intro a h1 h2
        exact hmem_bucket a
          (Or.inr ⟨⟨s, hs⟩, b, m, hxm, Or.inl ⟨h1, by rw [hvCapMeta, heCapMeta]; exact h2⟩⟩)
      have hm_s : mem (slotsPtr + k) = s := by
        have hnot : slotsPtr + k < embH + 2 ∨ embH + 2 + eCap ≤ slotsPtr + k := by
          have := hdisjL (slotsPtr + k) (by omega) (by omega); omega
        rw [hfr (slotsPtr + k) (by omega) hnot]
        exact hlist k hk
      have hspan_s_lt : spanH + s < h₀ := hbFoot (spanH + s) (Or.inl ⟨by omega, by omega⟩)
      have hm_b : mem (spanH + s) = b := by
        rw [hmem_bucket (spanH + s) (Or.inl ⟨by omega, by omega⟩)]; exact hmb
      have hmT : mem (b + dsTOff) = (d.state P).t := by
        rw [hmem_fixed _ (by omega) hB.1]; exact hSt.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hmL : mem (b + dsLOff) = P.L := by
        rw [hmem_fixed _ (by omega) hB.2.1]; exact hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hmV : mem (b + dsVCapOff) = P.vCap := by
        rw [hmem_fixed _ (by omega) hB.2.2.1]; exact hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hmE : mem (b + dsECapOff) = P.eCap := by
        rw [hmem_fixed _ (by omega) hB.2.2.2.1]; exact hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hmM : mem (dsGPtr b + dgMOff) = eL.length := by
        rw [hmem_fixed _ (by simp [dsGPtr, dsHdrSize, dgMOff]; omega) hB.2.2.2.2.2.2.2.2.2.2.2.1,
          heL_len]
        exact hGAt.2.2.2.2.2.2.1
      have hdgEq : 4 + (7 * P.vCap + 9 * P.eCap) = dynGraphSize P.vCap P.eCap := by
        simp only [dynGraphSize]; omega
      have hgelEq : dsGPtr b + 4 + 7 * P.vCap + P.eCap = dgEListBase (dsGPtr b) P.vCap P.eCap := rfl
      have hhepEq : dsHPtr b P.vCap P.eCap + 4 + 7 * P.vCap =
          dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap := rfl
      have hdomEq : dsGPtr b + 3 * dynGraphSize P.vCap P.eCap +
          (3 * P.eCap + 2 * (P.L + 1)) = dsDomGenBase b P.L P.vCap P.eCap := by
        rw [dsDomGenBase_eq, dsMinHBase_eq]; rfl
      have hpiEq : dsDomGenBase b P.L P.vCap P.eCap + (P.L + 1) + (P.L + 1) * P.eCap =
          dsPiPtrBase b P.L P.vCap P.eCap := rfl
      -- Heap upper bound for this slot
      have htakeSucc : ((slots.take (k + 1)).map (slotWalkWords P S6)).sum =
          ((slots.take k).map (slotWalkWords P S6)).sum + slotWalkWords P S6 s := by
        rw [List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append,
          List.map_singleton, List.sum_singleton]
      have htakeLe : ((slots.take (k + 1)).map (slotWalkWords P S6)).sum ≤
          (slots.map (slotWalkWords P S6)).sum := by
        have hsplit : slots = slots.take (k + 1) ++ slots.drop (k + 1) :=
          (List.take_append_drop _ _).symm
        conv_rhs => rw [hsplit]
        rw [List.map_append, List.sum_append]
        exact Nat.le_add_right _ _
      have hSlotEndLt : hp + slotWalkWords P S6 s < 2 ^ P.w := by omega
      have hslotGE : slotGE P S6 s = (d.state P).G.E := by
        unfold slotGE; simp only [hs, ↓reduceDIte, hSj]
      have hpiAt : ∀ e ∈ (d.state P).G.E,
          MeetsContract P.w p (bRead + spanReadIdxPiWalkPtr) (spanPiWalkPtrContract P b e d m.2) :=
        fun e _ => spanPiWalkPtr_meetsContract hread
      have hinner := embRefreshInner_triple (slotsPtr := slotsPtr) (n := slots.length)
        hcopy hs hSj hxm hS6 hpiAt heL_len heL_nd heL_mem
        heL_at (fun e he => heCap_all s hsMem e (hslotGE ▸ he)) htab hold hbFoot hdisjB hw16
        (k := k) (hpStart := hp) (vStart := curV) (ptrStart := curPtr) (by omega) hSlotEndLt
      -- Execute the 15 setup assignments with flat state updates, then splice `hinner`.
      dsimp only [embRefreshSlotBody]
      refine runs_start_le ?_
      refine runs_seq_assign_flat (v := s)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr6)
          (by omega)) hm_s) ?_
      refine runs_seq_assign_flat (v := b)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr1]))
          (Expr.eval_reg_of_eq (by simp)) (by omega)) hm_b) ?_
      refine runs_seq_assign_flat (v := (d.state P).t)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_const (by simp only [dsTOff]; omega)) (by omega)) hmT) ?_
      refine runs_seq_assign_flat (v := P.L)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_const (by simp [dsLOff]; omega)) (by omega)) hmL) ?_
      refine runs_seq_assign_flat (v := P.vCap)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_const (by simp [dsVCapOff]; omega)) (by omega)) hmV) ?_
      refine runs_seq_assign_flat (v := P.eCap)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_const (by simp [dsECapOff]; omega)) (by omega)) hmE) ?_
      refine runs_seq_assign_flat (v := dynGraphSize P.vCap P.eCap)
        (by
          rw [← hdgEq]
          exact Expr.eval_add (Expr.eval_const (by omega))
            (Expr.eval_add
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
              (by omega))
            (by rw [hdgEq]; omega)) ?_
      refine runs_seq_assign_flat (v := dsGPtr b)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_const (by simp only [dsHdrSize]; omega))
          (by change dsGPtr b < 2 ^ P.w; exact lt_trans hB.2.2.2.2.2.2.2.2.2.2.1 hfixW)) ?_
      refine runs_seq_assign_flat (v := dsHPtr b P.vCap P.eCap)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
          (by change dsHPtr b P.vCap P.eCap < 2 ^ P.w; omega)) ?_
      refine runs_seq_assign_flat (v := dgEListBase (dsGPtr b) P.vCap P.eCap)
        (by
          rw [← hgelEq]
          have h1 : dsGPtr b + 4 < 2 ^ P.w := by
            have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [dgEListBase] at this; omega
          have h2 : dsGPtr b + 4 + 7 * P.vCap < 2 ^ P.w := by
            have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [dgEListBase] at this; omega
          have h3 : dsGPtr b + 4 + 7 * P.vCap + P.eCap < 2 ^ P.w := by
            have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [dgEListBase] at this; omega
          exact Expr.eval_add
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) h1)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
              h2)
            (Expr.eval_reg_of_eq (by simp)) h3) ?_
      refine runs_seq_assign_flat (v := eL.length)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_const (by simp [dgMOff]; omega)) (by omega)) hmM) ?_
      refine runs_seq_assign_flat (v := dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap)
        (by
          rw [← hhepEq]
          have h1 : dsHPtr b P.vCap P.eCap + 4 < 2 ^ P.w := by
            have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [dgEPresBase] at this; omega
          have h2 : dsHPtr b P.vCap P.eCap + 4 + 7 * P.vCap < 2 ^ P.w := by
            have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [dgEPresBase] at this; omega
          exact Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) h1)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
            h2) ?_
      refine runs_seq_assign_flat (v := P.L + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_seq_assign_flat (v := dsDomGenBase b P.L P.vCap P.eCap)
        (by
          rw [← hdomEq]
          have hmin : dsGPtr b + 3 * dynGraphSize P.vCap P.eCap < 2 ^ P.w := by
            change b + dsHdrSize + 3 * dynGraphSize P.vCap P.eCap < 2 ^ P.w
            rw [← dsMinHBase_eq]; omega
          exact Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
              hmin)
            (Expr.eval_add
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
              (by omega))
            (by rw [hdomEq]; omega)) ?_
      refine runs_seq_assign_flat (v := dsPiPtrBase b P.L P.vCap P.eCap)
        (by
          rw [← hpiEq]
          have hed : dsDomGenBase b P.L P.vCap P.eCap + (P.L + 1) < 2 ^ P.w := by
            change dsEdgeDomGenBase b P.L P.vCap P.eCap < 2 ^ P.w; omega
          exact Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) hed)
            (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (by omega))
            (by rw [hpiEq]; omega)) ?_
      -- Now run `hinner` directly and close the postcondition and cost!
      refine runs_of_triple_le hinner ?_ ?_ ?_
      · dsimp only [EmbRefreshInnerInv]
        simp only [List.take_zero, slotChange, List.map_nil, EmbView.apply_nil, List.foldl_nil]
        refine ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3],
          by simp [hr4, hhp_def], by simp [hr5], by simp [hr6], by simp, by simp,
          by simp, by simp, by simp, by simp, by simp, hrep, hfr, hz, hloc⟩
      · intro o₁ st₁ hq₁
        cases o₁ with
        | returned u => exact False.elim hq₁
        | normal =>
          dsimp only [normalPost, EmbRefreshInnerInv] at hq₁ ⊢
          simp only [List.take_length] at hq₁
          obtain ⟨r0', r1', r2', r3', r4', r5', r6', -, -, -, -, -, -, -,
            hrep', hfr', hz', hloc'⟩ := hq₁
          set curV' := curV.apply (slotChange P S6 s eL) with hcurV'
          set curS' := (slotChange P S6 s eL).foldl embConcStep (curPtr, hp) with hcurS'
          have hwalk_eL : (eL.map fun e => Read.walkWords (slotWalk P S6 s e)).sum =
              slotWalkWords P S6 s := by
            unfold slotWalkWords
            rw [hslotGE]
            have hto : eL.toFinset = (d.state P).G.E := by ext x; simp [heL_mem]
            rw [← hto]
            exact (List.sum_toFinset _ heL_nd).symm
          have hhp' : curS'.2 = h₀ + ((slots.take (k + 1)).map (slotWalkWords P S6)).sum := by
            rw [hcurS', embConcStep_fold_snd]
            simp only [slotChange, List.map_map, Function.comp_def]
            rw [hwalk_eL, hhp_def, htakeSucc, Nat.add_assoc]
          obtain ⟨hdom', hin', hout'⟩ :=
            slotChange_apply_props (fun e => by rw [hslotGE]; exact heL_mem e) curV
          refine ⟨⟨curV', curS'.1, by simp [r0'], by simp [r1'], by simp [r2'], by simp [r3'],
            by simp [r4', hhp'], by simp [r5'], by simp, hrep', hfr', hhp' ▸ hz',
            fun e he => by simpa [hhp'] using hloc' e he, ?_, ?_, ?_⟩, r6'⟩
          · rw [hcurV', hdom', hdom, slotsGE_take_succ P S6 slots hk, Finset.union_assoc]
          · intro e he
            rw [slotsGE_take_succ P S6 slots hk, Finset.mem_union] at he
            by_cases heS : e ∈ slotGE P S6 s
            · refine ⟨s, ?_, heS, hin' e heS⟩
              rw [List.take_succ_eq_append_getElem hk]
              exact List.mem_append_right _ (List.mem_singleton_self _)
            · have hePre : e ∈ slotsGE P S6 (slots.take k) := he.resolve_right heS
              obtain ⟨s', hs', heS', hemb'⟩ := hin e hePre
              refine ⟨s', ?_, heS', (hout' e heS).trans hemb'⟩
              rw [List.take_succ_eq_append_getElem hk]
              exact List.mem_append_left _ hs'
          · intro e he
            rw [slotsGE_take_succ P S6 slots hk, Finset.mem_union, not_or] at he
            exact (hout' e he.2).trans (hout e he.1)
      · have hsr : slotRefreshSizeAt P S6 s =
            ((d.state P).G.E.sum fun e =>
              Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2) + 1 := by
          unfold slotRefreshSizeAt
          simp only [hs, ↓reduceDIte, hSj]
        simp only [Expr.size]
        rw [hsr]
        omega

/-- **Main run theorem for `embRefreshStmt`**: refreshes the embedding table for all `slots`
under `SlotWalkAgree`, allocating at most `embRefreshSizeAt P S6 slots` words and costing at most
`embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1)`. -/
theorem embRefresh_runs (impl : SparsifyImpl) (w depth : ℕ) (p : Program)
    (f bCopy bRead : ℕ)
    (hf : p.procs[f]? = some (embRefreshStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    (mMax spV spE splitB cap eCap embH spanH slotsPtr h : ℕ) (slots : List ℕ)
    (v : EmbView) (y : EmbConc) (S6 : BucketSpannerState cap) (x6 : BucketSpannerMeta depth cap)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hargs : ∀ a ∈ [embH, spanH, slotsPtr, slots.length, h], a < 2 ^ w)
    (hEmb : (embRep eCap).rep embH v y mem)
    (hS6 : (bucketSpannerRep ⟨impl, mMax, w, depth, spV, spE, splitB⟩ cap).rep spanH S6 x6 mem)
    (hlist : ListAt mem slotsPtr slots) (hlist_h : slotsPtr + slots.length ≤ h)
    (hS6act : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (heCap_all : ∀ s ∈ slots, ∀ e ∈ slotGE ⟨impl, mMax, w, depth, spV, spE, splitB⟩ S6 s,
      e < eCap)
    (hAgree : SlotWalkAgree ⟨impl, mMax, w, depth, spV, spE, splitB⟩ S6 slots)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h)
    (hSpanF : ∀ a, bucketFoot spanH x6 a → a < h)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanH x6 a)
    (hDisjL : ∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length → ¬ embFoot eCap embH y a)
    (hz : ZeroFrom mem h)
    (hsp : h + embRefreshMul *
      (embRefreshSizeAt ⟨impl, mMax, w, depth, spV, spE, splitB⟩ S6 slots +
        slots.length + 1) < 2 ^ w) :
    let P : DSParams := ⟨impl, mMax, w, depth, spV, spE, splitB⟩
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c y',
      Runs w p ω body (startState [embH, spanH, slotsPtr, slots.length, h] mem pos) o st' c ∧
      (embRep eCap).rep embH (v.refresh P S6 slots) y' st'.mem ∧
      h ≤ o.value ∧
      o.value ≤ h + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ embFoot eCap embH y a → st'.mem a = mem a) ∧
      (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h ≤ a ∧ a < o.value)) ∧
      c ≤ embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) := by
  intro P
  obtain ⟨hv, hrep0⟩ := hEmb
  subst hv
  obtain ⟨htab, hold⟩ := embFoot_below_parts hEmbF
  have hsp' : h + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) < 2 ^ w := hsp
  have hw16 : 16 ≤ 2 ^ w := by
    have hmul : embRefreshMul ≤ h + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) := by
      have h1 : 1 ≤ embRefreshSizeAt P S6 slots + slots.length + 1 := Nat.succ_pos _
      exact le_trans (Nat.le_mul_of_pos_right embRefreshMul h1) (Nat.le_add_left _ _)
    have hlt := lt_of_le_of_lt hmul hsp'
    simp only [embRefreshMul] at hlt
    omega
  have hsumLe : (slots.map (slotWalkWords P S6)).sum ≤ embRefreshSizeAt P S6 slots :=
    sum_slotWalkWords_le_embRefreshSizeAt P S6 slots
  have hEndLt : h + (slots.map (slotWalkWords P S6)).sum < 2 ^ w := by
    have : (slots.map (slotWalkWords P S6)).sum ≤
        embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) := by
      simp only [embRefreshMul]; omega
    omega
  have hlenLt : slots.length < 2 ^ w := hargs slots.length (by simp)
  have hdisjB' : ∀ a, embH + 2 ≤ a → a < embH + 2 + eCap → ¬ bucketFoot spanH x6 a :=
    fun a h1 h2 => hDisj a (Or.inl ⟨by omega, h2⟩)
  have hdisjL' : ∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length →
      ¬ (embH + 2 ≤ a ∧ a < embH + 2 + eCap) :=
    fun a h1 h2 hc => hDisjL a h1 h2 (Or.inl ⟨by omega, hc.2⟩)
  set stepC : ℕ → ℕ := fun k =>
    if hk : k < slots.length then 142 * slotRefreshSizeAt P S6 (slots[k]'hk) else 0
  have hPw : P.w = w := rfl
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 3)
    (body := embRefreshSlotBody bCopy (bRead + spanReadIdxPiWalkPtr))
    (P := fun st =>
      EmbRefreshOuterInv P eCap embH spanH slotsPtr h mem y.view y.ptr S6 slots 0
        { st with regs := Function.update st.regs 6 0 })
    (Inv := EmbRefreshOuterInv P eCap embH spanH slotsPtr h mem y.view y.ptr S6 slots)
    stepC 0 slots.length (Nat.zero_le _) (by omega) (fun _ => hlenLt)
    (fun st hI => ⟨Expr.eval_const (by omega), hI⟩)
    (fun _ _ _ _ hI => by obtain ⟨_, _, -, -, -, -, -, -, hr6, -⟩ := hI; exact hr6)
    (fun _ _ _ _ hI => by
      obtain ⟨_, _, -, -, -, hr3, -⟩ := hI
      exact Expr.eval_reg_of_eq hr3)
    (fun k _ hk => by
      have hstep := embRefreshSlot_step (copyWords_meetsContract hcopy) hread hS6 hlist hlist_h
        hS6act heCap_all htab hold hSpanF hdisjB' hdisjL' hw16 hEndLt hk
      simpa only [stepC, dite_eq_left_of_eq_true (eq_true hk)] using hstep)
  have hrc : rangeCost stepC 0 slots.length =
      142 * embRefreshSizeAt P S6 slots := by
    have h1 := rangeCost_getElem_eq_map_sum_outer slots (fun s => 142 * slotRefreshSizeAt P S6 s)
    rw [show stepC = fun k =>
      if hk : k < slots.length then 142 * slotRefreshSizeAt P S6 (slots[k]'hk) else 0 from rfl, h1]
    rw [embRefreshSizeAt_eq_sum]
    have hmulSum : ∀ l : List ℕ,
        (l.map fun s => 142 * slotRefreshSizeAt P S6 s).sum =
          142 * (l.map (slotRefreshSizeAt P S6)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a as ih => simp [ih, Nat.mul_add]
    exact hmulSum slots
  refine ⟨_, hf, ?_⟩
  have hrun : ∃ o st' c, Runs w p ω (embRefreshStmt bCopy (bRead + spanReadIdxPiWalkPtr))
      (startState [embH, spanH, slotsPtr, slots.length, h] mem pos) o st' c ∧
      (o = .returned (h + (slots.map (slotWalkWords P S6)).sum) ∧
        EmbRefreshOuterInv P eCap embH spanH slotsPtr h mem y.view y.ptr S6 slots
          slots.length st') ∧
      c ≤ embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) := by
    dsimp only [embRefreshStmt]
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := embH + 2)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := embH) (by simp [startState])) hrep0.1) ?_
    refine runs_seq_triple_le hloop ?_ ?_
    · refine ⟨y.view, y.ptr, by simp [startState], by simp [startState], by simp [startState],
        by simp [startState], by simp [startState], by simp, by simp, hrep0, fun _ _ _ => rfl,
        by simpa [startState] using hz, fun e he => Or.inl ⟨rfl, rfl, he⟩, ?_, ?_, ?_⟩
      · simp [slotsGE]
      · intro e he; simp [slotsGE] at he
      · intro _ _; rfl
    · intro st₁ hI
      obtain ⟨curV, curPtr, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hrest⟩ := hI
      simp only [List.take_length] at hr4 hrest
      refine runs_ret_le (v := h + (slots.map (slotWalkWords P S6)).sum)
        (Expr.eval_reg_of_eq hr4)
        ⟨rfl, curV, curPtr, hr0, hr1, hr2, hr3, by simpa using hr4, hr5, hr6,
          by simpa using hrest⟩ ?_
      rw [hrc]
      simp only [Expr.size, Nat.sub_zero, embRefreshMul]
      omega
  obtain ⟨o, st', c, hrun, ⟨rfl, hInvEnd⟩, hc⟩ := hrun
  obtain ⟨curV, curPtr, -, -, -, -, -, -, -, hrep', hfr', hz', hloc', hdom', hin', hout'⟩ :=
    hInvEnd
  simp only [List.take_length] at hz' hloc' hdom' hin' hout'
  have hvEq : curV = y.view.refresh P S6 slots :=
    embView_eq_refresh hAgree hdom' hin' hout'
  refine ⟨_, st', c, ⟨curPtr, curV⟩, hrun, ⟨hvEq, hvEq ▸ hrep'⟩,
    by simp [Outcome.value], ?_, hz', ?_, ?_, hc⟩
  · simp only [Outcome.value, embRefreshMul]; omega
  · intro a ha hnf
    refine hfr' a ha ?_
    simp only [embFoot, not_or, not_and, not_lt] at hnf
    by_cases hle : embH ≤ a
    · exact Or.inr (hnf.1 hle)
    · exact Or.inl (by omega)
  · rintro a (ha | ⟨e, he, ha1, ha2⟩)
    · exact Or.inl (Or.inl ha)
    · simp only [Outcome.value]
      rcases hloc' e he with ⟨hp', hemb', hdom0⟩ | ⟨hl1, hl2⟩
      · exact Or.inl (Or.inr ⟨e, hdom0, hp' ▸ ha1, by
          simp only at ha2; rw [hp', hemb'] at ha2; exact ha2⟩)
      · exact Or.inr ⟨by simp only at ha1; omega, by simp only at ha2; omega⟩

/-- Corollary matching `embRefreshSize` (since `embRefreshSizeAt ≤ embRefreshSize`). -/
theorem embRefresh_runs_embRefreshSize (impl : SparsifyImpl) (w depth : ℕ) (p : Program)
    (f bCopy bRead : ℕ)
    (hf : p.procs[f]? = some (embRefreshStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    (mMax spV spE splitB cap eCap embH spanH slotsPtr h : ℕ) (slots : List ℕ)
    (v : EmbView) (y : EmbConc) (S6 : BucketSpannerState cap) (x6 : BucketSpannerMeta depth cap)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hargs : ∀ a ∈ [embH, spanH, slotsPtr, slots.length, h], a < 2 ^ w)
    (hEmb : (embRep eCap).rep embH v y mem)
    (hS6 : (bucketSpannerRep ⟨impl, mMax, w, depth, spV, spE, splitB⟩ cap).rep spanH S6 x6 mem)
    (hlist : ListAt mem slotsPtr slots) (hlist_h : slotsPtr + slots.length ≤ h)
    (hS6act : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (heCap_all : ∀ s ∈ slots, ∀ e ∈ slotGE ⟨impl, mMax, w, depth, spV, spE, splitB⟩ S6 s,
      e < eCap)
    (hAgree : SlotWalkAgree ⟨impl, mMax, w, depth, spV, spE, splitB⟩ S6 slots)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h)
    (hSpanF : ∀ a, bucketFoot spanH x6 a → a < h)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanH x6 a)
    (hDisjL : ∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length → ¬ embFoot eCap embH y a)
    (hz : ZeroFrom mem h)
    (hsp : h + embRefreshMul *
      (embRefreshSize ⟨impl, mMax, w, depth, spV, spE, splitB⟩ S6 slots +
        slots.length + 1) < 2 ^ w) :
    let P : DSParams := ⟨impl, mMax, w, depth, spV, spE, splitB⟩
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c y',
      Runs w p ω body (startState [embH, spanH, slotsPtr, slots.length, h] mem pos) o st' c ∧
      (embRep eCap).rep embH (v.refresh P S6 slots) y' st'.mem ∧
      h ≤ o.value ∧
      o.value ≤ h + embRefreshMul * (embRefreshSize P S6 slots + slots.length + 1) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ embFoot eCap embH y a → st'.mem a = mem a) ∧
      (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h ≤ a ∧ a < o.value)) ∧
      c ≤ embRefreshMul * (embRefreshSize P S6 slots + slots.length + 1) := by
  intro P
  have hle := embRefreshSizeAt_le_embRefreshSize P S6 slots
  have hmulLe : embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) ≤
      embRefreshMul * (embRefreshSize P S6 slots + slots.length + 1) :=
    Nat.mul_le_mul_left embRefreshMul (by omega)
  obtain ⟨body, hb, o, st', c, y', hrun, hrep', hlo, hhi, hz', hfr, hft, hc⟩ :=
    embRefresh_runs impl w depth p f bCopy bRead hf hcopy hread mMax spV spE splitB cap eCap
      embH spanH slotsPtr h slots v y S6 x6 mem pos ω hargs hEmb hS6 hlist hlist_h hS6act
      heCap_all hAgree hEmbF hSpanF hDisj hDisjL hz
      (lt_of_le_of_lt (Nat.add_le_add_left hmulLe h) hsp)
  exact ⟨body, hb, o, st', c, y', hrun, hrep', hlo, le_trans hhi (Nat.add_le_add_left hmulLe h),
    hz', hfr, hft, le_trans hc hmulLe⟩

/-! ## Interface packaging, `bucketSpannerProcs` link, and restart cost bound -/

public section

/-- `embRefreshStmt` meets `AsmBrEmbRefreshDisjAt` with multiplier `embRefreshMul = 300`. -/
theorem embRefresh_asmBrEmbRefreshDisjAt (impl : SparsifyImpl) (w depth : ℕ) (p : Program)
    (f bCopy bRead : ℕ)
    (hf : p.procs[f]? = some (embRefreshStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs) :
    AsmBrEmbRefreshDisjAt impl w depth p f embRefreshMul where
  runs := embRefresh_runs impl w depth p f bCopy bRead hf hcopy hread

/-- `bucketSpannerProcs impl bSpan` contains `spanReadoutProcs` at `bSpan + bsOffRead`. -/
theorem bucketSpannerProcs_hasReadout {impl : SparsifyImpl} {p : Program} {bSpan : ℕ}
    (hp : p.HasAt bSpan (bucketSpannerProcs impl bSpan)) :
    p.HasAt (bSpan + bsOffRead) spanReadoutProcs := by
  intro i hi
  have hlenP : (spanParamProcs (bSpan + bsOffParam)).length = bsOffRead := rfl
  have hlt : bsOffRead + i < (bucketSpannerProcs impl bSpan).length := by
    simp only [bucketSpannerProcs, List.length_append, hlenP]; omega
  have hget := hp (bsOffRead + i) hlt
  rw [← Nat.add_assoc] at hget
  rw [hget]
  congr 1
  simp only [bucketSpannerProcs]
  rw [List.getElem_append_left (by simp only [List.length_append, hlenP]; omega)]
  rw [List.getElem_append_left (by simp only [List.length_append, hlenP]; omega)]
  rw [List.getElem_append_right (by rw [hlenP]; omega)]
  simp [hlenP]

/-- `embRefreshStmt` meets `AsmBrEmbRefreshDisjAt` directly from `bucketSpannerProcs`. -/
theorem embRefresh_asmBrEmbRefreshDisjAt_of_bucketSpanner (impl : SparsifyImpl) (w depth : ℕ)
    (p : Program) (f bCopy bSpan : ℕ)
    (hf : p.procs[f]? = some (embRefreshStmt bCopy (bSpan + bsOffRead + spanReadIdxPiWalkPtr)))
    (hcopy : p.HasAt bCopy [copyWords])
    (hpS : p.HasAt bSpan (bucketSpannerProcs impl bSpan)) :
    AsmBrEmbRefreshDisjAt impl w depth p f embRefreshMul :=
  embRefresh_asmBrEmbRefreshDisjAt impl w depth p f bCopy (bSpan + bsOffRead) hf hcopy
    (bucketSpannerProcs_hasReadout hpS)

/-- **End-to-end restart cost bound for the embedding-table refresh.** On `restartSpanState`, the
cost and heap allocation bound `embRefreshMul * (embRefreshSizeAt ... + slots.length + 1)` of
`embRefresh_runs` is at most `1200 * singleBundleRestartMachCost ...` (input-free constant,
independent of `P.L`). -/
theorem embRefresh_restart_cost_le {slotCap cap : ℕ} (P : DSParams)
    {tr : BundleTreeState P.L} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : Fin slotCap → Option BundleState} (S6 : BucketSpannerState cap) (ord : ℕ → List End)
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hok : ∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s))
    (hP : SparsifyParamsLe (canonicalSparsifyParams P.impl P.mMax).absorbTime tr.spanParams)
    (hC : dsAmortConst P.impl ≤ tr.spanConst) (hSB : P.splitBound = tr.splitBound) :
    embRefreshMul *
        (embRefreshSizeAt P (restartSpanState S6 S tr.cs ord tr.k slots) slots +
          slots.length + 1) ≤
      1200 * singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
  have h1 := embRefreshSizeAt_restartSpanState_le_machCost P S6 ord hMap hMatch hok hP hC hSB
  calc embRefreshMul *
          (embRefreshSizeAt P (restartSpanState S6 S tr.cs ord tr.k slots) slots +
            slots.length + 1)
      ≤ embRefreshMul *
          (4 * singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord) :=
        Nat.mul_le_mul_left embRefreshMul h1
    _ = 1200 * singleBundleRestartMachCost P.L (fun _ => canonicalSparsify P.impl) tr ord := by
        simp only [embRefreshMul]; ring

/-- Non-vacuity witness: the preconditions of `AsmBrEmbRefreshDisjAt` are simultaneously
satisfiable (for `slots = []`, `cap = 0`, `eCap = 0`, `v = EmbView.empty`, `h = 4`, `w = 12`). -/
theorem exists_embRefreshDisjPre (impl : SparsifyImpl) (depth : ℕ) :
    let P : DSParams := ⟨impl, 0, 12, depth, 0, 0, 0⟩
    ∃ (mem : ℕ → ℕ) (y : EmbConc) (S6 : BucketSpannerState 0) (x6 : BucketSpannerMeta depth 0),
      (∀ a ∈ [0, 3, 3, ([] : List ℕ).length, 4], a < 2 ^ 12) ∧
      (embRep 0).rep 0 EmbView.empty y mem ∧
      (bucketSpannerRep P 0).rep 3 S6 x6 mem ∧
      ListAt mem 3 [] ∧ 3 + ([] : List ℕ).length ≤ 4 ∧
      (∀ s ∈ ([] : List ℕ), ∃ hs : s < 0, (S6 ⟨s, hs⟩).isSome) ∧
      (∀ s ∈ ([] : List ℕ), ∀ e ∈ slotGE P S6 s, e < 0) ∧
      SlotWalkAgree P S6 [] ∧
      (∀ a, embFoot 0 0 y a → a < 4) ∧ (∀ a, bucketFoot 3 x6 a → a < 4) ∧
      (∀ a, embFoot 0 0 y a → ¬ bucketFoot 3 x6 a) ∧
      (∀ a, 3 ≤ a → a < 3 + ([] : List ℕ).length → ¬ embFoot 0 0 y a) ∧
      ZeroFrom mem 4 ∧
      4 + embRefreshMul * (embRefreshSizeAt P S6 [] + ([] : List ℕ).length + 1) < 2 ^ 12 := by
  intro P
  refine ⟨fun a => if a = 0 then 2 else 0, ⟨fun _ => 0, EmbView.empty⟩,
    fun j => Fin.elim0 j, ⟨fun j => Fin.elim0 j⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro a ha; simp only [List.mem_cons, List.not_mem_nil, List.length_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨rfl, by simp, by simp, fun e he => by simp [EmbView.empty] at he⟩
  · exact ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  · intro i hi; simp at hi
  · simp
  · intro s hs; simp at hs
  · intro s hs; simp at hs
  · intro s hs; simp at hs
  · rintro a (⟨h1, h2⟩ | ⟨e, he, -⟩)
    · omega
    · simp [EmbView.empty] at he
  · rintro a (⟨h1, h2⟩ | ⟨j, -⟩)
    · omega
    · exact Fin.elim0 j
  · rintro a _ (⟨h1, h2⟩ | ⟨j, -⟩)
    · omega
    · exact Fin.elim0 j
  · intro a h1 h2; simp at h2; omega
  · intro a ha; simp [show a ≠ 0 by omega]
  · simp [embRefreshSizeAt, embRefreshMul]

end

end MinCostFlow.SparseCore.Program
