module

public import MinCostFlow.SparseCore.Program.EmbRefreshDefs

import WordRAM.Tactic

/-!
# Inner loop of the embedding-table refresh (`EmbRefreshInner`)

Verifies the inner `forRange` loop of `embRefreshSlotBody` (`EmbRefreshDefs.lean`), which scans the
edge list `eL` of one active bucket spanner `d = S6 ⟨s, hs⟩` and writes the refreshed walk
`slotWalk P S6 s e` of every edge `e ∈ eL` into the embedding table at `embH` and the heap starting
at `hpStart`.

* `embRefreshEdge_step`: one iteration of `embRefreshEdgeBody bCopy bPi` on edge `e = eL[i]`.
  If `e ∈ H.E`, it stores the 3-word encoding `[1, e, 1]` directly; otherwise it loads the walk
  pointer in `O(1)` when `(d.state P).t = 0` or via `spanPiWalkPtrStmt` (`bPi`) when `t ≠ 0`, and
  copies the walk with `copyWords` (`bCopy`).
* `embRefreshInner_triple`: `Triple` for `forRange 21 (.const 0) (.reg 17) (embRefreshEdgeBody bCopy bPi)`
  using `Triple.forRange_le`, with total cost bounded by
  `142 * ((d.state P).G.E.sum fun e => walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2) + 10`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

/-! ## Pure change-list and inner-loop definitions -/

@[expose] public section

/-- The `EmbChange` list produced by refreshing a list of edges `es` from slot `s`. -/
noncomputable def slotChange (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (s : ℕ) (es : List ℕ) : EmbChange :=
  es.map fun e => (e, slotWalk P S6 s e)

/-- Per-edge cost bound of `embRefreshEdgeBody` for edge `e` of slot `s` holding history `d`. -/
noncomputable def edgeStepCost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (s : ℕ) (d : DSHist) (e : ℕ) : ℕ :=
  17 * Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else 65 * P.L) + 275

/-- Loop invariant of the inner edge scan over `eL` for one active slot `s`. -/
def EmbRefreshInnerInv (P : DSParams) {cap : ℕ} (eCap embH spanH slotsPtr n h₀ : ℕ)
    (mem₀ : ℕ → ℕ) (vInit : EmbView) (ptrInit : ℕ → ℕ)
    (S6 : BucketSpannerState cap) (s : ℕ) (d : DSHist) (b : ℕ) (eL : List ℕ)
    (k hpStart : ℕ) (vStart : EmbView) (ptrStart : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  let pre := slotChange P S6 s (eL.take i)
  let curV := vStart.apply pre
  let curS := pre.foldl embConcStep (ptrStart, hpStart)
  st.regs 0 = embH ∧ st.regs 1 = spanH ∧ st.regs 2 = slotsPtr ∧ st.regs 3 = n ∧
  st.regs 4 = curS.2 ∧ st.regs 5 = embH + 2 ∧ st.regs 6 = k ∧
  st.regs 8 = b ∧ st.regs 9 = (d.state P).t ∧
  st.regs 16 = dgEListBase (dsGPtr b) P.vCap P.eCap ∧ st.regs 17 = eL.length ∧
  st.regs 18 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap ∧
  st.regs 19 = dsPiPtrBase b P.L P.vCap P.eCap ∧ st.regs 21 = i ∧
  EmbRepAt eCap embH curV curS.1 st.mem ∧
  (∀ x < h₀, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → st.mem x = mem₀ x) ∧
  ZeroFrom st.mem curS.2 ∧
  ∀ e ∈ curV.dom,
    (curS.1 e = ptrInit e ∧ curV.emb e = vInit.emb e ∧ e ∈ vInit.dom) ∨
    (h₀ ≤ curS.1 e ∧ curS.1 e + Read.walkWords (curV.emb e) ≤ curS.2)

end

/-! ## Private helper lemmas -/

private lemma runs_cond_true_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h : ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + c + 1,
    runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩, hq, by omega⟩

private lemma runs_cond_false_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some 0)
    (h : ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + c + 1,
    runs_cond_iff.mpr ⟨0, c, he, by simpa using hr, rfl⟩, hq, by omega⟩

private lemma runs_seq_split_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt}
    {st : State} {k T₁ T : ℕ} {P₁ : State → Prop} {Q : Outcome → State → Prop}
    (h₁ : ∃ o₁ st₁ c₁, Runs w p ω s₁ st o₁ st₁ c₁ ∧ (o₁ = .normal ∧ P₁ st₁) ∧ 0 + c₁ ≤ T₁)
    (h₂ : ∀ st₁, P₁ st₁ →
      ∃ o₂ st₂ c₂, Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ Q o₂ st₂ ∧ (k + T₁ + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (s₁ ;; s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h₁ with ⟨_, st₁, c₁, hr₁, ⟨rfl, hp₁⟩, hc₁⟩
  rcases h₂ st₁ hp₁ with ⟨o₂, st₂, c₂, hr₂, hq₂, hc₂⟩
  exact ⟨o₂, st₂, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩),
    hq₂, by omega⟩

private lemma slotChange_take_succ (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (s : ℕ) (eL : List ℕ) {i : ℕ} (hi : i < eL.length) :
    slotChange P S6 s (eL.take (i + 1)) =
      slotChange P S6 s (eL.take i) ++ [(eL[i], slotWalk P S6 s eL[i])] := by
  unfold slotChange
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.map_singleton]

private lemma slotChange_walkWords_sum (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (s : ℕ) (es : List ℕ) :
    ((slotChange P S6 s es).map fun p => Read.walkWords p.2).sum =
      (es.map fun e => Read.walkWords (slotWalk P S6 s e)).sum := by
  unfold slotChange
  rw [List.map_map]
  rfl

private lemma list_map_sum_eq_finset_sum {α : Type*} [DecidableEq α] (l : List α)
    (hnd : l.Nodup) (s : Finset α) (hmem : ∀ x, x ∈ l ↔ x ∈ s) (f : α → ℕ) :
    (l.map f).sum = s.sum f := by
  have hto : l.toFinset = s := by
    ext x
    simp [hmem]
  rw [← hto]
  exact (List.sum_toFinset f hnd).symm

private lemma rangeCost_getElem_eq_map_sum {α : Type*} (l : List α) (f : α → ℕ) :
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

/-- Helper updating `EmbRepAt`, frame, `ZeroFrom`, and pointer locality after writing walk `W` of
edge `e` into `[H, H + walkWords W)` and pointing `embH + 2 + e` to `H`. -/
private lemma embRefresh_update_step {eCap embH h₀ H e : ℕ} {mem₀ m_cur m_new : ℕ → ℕ}
    {vInit curV : EmbView} {ptrInit curPtr : ℕ → ℕ} {W : List (ℕ × Bool)}
    (htab : embH + 2 + eCap ≤ h₀) (hHge : h₀ ≤ H) (heCap : e < eCap)
    (hold : ∀ e' ∈ vInit.dom, ptrInit e' + Read.walkWords (vInit.emb e') ≤ h₀)
    (hrep : EmbRepAt eCap embH curV curPtr m_cur)
    (hfr : ∀ x < h₀, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → m_cur x = mem₀ x)
    (hz : ZeroFrom m_cur H)
    (hloc : ∀ e' ∈ curV.dom,
      (curPtr e' = ptrInit e' ∧ curV.emb e' = vInit.emb e' ∧ e' ∈ vInit.dom) ∨
      (h₀ ≤ curPtr e' ∧ curPtr e' + Read.walkWords (curV.emb e') ≤ H))
    (hwalk : MWalkAt m_new H W)
    (htab_e : m_new (embH + 2 + e) = H)
    (hout : ∀ x, x ≠ embH + 2 + e → (x < H ∨ H + Read.walkWords W ≤ x) → m_new x = m_cur x) :
    EmbRepAt eCap embH ⟨Function.update curV.emb e W, insert e curV.dom⟩
      (Function.update curPtr e H) m_new ∧
    (∀ x < h₀, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → m_new x = mem₀ x) ∧
    ZeroFrom m_new (H + Read.walkWords W) ∧
    ∀ e' ∈ insert e curV.dom,
      (Function.update curPtr e H e' = ptrInit e' ∧
        Function.update curV.emb e W e' = vInit.emb e' ∧ e' ∈ vInit.dom) ∨
      (h₀ ≤ Function.update curPtr e H e' ∧
        Function.update curPtr e H e' + Read.walkWords (Function.update curV.emb e W e') ≤
          H + Read.walkWords W) := by
  obtain ⟨hr0, hr1, hrE⟩ := hrep
  have hWw : Read.walkWords W = 1 + 2 * W.length := rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hout embH (by omega) (Or.inl (by omega))]; exact hr0
  · rw [hout (embH + 1) (by omega) (Or.inl (by omega))]; exact hr1
  · intro e' he'
    simp only [Finset.mem_insert] at he'
    by_cases hee : e' = e
    · subst hee
      simp only [Function.update_self]
      exact ⟨heCap, by omega, htab_e, hwalk⟩
    · have he'd : e' ∈ curV.dom := he'.resolve_left hee
      obtain ⟨hlt', hge', htab', hwk'⟩ := hrE e' he'd
      simp only [Function.update_of_ne hee]
      refine ⟨hlt', hge', ?_, ?_⟩
      · rw [hout (embH + 2 + e') (by omega) (Or.inl (by omega))]; exact htab'
      · have hbelow : curPtr e' + Read.walkWords (curV.emb e') ≤ H := by
          rcases hloc e' he'd with ⟨hp, hem, hdom⟩ | ⟨_, hle⟩
          · have := hold e' hdom; rw [hp, hem]; omega
          · exact hle
        refine hwk'.of_agree fun x hx1 hx2 => ?_
        simp only [Read.walkWords] at hbelow
        exact hout x (by omega) (Or.inl (by omega))
  · intro x hx hx'
    rw [hout x (by omega) (Or.inl (by omega))]
    exact hfr x hx hx'
  · intro x hx
    rw [hout x (by omega) (Or.inr hx)]
    exact hz x (by omega)
  · intro e' he'
    simp only [Finset.mem_insert] at he'
    by_cases hee : e' = e
    · subst hee
      right
      simp only [Function.update_self]
      omega
    · have he'd : e' ∈ curV.dom := he'.resolve_left hee
      simp only [Function.update_of_ne hee]
      rcases hloc e' he'd with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩

/-! ## Inner edge-scan verification -/

public section

/-- One iteration of `embRefreshEdgeBody` updates the embedding table and heap for `e = eL[i]`. -/
theorem embRefreshEdge_step {P : DSParams} {cap eCap embH spanH slotsPtr n h₀ : ℕ}
    {p : Program} {bCopy bPi : ℕ}
    (hcopy : MeetsContract P.w p bCopy (copyWordsContract P.w))
    {mem₀ : ℕ → ℕ} {vInit : EmbView} {ptrInit : ℕ → ℕ}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap}
    {s : ℕ} (hs : s < cap) {d : DSHist} {b : ℕ} {m : DSHist × DynSpannerMeta P.L}
    (hSj : S6 ⟨s, hs⟩ = some d) (hxm : x6.slots ⟨s, hs⟩ = some (b, m))
    (hS6 : (bucketSpannerRep P cap).rep spanH S6 x6 mem₀)
    (hpiAt : ∀ e ∈ (d.state P).G.E, MeetsContract P.w p bPi (spanPiWalkPtrContract P b e d m.2))
    {eL : List ℕ} (heL_len : eL.length = (d.state P).G.m)
    (heL_mem : ∀ e, e ∈ eL ↔ e ∈ (d.state P).G.E)
    (heL_at : ListAt mem₀ (dgEListBase (dsGPtr b) P.vCap P.eCap) eL)
    (heCap_all : ∀ e ∈ (d.state P).G.E, e < eCap)
    (htab : embH + 2 + eCap ≤ h₀)
    (hold : ∀ e' ∈ vInit.dom, ptrInit e' + Read.walkWords (vInit.emb e') ≤ h₀)
    (hbFoot : ∀ a, bucketFoot spanH x6 a → a < h₀)
    (hdisj : ∀ a, embH + 2 ≤ a → a < embH + 2 + eCap → ¬ bucketFoot spanH x6 a)
    (hw16 : 16 ≤ 2 ^ P.w)
    {k hpStart : ℕ} {vStart : EmbView} {ptrStart : ℕ → ℕ}
    (hStartGe : h₀ ≤ hpStart)
    {i : ℕ} (hi : i < eL.length)
    (hHlt : hpStart + ((eL.take (i + 1)).map fun e => Read.walkWords (slotWalk P S6 s e)).sum < 2 ^ P.w) :
    Triple P.w p
      (EmbRefreshInnerInv P eCap embH spanH slotsPtr n h₀ mem₀ vInit ptrInit S6 s d b eL
        k hpStart vStart ptrStart i)
      (embRefreshEdgeBody bCopy bPi)
      (normalPost fun st₁ =>
        EmbRefreshInnerInv P eCap embH spanH slotsPtr n h₀ mem₀ vInit ptrInit S6 s d b eL
          k hpStart vStart ptrStart (i + 1)
          { st₁ with regs := Function.update st₁.regs 21 (i + 1) } ∧
        st₁.regs 21 = i)
      (fun _ => edgeStepCost P S6 s d (eL[i]'hi)) := by
  intro st ω hInv
  dsimp only [EmbRefreshInnerInv] at hInv
  set pre := slotChange P S6 s (eL.take i) with hpre_def
  set curV := vStart.apply pre with hcurV_def
  set curS := pre.foldl embConcStep (ptrStart, hpStart) with hcurS_def
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr8, hr9, hr16, hr17, hr18, hr19, hr21,
    hrep, hfr, hz, hloc⟩ := hInv
  set e := eL[i]'hi with he_def
  set H := curS.2 with hH_def
  set W := slotWalk P S6 s e with hW_def
  have hslot := hS6.1 ⟨s, hs⟩
  rw [hSj, hxm] at hslot
  obtain ⟨_, ⟨hm1, hdsRep, _⟩, _⟩ := hslot
  have hSt := hdsRep.2.2.2.2.2.2.2.1
  have hGAt : DynGraphAt mem₀ (dsGPtr b) P.vCap P.eCap (d.state P).G :=
    hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hHAt : DynGraphAt mem₀ (dsHPtr b P.vCap P.eCap) P.vCap P.eCap (d.state P).H :=
    hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfixH : b + dsFixedSize P.L P.vCap P.eCap ≤ h₀ :=
    slot_fixedSize_le_h hS6 hSj hxm hbFoot
  have hB := embRefresh_fixedBounds (b := b) (L := P.L) (vCap := P.vCap) (eCap := P.eCap)
  have hHge_start : hpStart ≤ H := by
    rw [hH_def, hcurS_def, embConcStep_fold_snd]; omega
  have hHge : h₀ ≤ H := le_trans hStartGe hHge_start
  have hHsum : H + Read.walkWords W =
      hpStart + ((eL.take (i + 1)).map fun x => Read.walkWords (slotWalk P S6 s x)).sum := by
    rw [hH_def, hcurS_def, embConcStep_fold_snd, hpre_def, slotChange_walkWords_sum,
      List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, hW_def, he_def, Nat.add_assoc]
  have hHlt' : H + Read.walkWords W < 2 ^ P.w := by rw [hHsum]; exact hHlt
  have hh₀W : h₀ < 2 ^ P.w := by omega
  have hfixW : b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w := lt_of_le_of_lt hfixH hh₀W
  have heG : e ∈ (d.state P).G.E := (heL_mem e).mp (List.getElem_mem hi)
  have heCap : e < eCap := heCap_all e heG
  have heSpE : e < P.eCap := hSt.2.2.2.2.2.2.2.2.2.2.1 e heG
  have hmLeSpE : eL.length ≤ P.eCap := by
    rw [heL_len]
    have hsub : (d.state P).G.E ⊆ Finset.range P.eCap := fun x hx =>
      Finset.mem_range.mpr (hSt.2.2.2.2.2.2.2.2.2.2.1 x hx)
    simpa [MGraph.m] using Finset.card_le_card hsub
  have hvCapMeta : m.2.vCap = P.vCap := hSt.1
  have heCapMeta : m.2.eCap = P.eCap := hSt.2.1
  -- All cells of `bucketFoot spanH x6` are untouched in `st.mem`.
  have hmem_bucket : ∀ a, bucketFoot spanH x6 a → st.mem a = mem₀ a := by
    intro a ha
    have halt : a < h₀ := hbFoot a ha
    refine hfr a halt ?_
    by_contra hnot
    push Not at hnot
    exact hdisj a hnot.1 hnot.2 ha
  have hmem_fixed : ∀ a, b ≤ a → a < b + dsFixedSize P.L P.vCap P.eCap → st.mem a = mem₀ a := by
    intro a h1 h2
    exact hmem_bucket a (Or.inr ⟨⟨s, hs⟩, b, m, hxm, Or.inl ⟨h1, by rw [hvCapMeta, heCapMeta]; exact h2⟩⟩)
  -- Read `e = eL[i]` from `dgEListBase`.
  have hgeL_ge : b ≤ dgEListBase (dsGPtr b) P.vCap P.eCap + i := by
    simp only [dgEListBase, dsGPtr, dsHdrSize]; omega
  have hgeL_lt : dgEListBase (dsGPtr b) P.vCap P.eCap + i < b + dsFixedSize P.L P.vCap P.eCap := by
    have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have he_mem : st.mem (dgEListBase (dsGPtr b) P.vCap P.eCap + i) = e := by
    rw [hmem_fixed _ hgeL_ge hgeL_lt]; exact heL_at i hi
  -- Read `inH = if e ∈ H.E then 1 else 0` from `dgEPresBase`.
  have hhep_ge : b ≤ dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + e := by
    simp only [dgEPresBase, dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]; omega
  have hhep_lt : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + e < b + dsFixedSize P.L P.vCap P.eCap := by
    have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hinH_mem : st.mem (dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + e) =
      if e ∈ (d.state P).H.E then 1 else 0 := by
    rw [hmem_fixed _ hhep_ge hhep_lt]
    exact hHAt.2.2.2.2.2.2.2.2.2.2.2.1 e heSpE
  have htab_e_W : embH + 2 + e < 2 ^ P.w := by omega
  -- Next state fold identities
  have hpre_succ : slotChange P S6 s (eL.take (i + 1)) = pre ++ [(e, W)] :=
    slotChange_take_succ P S6 s eL hi
  have hfold_succ : (pre ++ [(e, W)]).foldl embConcStep (ptrStart, hpStart) =
      (Function.update curS.1 e H, H + Read.walkWords W) := by
    simp [List.foldl_append, embConcStep, hcurS_def, hH_def]
  have hview_succ : vStart.apply (pre ++ [(e, W)]) =
      ⟨Function.update curV.emb e W, insert e curV.dom⟩ := by
    rw [EmbView.apply_append, EmbView.apply_singleton]
  -- Start executing `embRefreshEdgeBody`
  dsimp only [embRefreshEdgeBody]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hr16) (Expr.eval_reg_of_eq hr21) (by omega))
      he_mem) ?_
  refine runs_seq_assign_le (v := if e ∈ (d.state P).H.E then 1 else 0)
    (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr18])) (Expr.eval_reg_of_eq (by simp))
        (by omega))
      hinH_mem) ?_
  by_cases heH : e ∈ (d.state P).H.E
  · -- Branch 1: `e ∈ H.E`, walk is `[(e, true)]`, encoded directly as `[1, e, 1]`.
    have hW_eq : W = [(e, true)] := by
      simp only [hW_def, slotWalk, hs, ↓reduceDIte, hSj, heH, ↓reduceIte]
    have hWw3 : Read.walkWords W = 3 := by rw [hW_eq]; rfl
    refine runs_cond_true_le (v := 1) (Expr.eval_reg_of_eq (by simp [heH])) (by decide) ?_
    refine runs_seq_store_le (x := H) (v := 1)
      (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := H + 1) (v := e)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) (Expr.eval_const (by omega))
        (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := H + 2) (v := 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) (Expr.eval_const (by omega))
        (by omega))
      (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := embH + 2 + e) (v := H)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr5])) (Expr.eval_reg_of_eq (by simp))
        htab_e_W)
      (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) ?_
    refine runs_assign_le (v := H + 3)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) (Expr.eval_const (by omega))
        (by omega)) ?_ ?_
    · dsimp only [normalPost]
      set mNew := Function.update (Function.update (Function.update (Function.update st.mem
        H 1) (H + 1) e) (H + 2) 1) (embH + 2 + e) H with hmNew
      have hmNew_H0 : mNew H = 1 := by
        simp only [hmNew, Function.update_apply, show H ≠ embH + 2 + e by omega,
          show H ≠ H + 2 by omega, show H ≠ H + 1 by omega, ite_false, ite_true]
      have hmNew_H1 : mNew (H + 1) = e := by
        simp only [hmNew, Function.update_apply, show H + 1 ≠ embH + 2 + e by omega,
          show H + 1 ≠ H + 2 by omega, ite_false, ite_true]
      have hmNew_H2 : mNew (H + 2) = 1 := by
        simp only [hmNew, Function.update_apply, show H + 2 ≠ embH + 2 + e by omega,
          ite_false, ite_true]
      have hmNew_tab : mNew (embH + 2 + e) = H := by simp [hmNew]
      have hmNew_out : ∀ x, x ≠ embH + 2 + e → (x < H ∨ H + Read.walkWords W ≤ x) →
          mNew x = st.mem x := by
        intro x hx1 hx2
        rw [hWw3] at hx2
        simp only [hmNew, Function.update_apply, hx1, show x ≠ H + 2 by omega,
          show x ≠ H + 1 by omega, show x ≠ H by omega, ite_false]
      have hupd := embRefresh_update_step htab hHge heCap hold hrep hfr hz hloc
        (hW_eq ▸ mWalkAt_single_true hmNew_H0 hmNew_H1 hmNew_H2) hmNew_tab hmNew_out
      refine ⟨?_, by simp [hr21]⟩
      dsimp only [EmbRefreshInnerInv]
      rw [hpre_succ, hview_succ, hfold_succ]
      refine ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3],
        by simp [hWw3], by simp [hr5], by simp [hr6], by simp [hr8], by simp [hr9],
        by simp [hr16], by simp [hr17], by simp [hr18], by simp [hr19], by simp,
        hupd.1, hupd.2.1, hupd.2.2.1, hupd.2.2.2⟩
    · simp only [Expr.size, edgeStepCost, hW_def.symm, hWw3]; omega
  · -- Branch 2: `e ∉ H.E`, walk is `piTotal (d.state P) e`, read from spanner and copied.
    have hW_eq : W = piTotal (d.state P) e := by
      simp only [hW_def, slotWalk, hs, ↓reduceDIte, hSj, heH, ↓reduceIte]
    have hdsRep_cur : DSRepAt P b d m.2 st.mem := by
      have hloc_ds := dynSpannerRep_local P b d m mem₀ st.mem (fun a ha =>
        (hmem_bucket a (Or.inr ⟨⟨s, hs⟩, b, m, hxm, ha⟩)).symm)
      exact (hloc_ds.1 ⟨hm1, hdsRep, (hS6.1 ⟨s, hs⟩ |> fun h => by rw [hSj, hxm] at h; exact h.2.1.2.2)⟩).2.1
    refine runs_cond_false_le (Expr.eval_reg_of_eq (by simp [heH])) ?_
    -- Compute `wPtr` in register 24, splitting on `(d.state P).t = 0` vs `≠ 0`.
    have hcont : ∀ (wPtr : ℕ) (reg24_st : State) (cPrev : ℕ),
        reg24_st.mem = st.mem →
        reg24_st.regs 0 = embH → reg24_st.regs 1 = spanH → reg24_st.regs 2 = slotsPtr →
        reg24_st.regs 3 = n → reg24_st.regs 4 = H → reg24_st.regs 5 = embH + 2 →
        reg24_st.regs 6 = k → reg24_st.regs 8 = b → reg24_st.regs 9 = (d.state P).t →
        reg24_st.regs 16 = dgEListBase (dsGPtr b) P.vCap P.eCap →
        reg24_st.regs 17 = eL.length →
        reg24_st.regs 18 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap →
        reg24_st.regs 19 = dsPiPtrBase b P.L P.vCap P.eCap →
        reg24_st.regs 21 = i → reg24_st.regs 22 = e → reg24_st.regs 24 = wPtr →
        MWalkAt st.mem wPtr W →
        RangeInHeapFoot m.2 wPtr (wPtr + (mWalkEncode W).length) →
        cPrev + 17 * Read.walkWords W + 35 ≤ edgeStepCost P S6 s d e →
        ∃ o st' c,
          Runs P.w p ω
            (.assign 25 (.bin .add (.const 1) (.bin .mul (.const 2) (.load (.reg 24)))) ;;
             .call 26 bCopy [.reg 24, .reg 4, .reg 25] ;;
             .store (.bin .add (.reg 5) (.reg 22)) (.reg 4) ;;
             .assign 4 (.bin .add (.reg 4) (.reg 25)))
            reg24_st o st' c ∧
          normalPost (fun st₁ =>
            EmbRefreshInnerInv P eCap embH spanH slotsPtr n h₀ mem₀ vInit ptrInit S6 s d b eL
              k hpStart vStart ptrStart (i + 1)
              { st₁ with regs := Function.update st₁.regs 21 (i + 1) } ∧
            st₁.regs 21 = i) o st' ∧
          cPrev + c ≤ edgeStepCost P S6 s d e := by
      intro wPtr rst cPrev hmR r0 r1 r2 r3 r4 r5 r6 r8 r9 r16 r17 r18 r19 r21 r22 r24
        hwAt hrng hcPrev
      have hWw : Read.walkWords W = 1 + 2 * W.length := rfl
      have hEncLen : (mWalkEncode W).length = Read.walkWords W := mWalkEncode_length W
      have hwEnd : wPtr + Read.walkWords W ≤ h₀ :=
        rangeInHeapFoot_lt_h hxm hbFoot (hEncLen ▸ hrng) (by omega)
      have hwHead : rst.mem wPtr = W.length := by rw [hmR]; exact MWalkAt_head hwAt
      refine runs_seq_assign_le (v := Read.walkWords W)
        (by
          rw [hWw]
          exact Expr.eval_add (Expr.eval_const (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_load_of_eq (Expr.eval_reg_of_eq r24) hwHead) (by omega))
            (by omega)) ?_
      refine runs_seq_call_le (vs := [wPtr, H, Read.walkWords W]) hcopy
        (evalArgs_cons (Expr.eval_reg_of_eq (by simp [r24]))
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp [r4]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) (evalArgs_nil _ _))))
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
        ⟨wPtr, H, Read.walkWords W, rfl, by omega, by omega, by omega, Or.inr (by omega)⟩ ?_
      rintro _ m2 pos2 ⟨_, _, _, hargs, -, hcp, hcfr⟩
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      refine runs_seq_store_le (x := embH + 2 + e) (v := H)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5]))
          (Expr.eval_reg_of_eq (by simp [r22])) htab_e_W)
        (Expr.eval_reg_of_eq (by simp [r4])) ?_
      refine runs_assign_le (v := H + Read.walkWords W)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4]))
          (Expr.eval_reg_of_eq (by simp)) hHlt') ?_ ?_
      · dsimp only [normalPost]
        set mNew := Function.update m2 (embH + 2 + e) H with hmNew
        have hwalk_new : MWalkAt mNew H W := by
          intro j hj
          have hj' : j < Read.walkWords W := by simpa [hEncLen] using hj
          rw [hmNew, Function.update_of_ne (by omega), hcp j hj', hmR]
          exact hwAt j hj
        have hmNew_tab : mNew (embH + 2 + e) = H := by simp [hmNew]
        have hmNew_out : ∀ x, x ≠ embH + 2 + e → (x < H ∨ H + Read.walkWords W ≤ x) →
            mNew x = st.mem x := by
          intro x hx1 hx2
          rw [hmNew, Function.update_of_ne hx1, hcfr x hx2, hmR]
        have hupd := embRefresh_update_step htab hHge heCap hold hrep hfr hz hloc
          hwalk_new hmNew_tab hmNew_out
        refine ⟨?_, by simp [r21]⟩
        dsimp only [EmbRefreshInnerInv]
        rw [hpre_succ, hview_succ, hfold_succ]
        refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3],
          by simp, by simp [r5], by simp [r6], by simp [r8], by simp [r9],
          by simp [r16], by simp [r17], by simp [r18], by simp [r19], by simp,
          hupd.1, hupd.2.1, hupd.2.2.1, hupd.2.2.2⟩
      · simp only [Expr.size, argsSize, copyWordsContract]; omega
    -- Now dispatch on `(d.state P).t = 0` vs `≠ 0`.
    by_cases ht0 : (d.state P).t = 0
    · -- Fresh spanner: read level-0 walk pointer directly in `O(1)`.
      obtain ⟨hwAt, hrng⟩ := dsRepAt_fresh_piWalk hdsRep_cur ht0 heG
      rw [← hW_eq] at hwAt hrng
      have hpi_lt : dsPiPtrBase b P.L P.vCap P.eCap + e < b + dsFixedSize P.L P.vCap P.eCap := by
        have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
      refine runs_seq_split_le (T₁ := 20)
        (P₁ := fun st₁ =>
          st₁.mem = st.mem ∧ st₁.regs 0 = embH ∧ st₁.regs 1 = spanH ∧ st₁.regs 2 = slotsPtr ∧
          st₁.regs 3 = n ∧ st₁.regs 4 = H ∧ st₁.regs 5 = embH + 2 ∧ st₁.regs 6 = k ∧
          st₁.regs 8 = b ∧ st₁.regs 9 = (d.state P).t ∧
          st₁.regs 16 = dgEListBase (dsGPtr b) P.vCap P.eCap ∧ st₁.regs 17 = eL.length ∧
          st₁.regs 18 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap ∧
          st₁.regs 19 = dsPiPtrBase b P.L P.vCap P.eCap ∧
          st₁.regs 21 = i ∧ st₁.regs 22 = e ∧
          st₁.regs 24 = st.mem (dsPiPtrBase b P.L P.vCap P.eCap + e)) ?_ ?_
      · refine runs_cond_false_le (Expr.eval_reg_of_eq (by simp [hr9, ht0])) ?_
        refine runs_assign_le (v := st.mem (dsPiPtrBase b P.L P.vCap P.eCap + e))
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr19])) (Expr.eval_reg_of_eq (by simp))
              (by omega))
            rfl)
          ⟨rfl, rfl, by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3],
            by simp [hr4, hH_def], by simp [hr5], by simp [hr6], by simp [hr8], by simp [hr9],
            by simp [hr16], by simp [hr17], by simp [hr18], by simp [hr19], by simp [hr21],
            by simp, by simp⟩
          (by simp only [Expr.size]; omega)
      · rintro st₁ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
        exact hcont _ st₁ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 hwAt hrng
          (by simp only [Expr.size, edgeStepCost, hW_def.symm]; omega)
    · -- General spanner (`t ≠ 0`, so `d.Us ≠ []`): call `spanPiWalkPtrStmt` at `bPi`.
      have hUs_ne : d.Us ≠ [] := fun hnil => ht0 (dsRepAt_t_eq_zero_of_nil hnil)
      have hbW : b < 2 ^ P.w := by omega
      have hfootW : ∀ a, heapFoot m.2 a → a < 2 ^ P.w := fun a ha =>
        lt_trans (hbFoot a (Or.inr ⟨⟨s, hs⟩, b, m, hxm, Or.inr ha⟩)) hh₀W
      refine runs_seq_split_le (T₁ := spanPiWalkPtrCost P.L + 20)
        (P₁ := fun st₁ =>
          st₁.mem = st.mem ∧ st₁.regs 0 = embH ∧ st₁.regs 1 = spanH ∧ st₁.regs 2 = slotsPtr ∧
          st₁.regs 3 = n ∧ st₁.regs 4 = H ∧ st₁.regs 5 = embH + 2 ∧ st₁.regs 6 = k ∧
          st₁.regs 8 = b ∧ st₁.regs 9 = (d.state P).t ∧
          st₁.regs 16 = dgEListBase (dsGPtr b) P.vCap P.eCap ∧ st₁.regs 17 = eL.length ∧
          st₁.regs 18 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap ∧
          st₁.regs 19 = dsPiPtrBase b P.L P.vCap P.eCap ∧
          st₁.regs 21 = i ∧ st₁.regs 22 = e ∧
          MWalkAt st.mem (st₁.regs 24) W ∧
          RangeInHeapFoot m.2 (st₁.regs 24) (st₁.regs 24 + (mWalkEncode W).length)) ?_ ?_
      · refine runs_cond_true_le (v := (d.state P).t)
          (Expr.eval_reg_of_eq (by simp [hr9])) ht0 ?_
        refine runs_call_le (vs := [b, e]) (hpiAt e heG)
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr8]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) (evalArgs_nil _ _)))
          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
          ⟨rfl, hw16, hdsRep_cur, heG, hfixW, hfootW⟩
          (fun ret m' pos' ⟨hm', hw', hrng'⟩ => by
            rw [hm'] at hw'
            rw [← hW_eq] at hw' hrng'
            refine ⟨⟨rfl, hm', by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3],
              by simp [hr4, hH_def], by simp [hr5], by simp [hr6], by simp [hr8], by simp [hr9],
              by simp [hr16], by simp [hr17], by simp [hr18], by simp [hr19], by simp [hr21],
              by simp, by simpa using hw', by simpa using hrng'⟩, ?_⟩
            simp only [Expr.size, argsSize, spanPiWalkPtrContract]; omega)
      · rintro st₁ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hwAt, hrng⟩
        exact hcont (st₁.regs 24) st₁ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
          rfl hwAt hrng
          (by simp only [Expr.size, edgeStepCost, hW_def.symm, spanPiWalkPtrCost, hUs_ne,
            ↓reduceIte]; omega)

/-- Full inner loop `forRange 21 (.const 0) (.reg 17) (embRefreshEdgeBody bCopy bPi)` for one
active slot `s`. -/
theorem embRefreshInner_triple {P : DSParams} {cap eCap embH spanH slotsPtr n h₀ : ℕ}
    {p : Program} {bCopy bPi : ℕ}
    (hcopy : MeetsContract P.w p bCopy (copyWordsContract P.w))
    {mem₀ : ℕ → ℕ} {vInit : EmbView} {ptrInit : ℕ → ℕ}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap}
    {s : ℕ} (hs : s < cap) {d : DSHist} {b : ℕ} {m : DSHist × DynSpannerMeta P.L}
    (hSj : S6 ⟨s, hs⟩ = some d) (hxm : x6.slots ⟨s, hs⟩ = some (b, m))
    (hS6 : (bucketSpannerRep P cap).rep spanH S6 x6 mem₀)
    (hpiAt : ∀ e ∈ (d.state P).G.E, MeetsContract P.w p bPi (spanPiWalkPtrContract P b e d m.2))
    {eL : List ℕ} (heL_len : eL.length = (d.state P).G.m) (heL_nd : eL.Nodup)
    (heL_mem : ∀ e, e ∈ eL ↔ e ∈ (d.state P).G.E)
    (heL_at : ListAt mem₀ (dgEListBase (dsGPtr b) P.vCap P.eCap) eL)
    (heCap_all : ∀ e ∈ (d.state P).G.E, e < eCap)
    (htab : embH + 2 + eCap ≤ h₀)
    (hold : ∀ e' ∈ vInit.dom, ptrInit e' + Read.walkWords (vInit.emb e') ≤ h₀)
    (hbFoot : ∀ a, bucketFoot spanH x6 a → a < h₀)
    (hdisj : ∀ a, embH + 2 ≤ a → a < embH + 2 + eCap → ¬ bucketFoot spanH x6 a)
    (hw16 : 16 ≤ 2 ^ P.w)
    {k hpStart : ℕ} {vStart : EmbView} {ptrStart : ℕ → ℕ}
    (hStartGe : h₀ ≤ hpStart)
    (hEndLt : hpStart + slotWalkWords P S6 s < 2 ^ P.w) :
    Triple P.w p
      (fun st =>
        EmbRefreshInnerInv P eCap embH spanH slotsPtr n h₀ mem₀ vInit ptrInit S6 s d b eL
          k hpStart vStart ptrStart 0 { st with regs := Function.update st.regs 21 0 })
      (forRange 21 (.const 0) (.reg 17) (embRefreshEdgeBody bCopy bPi))
      (normalPost (EmbRefreshInnerInv P eCap embH spanH slotsPtr n h₀ mem₀ vInit ptrInit S6 s d b eL
        k hpStart vStart ptrStart eL.length))
      (fun _ => 142 * ((d.state P).G.E.sum fun e =>
        Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2) + 10) := by
  have hslotGE : slotGE P S6 s = (d.state P).G.E := by
    unfold slotGE; simp only [hs, ↓reduceDIte, hSj]
  have hwalkEq : (eL.map fun e => Read.walkWords (slotWalk P S6 s e)).sum =
      slotWalkWords P S6 s := by
    unfold slotWalkWords
    rw [hslotGE]
    exact list_map_sum_eq_finset_sum eL heL_nd (d.state P).G.E heL_mem _
  have hlenLt : eL.length < 2 ^ P.w := by
    have hslot := hS6.1 ⟨s, hs⟩
    rw [hSj, hxm] at hslot
    have hSt := hslot.2.1.2.1.2.2.2.2.2.2.2.1
    have hsub : (d.state P).G.E ⊆ Finset.range P.eCap := fun x hx =>
      Finset.mem_range.mpr (hSt.2.2.2.2.2.2.2.2.2.2.1 x hx)
    have hcard : eL.length ≤ P.eCap := by
      rw [heL_len]; simpa [MGraph.m] using Finset.card_le_card hsub
    have hfixH := slot_fixedSize_le_h hS6 hSj hxm hbFoot
    have hB := embRefresh_fixedBounds (b := b) (L := P.L) (vCap := P.vCap) (eCap := P.eCap)
    omega
  set stepC : ℕ → ℕ := fun i => if hi : i < eL.length then edgeStepCost P S6 s d (eL[i]'hi) else 0
  have hloop := Triple.forRange_le (w := P.w) (p := p) (r := 21) (lo := .const 0) (hi := .reg 17)
    (body := embRefreshEdgeBody bCopy bPi)
    (P := fun st =>
      EmbRefreshInnerInv P eCap embH spanH slotsPtr n h₀ mem₀ vInit ptrInit S6 s d b eL
        k hpStart vStart ptrStart 0 { st with regs := Function.update st.regs 21 0 })
    (Inv := EmbRefreshInnerInv P eCap embH spanH slotsPtr n h₀ mem₀ vInit ptrInit S6 s d b eL
      k hpStart vStart ptrStart)
    stepC 0 eL.length (Nat.zero_le _) (by omega) (fun _ => hlenLt)
    (fun st h => ⟨Expr.eval_const (by omega), h⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.2.2.2.2.2.2.1)
    (fun i _ hi => by
      have htakeLe :
          ((eL.take (i + 1)).map fun e => Read.walkWords (slotWalk P S6 s e)).sum ≤
            (eL.map fun e => Read.walkWords (slotWalk P S6 s e)).sum := by
        have hsplit : eL = eL.take (i + 1) ++ eL.drop (i + 1) := (List.take_append_drop _ _).symm
        conv_rhs => rw [hsplit]
        rw [List.map_append, List.sum_append]
        exact Nat.le_add_right _ _
      have hstep := embRefreshEdge_step (slotsPtr := slotsPtr) (n := n) (k := k)
        (vStart := vStart) (ptrStart := ptrStart) hcopy hs hSj hxm hS6 hpiAt heL_len
        heL_mem heL_at heCap_all htab hold hbFoot hdisj hw16 hStartGe hi (by omega)
      simpa only [stepC, dite_eq_left_of_eq_true (eq_true hi)] using hstep)
  refine hloop.conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => ?_)
  have hrc : rangeCost stepC 0 eL.length = (eL.map (edgeStepCost P S6 s d)).sum :=
    rangeCost_getElem_eq_map_sum eL (edgeStepCost P S6 s d)
  rw [hrc, list_map_sum_eq_finset_sum eL heL_nd (d.state P).G.E heL_mem]
  have hcard : eL.length = (d.state P).G.E.card := heL_len
  simp only [Nat.sub_zero, Expr.size, hcard]
  have hsum :
      ((d.state P).G.E.sum (edgeStepCost P S6 s d)) + (d.state P).G.E.card * 9 ≤
        142 * ((d.state P).G.E.sum fun e =>
          Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2) := by
    rw [Finset.mul_sum]
    have hcard_sum : (d.state P).G.E.card * 9 = (d.state P).G.E.sum (fun _ => 9) := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [hcard_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    unfold edgeStepCost
    split_ifs <;> omega
  omega

end

end MinCostFlow.SparseCore.Program
