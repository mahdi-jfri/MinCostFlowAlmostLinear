module

public import MinCostFlow.SparseCore.Program.AssemblyFirstEmbCopyIns
public import MinCostFlow.SparseCore.Program.SpanBucketDefs

import WordRAM.Tactic

/-!
# Per-slot selective embedding-table walk copy (`AssemblyFirstEmbCopy`)

Implements and verifies `asmFirstCopySlotListStmt bCopy bPi` (`[embH, spanH, s, eListPtr, m, h]`):
given a bucket spanner slot `s` holding `d = S6 ⟨s, hs⟩` and an arbitrary edge list `eL` at
`eListPtr` (`∀ e ∈ eL, e ∈ slotGE P S6 s`, such as the re-embedded/leaving edges of an updated
slot or the edge list of a freshly activated slot), reuses `embRefreshEdgeBody bCopy bPi`
(`EmbRefreshDefs.lean`) to copy `slotWalk P S6 s e` for each `e ∈ eL` into `embH`, allocating
only the exact walk words `slotListWalkWords P S6 s eL` (zero scratch) and running in
`142 * slotListCopyWork P S6 s d eL + 120` time (with zero `+ P.L` overhead when `d.Us = []`).

The companion entering-edge updater `asmFirstCopyInsStmt` is in `AssemblyFirstEmbCopyIns.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Procedure and cost/space definitions -/

@[expose] public section

/-- **Per-slot selective walk copy**, `[embH, spanH, s, eListPtr, m, h]`, calling `copyWords` at
`bCopy` and `spanPiWalkPtrStmt` at `bPi`. Reuses `embRefreshEdgeBody bCopy bPi` with `reg 16 =
eListPtr` and `reg 17 = m`, returning the new heap pointer. -/
def asmFirstCopySlotListStmt (bCopy bPi : ℕ) : Stmt :=
  .assign 16 (.reg 3) ;;
  .assign 17 (.reg 4) ;;
  .assign 4 (.reg 5) ;;
  .assign 5 (.load (.reg 0)) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.reg 2))) ;;
  .assign 9 (.load (.bin .add (.reg 8) (.const dsTOff))) ;;
  .assign 10 (.load (.bin .add (.reg 8) (.const dsLOff))) ;;
  .assign 11 (.load (.bin .add (.reg 8) (.const dsVCapOff))) ;;
  .assign 12 (.load (.bin .add (.reg 8) (.const dsECapOff))) ;;
  .assign 13 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 11)) (.bin .mul (.const 9) (.reg 12)))) ;;
  .assign 14 (.bin .add (.reg 8) (.const dsHdrSize)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 13)) ;;
  .assign 18 (.bin .add (.bin .add (.reg 15) (.const 4))
    (.bin .mul (.const 7) (.reg 11))) ;;
  .assign 20 (.bin .add (.reg 10) (.const 1)) ;;
  .assign 19 (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 13)))
    (.bin .add (.bin .mul (.const 3) (.reg 12)) (.bin .mul (.const 2) (.reg 20)))) ;;
  .assign 19 (.bin .add (.bin .add (.reg 19) (.reg 20))
    (.bin .mul (.reg 20) (.reg 12))) ;;
  forRange 21 (.const 0) (.reg 17) (embRefreshEdgeBody bCopy bPi) ;;
  .ret (.reg 4)

/-- Per-list walk-word allocation for `asmFirstCopySlotListStmt`. -/
noncomputable def slotListWalkWords (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (s : ℕ) (eL : List ℕ) : ℕ :=
  (eL.map fun e => Read.walkWords (slotWalk P S6 s e)).sum

/-- Per-list work unit for `asmFirstCopySlotListStmt`. -/
noncomputable def slotListCopyWork (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (s : ℕ) (d : DSHist) (eL : List ℕ) : ℕ :=
  (eL.map fun e => Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2).sum

end

/-! ## Determinism -/

public section

theorem asmFirstCopySlotListStmt_noRand (bCopy bPi : ℕ) :
    (asmFirstCopySlotListStmt bCopy bPi).NoRand := by
  simp [asmFirstCopySlotListStmt, embRefreshEdgeBody, forRange, forUp, Stmt.NoRand]

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

/-! ## Verification of `asmFirstCopySlotListStmt` -/

private def slotListInv (P : DSParams) {cap : ℕ} (eCap embH _spanH eListPtr h₀ : ℕ)
    (mem₀ : ℕ → ℕ) (vInit : EmbView) (ptrInit : ℕ → ℕ)
    (S6 : BucketSpannerState cap) (s : ℕ) (d : DSHist) (b : ℕ) (eL : List ℕ)
    (i : ℕ) (st : State) : Prop :=
  let pre := slotChange P S6 s (eL.take i)
  let curV := vInit.apply pre
  let curS := pre.foldl embConcStep (ptrInit, h₀)
  st.regs 4 = curS.2 ∧ st.regs 5 = embH + 2 ∧
  st.regs 8 = b ∧ st.regs 9 = (d.state P).t ∧
  st.regs 16 = eListPtr ∧ st.regs 17 = eL.length ∧
  st.regs 18 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap ∧
  st.regs 19 = dsPiPtrBase b P.L P.vCap P.eCap ∧ st.regs 21 = i ∧
  EmbRepAt eCap embH curV curS.1 st.mem ∧
  (∀ x < h₀, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → st.mem x = mem₀ x) ∧
  ZeroFrom st.mem curS.2 ∧
  ∀ e ∈ curV.dom,
    (curS.1 e = ptrInit e ∧ curV.emb e = vInit.emb e ∧ e ∈ vInit.dom) ∨
    (h₀ ≤ curS.1 e ∧ curS.1 e + Read.walkWords (curV.emb e) ≤ curS.2)

private lemma slotList_edge_step {P : DSParams} {cap eCap embH spanH eListPtr h₀ : ℕ}
    {p : Program} {bCopy bPi : ℕ}
    (hcopy : MeetsContract P.w p bCopy (copyWordsContract P.w))
    {mem₀ : ℕ → ℕ} {vInit : EmbView} {ptrInit : ℕ → ℕ}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap}
    {s : ℕ} (hs : s < cap) {d : DSHist} {b : ℕ} {m : DSHist × DynSpannerMeta P.L}
    (hSj : S6 ⟨s, hs⟩ = some d) (hxm : x6.slots ⟨s, hs⟩ = some (b, m))
    (hS6 : (bucketSpannerRep P cap).rep spanH S6 x6 mem₀)
    (hpiAt : ∀ e ∈ (d.state P).G.E, MeetsContract P.w p bPi (spanPiWalkPtrContract P b e d m.2))
    {eL : List ℕ} (heL_at : ListAt mem₀ eListPtr eL) (heL_le : eListPtr + eL.length ≤ h₀)
    (heL_sub : ∀ e ∈ eL, e ∈ (d.state P).G.E ∧ e < eCap)
    (heL_disj : ∀ a, eListPtr ≤ a → a < eListPtr + eL.length → a < embH + 2 ∨ embH + 2 + eCap ≤ a)
    (htab : embH + 2 + eCap ≤ h₀)
    (hold : ∀ e' ∈ vInit.dom, ptrInit e' + Read.walkWords (vInit.emb e') ≤ h₀)
    (hbFoot : ∀ a, bucketFoot spanH x6 a → a < h₀)
    (hdisj : ∀ a, embH + 2 ≤ a → a < embH + 2 + eCap → ¬ bucketFoot spanH x6 a)
    (hw16 : 16 ≤ 2 ^ P.w)
    {i : ℕ} (hi : i < eL.length)
    (hHlt : h₀ + ((eL.take (i + 1)).map fun e => Read.walkWords (slotWalk P S6 s e)).sum < 2 ^ P.w) :
    Triple P.w p
      (slotListInv P eCap embH spanH eListPtr h₀ mem₀ vInit ptrInit S6 s d b eL i)
      (embRefreshEdgeBody bCopy bPi)
      (normalPost fun st₁ =>
        slotListInv P eCap embH spanH eListPtr h₀ mem₀ vInit ptrInit S6 s d b eL (i + 1)
          { st₁ with regs := Function.update st₁.regs 21 (i + 1) } ∧ st₁.regs 21 = i)
      (fun _ => edgeStepCost P S6 s d (eL[i]'hi)) := by
  intro st ω hInv
  dsimp only [slotListInv] at hInv
  set pre := slotChange P S6 s (eL.take i) with hpre_def
  set curV := vInit.apply pre with hcurV_def
  set curS := pre.foldl embConcStep (ptrInit, h₀) with hcurS_def
  obtain ⟨hr4, hr5, hr8, hr9, hr16, hr17, hr18, hr19, hr21, hrep, hfr, hz, hloc⟩ := hInv
  set e := eL[i]'hi with he_def
  set H := curS.2 with hH_def
  set W := slotWalk P S6 s e with hW_def
  have hslot := hS6.1 ⟨s, hs⟩
  rw [hSj, hxm] at hslot
  obtain ⟨_, ⟨hm1, hdsRep, hdsFoot⟩, _⟩ := hslot
  have hSt := hdsRep.2.2.2.2.2.2.2.1
  have hHAt : DynGraphAt mem₀ (dsHPtr b P.vCap P.eCap) P.vCap P.eCap (d.state P).H :=
    hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfixH : b + dsFixedSize P.L P.vCap P.eCap ≤ h₀ := slot_fixedSize_le_h hS6 hSj hxm hbFoot
  have hB := embRefresh_fixedBounds (b := b) (L := P.L) (vCap := P.vCap) (eCap := P.eCap)
  have hHge : h₀ ≤ H := by rw [hH_def, hcurS_def, embConcStep_fold_snd]; omega
  have hHsum : H + Read.walkWords W =
      h₀ + ((eL.take (i + 1)).map fun x => Read.walkWords (slotWalk P S6 s x)).sum := by
    rw [hH_def, hcurS_def, embConcStep_fold_snd, hpre_def]
    have hmap : ((slotChange P S6 s (eL.take i)).map fun p => Read.walkWords p.2).sum =
        ((eL.take i).map fun x => Read.walkWords (slotWalk P S6 s x)).sum := by
      unfold slotChange; rw [List.map_map]; rfl
    rw [hmap, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, hW_def, he_def, Nat.add_assoc]
  have hHlt' : H + Read.walkWords W < 2 ^ P.w := by rw [hHsum]; exact hHlt
  have hh₀W : h₀ < 2 ^ P.w := by omega
  have hfixW : b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w := lt_of_le_of_lt hfixH hh₀W
  have ⟨heG, heCap⟩ := heL_sub e (List.getElem_mem hi)
  have heSpE : e < P.eCap := hSt.2.2.2.2.2.2.2.2.2.2.1 e heG
  have hvCapMeta : m.2.vCap = P.vCap := hSt.1
  have heCapMeta : m.2.eCap = P.eCap := hSt.2.1
  have hmem_bucket : ∀ a, bucketFoot spanH x6 a → st.mem a = mem₀ a := by
    intro a ha
    refine hfr a (hbFoot a ha) ?_
    by_contra hnot; push Not at hnot; exact hdisj a hnot.1 hnot.2 ha
  have hmem_fixed : ∀ a, b ≤ a → a < b + dsFixedSize P.L P.vCap P.eCap → st.mem a = mem₀ a :=
    fun a h1 h2 => hmem_bucket a (Or.inr ⟨⟨s, hs⟩, b, m, hxm, Or.inl ⟨h1, by rw [hvCapMeta, heCapMeta]; exact h2⟩⟩)
  have he_mem : st.mem (eListPtr + i) = e := by
    rw [hfr (eListPtr + i) (by omega) (heL_disj _ (by omega) (by omega))]; exact heL_at i hi
  have hinH_mem : st.mem (dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + e) =
      if e ∈ (d.state P).H.E then 1 else 0 := by
    have hge : b ≤ dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + e := by
      simp only [dgEPresBase, dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]; omega
    have hlt : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + e < b + dsFixedSize P.L P.vCap P.eCap := by
      have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    rw [hmem_fixed _ hge hlt]
    exact hHAt.2.2.2.2.2.2.2.2.2.2.2.1 e heSpE
  have hpre_succ : slotChange P S6 s (eL.take (i + 1)) = pre ++ [(e, W)] := by
    unfold slotChange; rw [List.take_succ_eq_append_getElem hi, List.map_append, List.map_singleton]; rfl
  have hfold_succ : (pre ++ [(e, W)]).foldl embConcStep (ptrInit, h₀) =
      (Function.update curS.1 e H, H + Read.walkWords W) := by
    simp [List.foldl_append, embConcStep, hcurS_def, hH_def]
  have hview_succ : vInit.apply (pre ++ [(e, W)]) = ⟨Function.update curV.emb e W, insert e curV.dom⟩ := by
    rw [EmbView.apply_append, EmbView.apply_singleton]
  dsimp only [embRefreshEdgeBody]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr16) (Expr.eval_reg_of_eq hr21)
      (by omega)) he_mem) ?_
  refine runs_seq_assign_le (v := if e ∈ (d.state P).H.E then 1 else 0)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr18]))
      (Expr.eval_reg_of_eq (by simp)) (by have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega)) hinH_mem) ?_
  by_cases heH : e ∈ (d.state P).H.E
  · have hW_eq : W = [(e, true)] := by simp only [hW_def, slotWalk, hs, ↓reduceDIte, hSj, heH, ↓reduceIte]
    have hWw3 : Read.walkWords W = 3 := by rw [hW_eq]; rfl
    refine runs_cond_true_le (v := 1) (Expr.eval_reg_of_eq (by simp [heH])) (by decide) ?_
    refine runs_seq_store_le (x := H) (v := 1)
      (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := H + 1) (v := e)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := H + 2) (v := 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := embH + 2 + e) (v := H)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr5])) (Expr.eval_reg_of_eq (by simp)) (by omega))
      (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) ?_
    refine runs_assign_le (v := H + 3)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr4, hH_def])) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
    · dsimp only [normalPost]
      have hupd := embUpdate_step
        (m_new := Function.update (Function.update (Function.update (Function.update st.mem
          H 1) (H + 1) e) (H + 2) 1) (embH + 2 + e) H)
        htab hHge heCap hold hrep hfr hz hloc
        (hW_eq ▸ mWalkAt_single_true
          (by simp [Function.update, show H ≠ embH + 2 + e by omega])
          (by simp [Function.update, show H + 1 ≠ embH + 2 + e by omega])
          (by simp [Function.update, show H + 2 ≠ embH + 2 + e by omega]))
        (by simp [Function.update])
        (fun x hx1 hx2 => by
          rw [hWw3] at hx2
          simp [Function.update, hx1, show x ≠ H + 2 by omega, show x ≠ H + 1 by omega,
            show x ≠ H by omega])
      refine ⟨?_, by simp [hr21]⟩
      dsimp only [slotListInv]
      rw [hpre_succ, hview_succ, hfold_succ]
      exact ⟨by simp [hWw3], by simp [hr5], by simp [hr8], by simp [hr9], by simp [hr16],
        by simp [hr17], by simp [hr18], by simp [hr19], by simp,
        hupd.1, hupd.2.1, hupd.2.2.1, hupd.2.2.2⟩
    · simp only [Expr.size, edgeStepCost, hW_def.symm, hWw3]; omega
  · have hW_eq : W = piTotal (d.state P) e := by
      simp only [hW_def, slotWalk, hs, ↓reduceDIte, hSj, heH, ↓reduceIte]
    have hdsRep_cur : DSRepAt P b d m.2 st.mem :=
      ((dynSpannerRep_local P b d m mem₀ st.mem fun a ha =>
        (hmem_bucket a (Or.inr ⟨⟨s, hs⟩, b, m, hxm, ha⟩)).symm).1 ⟨hm1, hdsRep, hdsFoot⟩).2.1
    refine runs_cond_false_le (Expr.eval_reg_of_eq (by simp [heH])) ?_
    have hcont : ∀ (wPtr : ℕ) (rst : State) (cPrev : ℕ),
        rst.mem = st.mem → rst.regs 4 = H → rst.regs 5 = embH + 2 →
        rst.regs 8 = b → rst.regs 9 = (d.state P).t →
        rst.regs 16 = eListPtr → rst.regs 17 = eL.length →
        rst.regs 18 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap →
        rst.regs 19 = dsPiPtrBase b P.L P.vCap P.eCap →
        rst.regs 21 = i → rst.regs 22 = e → rst.regs 24 = wPtr →
        MWalkAt st.mem wPtr W →
        RangeInHeapFoot m.2 wPtr (wPtr + (mWalkEncode W).length) →
        cPrev + 17 * Read.walkWords W + 35 ≤ edgeStepCost P S6 s d e →
        ∃ o st' c,
          Runs P.w p ω
            (.assign 25 (.bin .add (.const 1) (.bin .mul (.const 2) (.load (.reg 24)))) ;;
             .call 26 bCopy [.reg 24, .reg 4, .reg 25] ;;
             .store (.bin .add (.reg 5) (.reg 22)) (.reg 4) ;;
             .assign 4 (.bin .add (.reg 4) (.reg 25)))
            rst o st' c ∧
          normalPost (fun st₁ =>
            slotListInv P eCap embH spanH eListPtr h₀ mem₀ vInit ptrInit S6 s d b eL (i + 1)
              { st₁ with regs := Function.update st₁.regs 21 (i + 1) } ∧ st₁.regs 21 = i) o st' ∧
          cPrev + c ≤ edgeStepCost P S6 s d e := by
      intro wPtr rst cPrev hmR r4 r5 r8 r9 r16 r17 r18 r19 r21 r22 r24 hwAt hrng hcPrev
      have hWw : Read.walkWords W = 1 + 2 * W.length := rfl
      have hEncLen : (mWalkEncode W).length = Read.walkWords W := mWalkEncode_length W
      have hwEnd : wPtr + Read.walkWords W ≤ h₀ :=
        rangeInHeapFoot_lt_h hxm hbFoot (hEncLen ▸ hrng) (by omega)
      have hwHead : rst.mem wPtr = W.length := by rw [hmR]; exact MWalkAt_head hwAt
      refine runs_seq_assign_le (v := Read.walkWords W)
        (by rw [hWw]
            exact Expr.eval_add (Expr.eval_const (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_load_of_eq (Expr.eval_reg_of_eq r24) hwHead) (by omega)) (by omega)) ?_
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
          (Expr.eval_reg_of_eq (by simp [r22])) (by omega))
        (Expr.eval_reg_of_eq (by simp [r4])) ?_
      refine runs_assign_le (v := H + Read.walkWords W)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4])) (Expr.eval_reg_of_eq (by simp)) hHlt') ?_ ?_
      · dsimp only [normalPost]
        set mNew := Function.update m2 (embH + 2 + e) H with hmNew
        have hwalk_new : MWalkAt mNew H W := fun j hj => by
          have hj' : j < Read.walkWords W := by simpa [hEncLen] using hj
          rw [hmNew, Function.update_of_ne (by omega), hcp j hj', hmR]; exact hwAt j hj
        have hupd := embUpdate_step htab hHge heCap hold hrep hfr hz hloc hwalk_new
          (by simp [hmNew])
          (fun x hx1 hx2 => by rw [hmNew, Function.update_of_ne hx1, hcfr x hx2, hmR])
        refine ⟨?_, by simp [r21]⟩
        dsimp only [slotListInv]
        rw [hpre_succ, hview_succ, hfold_succ]
        exact ⟨by simp, by simp [r5], by simp [r8], by simp [r9], by simp [r16], by simp [r17],
          by simp [r18], by simp [r19], by simp, hupd.1, hupd.2.1, hupd.2.2.1, hupd.2.2.2⟩
      · simp only [Expr.size, argsSize, copyWordsContract]; omega
    by_cases ht0 : (d.state P).t = 0
    · obtain ⟨hwAt, hrng⟩ := dsRepAt_fresh_piWalk hdsRep_cur ht0 heG
      rw [← hW_eq] at hwAt hrng
      have hpi_lt : dsPiPtrBase b P.L P.vCap P.eCap + e < b + dsFixedSize P.L P.vCap P.eCap := by
        have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
      refine runs_seq_split_le (T₁ := 20)
        (P₁ := fun st₁ =>
          st₁.mem = st.mem ∧ st₁.regs 4 = H ∧ st₁.regs 5 = embH + 2 ∧
          st₁.regs 8 = b ∧ st₁.regs 9 = (d.state P).t ∧
          st₁.regs 16 = eListPtr ∧ st₁.regs 17 = eL.length ∧
          st₁.regs 18 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap ∧
          st₁.regs 19 = dsPiPtrBase b P.L P.vCap P.eCap ∧ st₁.regs 21 = i ∧ st₁.regs 22 = e ∧
          st₁.regs 24 = st.mem (dsPiPtrBase b P.L P.vCap P.eCap + e)) ?_ ?_
      · refine runs_cond_false_le (Expr.eval_reg_of_eq (by simp [hr9, ht0])) ?_
        refine runs_assign_le (v := st.mem (dsPiPtrBase b P.L P.vCap P.eCap + e))
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr19]))
            (Expr.eval_reg_of_eq (by simp)) (by omega)) rfl)
          ⟨rfl, rfl, by simp [hr4, hH_def], by simp [hr5], by simp [hr8], by simp [hr9],
            by simp [hr16], by simp [hr17], by simp [hr18], by simp [hr19], by simp [hr21],
            by simp, by simp⟩
          (by simp only [Expr.size]; omega)
      · rintro st₁ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
        exact hcont _ st₁ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hwAt hrng
          (by simp only [Expr.size, edgeStepCost, hW_def.symm]; omega)
    · have hUs_ne : d.Us ≠ [] := fun hnil => ht0 (dsRepAt_t_eq_zero_of_nil hnil)
      have hfootW : ∀ a, heapFoot m.2 a → a < 2 ^ P.w := fun a ha =>
        lt_trans (hbFoot a (Or.inr ⟨⟨s, hs⟩, b, m, hxm, Or.inr ha⟩)) hh₀W
      refine runs_seq_split_le (T₁ := spanPiWalkPtrCost P.L + 20)
        (P₁ := fun st₁ =>
          st₁.mem = st.mem ∧ st₁.regs 4 = H ∧ st₁.regs 5 = embH + 2 ∧
          st₁.regs 8 = b ∧ st₁.regs 9 = (d.state P).t ∧
          st₁.regs 16 = eListPtr ∧ st₁.regs 17 = eL.length ∧
          st₁.regs 18 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap ∧
          st₁.regs 19 = dsPiPtrBase b P.L P.vCap P.eCap ∧ st₁.regs 21 = i ∧ st₁.regs 22 = e ∧
          MWalkAt st.mem (st₁.regs 24) W ∧
          RangeInHeapFoot m.2 (st₁.regs 24) (st₁.regs 24 + (mWalkEncode W).length)) ?_ ?_
      · refine runs_cond_true_le (v := (d.state P).t) (Expr.eval_reg_of_eq (by simp [hr9])) ht0 ?_
        refine runs_call_le (vs := [b, e]) (hpiAt e heG)
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr8]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by simp)) (evalArgs_nil _ _)))
          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
          ⟨rfl, hw16, hdsRep_cur, heG, hfixW, hfootW⟩
          (fun ret m' pos' ⟨hm', hw', hrng'⟩ => by
            rw [hm'] at hw'; rw [← hW_eq] at hw' hrng'
            refine ⟨⟨rfl, hm', by simp [hr4, hH_def], by simp [hr5], by simp [hr8], by simp [hr9],
              by simp [hr16], by simp [hr17], by simp [hr18], by simp [hr19], by simp [hr21],
              by simp, by simpa using hw', by simpa using hrng'⟩, ?_⟩
            simp only [Expr.size, argsSize, spanPiWalkPtrContract]; omega)
      · rintro st₁ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hwAt, hrng⟩
        exact hcont (st₁.regs 24) st₁ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 rfl hwAt hrng
          (by simp only [Expr.size, edgeStepCost, hW_def.symm, spanPiWalkPtrCost, hUs_ne, ↓reduceIte]; omega)

public section

/-- **Verification of `asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr)`**:
copies `slotWalk P S6 s e` for every edge `e` in `eL` (at `eListPtr`) into `embH`, allocating
exact space `slotListWalkWords P S6 s eL` (zero scratch) and running in
`142 * slotListCopyWork P S6 s d eL + 120` time (with zero `+ P.L` overhead when `d.Us = []`). -/
theorem asmFirstCopySlotList_runs {P : DSParams} {cap eCap embH spanH s eListPtr h pos : ℕ}
    {p : Program} {bCopy bRead : ℕ}
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    {v : EmbView} {y : EmbConc} {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap}
    (hs : s < cap) {d : DSHist} (hSj : S6 ⟨s, hs⟩ = some d)
    {eL : List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hS6 : (bucketSpannerRep P cap).rep spanH S6 x6 mem₀)
    (heL_at : ListAt mem₀ eListPtr eL) (heL_le : eListPtr + eL.length ≤ h)
    (heL_sub : ∀ e ∈ eL, e ∈ (d.state P).G.E ∧ e < eCap)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h)
    (hSpanF : ∀ a, bucketFoot spanH x6 a → a < h)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanH x6 a)
    (hDisjL : ∀ a, eListPtr ≤ a → a < eListPtr + eL.length → ¬ embFoot eCap embH y a)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + slotListWalkWords P S6 s eL < 2 ^ P.w) :
    ∃ o st' c y',
      Runs P.w p ω (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr))
        (startState [embH, spanH, s, eListPtr, eL.length, h] mem₀ pos) o st' c ∧
      (embRep eCap).rep embH (v.apply (slotChange P S6 s eL)) y' st'.mem ∧
      o.value = h + slotListWalkWords P S6 s eL ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ embFoot eCap embH y a → st'.mem a = mem₀ a) ∧
      (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h ≤ a ∧ a < o.value)) ∧
      c ≤ 142 * slotListCopyWork P S6 s d eL + 120 := by
  obtain ⟨hv, hrep0⟩ := hEmb
  obtain ⟨htab, hold⟩ := embFoot_below_parts hEmbF
  have hold' : ∀ e' ∈ v.dom, y.ptr e' + Read.walkWords (v.emb e') ≤ h := by rw [← hv]; exact hold
  have hslot := hS6.1 ⟨s, hs⟩
  rw [hSj] at hslot
  rcases hxm : x6.slots ⟨s, hs⟩ with _ | ⟨b, m⟩
  · rw [hxm] at hslot; exact False.elim hslot
  rw [hxm] at hslot
  obtain ⟨hmb, ⟨hm1, hdsRep, _⟩, _⟩ := hslot
  have hfixH := slot_fixedSize_le_h hS6 hSj hxm hSpanF
  have hhW : h < 2 ^ P.w := by omega
  have hfixW : b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w := lt_of_le_of_lt hfixH hhW
  have hB := embRefresh_fixedBounds (b := b) (L := P.L) (vCap := P.vCap) (eCap := P.eCap)
  have hspan_s_lt : spanH + s < h := hSpanF _ (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmT, hmL, hmV, hmE, -⟩ :=
    hdsRep.2.2.2.2.2.2.2.1
  have hdisjB' : ∀ a, embH + 2 ≤ a → a < embH + 2 + eCap → ¬ bucketFoot spanH x6 a :=
    fun a h1 h2 => hDisj a (Or.inl ⟨by omega, h2⟩)
  have hdisjL' : ∀ a, eListPtr ≤ a → a < eListPtr + eL.length → a < embH + 2 ∨ embH + 2 + eCap ≤ a := by
    intro a h1 h2; by_contra hnot; push Not at hnot; exact hDisjL a h1 h2 (Or.inl ⟨by omega, hnot.2⟩)
  have hpiAt : ∀ e ∈ (d.state P).G.E,
      MeetsContract P.w p (bRead + spanReadIdxPiWalkPtr) (spanPiWalkPtrContract P b e d m.2) :=
    fun _ _ => spanPiWalkPtr_meetsContract hread
  set stepC : ℕ → ℕ := fun i => if hi : i < eL.length then edgeStepCost P S6 s d (eL[i]'hi) else 0
  have hloop := Triple.forRange_le (w := P.w) (p := p) (r := 21) (lo := .const 0) (hi := .reg 17)
    (body := embRefreshEdgeBody bCopy (bRead + spanReadIdxPiWalkPtr))
    (P := fun st =>
      slotListInv P eCap embH spanH eListPtr h mem₀ v y.ptr S6 s d b eL 0
        { st with regs := Function.update st.regs 21 0 })
    (Inv := slotListInv P eCap embH spanH eListPtr h mem₀ v y.ptr S6 s d b eL)
    stepC 0 eL.length (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const (by omega), hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.2.1)
    (fun i _ hi => by
      have htakeLe : ((eL.take (i + 1)).map fun e => Read.walkWords (slotWalk P S6 s e)).sum ≤
          slotListWalkWords P S6 s eL := by
        unfold slotListWalkWords
        have hsplit : eL = eL.take (i + 1) ++ eL.drop (i + 1) := (List.take_append_drop _ _).symm
        conv_rhs => rw [hsplit]
        rw [List.map_append, List.sum_append]; exact Nat.le_add_right _ _
      have hstep := slotList_edge_step (copyWords_meetsContract hcopy) hs hSj hxm hS6 hpiAt
        heL_at heL_le heL_sub hdisjL' htab hold' hSpanF hdisjB' hw16 hi (by omega)
      simpa only [stepC, dite_eq_left_of_eq_true (eq_true hi)] using hstep)
  have hrc : rangeCost stepC 0 eL.length = (eL.map (edgeStepCost P S6 s d)).sum :=
    rangeCost_getElem_eq_map_sum eL (edgeStepCost P S6 s d)
  have hsum_le : (eL.map (edgeStepCost P S6 s d)).sum + eL.length * 9 ≤
      142 * slotListCopyWork P S6 s d eL := by
    have haux : ∀ (l : List ℕ), (l.map (edgeStepCost P S6 s d)).sum + l.length * 9 ≤
        142 * slotListCopyWork P S6 s d l := by
      intro l
      unfold slotListCopyWork
      induction l with
      | nil => simp
      | cons a as ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
        have h1 : edgeStepCost P S6 s d a + 9 ≤
            142 * (Read.walkWords (slotWalk P S6 s a) + (if d.Us = [] then 0 else P.L) + 2) := by
          unfold edgeStepCost; split_ifs <;> omega
        omega
    exact haux eL
  have hdgEq : 4 + (7 * P.vCap + 9 * P.eCap) = dynGraphSize P.vCap P.eCap := by
    simp only [dynGraphSize]; omega
  have hhepEq : dsHPtr b P.vCap P.eCap + 4 + 7 * P.vCap = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap := rfl
  have hdomEq : dsGPtr b + 3 * dynGraphSize P.vCap P.eCap + (3 * P.eCap + 2 * (P.L + 1)) =
      dsDomGenBase b P.L P.vCap P.eCap := by
    have h1 := dsMinHBase_eq b P.vCap P.eCap
    have h2 := dsDomGenBase_eq b P.L P.vCap P.eCap
    have h5 : dsGPtr b = b + dsHdrSize := rfl
    omega
  have hpiEq : dsDomGenBase b P.L P.vCap P.eCap + (P.L + 1) + (P.L + 1) * P.eCap =
      dsPiPtrBase b P.L P.vCap P.eCap := rfl
  suffices hmain : ∃ o st' c,
      Runs P.w p ω (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr))
        (startState [embH, spanH, s, eListPtr, eL.length, h] mem₀ pos) o st' c ∧
      (∃ y', (embRep eCap).rep embH (v.apply (slotChange P S6 s eL)) y' st'.mem ∧
        o.value = h + slotListWalkWords P S6 s eL ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ embFoot eCap embH y a → st'.mem a = mem₀ a) ∧
        (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h ≤ a ∧ a < o.value))) ∧
      0 + c ≤ 142 * slotListCopyWork P S6 s d eL + 120 by
    obtain ⟨o, st', c, hr, ⟨y', h1, h2, h3, h4, h5⟩, hc⟩ := hmain
    exact ⟨o, st', c, y', hr, h1, h2, h3, h4, h5, by omega⟩
  dsimp only [asmFirstCopySlotListStmt, startState]
  refine runs_seq_assign_flat (v := eListPtr) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_assign_flat (v := eL.length) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_assign_flat (v := h) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_assign_flat (v := embH + 2)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hrep0.1) ?_
  refine runs_seq_assign_flat (v := b)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := spanH) (by simp))
      (Expr.eval_reg_of_eq (v := s) (by simp)) (by omega)) hmb) ?_
  refine runs_seq_assign_flat (v := (d.state P).t)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := b) (by simp))
      (Expr.eval_const (by have := hB.1; omega)) (by have := hB.1; omega)) hmT) ?_
  refine runs_seq_assign_flat (v := P.L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := b) (by simp))
      (Expr.eval_const (by have := hB.2.1; omega)) (by have := hB.2.1; omega)) hmL) ?_
  refine runs_seq_assign_flat (v := P.vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := b) (by simp))
      (Expr.eval_const (by have := hB.2.2.1; omega)) (by have := hB.2.2.1; omega)) hmV) ?_
  refine runs_seq_assign_flat (v := P.eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := b) (by simp))
      (Expr.eval_const (by have := hB.2.2.2.1; omega)) (by have := hB.2.2.2.1; omega)) hmE) ?_
  refine runs_seq_assign_flat (v := dynGraphSize P.vCap P.eCap)
    (by rw [← hdgEq]
        exact Expr.eval_add (Expr.eval_const (by omega))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
            (by omega))
          (by rw [hdgEq]; omega)) ?_
  refine runs_seq_assign_flat (v := dsGPtr b)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by simp [dsHdrSize]; omega))
      (by change dsGPtr b < 2 ^ P.w; exact lt_trans hB.2.2.2.2.2.2.2.2.2.2.1 hfixW)) ?_
  refine runs_seq_assign_flat (v := dsHPtr b P.vCap P.eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
      (by change dsHPtr b P.vCap P.eCap < 2 ^ P.w; omega)) ?_
  refine runs_seq_assign_flat (v := dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap)
    (by rw [← hhepEq]
        have h1 : dsHPtr b P.vCap P.eCap + 4 < 2 ^ P.w := by
          have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [dgEPresBase] at this; omega
        have h2 : dsHPtr b P.vCap P.eCap + 4 + 7 * P.vCap < 2 ^ P.w := by
          have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [dgEPresBase] at this; omega
        exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) h1)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega)) h2) ?_
  refine runs_seq_assign_flat (v := P.L + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_assign_flat (v := dsDomGenBase b P.L P.vCap P.eCap)
    (by rw [← hdomEq]
        have h1 : dsGPtr b + 3 * dynGraphSize P.vCap P.eCap < 2 ^ P.w := by
          have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; rw [dsMinHBase_eq] at this
          change b + dsHdrSize + 3 * dynGraphSize P.vCap P.eCap < 2 ^ P.w; omega
        have h2 : dsGPtr b + 3 * dynGraphSize P.vCap P.eCap + (3 * P.eCap + 2 * (P.L + 1)) < 2 ^ P.w := by
          rw [hdomEq]; exact lt_trans hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hfixW
        exact Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega)) h1)
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
            (by omega)) h2) ?_
  refine runs_seq_assign_flat (v := dsPiPtrBase b P.L P.vCap P.eCap)
    (by rw [← hpiEq]
        have h1 : dsDomGenBase b P.L P.vCap P.eCap + (P.L + 1) < 2 ^ P.w := by
          change dsEdgeDomGenBase b P.L P.vCap P.eCap < 2 ^ P.w
          exact lt_trans hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hfixW
        have h2 : dsDomGenBase b P.L P.vCap P.eCap + (P.L + 1) + (P.L + 1) * P.eCap < 2 ^ P.w := by
          rw [hpiEq]; have := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
        exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) h1)
          (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (by omega)) h2) ?_
  refine runs_seq_split_le (T₁ := 142 * slotListCopyWork P S6 s d eL + 10)
    (P₁ := slotListInv P eCap embH spanH eListPtr h mem₀ v y.ptr S6 s d b eL eL.length) ?_ ?_
  · have hloop' : ∀ st,
        slotListInv P eCap embH spanH eListPtr h mem₀ v y.ptr S6 s d b eL 0
          { st with regs := Function.update st.regs 21 0 } →
        ∃ o st' c,
          Runs P.w p ω (forRange 21 (.const 0) (.reg 17)
              (embRefreshEdgeBody bCopy (bRead + spanReadIdxPiWalkPtr))) st o st' c ∧
          (o = Outcome.normal ∧
            slotListInv P eCap embH spanH eListPtr h mem₀ v y.ptr S6 s d b eL eL.length st') ∧
          0 + c ≤ 142 * slotListCopyWork P S6 s d eL + 10 := by
      intro st hpre
      obtain ⟨oL, stL, cL, hrL, hpostL, hcL⟩ := hloop st ω hpre
      cases oL with
      | returned _ => cases hpostL
      | normal =>
        dsimp only at hcL; rw [hrc] at hcL; simp only [Nat.sub_zero, Expr.size] at hcL
        exact ⟨.normal, stL, cL, hrL, ⟨rfl, hpostL⟩, by omega⟩
    apply hloop'
    dsimp only [slotListInv]
    exact ⟨by simp [slotChange], by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simpa [slotChange, EmbView.apply, ← hv] using hrep0, fun _ _ _ => rfl,
      by simpa [slotChange] using hz,
      fun e he => Or.inl ⟨rfl, rfl, by simpa [slotChange, EmbView.apply] using he⟩⟩
  · intro stL hInvEnd
    obtain ⟨hr4E, -, -, -, -, -, -, -, -, hrepE, hfrE, hzE, hlocE⟩ := hInvEnd
    rw [List.take_length] at hr4E hrepE hzE hlocE
    have hfoldSnd : ((slotChange P S6 s eL).foldl embConcStep (y.ptr, h)).2 =
        h + slotListWalkWords P S6 s eL := by
      rw [embConcStep_fold_snd]; unfold slotChange slotListWalkWords; rw [List.map_map]; rfl
    rw [hfoldSnd] at hr4E hzE hlocE
    have hpkg := embConc_of_inv hv hrepE hfrE hlocE
    refine ⟨.returned (h + slotListWalkWords P S6 s eL), stL, (Expr.reg 4).size + 1,
      runs_ret_iff.mpr ⟨_, Expr.eval_reg_of_eq hr4E, rfl, rfl, rfl⟩,
      ⟨_, hpkg.1, rfl, hzE, hpkg.2.1, hpkg.2.2⟩, ?_⟩
    simp only [Expr.size]; omega

end

end MinCostFlow.SparseCore.Program
