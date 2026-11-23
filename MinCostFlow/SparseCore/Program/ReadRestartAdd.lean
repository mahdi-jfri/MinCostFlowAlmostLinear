module

public import MinCostFlow.SparseCore.Program.ReadRestartOps
public import MinCostFlow.SparseCore.Program.ReadTree

import WordRAM.Tactic

/-!
# Inserting one slot's spanner edges at their core ends (`ReadRestartAdd`)

Provides `restartAddSlotEdgesStmt` (`[sPtr, gPtr, h_s, b4, j, h]`): iterates over every edge `e`
of a slot's spanner `H_s`; for each `e ∈ G.E`, queries the roots `ru`, `rv` of `G.tail e`,
`G.head e` through P4's root query `Q : RootQueryAt`, and inserts `e` into `S` at `(ru, rv)`
whenever both roots lie in `S.V`. Proved in `restartAddSlotEdges_runs` using `forRange_phi_runs`
and `foldl_addCoreEdgeStep`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart MinCostFlow.Chain

/-- One edge insertion step on `S`: if `e ∈ G.E` and both core ends of `e` lie in `S.V`, insert
`e` into `S` at its core ends (unless already present). -/
noncomputable def addCoreEdgeStep (G : MGraph) (lsf : LSF) (eCap : ℕ) (S : MGraph) (e : ℕ) :
    MGraph :=
  open Classical in
  if e ∈ G.E ∧ (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V ∧
      e < eCap ∧ e ∉ S.E then
    S.applyUpdate (.insert e ((coreGraph G lsf).tail e) ((coreGraph G lsf).head e))
  else S

/-- `[sPtr, gPtr, h_s, b4, j, h]`: iterate over all edges `e` of the spanner graph `H_s` at `h_s`;
for each `e ∈ G.E`, query the roots `ru`, `rv` of `G.tail e`, `G.head e` through `fRoot`, and if
both lie in `S.V`, insert `(e, ru, rv)` into `S`. Returns the updated heap pointer. -/
def restartAddSlotEdgesStmt (bOps bEdge fRoot : ℕ) : Stmt :=
  .assign 6 (.load (.reg 1)) ;;
  .assign 7 (.load (.reg 2)) ;;
  .assign 8 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .assign 9 (.load (.bin .add (.reg 2) (.const 3))) ;;
  .assign 10 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
    (.bin .mul (.const 7) (.reg 7))) (.reg 8)) ;;
  .assign 11 (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 7) (.reg 6))) ;;
  .assign 12 (.bin .add (.reg 0) (.const 4)) ;;
  .assign 13 (.reg 5) ;;
  forRange 14 (.const 0) (.reg 9)
    (.assign 15 (.load (.bin .add (.reg 10) (.reg 14))) ;;
     .cond (.load (.bin .add (.reg 11) (.reg 15)))
       (.call 16 (bOps + dgIdxGetTail) [.reg 1, .reg 15] ;;
        .call 17 (bOps + dgIdxGetHead) [.reg 1, .reg 15] ;;
        .assign 18 (.reg 13) ;;
        .call 13 fRoot [.reg 3, .reg 4, .reg 16, .reg 18] ;;
        .assign 19 (.load (.reg 18)) ;;
        .assign 18 (.reg 13) ;;
        .call 13 fRoot [.reg 3, .reg 4, .reg 17, .reg 18] ;;
        .assign 20 (.load (.reg 18)) ;;
        .cond (.bin .lt (.reg 19) (.reg 6))
          (.cond (.bin .lt (.reg 20) (.reg 6))
            (.cond (.load (.bin .add (.reg 12) (.reg 19)))
              (.cond (.load (.bin .add (.reg 12) (.reg 20)))
                (.call 21 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 15, .reg 19, .reg 20])
                .nop)
              .nop)
            .nop)
          .nop)
       .nop) ;;
  .ret (.reg 13)

theorem restartAddSlotEdgesStmt_noRand (bOps bEdge fRoot : ℕ) :
    (restartAddSlotEdgesStmt bOps bEdge fRoot).NoRand := by
  simp [restartAddSlotEdgesStmt, forRange, forUp, Stmt.NoRand]

/-- Folding `addCoreEdgeStep` over a list `eL` adds every `e ∈ eL ∩ G.E` whose core ends lie in
`S.V` (at their core ends, when `e < eCap` and any `e ∈ eL ∩ S.E` already has its core ends). -/
theorem foldl_addCoreEdgeStep {G : MGraph} {lsf : LSF} {eCap : ℕ} {S : MGraph} {eL : List ℕ}
    (heCap : ∀ e ∈ eL, e < eCap)
    (hagree : ∀ e ∈ eL, e ∈ S.E →
      S.tail e = (coreGraph G lsf).tail e ∧ S.head e = (coreGraph G lsf).head e) :
    let add := (eL.toFinset ∩ G.E).filter fun e =>
      (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V
    SameGraph (eL.foldl (addCoreEdgeStep G lsf eCap) S)
      { V := S.V
        E := S.E ∪ add
        tail := fun e => if e ∈ add then (coreGraph G lsf).tail e else S.tail e
        head := fun e => if e ∈ add then (coreGraph G lsf).head e else S.head e } := by
  classical
  induction eL generalizing S with
  | nil => refine ⟨rfl, by simp, fun e _ => by simp⟩
  | cons x xs ih =>
    set M₁ := addCoreEdgeStep G lsf eCap S x with hM₁
    have hMV : M₁.V = S.V := by unfold M₁ addCoreEdgeStep; split_ifs <;> rfl
    have hlt_xs : ∀ e ∈ xs, e < eCap := fun e he => heCap e (List.mem_cons_of_mem _ he)
    have hagree₁ : ∀ e ∈ xs, e ∈ M₁.E →
        M₁.tail e = (coreGraph G lsf).tail e ∧ M₁.head e = (coreGraph G lsf).head e := by
      intro e he hmem
      unfold M₁ addCoreEdgeStep at hmem ⊢
      split_ifs at hmem ⊢ with hc
      · simp only [MGraph.applyUpdate] at hmem ⊢
        rcases Finset.mem_insert.mp hmem with rfl | hM
        · simp
        · have hne : e ≠ x := fun h => hc.2.2.2.2 (h ▸ hM)
          simp only [Function.update_of_ne hne]
          exact hagree e (List.mem_cons_of_mem _ he) hM
      · exact hagree e (List.mem_cons_of_mem _ he) hmem
    have hih := ih hlt_xs hagree₁
    rw [List.foldl_cons]
    refine hih.trans ⟨hMV, ?_, ?_⟩
    · ext e
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_inter, List.mem_toFinset,
        List.mem_cons, hMV]
      unfold M₁ addCoreEdgeStep
      split_ifs with hc
      · simp only [MGraph.applyUpdate, Finset.mem_insert]
        constructor
        · rintro ((rfl | hM) | ⟨⟨hxs, hG⟩, hEnds⟩)
          · exact Or.inr ⟨⟨Or.inl rfl, hc.1⟩, hc.2.1, hc.2.2.1⟩
          · exact Or.inl hM
          · exact Or.inr ⟨⟨Or.inr hxs, hG⟩, hEnds⟩
        · rintro (hM | ⟨⟨rfl | hxs, hG⟩, hEnds⟩)
          · exact Or.inl (Or.inr hM)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨⟨hxs, hG⟩, hEnds⟩
      · have hxc : ¬ (x ∈ G.E ∧ (coreGraph G lsf).tail x ∈ S.V ∧ (coreGraph G lsf).head x ∈ S.V ∧
            x ∉ S.E) := fun h => hc ⟨h.1, h.2.1, h.2.2.1, heCap x List.mem_cons_self, h.2.2.2⟩
        constructor
        · rintro (hM | ⟨⟨hxs, hG⟩, hEnds⟩)
          · exact Or.inl hM
          · exact Or.inr ⟨⟨Or.inr hxs, hG⟩, hEnds⟩
        · rintro (hM | ⟨⟨rfl | hxs, hG⟩, hEnds⟩)
          · exact Or.inl hM
          · by_cases hxM : e ∈ S.E
            · exact Or.inl hxM
            · exact absurd ⟨hG, hEnds.1, hEnds.2, hxM⟩ hxc
          · exact Or.inr ⟨⟨hxs, hG⟩, hEnds⟩
    · intro e he
      simp only [hMV] at he ⊢
      by_cases hxs : e ∈ (xs.toFinset ∩ G.E).filter (fun e =>
          (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V)
      · have hcons : e ∈ ((x :: xs).toFinset ∩ G.E).filter (fun e =>
            (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V) := by
          simp only [Finset.mem_filter, Finset.mem_inter, List.mem_toFinset, List.mem_cons] at hxs ⊢
          exact ⟨⟨Or.inr hxs.1.1, hxs.1.2⟩, hxs.2⟩
        simp only [hxs, hcons, ↓reduceIte, and_self]
      · simp only [hxs, ↓reduceIte]
        have heM₁ : e ∈ M₁.E := (Finset.mem_union.mp he).resolve_right hxs
        by_cases hcons : e ∈ ((x :: xs).toFinset ∩ G.E).filter (fun e =>
            (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V)
        · simp only [hcons, ↓reduceIte]
          have hex : e = x := by
            simp only [Finset.mem_filter, Finset.mem_inter, List.mem_toFinset, List.mem_cons] at hcons hxs
            rcases hcons.1.1 with rfl | h1
            · rfl
            · exact absurd ⟨⟨h1, hcons.1.2⟩, hcons.2⟩ hxs
          subst hex
          unfold M₁ addCoreEdgeStep at heM₁ ⊢
          split_ifs at heM₁ ⊢ with hc
          · simp [MGraph.applyUpdate]
          · exact hagree e List.mem_cons_self heM₁
        · simp only [hcons, ↓reduceIte]
          unfold M₁ addCoreEdgeStep at heM₁ ⊢
          split_ifs at heM₁ ⊢ with hc
          · simp only [MGraph.applyUpdate] at heM₁ ⊢
            have hne : e ≠ x := by
              intro hEq; subst hEq
              apply hcons
              simp [hc.1, hc.2.1, hc.2.2.1]
            simp [Function.update_of_ne hne]
          · exact ⟨rfl, rfl⟩

/-- One iteration of the edge loop in `restartAddSlotEdgesStmt`: processes edge `e` of `H_s`. -/
private theorem addSlotEdge_step_runs {w vCap eCap spVCap spECap fRoot bOps bEdge : ℕ}
    {p : Program} {Q : RootQueryAt w p fRoot}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    {sPtr gPtr h_s eList_H b4 j h0 : ℕ} {G S H_s : MGraph} {lsf : LSF}
    {s4 : Q.σ} {x4₀ : Q.R.τ} {mem₀ : ℕ → ℕ} {eL : List ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hSPe : spECap ≤ eCap)
    (hsPtrB : sPtr + dynGraphSize vCap eCap ≤ h0) (hgPtrB : gPtr + dynGraphSize vCap eCap ≤ h0)
    (hh_sB : h_s + dynGraphSize spVCap spECap ≤ h0)
    (hb4W : b4 < 2 ^ w) (hjW : j < 2 ^ w)
    (heL_len : eL.length = H_s.m) (heL_mem : ∀ e, e ∈ eL ↔ e ∈ H_s.E)
    (heL_at : ListAt mem₀ eList_H eL) (heList_eq : eList_H = dgEListBase h_s spVCap spECap)
    (hG₀ : DynGraphAt mem₀ gPtr vCap eCap G) (hHs₀ : DynGraphAt mem₀ h_s spVCap spECap H_s)
    (hQok : ∀ u ∈ G.V, Q.ok s4 j u ∧ Q.root s4 j u = lsf.F.root u)
    (hfoot4₀ : ∀ a, Q.R.foot b4 x4₀ a → a < h0)
    (hdisj_SG : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
      a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a)
    (hdisj_SH : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
      a < h_s ∨ h_s + dynGraphSize spVCap spECap ≤ a)
    (hdisj_S4 : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4₀ a)
    (hdisj_G4 : ∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4₀ a)
    (hdisj_H4 : ∀ a, h_s ≤ a → a < h_s + dynGraphSize spVCap spECap → ¬ Q.R.foot b4 x4₀ a)
    {k : ℕ} (hk : k < eL.length) {st : State} {x4 : Q.R.τ} {ω : ℕ → Bool}
    (hRegs : st.regs 0 = sPtr ∧ st.regs 1 = gPtr ∧ st.regs 2 = h_s ∧ st.regs 3 = b4 ∧
      st.regs 4 = j ∧ st.regs 6 = vCap ∧ st.regs 9 = eL.length ∧ st.regs 10 = eList_H ∧
      st.regs 11 = dgEPresBase gPtr vCap ∧ st.regs 12 = dgVPresBase sPtr ∧ st.regs 14 = k)
    (hh_lo : h0 ≤ st.regs 13) (hh_hi : st.regs 13 + 2 < 2 ^ w)
    (hz : ZeroFrom st.mem (st.regs 13))
    (hS : DynGraphAt st.mem sPtr vCap eCap ((eL.take k).foldl (addCoreEdgeStep G lsf eCap) S))
    (hrep4 : Q.R.rep b4 s4 x4 st.mem)
    (hfoot4 : ∀ a, Q.R.foot b4 x4 a → Q.R.foot b4 x4₀ a ∨ (h0 ≤ a ∧ a < st.regs 13))
    (hframe : ∀ a < h0, (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) →
      ¬ Q.R.foot b4 x4₀ a → st.mem a = mem₀ a) :
    let body : Stmt :=
      .assign 15 (.load (.bin .add (.reg 10) (.reg 14))) ;;
      .cond (.load (.bin .add (.reg 11) (.reg 15)))
        (.call 16 (bOps + dgIdxGetTail) [.reg 1, .reg 15] ;;
         .call 17 (bOps + dgIdxGetHead) [.reg 1, .reg 15] ;;
         .assign 18 (.reg 13) ;;
         .call 13 fRoot [.reg 3, .reg 4, .reg 16, .reg 18] ;;
         .assign 19 (.load (.reg 18)) ;;
         .assign 18 (.reg 13) ;;
         .call 13 fRoot [.reg 3, .reg 4, .reg 17, .reg 18] ;;
         .assign 20 (.load (.reg 18)) ;;
         .cond (.bin .lt (.reg 19) (.reg 6))
           (.cond (.bin .lt (.reg 20) (.reg 6))
             (.cond (.load (.bin .add (.reg 12) (.reg 19)))
               (.cond (.load (.bin .add (.reg 12) (.reg 20)))
                 (.call 21 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 15, .reg 19, .reg 20])
                 .nop)
               .nop)
             .nop)
           .nop)
        .nop
    ∃ st₁ c₁ x4', Runs w p ω body st .normal st₁ c₁ ∧
      st₁.regs 0 = sPtr ∧ st₁.regs 1 = gPtr ∧ st₁.regs 2 = h_s ∧ st₁.regs 3 = b4 ∧
      st₁.regs 4 = j ∧ st₁.regs 6 = vCap ∧ st₁.regs 9 = eL.length ∧ st₁.regs 10 = eList_H ∧
      st₁.regs 11 = dgEPresBase gPtr vCap ∧ st₁.regs 12 = dgVPresBase sPtr ∧ st₁.regs 14 = k ∧
      st.regs 13 ≤ st₁.regs 13 ∧ st₁.regs 13 ≤ st.regs 13 + 2 ∧ ZeroFrom st₁.mem (st₁.regs 13) ∧
      DynGraphAt st₁.mem sPtr vCap eCap ((eL.take (k + 1)).foldl (addCoreEdgeStep G lsf eCap) S) ∧
      Q.R.rep b4 s4 x4' st₁.mem ∧
      (∀ a, Q.R.foot b4 x4' a → Q.R.foot b4 x4₀ a ∨ (h0 ≤ a ∧ a < st₁.regs 13)) ∧
      (∀ a < h0, (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) →
        ¬ Q.R.foot b4 x4₀ a → st₁.mem a = mem₀ a) ∧
      c₁ + Q.R.phi b4 x4' st₁.mem ≤ 660 + 2 * Q.cost + Q.R.phi b4 x4 st.mem := by
  intro body
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr6, hr9, hr10, hr11, hr12, hr14⟩ := hRegs
  set e := eL[k] with he_def
  set Sk := (eL.take k).foldl (addCoreEdgeStep G lsf eCap) S with hSk_def
  have heHs : e ∈ H_s.E := (heL_mem e).mp (List.getElem_mem hk)
  have he_lt_sp : e < spECap := hHs₀.2.2.1 e heHs
  have he_lt : e < eCap := lt_of_lt_of_le he_lt_sp hSPe
  have hS_lt_w : sPtr + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hG_lt_w : gPtr + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hH_lt_w : h_s + dynGraphSize spVCap spECap < 2 ^ w := by omega
  have hm_le_sp : H_s.m ≤ spECap := by
    have hsub : H_s.E ⊆ Finset.range spECap := fun x hx => Finset.mem_range.mpr (hHs₀.2.2.1 x hx)
    exact (Finset.card_le_card hsub).trans (by simp)
  have hG_cur : DynGraphAt st.mem gPtr vCap eCap G :=
    hG₀.of_agree fun a ha1 ha2 => hframe a (lt_of_lt_of_le ha2 hgPtrB)
      (by by_contra hnot; have := hdisj_SG a (by omega) (by omega); omega) (hdisj_G4 a ha1 ha2)
  have he_val : st.mem (eList_H + k) = e := by
    have ha1 : h_s ≤ eList_H + k := by rw [heList_eq]; dsimp [dgEListBase]; omega
    have ha2 : eList_H + k < h_s + dynGraphSize spVCap spECap := by
      rw [heList_eq]; dsimp [dgEListBase, dynGraphSize]; omega
    rw [hframe (eList_H + k) (lt_of_lt_of_le ha2 hh_sB)
      (by by_contra hnot; have := hdisj_SH (eList_H + k) (by omega) (by omega); omega)
      (hdisj_H4 (eList_H + k) ha1 ha2)]
    exact heL_at k hk
  have heList_k_lt : eList_H + k < 2 ^ w := by
    rw [heList_eq]; dsimp [dgEListBase, dynGraphSize] at hH_lt_w ⊢; omega
  have hep_lt : dgEPresBase gPtr vCap + e < 2 ^ w := by
    dsimp [dgEPresBase, dynGraphSize] at hG_lt_w ⊢; omega
  have hep_eq : st.mem (dgEPresBase gPtr vCap + e) = if e ∈ G.E then 1 else 0 :=
    hG_cur.2.2.2.2.2.2.2.2.2.2.2.1 e he_lt
  have htake_eq : (eL.take (k + 1)).foldl (addCoreEdgeStep G lsf eCap) S =
      addCoreEdgeStep G lsf eCap Sk e := by
    rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hr_e : Runs w p ω (.assign 15 (.load (.bin .add (.reg 10) (.reg 14)))) st .normal
      { st with regs := Function.update st.regs 15 e } 5 :=
    runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hr10) (Expr.eval_reg_of_eq hr14) heList_k_lt) he_val,
      rfl, rfl, by simp [Expr.size]⟩
  set stA : State := { st with regs := Function.update st.regs 15 e }
  by_cases heG : e ∈ G.E
  · have hep_1 : stA.mem (dgEPresBase gPtr vCap + e) = 1 := by simpa [stA, heG] using hep_eq
    have hcond1 : (Expr.load (.bin .add (.reg 11) (.reg 15))).eval w stA = some 1 :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, hr11]))
        (Expr.eval_reg_of_eq (by simp [stA])) hep_lt) hep_1
    have htail_call := runs_call_of_meetsContract (r := 16) (dgGetTail_meetsContract hpOps)
      (show evalArgs w stA [.reg 1, .reg 15] = some [gPtr, e] by simp [evalArgs, Expr.eval, stA, hr1])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl | rfl) <;>
          (dsimp [dynGraphSize] at hG_lt_w; omega))
      ⟨gPtr, e, rfl, hw16, hG_lt_w, heG, hG_cur⟩ ω
    obtain ⟨stB, cB, u, hrB, ⟨_, _, hEqB, hmemB, hu_eq⟩, hresB, hregsB, hcB⟩ := htail_call
    simp only [List.cons.injEq, and_true] at hEqB
    obtain ⟨rfl, rfl⟩ := hEqB
    have hu_V : u ∈ G.V := hu_eq ▸ (hG₀.1 e heG).1
    have hu_lt_w : u < 2 ^ w := by have := hG₀.2.1 u hu_V; dsimp [dynGraphSize] at hG_lt_w; omega
    have hhead_call := runs_call_of_meetsContract (r := 17) (dgGetHead_meetsContract hpOps)
      (show evalArgs w stB [.reg 1, .reg 15] = some [gPtr, e] by
        simp [evalArgs, Expr.eval, hregsB 1 (by decide), hregsB 15 (by decide), stA, hr1])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl | rfl) <;>
          (dsimp [dynGraphSize] at hG_lt_w; omega))
      ⟨gPtr, e, rfl, hw16, hG_lt_w, heG, hmemB ▸ hG_cur⟩ ω
    obtain ⟨stC, cC, v_e, hrC, ⟨_, _, hEqC, hmemC, hv_eq⟩, hresC, hregsC, hcC⟩ := hhead_call
    simp only [List.cons.injEq, and_true] at hEqC
    obtain ⟨rfl, rfl⟩ := hEqC
    have hv_V : v_e ∈ G.V := hv_eq ▸ (hG₀.1 e heG).2
    have hv_lt_w : v_e < 2 ^ w := by have := hG₀.2.1 v_e hv_V; dsimp [dynGraphSize] at hG_lt_w; omega
    have hmemC_eq : stC.mem = st.mem := hmemC.trans hmemB
    have hC13 : stC.regs 13 = st.regs 13 := by
      rw [hregsC 13 (by decide), hregsB 13 (by decide)]; simp [stA]
    have hass18a : Runs w p ω (.assign 18 (.reg 13)) stC .normal
        { stC with regs := Function.update stC.regs 18 (st.regs 13) } 2 :=
      runs_assign_iff.mpr ⟨st.regs 13, Expr.eval_reg_of_eq hC13, rfl, rfl, by simp [Expr.size]⟩
    set stD := { stC with regs := Function.update stC.regs 18 (st.regs 13) }
    have hQ1_foot : ∀ a, Q.R.foot b4 x4 a → a < st.regs 13 := fun a ha => by
      rcases hfoot4 a ha with h1 | h2
      · exact lt_of_lt_of_le (hfoot4₀ a h1) hh_lo
      · exact h2.2
    obtain ⟨bodyQ1, hbodyQ1, oQ1, stQ1, cQ1, x4₁, hrQ1, hru_mem, hrep4₁, hQ1_lo, hQ1_hi, hzQ1,
        hQ1_fr, hQ1_foot', hQ1_cost⟩ :=
      Q.runs b4 j u (st.regs 13) s4 x4 st.mem stD.pos ω hb4W hjW hu_lt_w (by omega)
        (hQok u hu_V).1 hrep4 hQ1_foot hz (by omega)
    have hcallQ1 : Runs w p ω (.call 13 fRoot [.reg 3, .reg 4, .reg 16, .reg 18]) stD .normal
        { mem := stQ1.mem, regs := Function.update stD.regs 13 oQ1.value, pos := stQ1.pos }
        (cQ1 + 5) := by
      refine runs_call_iff.mpr ⟨[b4, j, u, st.regs 13], bodyQ1, oQ1, stQ1, cQ1, ?_, hbodyQ1, ?_,
        rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      · simp [evalArgs, Expr.eval, stD, hregsC 3 (by decide), hregsC 4 (by decide),
          hregsC 16 (by decide), hregsB 3 (by decide), hregsB 4 (by decide), hresB, stA, hr3, hr4]
      · simpa [stD, hmemC_eq] using hrQ1
    set stE : State := { mem := stQ1.mem, regs := Function.update stD.regs 13 oQ1.value, pos := stQ1.pos }
    set ru := lsf.F.root u
    have hass19 : Runs w p ω (.assign 19 (.load (.reg 18))) stE .normal
        { stE with regs := Function.update stE.regs 19 ru } 3 :=
      runs_assign_iff.mpr ⟨ru, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [stE, stD]))
        (hru_mem.trans (hQok u hu_V).2), rfl, rfl, by simp [Expr.size]⟩
    set stF := { stE with regs := Function.update stE.regs 19 ru }
    have hass18b : Runs w p ω (.assign 18 (.reg 13)) stF .normal
        { stF with regs := Function.update stF.regs 18 oQ1.value } 2 :=
      runs_assign_iff.mpr ⟨oQ1.value, Expr.eval_reg_of_eq (by simp [stF, stE]), rfl, rfl,
        by simp [Expr.size]⟩
    set stG := { stF with regs := Function.update stF.regs 18 oQ1.value }
    have hQ2_foot : ∀ a, Q.R.foot b4 x4₁ a → a < oQ1.value := fun a ha => by
      rcases hQ1_foot' a ha with h1 | h2
      · exact lt_of_lt_of_le (hQ1_foot a h1) hQ1_lo
      · exact h2.2
    obtain ⟨bodyQ2, hbodyQ2, oQ2, stQ2, cQ2, x4₂, hrQ2, hrv_mem, hrep4₂, hQ2_lo, hQ2_hi, hzQ2,
        hQ2_fr, hQ2_foot', hQ2_cost⟩ :=
      Q.runs b4 j v_e oQ1.value s4 x4₁ stQ1.mem stG.pos ω hb4W hjW hv_lt_w (by omega)
        (hQok v_e hv_V).1 hrep4₁ hQ2_foot hzQ1 (by omega)
    have hcallQ2 : Runs w p ω (.call 13 fRoot [.reg 3, .reg 4, .reg 17, .reg 18]) stG .normal
        { mem := stQ2.mem, regs := Function.update stG.regs 13 oQ2.value, pos := stQ2.pos }
        (cQ2 + 5) := by
      refine runs_call_iff.mpr ⟨[b4, j, v_e, oQ1.value], bodyQ2, oQ2, stQ2, cQ2, ?_, hbodyQ2, ?_,
        rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      · simp [evalArgs, Expr.eval, stG, stF, stE, stD, hregsC 3 (by decide), hregsC 4 (by decide),
          hregsB 3 (by decide), hregsB 4 (by decide), hresC, stA, hr3, hr4]
      · simpa [stG, stF, stE] using hrQ2
    set stH : State := { mem := stQ2.mem, regs := Function.update stG.regs 13 oQ2.value, pos := stQ2.pos }
    set rv := lsf.F.root v_e
    have hass20 : Runs w p ω (.assign 20 (.load (.reg 18))) stH .normal
        { stH with regs := Function.update stH.regs 20 rv } 3 :=
      runs_assign_iff.mpr ⟨rv, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [stH, stG]))
        (hrv_mem.trans (hQok v_e hv_V).2), rfl, rfl, by simp [Expr.size]⟩
    set stI := { stH with regs := Function.update stH.regs 20 rv }
    have hQ12_fr : ∀ a < h0, ¬ Q.R.foot b4 x4₀ a → stQ2.mem a = st.mem a := fun a ha hna => by
      have ha1 : a < st.regs 13 := lt_of_lt_of_le ha hh_lo
      have hna4 : ¬ Q.R.foot b4 x4 a := fun hc => (hfoot4 a hc).elim hna (by omega)
      have hna4₁ : ¬ Q.R.foot b4 x4₁ a := fun hc => (hQ1_foot' a hc).elim hna4 (by omega)
      exact (hQ2_fr a (lt_of_lt_of_le ha1 hQ1_lo) hna4₁).trans (hQ1_fr a ha1 hna4)
    have hS_Q2 : DynGraphAt stQ2.mem sPtr vCap eCap Sk :=
      hS.of_agree fun a ha1 ha2 => hQ12_fr a (lt_of_lt_of_le ha2 hsPtrB) (hdisj_S4 a ha1 ha2)
    have hfoot4₂ : ∀ a, Q.R.foot b4 x4₂ a → Q.R.foot b4 x4₀ a ∨ (h0 ≤ a ∧ a < oQ2.value) := fun a ha => by
      rcases hQ2_foot' a ha with h1 | h2
      · rcases hQ1_foot' a h1 with h3 | h4
        · rcases hfoot4 a h3 with h5 | h6
          · exact Or.inl h5
          · exact Or.inr ⟨h6.1, lt_of_lt_of_le h6.2 (le_trans hQ1_lo hQ2_lo)⟩
        · exact Or.inr ⟨le_trans hh_lo h4.1, lt_of_lt_of_le h4.2 hQ2_lo⟩
      · exact Or.inr ⟨le_trans hh_lo (le_trans hQ1_lo h2.1), h2.2⟩
    have hframe_Q2 : ∀ a < h0, (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) →
        ¬ Q.R.foot b4 x4₀ a → stQ2.mem a = mem₀ a := fun a ha hs hna =>
      (hQ12_fr a ha hna).trans (hframe a ha hs hna)
    have hI0 : stI.regs 0 = sPtr := by simp [stI, stH, stG, stF, stE, stD, hregsC 0 (by decide), hregsB 0 (by decide), stA, hr0]
    have hI1 : stI.regs 1 = gPtr := by simp [stI, stH, stG, stF, stE, stD, hregsC 1 (by decide), hregsB 1 (by decide), stA, hr1]
    have hI2 : stI.regs 2 = h_s := by simp [stI, stH, stG, stF, stE, stD, hregsC 2 (by decide), hregsB 2 (by decide), stA, hr2]
    have hI3 : stI.regs 3 = b4 := by simp [stI, stH, stG, stF, stE, stD, hregsC 3 (by decide), hregsB 3 (by decide), stA, hr3]
    have hI4 : stI.regs 4 = j := by simp [stI, stH, stG, stF, stE, stD, hregsC 4 (by decide), hregsB 4 (by decide), stA, hr4]
    have hI6 : stI.regs 6 = vCap := by simp [stI, stH, stG, stF, stE, stD, hregsC 6 (by decide), hregsB 6 (by decide), stA, hr6]
    have hI9 : stI.regs 9 = eL.length := by simp [stI, stH, stG, stF, stE, stD, hregsC 9 (by decide), hregsB 9 (by decide), stA, hr9]
    have hI10 : stI.regs 10 = eList_H := by simp [stI, stH, stG, stF, stE, stD, hregsC 10 (by decide), hregsB 10 (by decide), stA, hr10]
    have hI11 : stI.regs 11 = dgEPresBase gPtr vCap := by simp [stI, stH, stG, stF, stE, stD, hregsC 11 (by decide), hregsB 11 (by decide), stA, hr11]
    have hI12 : stI.regs 12 = dgVPresBase sPtr := by simp [stI, stH, stG, stF, stE, stD, hregsC 12 (by decide), hregsB 12 (by decide), stA, hr12]
    have hI13 : stI.regs 13 = oQ2.value := by simp [stI, stH]
    have hI14 : stI.regs 14 = k := by simp [stI, stH, stG, stF, stE, stD, hregsC 14 (by decide), hregsB 14 (by decide), stA, hr14]
    have hI15 : stI.regs 15 = e := by simp [stI, stH, stG, stF, stE, stD, hregsC 15 (by decide), hregsB 15 (by decide), stA]
    have hI19 : stI.regs 19 = ru := by simp [stI, stH, stG, stF]
    have hI20 : stI.regs 20 = rv := by simp [stI]
    let innerCond : Stmt :=
      .cond (.bin .lt (.reg 19) (.reg 6))
        (.cond (.bin .lt (.reg 20) (.reg 6))
          (.cond (.load (.bin .add (.reg 12) (.reg 19)))
            (.cond (.load (.bin .add (.reg 12) (.reg 20)))
              (.call 21 (bEdge + dgIdxInsertEdge) [.reg 0, .reg 15, .reg 19, .reg 20])
              .nop)
            .nop)
          .nop)
        .nop
    have hcore_t : (coreGraph G lsf).tail e = ru := by simp [coreGraph, ru, hu_eq]
    have hcore_h : (coreGraph G lsf).head e = rv := by simp [coreGraph, rv, hv_eq]
    have hInner : ∃ stJ cJ, Runs w p ω innerCond stI .normal stJ cJ ∧
        (∀ r, r ≠ 21 → stJ.regs r = stI.regs r) ∧
        DynGraphAt stJ.mem sPtr vCap eCap (addCoreEdgeStep G lsf eCap Sk e) ∧
        (∀ a, a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a → stJ.mem a = stQ2.mem a) ∧
        cJ ≤ 485 := by
      by_cases hru_cap : ru < vCap
      · have hlt1 : (Expr.bin .lt (.reg 19) (.reg 6)).eval w stI = some 1 :=
          Expr.eval_lt_true (Expr.eval_reg_of_eq hI19) (Expr.eval_reg_of_eq hI6) hru_cap (by omega)
        by_cases hrv_cap : rv < vCap
        · have hlt2 : (Expr.bin .lt (.reg 20) (.reg 6)).eval w stI = some 1 :=
            Expr.eval_lt_true (Expr.eval_reg_of_eq hI20) (Expr.eval_reg_of_eq hI6) hrv_cap (by omega)
          have hvp_u_lt : dgVPresBase sPtr + ru < 2 ^ w := by dsimp [dgVPresBase, dynGraphSize] at *; omega
          have hvp_v_lt : dgVPresBase sPtr + rv < 2 ^ w := by dsimp [dgVPresBase, dynGraphSize] at *; omega
          have hvp_u : stI.mem (dgVPresBase sPtr + ru) = if ru ∈ Sk.V then 1 else 0 :=
            hS_Q2.2.2.2.2.2.2.2.1 ru hru_cap
          have hvp_v : stI.mem (dgVPresBase sPtr + rv) = if rv ∈ Sk.V then 1 else 0 :=
            hS_Q2.2.2.2.2.2.2.2.1 rv hrv_cap
          by_cases hruV : ru ∈ Sk.V
          · have hpres1 : (Expr.load (.bin .add (.reg 12) (.reg 19))).eval w stI = some 1 :=
              Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hI12)
                (Expr.eval_reg_of_eq hI19) hvp_u_lt) (by simpa [hruV] using hvp_u)
            by_cases hrvV : rv ∈ Sk.V
            · have hpres2 : (Expr.load (.bin .add (.reg 12) (.reg 20))).eval w stI = some 1 :=
                Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hI12)
                  (Expr.eval_reg_of_eq hI20) hvp_v_lt) (by simpa [hrvV] using hvp_v)
              have hins := runs_call_of_meetsContract (r := 21) (dgInsertEdge_meetsContract hpEdge hpOps)
                (show evalArgs w stI [.reg 0, .reg 15, .reg 19, .reg 20] = some [sPtr, e, ru, rv] by
                  simp [evalArgs, Expr.eval, hI0, hI15, hI19, hI20])
                (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl | rfl | rfl | rfl) <;>
                    (dsimp [dynGraphSize] at hS_lt_w; omega))
                ⟨sPtr, e, ru, rv, rfl, hw16, hS_lt_w, hruV, hrvV, hS_Q2⟩ ω
              obtain ⟨stJ, cJ, _, hrJ, ⟨_, _, _, _, hEqJ, _, hSJ, hfrJ⟩, _, hregsJ, hcJ⟩ := hins
              simp only [List.cons.injEq, and_true] at hEqJ
              obtain ⟨rfl, rfl, rfl, rfl⟩ := hEqJ
              have hstep_eq : (if e < eCap ∧ e ∉ Sk.E then Sk.applyUpdate (.insert e ru rv) else Sk) =
                  addCoreEdgeStep G lsf eCap Sk e := by
                unfold addCoreEdgeStep
                simp only [heG, hcore_t, hcore_h, hruV, hrvV, he_lt, true_and]
              have hrunI : Runs w p ω innerCond stI .normal stJ (cJ + 18) :=
                runs_cond_iff.mpr ⟨1, cJ + 14, hlt1,
                  runs_cond_iff.mpr ⟨1, cJ + 10, hlt2,
                    runs_cond_iff.mpr ⟨1, cJ + 5, hpres1,
                      runs_cond_iff.mpr ⟨1, cJ, hpres2, hrJ, by simp [Expr.size]; omega⟩,
                      by simp [Expr.size]; omega⟩,
                    by simp [Expr.size]; omega⟩,
                  by simp [Expr.size]; omega⟩
              refine ⟨stJ, cJ + 18, hrunI, hregsJ, hstep_eq ▸ hSJ, hfrJ, ?_⟩
              dsimp only [dgInsertEdgeContract, argsSize, Expr.size] at hcJ; omega
            · have hpres2 : (Expr.load (.bin .add (.reg 12) (.reg 20))).eval w stI = some 0 :=
                Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hI12)
                  (Expr.eval_reg_of_eq hI20) hvp_v_lt) (by simpa [hrvV] using hvp_v)
              have hstep_eq : addCoreEdgeStep G lsf eCap Sk e = Sk := by unfold addCoreEdgeStep; simp [hcore_h, hrvV]
              exact ⟨stI, 19, runs_cond_iff.mpr ⟨1, 15, hlt1,
                runs_cond_iff.mpr ⟨1, 11, hlt2,
                  runs_cond_iff.mpr ⟨1, 6, hpres1,
                    runs_cond_iff.mpr ⟨0, 1, hpres2, by simp [runs_nop_iff], by simp [Expr.size]⟩,
                    by simp [Expr.size]⟩,
                  by simp [Expr.size]⟩,
                by simp [Expr.size]⟩, fun _ _ => rfl, hstep_eq.symm ▸ hS_Q2, fun _ _ => rfl, by omega⟩
          · have hpres1 : (Expr.load (.bin .add (.reg 12) (.reg 19))).eval w stI = some 0 :=
              Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hI12)
                (Expr.eval_reg_of_eq hI19) hvp_u_lt) (by simpa [hruV] using hvp_u)
            have hstep_eq : addCoreEdgeStep G lsf eCap Sk e = Sk := by unfold addCoreEdgeStep; simp [hcore_t, hruV]
            exact ⟨stI, 14, runs_cond_iff.mpr ⟨1, 10, hlt1,
              runs_cond_iff.mpr ⟨1, 6, hlt2,
                runs_cond_iff.mpr ⟨0, 1, hpres1, by simp [runs_nop_iff], by simp [Expr.size]⟩,
                by simp [Expr.size]⟩,
              by simp [Expr.size]⟩, fun _ _ => rfl, hstep_eq.symm ▸ hS_Q2, fun _ _ => rfl, by omega⟩
        · have hrvV : rv ∉ Sk.V := fun hc => hrv_cap (hS_Q2.2.1 rv hc)
          have hlt2 : (Expr.bin .lt (.reg 20) (.reg 6)).eval w stI = some 0 :=
            Expr.eval_lt_false (Expr.eval_reg_of_eq hI20) (Expr.eval_reg_of_eq hI6) (by omega) (by omega)
          have hstep_eq : addCoreEdgeStep G lsf eCap Sk e = Sk := by unfold addCoreEdgeStep; simp [hcore_h, hrvV]
          exact ⟨stI, 9, runs_cond_iff.mpr ⟨1, 5, hlt1,
            runs_cond_iff.mpr ⟨0, 1, hlt2, by simp [runs_nop_iff], by simp [Expr.size]⟩,
            by simp [Expr.size]⟩, fun _ _ => rfl, hstep_eq.symm ▸ hS_Q2, fun _ _ => rfl, by omega⟩
      · have hruV : ru ∉ Sk.V := fun hc => hru_cap (hS_Q2.2.1 ru hc)
        have hlt1 : (Expr.bin .lt (.reg 19) (.reg 6)).eval w stI = some 0 :=
          Expr.eval_lt_false (Expr.eval_reg_of_eq hI19) (Expr.eval_reg_of_eq hI6) (by omega) (by omega)
        have hstep_eq : addCoreEdgeStep G lsf eCap Sk e = Sk := by unfold addCoreEdgeStep; simp [hcore_t, hruV]
        exact ⟨stI, 5, runs_cond_iff.mpr ⟨0, 1, hlt1, by simp [runs_nop_iff], by simp [Expr.size]⟩,
          fun _ _ => rfl, hstep_eq.symm ▸ hS_Q2, fun _ _ => rfl, by omega⟩
    obtain ⟨stJ, cJ, hrJ, hregsJ, hSJ, hfrJ, hcJ⟩ := hInner
    have hQ_agree : ∀ a, Q.R.foot b4 x4₂ a → stQ2.mem a = stJ.mem a := fun a ha => by
      symm; refine hfrJ a ?_
      rcases hfoot4₂ a ha with h1 | h2
      · by_contra hnot; exact hdisj_S4 a (by omega) (by omega) h1
      · exact Or.inr (le_trans hsPtrB h2.1)
    obtain ⟨hrep4_J, hphi4_J⟩ := Q.R_local b4 s4 x4₂ stQ2.mem stJ.mem hQ_agree
    have hz_final : ZeroFrom stJ.mem oQ2.value := fun a ha => by
      rw [hfrJ a (Or.inr (le_trans hsPtrB (le_trans hh_lo (le_trans hQ1_lo (le_trans hQ2_lo ha)))))]
      exact hzQ2 a ha
    have hseq9 := runs_seq_iff.mpr (Or.inr ⟨stI, 3, cJ, hass20, hrJ, rfl⟩)
    have hseq8 := runs_seq_iff.mpr (Or.inr ⟨stH, cQ2 + 5, _, hcallQ2, hseq9, rfl⟩)
    have hseq7 := runs_seq_iff.mpr (Or.inr ⟨stG, 2, _, hass18b, hseq8, rfl⟩)
    have hseq6 := runs_seq_iff.mpr (Or.inr ⟨stF, 3, _, hass19, hseq7, rfl⟩)
    have hseq5 := runs_seq_iff.mpr (Or.inr ⟨stE, cQ1 + 5, _, hcallQ1, hseq6, rfl⟩)
    have hseq4 := runs_seq_iff.mpr (Or.inr ⟨stD, 2, _, hass18a, hseq5, rfl⟩)
    have hseq3 := runs_seq_iff.mpr (Or.inr ⟨stC, cC, _, hrC, hseq4, rfl⟩)
    have hseq2 := runs_seq_iff.mpr (Or.inr ⟨stB, cB, _, hrB, hseq3, rfl⟩)
    have hcond_run := (runs_cond_iff (t := .nop)).mpr ⟨1, _, hcond1, hseq2, rfl⟩
    have hfull := runs_seq_iff.mpr (Or.inr ⟨stA, 5, _, hr_e, hcond_run, rfl⟩)
    refine ⟨stJ, _, x4₂, hfull,
      (hregsJ 0 (by decide)).trans hI0, (hregsJ 1 (by decide)).trans hI1,
      (hregsJ 2 (by decide)).trans hI2, (hregsJ 3 (by decide)).trans hI3,
      (hregsJ 4 (by decide)).trans hI4, (hregsJ 6 (by decide)).trans hI6,
      (hregsJ 9 (by decide)).trans hI9, (hregsJ 10 (by decide)).trans hI10,
      (hregsJ 11 (by decide)).trans hI11, (hregsJ 12 (by decide)).trans hI12,
      (hregsJ 14 (by decide)).trans hI14,
      ?_, ?_, ?_, htake_eq.symm ▸ hSJ, hrep4_J hrep4₂, ?_, ?_, ?_⟩
    · rw [(hregsJ 13 (by decide)).trans hI13]; omega
    · rw [(hregsJ 13 (by decide)).trans hI13]; omega
    · rw [(hregsJ 13 (by decide)).trans hI13]; exact hz_final
    · rw [(hregsJ 13 (by decide)).trans hI13]; exact hfoot4₂
    · intro a ha hS_out h4_out; exact (hfrJ a hS_out).trans (hframe_Q2 a ha hS_out h4_out)
    · dsimp only [dgGetTailContract, dgGetHeadContract, argsSize, Expr.size] at hcB hcC ⊢
      rw [← hphi4_J]; omega
  · have hep_0 : stA.mem (dgEPresBase gPtr vCap + e) = 0 := by simpa [stA, heG] using hep_eq
    have hcond0 : (Expr.load (.bin .add (.reg 11) (.reg 15))).eval w stA = some 0 :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, hr11]))
        (Expr.eval_reg_of_eq (by simp [stA])) hep_lt) hep_0
    have hfull : Runs w p ω body st .normal stA 12 :=
      runs_seq_iff.mpr (Or.inr ⟨stA, 5, 6, hr_e,
        runs_cond_iff.mpr ⟨0, 1, hcond0, by simp [runs_nop_iff], by simp [Expr.size]⟩, rfl⟩)
    have hstep_eq : addCoreEdgeStep G lsf eCap Sk e = Sk := by unfold addCoreEdgeStep; simp [heG]
    refine ⟨stA, 12, x4, hfull,
      by simp [stA, hr0], by simp [stA, hr1], by simp [stA, hr2], by simp [stA, hr3],
      by simp [stA, hr4], by simp [stA, hr6], by simp [stA, hr9], by simp [stA, hr10],
      by simp [stA, hr11], by simp [stA, hr12], by simp [stA, hr14],
      by simp [stA], by simp [stA], by simpa [stA] using hz,
      by rw [htake_eq, hstep_eq]; exact hS, hrep4,
      by simpa [stA] using hfoot4, hframe, by simp only [stA]; omega⟩

/-- Running `restartAddSlotEdgesStmt` inserts `(H_s.E ∩ G.E).filter (core ends in S.V)` into `S`
at their core ends, preserves `Q.R.rep`, allocates at most `2 * H_s.m` words, and costs (against
`Q.R.phi`) at most `(675 + 2 * Q.cost) * H_s.m + 70`. -/
theorem restartAddSlotEdges_runs {w vCap eCap spVCap spECap fRoot bOps bEdge : ℕ}
    {p : Program} {Q : RootQueryAt w p fRoot}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    {sPtr gPtr h_s b4 j h0 : ℕ} {G S H_s : MGraph} {lsf : LSF}
    {s4 : Q.σ} {x4 : Q.R.τ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hSPe : spECap ≤ eCap)
    (hsPtrB : sPtr + dynGraphSize vCap eCap ≤ h0) (hgPtrB : gPtr + dynGraphSize vCap eCap ≤ h0)
    (hh_sB : h_s + dynGraphSize spVCap spECap ≤ h0)
    (hb4W : b4 < 2 ^ w) (hjW : j < 2 ^ w)
    (hS : DynGraphAt mem sPtr vCap eCap S) (hG : DynGraphAt mem gPtr vCap eCap G)
    (hHs : DynGraphAt mem h_s spVCap spECap H_s)
    (hSagree : ∀ e ∈ H_s.E, e ∈ S.E →
      S.tail e = (coreGraph G lsf).tail e ∧ S.head e = (coreGraph G lsf).head e)
    (hrep4 : Q.R.rep b4 s4 x4 mem)
    (hQok : ∀ u ∈ G.V, Q.ok s4 j u ∧ Q.root s4 j u = lsf.F.root u)
    (hfoot4 : ∀ a, Q.R.foot b4 x4 a → a < h0)
    (hdisj_SG : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
      a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a)
    (hdisj_SH : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
      a < h_s ∨ h_s + dynGraphSize spVCap spECap ≤ a)
    (hdisj_S4 : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4 a)
    (hdisj_G4 : ∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4 a)
    (hdisj_H4 : ∀ a, h_s ≤ a → a < h_s + dynGraphSize spVCap spECap → ¬ Q.R.foot b4 x4 a)
    (hz : ZeroFrom mem h0) (hroom : h0 + 2 * H_s.m + 2 < 2 ^ w) :
    ∃ o st' c x4', Runs w p ω (restartAddSlotEdgesStmt bOps bEdge fRoot)
        (startState [sPtr, gPtr, h_s, b4, j, h0] mem pos) o st' c ∧
      h0 ≤ o.value ∧ o.value ≤ h0 + 2 * H_s.m ∧ ZeroFrom st'.mem o.value ∧
      (let add := (H_s.E ∩ G.E).filter fun e =>
          (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V
       DynGraphAt st'.mem sPtr vCap eCap
        { V := S.V, E := S.E ∪ add,
          tail := fun e => if e ∈ add then (coreGraph G lsf).tail e else S.tail e,
          head := fun e => if e ∈ add then (coreGraph G lsf).head e else S.head e }) ∧
      Q.R.rep b4 s4 x4' st'.mem ∧
      (∀ a, Q.R.foot b4 x4' a → Q.R.foot b4 x4 a ∨ (h0 ≤ a ∧ a < o.value)) ∧
      (∀ a < h0, (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) →
        ¬ Q.R.foot b4 x4 a → st'.mem a = mem a) ∧
      c + Q.R.phi b4 x4' st'.mem ≤ (675 + 2 * Q.cost) * H_s.m + 70 + Q.R.phi b4 x4 mem := by
  obtain ⟨eL, heL_len, _, heL_mem, heL_at, _⟩ := hHs.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hS_lt_w : sPtr + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hG_lt_w : gPtr + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hH_lt_w : h_s + dynGraphSize spVCap spECap < 2 ^ w := by omega
  have hvc_g : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hvc_h : mem h_s = spVCap := by simpa [dgVCapOff] using hHs.2.2.2.1
  have hec_h : mem (h_s + 1) = spECap := by simpa [dgECapOff] using hHs.2.2.2.2.1
  have hm_h : mem (h_s + 3) = eL.length := (by simpa [dgMOff] using hHs.2.2.2.2.2.2.1 : mem (h_s + 3) = H_s.m).trans heL_len.symm
  have hm_le_sp : H_s.m ≤ spECap := by
    have hsub : H_s.E ⊆ Finset.range spECap := fun x hx => Finset.mem_range.mpr (hHs.2.2.1 x hx)
    exact (Finset.card_le_card hsub).trans (by simp)
  have heL_lt_w : eL.length < 2 ^ w := by dsimp [dynGraphSize] at hH_lt_w; omega
  let st0 := startState [sPtr, gPtr, h_s, b4, j, h0] mem pos
  have hr6 : Runs w p ω (.assign 6 (.load (.reg 1))) st0 .normal
      { st0 with regs := Function.update st0.regs 6 vCap } 3 :=
    runs_assign_iff.mpr ⟨vCap, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st0, startState]))
      hvc_g, rfl, rfl, by simp [Expr.size]⟩
  set st1 := { st0 with regs := Function.update st0.regs 6 vCap }
  have hr7 : Runs w p ω (.assign 7 (.load (.reg 2))) st1 .normal
      { st1 with regs := Function.update st1.regs 7 spVCap } 3 :=
    runs_assign_iff.mpr ⟨spVCap, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st1, st0, startState]))
      hvc_h, rfl, rfl, by simp [Expr.size]⟩
  set st2 := { st1 with regs := Function.update st1.regs 7 spVCap }
  have hr8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 2) (.const 1)))) st2 .normal
      { st2 with regs := Function.update st2.regs 8 spECap } 5 :=
    runs_assign_iff.mpr ⟨spECap, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState])) (Expr.eval_const (by omega))
      (by dsimp [dynGraphSize] at hH_lt_w; omega)) hec_h, rfl, rfl, by simp [Expr.size]⟩
  set st3 := { st2 with regs := Function.update st2.regs 8 spECap }
  have hr9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 2) (.const 3)))) st3 .normal
      { st3 with regs := Function.update st3.regs 9 eL.length } 5 :=
    runs_assign_iff.mpr ⟨eL.length, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState])) (Expr.eval_const (by omega))
      (by dsimp [dynGraphSize] at hH_lt_w; omega)) hm_h, rfl, rfl, by simp [Expr.size]⟩
  set st4 := { st3 with regs := Function.update st3.regs 9 eL.length }
  have hr10 : Runs w p ω (.assign 10 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
      (.bin .mul (.const 7) (.reg 7))) (.reg 8))) st4 .normal
      { st4 with regs := Function.update st4.regs 10 (dgEListBase h_s spVCap spECap) } 10 :=
    runs_assign_iff.mpr ⟨dgEListBase h_s spVCap spECap,
      by dsimp only [dgEListBase]; dsimp only [dynGraphSize] at hH_lt_w
         simp only [st4, st3, st2, st1, st0, startState]; eval_expr,
      rfl, rfl, by simp [Expr.size]⟩
  set st5 := { st4 with regs := Function.update st4.regs 10 (dgEListBase h_s spVCap spECap) }
  have hr11 : Runs w p ω (.assign 11 (.bin .add (.bin .add (.reg 1) (.const 4))
      (.bin .mul (.const 7) (.reg 6)))) st5 .normal
      { st5 with regs := Function.update st5.regs 11 (dgEPresBase gPtr vCap) } 8 :=
    runs_assign_iff.mpr ⟨dgEPresBase gPtr vCap,
      by dsimp only [dgEPresBase]; dsimp only [dynGraphSize] at hG_lt_w
         simp only [st5, st4, st3, st2, st1, st0, startState]; eval_expr,
      rfl, rfl, by simp [Expr.size]⟩
  set st6 := { st5 with regs := Function.update st5.regs 11 (dgEPresBase gPtr vCap) }
  have hr12 : Runs w p ω (.assign 12 (.bin .add (.reg 0) (.const 4))) st6 .normal
      { st6 with regs := Function.update st6.regs 12 (dgVPresBase sPtr) } 4 :=
    runs_assign_iff.mpr ⟨dgVPresBase sPtr,
      by dsimp only [dgVPresBase]; dsimp only [dynGraphSize] at hS_lt_w
         simp only [st6, st5, st4, st3, st2, st1, st0, startState]; eval_expr,
      rfl, rfl, by simp [Expr.size]⟩
  set st7 := { st6 with regs := Function.update st6.regs 12 (dgVPresBase sPtr) }
  have hr13 : Runs w p ω (.assign 13 (.reg 5)) st7 .normal
      { st7 with regs := Function.update st7.regs 13 h0 } 2 :=
    runs_assign_iff.mpr ⟨h0, Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState]),
      rfl, rfl, by simp [Expr.size]⟩
  set st8 := { st7 with regs := Function.update st7.regs 13 h0 }
  let Inv : ℕ → State → Q.R.τ → Prop := fun k st x4k =>
    st.regs 0 = sPtr ∧ st.regs 1 = gPtr ∧ st.regs 2 = h_s ∧ st.regs 3 = b4 ∧
    st.regs 4 = j ∧ st.regs 6 = vCap ∧ st.regs 9 = eL.length ∧
    st.regs 10 = dgEListBase h_s spVCap spECap ∧
    st.regs 11 = dgEPresBase gPtr vCap ∧ st.regs 12 = dgVPresBase sPtr ∧ st.regs 14 = k ∧
    h0 ≤ st.regs 13 ∧ st.regs 13 ≤ h0 + 2 * k ∧ ZeroFrom st.mem (st.regs 13) ∧
    DynGraphAt st.mem sPtr vCap eCap ((eL.take k).foldl (addCoreEdgeStep G lsf eCap) S) ∧
    Q.R.rep b4 s4 x4k st.mem ∧
    (∀ a, Q.R.foot b4 x4k a → Q.R.foot b4 x4 a ∨ (h0 ≤ a ∧ a < st.regs 13)) ∧
    (∀ a < h0, (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) →
      ¬ Q.R.foot b4 x4 a → st.mem a = mem a)
  obtain ⟨stLoop, cLoop, x4', hrLoop, hInvEnd, hcLoop⟩ :=
    forRange_phi_runs (w := w) (p := p) (ω := ω) (Φ := fun x m => Q.R.phi b4 x m) (Inv := Inv)
      (fun _ => 660 + 2 * Q.cost) (n := eL.length) (by omega) (fun _ => heL_lt_w)
      (st₀ := st8) (x₀ := x4) (Expr.eval_const (by omega))
      (by refine ⟨by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
            by simp, by simp [st8], by simp [st8],
            by simpa [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState] using hz,
            by simpa [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState] using hS,
            by simpa [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState] using hrep4,
            fun a ha => Or.inl ha, fun _ _ _ _ => rfl⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.2.2.1)
      (fun k hk st x hI => by
        obtain ⟨r0, r1, r2, r3, r4, r6, r9, r10, r11, r12, r14, hlo, hhi, hzk, hSk, hr4k, hf4k, hfrk⟩ := hI
        obtain ⟨st₁, c₁, x4₁, hr₁, s0, s1, s2, s3, s4', s6, s9, s10, s11, s12, s14,
            h13_lo, h13_hi, hz₁, hS₁, hr4₁, hf4₁, hfr₁, hc₁⟩ :=
          addSlotEdge_step_runs hpOps hpEdge hw16 hSPe hsPtrB hgPtrB hh_sB hb4W hjW heL_len heL_mem
            heL_at rfl hG hHs hQok hfoot4 hdisj_SG hdisj_SH hdisj_S4 hdisj_G4 hdisj_H4 hk
            ⟨r0, r1, r2, r3, r4, r6, r9, r10, r11, r12, r14⟩ hlo (by omega) hzk hSk hr4k hf4k hfrk
        refine ⟨st₁, c₁, x4₁, hr₁, s14, ?_, hc₁⟩
        exact ⟨by simp [s0], by simp [s1], by simp [s2], by simp [s3], by simp [s4'],
          by simp [s6], by simp [s9], by simp [s10], by simp [s11], by simp [s12], by simp,
          by simp; omega, by simp; omega, by simpa using hz₁, hS₁, hr4₁, by simpa using hf4₁, hfr₁⟩)
  have hrRet : Runs w p ω (.ret (.reg 13)) stLoop (.returned (stLoop.regs 13)) stLoop 2 :=
    runs_ret_iff.mpr ⟨stLoop.regs 13, Expr.eval_reg_of_eq rfl, rfl, rfl, by simp [Expr.size]⟩
  have hLRet := runs_seq_iff.mpr (Or.inr ⟨stLoop, cLoop, 2, hrLoop, hrRet, rfl⟩)
  have hS7 := runs_seq_iff.mpr (Or.inr ⟨st8, 2, _, hr13, hLRet, rfl⟩)
  have hS6 := runs_seq_iff.mpr (Or.inr ⟨st7, 4, _, hr12, hS7, rfl⟩)
  have hS5 := runs_seq_iff.mpr (Or.inr ⟨st6, 8, _, hr11, hS6, rfl⟩)
  have hS4 := runs_seq_iff.mpr (Or.inr ⟨st5, 10, _, hr10, hS5, rfl⟩)
  have hS3 := runs_seq_iff.mpr (Or.inr ⟨st4, 5, _, hr9, hS4, rfl⟩)
  have hS2 := runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, hr8, hS3, rfl⟩)
  have hS1 := runs_seq_iff.mpr (Or.inr ⟨st2, 3, _, hr7, hS2, rfl⟩)
  have hS0 := runs_seq_iff.mpr (Or.inr ⟨st1, 3, _, hr6, hS1, rfl⟩)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlo, hhi, hze, hSe, hr4e, hf4e, hfre⟩ := hInvEnd
  have hS_same : SameGraph (eL.foldl (addCoreEdgeStep G lsf eCap) S)
      { V := S.V
        E := S.E ∪ ((H_s.E ∩ G.E).filter fun e =>
          (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V)
        tail := fun e =>
          if e ∈ (H_s.E ∩ G.E).filter (fun e =>
              (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V)
          then (coreGraph G lsf).tail e else S.tail e
        head := fun e =>
          if e ∈ (H_s.E ∩ G.E).filter (fun e =>
              (coreGraph G lsf).tail e ∈ S.V ∧ (coreGraph G lsf).head e ∈ S.V)
          then (coreGraph G lsf).head e else S.head e } := by
    have hfin : eL.toFinset = H_s.E := by ext e; simp [heL_mem]
    simpa only [hfin] using foldl_addCoreEdgeStep (G := G) (lsf := lsf) (eCap := eCap) (S := S)
      (fun e he => lt_of_lt_of_le (hHs.2.2.1 e ((heL_mem e).mp he)) hSPe)
      (fun e he => hSagree e ((heL_mem e).mp he))
  refine ⟨.returned (stLoop.regs 13), stLoop, _, x4', hS0, hlo, heL_len ▸ hhi, hze, ?_, hr4e, hf4e, hfre, ?_⟩
  · rw [List.take_of_length_le le_rfl] at hSe
    exact DynGraphAt.of_same hSe hS_same
  · rw [rangeCost_const, heL_len] at hcLoop
    simp only [Expr.size, Nat.sub_zero, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState] at hcLoop ⊢
    have hmul : H_s.m * (660 + 2 * Q.cost) + H_s.m * 9 ≤ (675 + 2 * Q.cost) * H_s.m := by
      rw [← Nat.mul_add, Nat.mul_comm]
      exact Nat.mul_le_mul_right H_s.m (by omega)
    omega

end MinCostFlow.SparseCore.Program.Read
