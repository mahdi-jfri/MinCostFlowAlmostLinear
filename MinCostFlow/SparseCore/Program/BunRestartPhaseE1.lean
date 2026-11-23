module

public import MinCostFlow.SparseCore.Program.BunRestartStage3

/-!
# The restart of the bundles: one round of loop E (`BunRestartPhaseE1`)

A round of loop E exports the graph of one new slot at the heap pointer (`bundleExportGraphStmt`)
and copies its four header words to the descriptor `h + 4 i` (`brCopy4`, `runs_copy4`).
`brLoopE_round` gives the state after the round, and `exportAt_of_post` shows that the
descriptor then describes the graph (`ExportAt`). `brExportAt_congr` shows that later rounds keep it.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- The copy of the four header words at the heap pointer (register `19`) to `h + 4 i`, followed
by the move of the heap pointer to the end of the export (register `12`). -/
def brCopy4 : Stmt :=
  .store (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.load (.reg 19)) ;;
  .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.const 1))
    (.load (.bin .add (.reg 19) (.const 1))) ;;
  .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.const 2))
    (.load (.bin .add (.reg 19) (.const 2))) ;;
  .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.const 3))
    (.load (.bin .add (.reg 19) (.const 3))) ;;
  .assign 19 (.reg 12)

end

public section

theorem brLoopEBody_eq (bExport : ℕ) :
    brLoopEBody bExport = (.assign 11 (.load (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 10)))) ;;
      (.call 12 bExport [.reg 0, .reg 11, .reg 19] ;; brCopy4)) := rfl

/-- `ExportAt` depends only on the descriptor and on the lists it points to. -/
theorem brExportAt_congr {mem mem' : ℕ → ℕ} {d hE hE' : ℕ} {G : MGraph}
    (hex : ExportAt mem d hE G) (hle : hE ≤ hE')
    (hag : ∀ a, (d ≤ a ∧ a < d + 4) ∨ (mem (d + 1) ≤ a ∧ a < mem (d + 1) + mem d) ∨
      (mem (d + 3) ≤ a ∧ a < mem (d + 3) + 3 * mem (d + 2)) → mem' a = mem a) :
    ExportAt mem' d hE' G := by
  have e0 := hag d (Or.inl ⟨le_rfl, by omega⟩)
  have e1 := hag (d + 1) (Or.inl ⟨by omega, by omega⟩)
  have e2 := hag (d + 2) (Or.inl ⟨by omega, by omega⟩)
  have e3 := hag (d + 3) (Or.inl ⟨by omega, by omega⟩)
  have hvl : readList mem' (mem' (d + 1)) (mem' d) = readList mem (mem (d + 1)) (mem d) := by
    rw [e0, e1]
    unfold readList
    exact List.map_congr_left fun i hi => hag _ (Or.inr (Or.inl ⟨by omega, by
      have := List.mem_range.mp hi; omega⟩))
  have het : readTriples mem' (mem' (d + 3)) (mem' (d + 2)) =
      readTriples mem (mem (d + 3)) (mem (d + 2)) := by
    rw [e2, e3]
    unfold readTriples
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    rw [hag _ (Or.inr (Or.inr ⟨by omega, by omega⟩)), hag _ (Or.inr (Or.inr ⟨by omega, by omega⟩)),
      hag _ (Or.inr (Or.inr ⟨by omega, by omega⟩))]
  obtain ⟨h0, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hex
  refine ⟨e0.trans h0, e2.trans h2, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hvl]; exact h3
  · rw [hvl]; exact h4
  · rw [het]; exact h5
  · rw [het]; exact h6
  · rw [het]; exact h7
  · rw [e1]; exact h9
  · rw [e3]; exact h10
  · rw [e0, e1]; omega
  · rw [e2, e3]; omega

variable {w : ℕ} {p : Program} {ω : ℕ → Bool}

/-- **The copy of the header.** With `h` in register `4`, `i` in register `10` and `src` in
register `19`, `brCopy4` copies the four words at `src` to `h + 4 i` and sets register `19` to
register `12`. -/
theorem runs_copy4 {st : State} {h i src : ℕ} (h4 : st.regs 4 = h) (h10 : st.regs 10 = i)
    (h19 : st.regs 19 = src) (hd : h + 4 * i + 4 ≤ src) (hw : src + 3 < 2 ^ w)
    (hw4 : 4 * i < 2 ^ w) :
    Runs w p ω brCopy4 st .normal
      { mem := Function.update (Function.update (Function.update
          (Function.update st.mem (h + 4 * i) (st.mem src)) (h + 4 * i + 1) (st.mem (src + 1)))
          (h + 4 * i + 2) (st.mem (src + 2))) (h + 4 * i + 3) (st.mem (src + 3)),
        regs := Function.update st.regs 19 (st.regs 12), pos := st.pos } 50 := by
  have hA : (Expr.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))).eval w st =
      some (h + 4 * i) :=
    Expr.eval_add (Expr.eval_reg_of_eq h4)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h10) hw4) (by omega)
  have hAt : ∀ (st' : State), st'.regs = st.regs → ∀ t, t < 4 →
      (Expr.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.const t)).eval w st' =
        some (h + 4 * i + t) := by
    intro st' hr t ht
    refine Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hr]; exact h4))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by rw [hr]; exact h10))
        hw4) (by omega)) (Expr.eval_const (by omega)) (by omega)
  have hVt : ∀ (st' : State), st'.regs = st.regs → ∀ t, t < 4 → ∀ v, st'.mem (src + t) = v →
      (Expr.load (.bin .add (.reg 19) (.const t))).eval w st' = some v := by
    intro st' hr t ht v hv
    exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hr]; exact h19))
      (Expr.eval_const (by omega)) (by omega)) hv
  set m1 := Function.update st.mem (h + 4 * i) (st.mem src) with hm1
  set m2 := Function.update m1 (h + 4 * i + 1) (st.mem (src + 1)) with hm2
  set m3 := Function.update m2 (h + 4 * i + 2) (st.mem (src + 2)) with hm3
  set m4 := Function.update m3 (h + 4 * i + 3) (st.mem (src + 3)) with hm4
  have r0 : Runs w p ω (.store (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10)))
      (.load (.reg 19))) st .normal { st with mem := m1 } 8 :=
    runs_store_iff.mpr ⟨_, _, hA, Expr.eval_load (Expr.eval_reg_of_eq h19), rfl,
      rfl, by simp [Expr.size]⟩
  have v1 : m1 (src + 1) = st.mem (src + 1) := by rw [hm1, Function.update_of_ne (by omega)]
  have r1 : Runs w p ω (.store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10)))
      (.const 1)) (.load (.bin .add (.reg 19) (.const 1)))) { st with mem := m1 } .normal
      { st with mem := m2 } 12 :=
    runs_store_iff.mpr ⟨_, _, hAt { st with mem := m1 } rfl 1 (by omega),
      hVt { st with mem := m1 } rfl 1 (by omega) _ v1, rfl,
      rfl, by simp [Expr.size]⟩
  have v2 : m2 (src + 2) = st.mem (src + 2) := by
    rw [hm2, Function.update_of_ne (by omega), hm1, Function.update_of_ne (by omega)]
  have r2 : Runs w p ω (.store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10)))
      (.const 2)) (.load (.bin .add (.reg 19) (.const 2)))) { st with mem := m2 } .normal
      { st with mem := m3 } 12 :=
    runs_store_iff.mpr ⟨_, _, hAt { st with mem := m2 } rfl 2 (by omega),
      hVt { st with mem := m2 } rfl 2 (by omega) _ v2, rfl,
      rfl, by simp [Expr.size]⟩
  have v3 : m3 (src + 3) = st.mem (src + 3) := by
    rw [hm3, Function.update_of_ne (by omega), hm2, Function.update_of_ne (by omega), hm1,
      Function.update_of_ne (by omega)]
  have r3 : Runs w p ω (.store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10)))
      (.const 3)) (.load (.bin .add (.reg 19) (.const 3)))) { st with mem := m3 } .normal
      { st with mem := m4 } 12 :=
    runs_store_iff.mpr ⟨_, _, hAt { st with mem := m3 } rfl 3 (by omega),
      hVt { st with mem := m3 } rfl 3 (by omega) _ v3, rfl,
      rfl, by simp [Expr.size]⟩
  have r4 : Runs w p ω (.assign 19 (.reg 12)) { st with mem := m4 } .normal
      { mem := m4, regs := Function.update st.regs 19 (st.regs 12), pos := st.pos } 2 :=
    runs_assign_iff.mpr ⟨_, Expr.eval_reg_of_eq rfl, rfl, rfl, by simp [Expr.size]⟩
  exact runs_seq_normal r0 (runs_seq_normal r1 (runs_seq_normal r2 (runs_seq_normal r3 r4)))

/-- What the copy writes: the words `src + t` at `d + t` for `t < 4`; it keeps the rest. -/
theorem copy4_mem {mem : ℕ → ℕ} {d src : ℕ} (hd : d + 4 ≤ src) (a : ℕ) :
    Function.update (Function.update (Function.update (Function.update mem d (mem src))
      (d + 1) (mem (src + 1))) (d + 2) (mem (src + 2))) (d + 3) (mem (src + 3)) a =
      if d ≤ a ∧ a < d + 4 then mem (src + (a - d)) else mem a := by
  by_cases h0 : a = d
  · subst h0; simp (disch := omega) [Function.update_of_ne]
  by_cases h1 : a = d + 1
  · subst h1; simp (disch := omega) [Function.update_of_ne]
  by_cases h2 : a = d + 2
  · subst h2; simp (disch := omega) [Function.update_of_ne]
  by_cases h3 : a = d + 3
  · subst h3; simp
  rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
    Function.update_of_ne h0, ite_eq_right (by omega)]

/-- **The descriptor of an export.** After an export at `hc` whose four header words were copied to
`d`, the descriptor at `d` describes the graph of the exported bundle state, as long as the memory
from `hc` on is that of the export. -/
theorem exportAt_of_post {slotCap vCap eCap tbl hc : ℕ} {T : BundleTableState slotCap}
    {M' : BundleTableMeta slotCap} {j : Fin slotCap} {B : BundleState} {args : List ℕ}
    {mem mem₁ mem₂ : ℕ → ℕ} {ret d : ℕ}
    (hpost : (bundleExportGraphContract w slotCap vCap eCap tbl hc T M' j B).post args mem ret mem₁)
    (hdh : d + 4 ≤ hc) (hd : ∀ t < 4, mem₂ (d + t) = mem₁ (hc + t))
    (hag : ∀ a, hc ≤ a → mem₂ a = mem₁ a) :
    ExportAt mem₂ d (hc + bundleExportSpace B) B.graph := by
  obtain ⟨-, -, -, e0, e1, e2, e3, hvL, hnd, hmemE, hspec, hgeq⟩ := hpost
  have f0 : mem₂ d = B.vertices.card := (hd 0 (by omega)).trans e0
  have f1 : mem₂ (d + 1) = hc + 4 := (hd 1 (by omega)).trans e1
  have f2 : mem₂ (d + 2) = B.edges.card := (hd 2 (by omega)).trans e2
  have f3 : mem₂ (d + 3) = hc + 4 + B.vertices.card := (hd 3 (by omega)).trans e3
  have hvl : readList mem₂ (mem₂ (d + 1)) (mem₂ d) =
      readList mem₁ (hc + 4) B.vertices.card := by
    rw [f0, f1]
    unfold readList
    exact List.map_congr_left fun i _ => hag _ (by omega)
  have het : readTriples mem₂ (mem₂ (d + 3)) (mem₂ (d + 2)) =
      readTriples mem₁ (hc + 4 + B.vertices.card) B.edges.card := by
    rw [f2, f3]
    unfold readTriples
    refine List.map_congr_left fun i _ => ?_
    rw [hag _ (by omega), hag _ (by omega), hag _ (by omega)]
  have hV : ∀ v, v ∈ List.range B.vertices.card ↔ v ∈ B.graph.V := by
    intro v
    rw [← hgeq.1, ← hvL]
    simp [graphOfLists]
  refine ⟨f0, f2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvl, hvL]; exact List.nodup_range
  · rw [hvl, hvL]; exact hV
  · rw [het]; exact hnd
  · rw [het]; exact hspec
  · rw [het]
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ((hmemE e).mpr he)
    exact ⟨t, ht, rfl⟩
  · unfold bundleExportSpace; omega
  · rw [f1]; omega
  · rw [f3]; omega
  · rw [f0, f1]; unfold bundleExportSpace; omega
  · rw [f2, f3]; unfold bundleExportSpace; omega

/-- **One round of loop E.** Register `10` holds `i`, the spec `i` holds the slot `s`, which holds
`B` in the table `T`, and register `19` holds the heap pointer `hc`. The round exports the graph
of `B` at `hc`, copies its header to `h + 4 i`, and moves the heap pointer to the end of the
export. Below `hc` it writes only the descriptor `h + 4 i`. -/
theorem brLoopE_round {bExport : ℕ} (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    {slotCap vCap eCap tbl h n i hc s : ℕ} {T : BundleTableState slotCap}
    {M' : BundleTableMeta slotCap} {B : BundleState} {st : State} (hw : 16 ≤ 2 ^ w)
    (h0 : st.regs 0 = tbl) (h4 : st.regs 4 = h) (h8 : st.regs 8 = h + 4 * n)
    (h10 : st.regs 10 = i) (h19 : st.regs 19 = hc) (hi : i < n)
    (hsm : st.mem (h + 4 * n + 2 * i) = s) (hs : s < slotCap) (hB : T ⟨s, hs⟩ = some B)
    (htab : BundleTableRepAt slotCap vCap eCap tbl T M' st.mem)
    (hfoot : ∀ a, bundleTableFoot eCap tbl M' a → a < hc) (hz : ZeroFrom st.mem hc)
    (hfit : hc + bundleExportSpace B < 2 ^ w)
    (htblw : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w) (hlay : h + 6 * n ≤ hc) :
    ∃ st₁ c, Runs w p ω (brLoopEBody bExport) st .normal st₁ c ∧
      st₁.regs = Function.update (Function.update (Function.update st.regs 11 s) 12
        (hc + bundleExportSpace B)) 19 (hc + bundleExportSpace B) ∧
      (∀ a < hc, ¬ (h + 4 * i ≤ a ∧ a < h + 4 * i + 4) → st₁.mem a = st.mem a) ∧
      ZeroFrom st₁.mem (hc + bundleExportSpace B) ∧
      ExportAt st₁.mem (h + 4 * i) (hc + bundleExportSpace B) B.graph ∧
      hc ≤ st₁.mem (h + 4 * i + 1) ∧ hc ≤ st₁.mem (h + 4 * i + 3) ∧
      c ≤ bundleExportCost B + 70 := by
  have hsw : s < 2 ^ w := by unfold bundleTableFixedSize at htblw; omega
  have hsp : 4 ≤ bundleExportSpace B := by unfold bundleExportSpace; omega
  have ra : Runs w p ω (.assign 11 (.load (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 10)))))
      st .normal { st with regs := Function.update st.regs 11 s } 7 :=
    runs_assign_iff.mpr ⟨s, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h8)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h10) (by omega))
      (by omega)) hsm, rfl, rfl, by simp [Expr.size]⟩
  have hf := bundleExportGraph_meetsContract (w := w) (slotCap := slotCap) (vCap := vCap)
    (eCap := eCap) (tbl := tbl) (h := hc) (S := T) (m := M') (j := ⟨s, hs⟩) (B := B) hpExport
  obtain ⟨st₂, c₂, v, rc, hpost, h12, hother, hc₂⟩ := runs_call_of_meetsContract (r := 12)
    (st := { st with regs := Function.update st.regs 11 s }) (vs := [tbl, s, hc])
    (args := [.reg 0, .reg 11, .reg 19]) hf (by
      simp only [evalArgs, Expr.eval, Function.update_self]
      simp [h0, h19, Function.update_of_ne]) (by
      intro x hx; simp at hx; omega)
    ⟨rfl, hw, htblw, hfit, hz, hfoot, htab, hB⟩ ω
  have hpost' := hpost
  obtain ⟨hret, hz₂, hlow₂, -⟩ := hpost'
  have hreg₂ : ∀ r, r ≠ 12 → st₂.regs r = Function.update st.regs 11 s r := hother
  have r4 : st₂.regs 4 = h := by rw [hreg₂ 4 (by omega)]; simp [h4]
  have r10 : st₂.regs 10 = i := by rw [hreg₂ 10 (by omega)]; simp [h10]
  have r19 : st₂.regs 19 = hc := by rw [hreg₂ 19 (by omega)]; simp [h19]
  have rcp := runs_copy4 (w := w) (p := p) (ω := ω) (st := st₂) r4 r10 r19 (by omega)
    (by omega) (by omega)
  have hmem₃ := copy4_mem (mem := st₂.mem) (d := h + 4 * i) (src := hc) (by omega)
  refine ⟨_, 7 + (c₂ + 50 + 1) + 1, runs_seq_normal ra (runs_seq_normal rc rcp), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · funext r
    simp only [Function.update_apply]
    by_cases r19' : r = 19
    · simp [r19', h12, hret]
    · by_cases r12' : r = 12
      · simp [r12', h12, hret]
      · simp only [r19', r12', ite_false]
        rw [hreg₂ r r12']
        simp [Function.update_apply]
  · intro a ha hna
    dsimp only
    rw [hmem₃, ite_eq_right hna]
    exact hlow₂ a ha
  · intro a ha
    dsimp only
    rw [hmem₃, ite_eq_right (by omega)]
    rw [← hret] at ha
    exact hz₂ a ha
  · exact exportAt_of_post hpost (by omega) (fun t ht => by
      dsimp only
      rw [hmem₃, ite_eq_left (by omega)]
      congr 2; omega) (fun a ha => by
        dsimp only
        rw [hmem₃, ite_eq_right (by omega)])
  · dsimp only
    rw [hmem₃, ite_eq_left (by omega), show hc + (h + 4 * i + 1 - (h + 4 * i)) = hc + 1 by omega,
      hpost.2.2.2.2.1]
    omega
  · dsimp only
    rw [hmem₃, ite_eq_left (by omega), show hc + (h + 4 * i + 3 - (h + 4 * i)) = hc + 3 by omega,
      hpost.2.2.2.2.2.2.1]
    omega
  · simp only [bundleExportGraphContract, argsSize_cons, argsSize_nil, Expr.size] at hc₂
    omega

end

end MinCostFlow.SparseCore.Program.Restart
