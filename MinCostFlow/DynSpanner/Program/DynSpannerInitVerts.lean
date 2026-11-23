module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitDefs

/-!
# Initialization vertex-insertion loop triple (`DynSpannerInitVerts`)
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private def dsAddVStep (G : MGraph) (v : ℕ) : MGraph :=
  { G with V := insert v G.V }

private lemma mem_empty_foldl_vStep {vL : List ℕ} :
    ∀ k (V₀ : Finset ℕ) (_e : ℕ),
      (vL.take k).foldl dsAddVStep { V := V₀, E := ∅, tail := fun _ => 0, head := fun _ => 0 } =
      { V := V₀ ∪ (vL.take k).toFinset, E := ∅, tail := fun _ => 0, head := fun _ => 0 } := by
  intro k
  induction k with
  | zero => intro V₀ _; simp
  | succ k ih =>
    intro V₀ e
    by_cases hk : k < vL.length
    · rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih V₀ e]
      dsimp only [dsAddVStep]
      simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
      congr 1; ext x; simp [Finset.mem_union, Finset.mem_insert]
    · have hk2 : vL.length ≤ k := Nat.le_of_not_lt hk
      simp only [List.take_of_length_le (Nat.le_succ_of_le hk2),
        List.take_of_length_le hk2] at ih ⊢
      exact ih V₀ e

lemma dsAddVerts_triple {w vCap eCap b : ℕ} {G : MGraph} {vL : List ℕ}
    {p : Program} {bOps : ℕ} (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hb_lt : dsHPtr b vCap eCap + dynGraphSize vCap eCap < 2 ^ w)
    (hG_v : ∀ v ∈ G.V, v < vCap) (hGn_w : G.n < 2 ^ w)
    (hvL_len : vL.length = G.n) (hvL_mem : ∀ v, v ∈ vL ↔ v ∈ G.V) :
    let hPtr := dsHPtr b vCap eCap
    let vListPtr := dgVListBase (dsGPtr b) vCap
    let emptyH : MGraph := { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
    ∀ (mem0 regs0 : ℕ → ℕ),
      DynGraphAt mem0 hPtr vCap eCap emptyMGraph →
      ListAt mem0 vListPtr vL →
      vListPtr + G.n ≤ hPtr →
      Triple w p
        (fun st => st.mem = mem0 ∧ (∀ r, r ≠ 13 → r ≠ 14 → st.regs r = regs0 r) ∧
          st.regs 6 = dsGPtr b ∧ st.regs 7 = hPtr ∧ st.regs 10 = G.n ∧ st.regs 12 = vListPtr)
        (forRange 13 (.const 0) (.reg 10)
          (.assign 14 (.load (.bin .add (.reg 12) (.reg 13))) ;;
           .call 14 (bOps + dgIdxAddVertex) [.reg 7, .reg 14]))
        (normalPost fun st =>
          DynGraphAt st.mem hPtr vCap eCap emptyH ∧
          (∀ r, r ≠ 13 → r ≠ 14 → st.regs r = regs0 r) ∧
          st.regs 6 = dsGPtr b ∧ st.regs 7 = hPtr ∧ st.regs 10 = G.n ∧ st.regs 12 = vListPtr ∧
          ∀ addr, addr < hPtr ∨ hPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem0 addr)
        (fun _ => G.n * (120 + (.reg 10 : Expr).size + 8) + ((.const 0 : Expr).size + (.reg 10 : Expr).size + 5)) := by
  intro hPtr vListPtr emptyH mem0 regs0 hH0 hvList hDisj
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun k st =>
    (∀ r, r ≠ 13 → r ≠ 14 → st.regs r = regs0 r) ∧
    st.regs 6 = dsGPtr b ∧ st.regs 7 = hPtr ∧ st.regs 10 = G.n ∧ st.regs 12 = vListPtr ∧
    st.regs 13 = k ∧
    DynGraphAt st.mem hPtr vCap eCap
      ((vL.take k).foldl dsAddVStep { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }) ∧
    ∀ addr, addr < hPtr ∨ hPtr + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem0 addr
  refine (Triple.forRange_const (P := fun st => st.mem = mem0 ∧
      (∀ r, r ≠ 13 → r ≠ 14 → st.regs r = regs0 r) ∧
      st.regs 6 = dsGPtr b ∧ st.regs 7 = hPtr ∧ st.regs 10 = G.n ∧ st.regs 12 = vListPtr)
    (Inv := Inv)
    120 0 G.n (Nat.zero_le _) h1_lt (fun _ => hGn_w)
    (fun st ⟨hm, hregs, r6, r7, r10, r12⟩ => by
      refine ⟨by eval_expr, fun r h13 h14 => by simp [h13, hregs r h13 h14],
        by simp [r6], by simp [r7], by simp [r10], by simp [r12], by simp,
        by simpa [emptyMGraph, hm] using hH0, fun _ _ => hm ▸ rfl⟩)
    (fun k st _ _ h => h.2.2.2.2.2.1)
    (fun k st _ _ h => by simp [Expr.eval, h.2.2.2.1])
    (fun k _ hk st ω ⟨hregs, hr6, hr7, hr10, hr12, hr13, hGk, hfr⟩ => by
      have hkv : k < vL.length := by omega
      let v := vL[k]'hkv
      have hv_cap : v < vCap := hG_v v ((hvL_mem v).mp (List.getElem_mem hkv))
      have hv_ltw : v < 2 ^ w := by dsimp only [dynGraphSize, hPtr, dsHPtr] at hb_lt; omega
      have haddr_ltw : vListPtr + k < 2 ^ w := by omega
      have hmem_v : st.mem (vListPtr + k) = v := (hfr _ (Or.inl (by omega))).trans (hvList k hkv)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := v)
        (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr12, hr13, haddr_ltw]) hmem_v) ?_
      have hpre_v : (dgAddVertexContract w vCap eCap _).pre [hPtr, v] st.mem :=
        ⟨hPtr, v, rfl, hw16, hb_lt, hv_cap, hGk⟩
      refine runs_call_le (r := 14) (dgAddVertex_meetsContract hpOps)
        (by simp [Expr.eval, evalArgs, hr7])
        (fun z hz => by simp at hz; rcases hz with rfl | rfl <;> omega)
        hpre_v ?_
      intro retV memV posV ⟨gPtrV, vV, hEqV, _, hGV, hfrV⟩
      simp only [List.cons.injEq, and_true] at hEqV
      rcases hEqV with ⟨rfl, rfl⟩
      dsimp only [normalPost]
      refine ⟨⟨⟨fun r h13 h14 => by simp [h13, h14, hregs r h13 h14],
        by simp [hr6], by simp [hr7], by simp [hr10], by simp [hr12], by simp,
        ?_, ?_⟩, by simp [hr13]⟩, ?_⟩
      · rw [List.take_succ_eq_append_getElem hkv, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact hGV
      · intro addr ha
        dsimp only
        rw [hfrV addr ha]
        exact hfr addr ha
      · dsimp only [dgAddVertexContract, argsSize, Expr.size]; omega)).strengthen_post ?_
  intro o st hq
  cases o with
  | returned _ => exact hq
  | normal =>
    rcases hq with ⟨hregs, hr6, hr7, hr10, hr12, _, hG_final, hfr⟩
    have hVeq : ((vL.take G.n).foldl dsAddVStep
        { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }).V = G.V := by
      have h1 := congrArg MGraph.V (mem_empty_foldl_vStep (vL := vL) G.n ∅ 0)
      rw [h1, ← hvL_len, List.take_length]
      ext v
      simp [hvL_mem v]
    have hEeq : ((vL.take G.n).foldl dsAddVStep
        { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }).E = emptyH.E := by
      have h1 := congrArg MGraph.E (mem_empty_foldl_vStep (vL := vL) G.n ∅ 0)
      exact h1
    exact ⟨dynGraphAt_congr hVeq hEeq (fun _ he => by rw [hEeq] at he; cases he) hG_final,
      hregs, hr6, hr7, hr10, hr12, hfr⟩


end

end MinCostFlow.DynSpanner.Program
