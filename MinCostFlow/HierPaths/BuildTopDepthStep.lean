module

public import MinCostFlow.HierPaths.BuildTopDepth

/-!
# One iteration of the parent scan

The reply directory stores the current heap pointer before the call.
The level contract preserves that cell and the other cells in the prefix.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited

/-- Run the parent call and leave its certified reply at the address in the directory. -/
theorem buildTopDepthBody_triple {w K call i gdir out base s k M r Δ L L' bh h ga : ℕ}
    {G : Graph} {p : Program} {st : State}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hc : MeetsContract w p call (buildTopParentCallContract w K space G (i * (s * k))
      s k M r Δ L L' bh))
    (h0 : st.regs 0 = gdir) (h1 : st.regs 1 = out) (h2 : st.regs 2 = base)
    (h3 : st.regs 3 = s) (h4 : st.regs 4 = k)
    (h6 : st.regs 6 = M) (h7 : st.regs 7 = r) (h8 : st.regs 8 = Δ)
    (h9 : st.regs 9 = L) (h10 : st.regs 10 = L') (h11 : st.regs 11 = bh)
    (h12 : st.regs 12 = h) (hi : st.regs 13 = i) (h15 : st.regs 15 = s * k)
    (hread : st.mem (gdir + i) = ga) (hsep : gdir + i ≠ out + i)
    (hpref : out + i < h) (hgword : gdir + i < 2 ^ w) (hdword : out + i < 2 ^ w)
    (hwords : ∀ v ∈ buildLevelArgs ga base (i * (s * k)) s k M r Δ L L' bh h, v < 2 ^ w)
    (hpre : (buildTopParentCallContract w K space G (i * (s * k)) s k M r Δ L L' bh).pre
      (buildLevelArgs ga base (i * (s * k)) s k M r Δ L L' bh h)
      (Function.update st.mem (out + i) h)) :
    Triple w p (fun t => t = st) (buildTopDepthBody call)
      (normalPost fun t =>
        (∀ j, j ≠ 12 → j ≠ 14 → t.regs j = st.regs j) ∧
        t.mem (out + i) = h ∧
        (buildLevelContract w K space G (i * (s * k)) s k M r Δ L L' bh).post
          (buildLevelArgs ga (base + i * (s * k)) (i * (s * k)) s k M r Δ L L' bh h)
          (Function.update st.mem (out + i) h) (t.regs 12) t.mem)
      (fun _ => buildLevelCost K G s k M r Δ L L' bh + 60) := by
  intro t ω ht
  subst t
  let start := i * (s * k)
  have hs : start < 2 ^ w := hwords _ (by simp [buildLevelArgs, start])
  refine runs_start_le ?_
  unfold buildTopDepthBody
  refine runs_seq_assign_le (v := start) (Expr.eval_mul (Expr.eval_reg_of_eq hi)
    (Expr.eval_reg_of_eq h15) hs) ?_
  refine runs_seq_store_le (x := out + i) (v := h) (Expr.eval_add
    (Expr.eval_reg_of_eq (r := 1) (by simpa using h1))
    (Expr.eval_reg_of_eq (r := 13) (by simpa using hi)) hdword)
    (Expr.eval_reg_of_eq (r := 12) (by simpa using h12)) ?_
  refine runs_call_le hc
    (vs := buildLevelArgs ga base start s k M r Δ L L' bh h) ?_ hwords hpre ?_
  · simp [evalArgs, Expr.eval, buildLevelArgs, BinOp.eval, h0, hi, hgword, hread,
      hsep, Ne.symm hsep, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12]
    exact (Function.update_of_ne hsep _ _).trans hread
  intro v mem' pos' hpost
  obtain ⟨ga', base', h', ha, hpost⟩ := hpost
  simp only [buildLevelArgs, start, List.cons.injEq, and_true, true_and] at ha
  obtain ⟨_, _, _⟩ := ha
  subst ga' base' h'
  have hf := hpost.1.2.2.1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro j hj hj'
    simp [Function.update_of_ne hj, Function.update_of_ne hj']
  · have he : heapArg (buildLevelArgs ga (base + start) start s k M r Δ L L' bh h) = h := by
      simp [heapArg, buildLevelArgs]
    exact (hf _ (he ▸ hpref)).trans (Function.update_self ..)
  · simpa using hpost
  · simp [buildTopParentCallContract, Expr.size, argsSize]; omega

/-- Accumulate the parent-step triples across a depth. The invariant can
retain the existential reply from each call and the directory of replies. -/
theorem buildTopDepth_runs {w call count s k : ℕ} {p : Program} {st : State}
    {I : ℕ → State → Prop} {cost : ℕ → ℕ} (ω : ℕ → Bool)
    (hs : st.regs 3 = s) (hk : st.regs 4 = k)
    (hsk : s * k < 2 ^ w) (hc : count < 2 ^ w) (hword : 1 < 2 ^ w)
    (hinit : I 0 {st with regs := Function.update (Function.update st.regs 15 (s * k)) 13 0})
    (hidx : ∀ i ≤ count, ∀ t, I i t → t.regs 13 = i)
    (hlen : ∀ i ≤ count, ∀ t, I i t → t.regs 5 = count)
    (hstep : ∀ i < count, Triple w p (I i) (buildTopDepthBody call)
      (normalPost fun t => I (i + 1) {t with regs := Function.update t.regs 13 (i + 1)} ∧
        t.regs 13 = i)
      (fun _ => cost i)) :
    ∃ v t c, Runs w p ω (buildTopDepth call) st (.returned v) t c ∧
      I count t ∧ v = t.regs 12 ∧ c ≤ rangeCost cost 0 count + 9 * count + 20 := by
  have hlo := Triple.forRange_le (w := w) (p := p) (r := 13) (lo := .const 0)
    (hi := .reg 5) (body := buildTopDepthBody call)
    (P := fun t => t = {st with regs := Function.update st.regs 15 (s * k)})
    (Inv := I) cost 0 count (Nat.zero_le _) hword (fun _ => hc)
    (fun t ht => by subst t; exact ⟨Expr.eval_const (Nat.two_pow_pos w), hinit⟩)
    (fun i t _ hi h => hidx i hi t h)
    (fun i t _ hi h => Expr.eval_reg_of_eq (hlen i hi t h))
    (fun i _ hi => hstep i hi)
  have hr : ∃ o t c, Runs w p ω (buildTopDepth call) st o t c ∧
      (o = .returned (t.regs 12) ∧ I count t) ∧ c ≤ rangeCost cost 0 count + 9 * count + 20 := by
    unfold buildTopDepth
    refine runs_start_le ?_
    refine runs_seq_assign_le (Expr.eval_mul (Expr.eval_reg_of_eq hs)
      (Expr.eval_reg_of_eq hk) hsk) ?_
    refine runs_seq_triple_le hlo rfl ?_
    intro t ht
    refine runs_ret_le (v := t.regs 12) (Expr.eval_reg_of_eq rfl) ⟨rfl, ht⟩ ?_
    simp [Expr.size]
    omega
  obtain ⟨o, t, c, ho, ⟨he, ht⟩, hc'⟩ := hr
  exact ⟨t.regs 12, t, c, he ▸ ho, ht, rfl, hc'⟩

end MinCostFlow.HierPaths

end
