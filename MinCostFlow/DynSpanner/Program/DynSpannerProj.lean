module

public import MinCostFlow.DynSpanner.Program.DynSpannerProjDefs
import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
public import MinCostFlow.DynSpanner.Program.EmbPrefix
public import MinCostFlow.DynSpanner.Program.StateLayout
import MinCostFlow.DynSpanner.Walks
import WordRAM.Tactic

/-!
# The projection of one affected edge: proof

`dsProjEdge_meetsContract` proves that `dsProjEdgeStmt` meets `dsProjEdgeContract`. The proof runs
the eight address computations and then the six calls in order. Each call writes one block of the
scratch area (or the output area), and the blocks are placed one after the other:

* `scr`: `W₁ = Π_{<j}(e)[a, â]` (at most `2|P| + 1` words),
* `scr + B`: `walkRev P` (`B = 2|P| + 1` words),
* `scr + 2B`: `W₂`,
* `scr + 3B`: `walkRev W₁`,
* `scr + 4B`: the one-edge walk `[(e, true)]` (three words),
* `scr + 4B + 3`: `walkRev W₁ ++ [(e, true)]`,
* `out + 2`: the final walk.

A walk written by an earlier call stays in memory because every later call writes a block
disjoint from it (lemma `MWalkAt.of_frame`). The cost is the sum of the costs of the six calls
plus a constant; each call costs at most `180 · |P| + 80`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

private lemma projEdgeWalk_length (H : MGraph) (e a b : ℕ) (P : List (ℕ × Bool)) (S : Finset ℕ) :
    (projEdgeWalk H e a b P S).length =
      (prefixWalk H a P S).2.length + 1 + (prefixWalk H b (walkRev P) S).2.length := by
  simp [projEdgeWalk, walkRev_length]; omega

private lemma mWalkAt_single {mem : ℕ → ℕ} {x e : ℕ} (h0 : mem x = 1) (h1 : mem (x + 1) = e)
    (h2 : mem (x + 2) = 1) : MWalkAt mem x [(e, true)] := by
  intro i hi
  simp only [mWalkEncode, List.length_cons, List.length_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, ite_true] at hi ⊢
  rcases i with _ | _ | _ | i
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · omega

public section

set_option maxHeartbeats 1000000 in
/-- `dsProjEdgeStmt` meets `dsProjEdgeContract`: it writes the endpoints `â`, `b̂` of the
projection of the walk `P` onto `S` and the walk `projEdgeWalk H e a b P S`, in time
`800 · |P| + 800`. -/
theorem dsProjEdge_meetsContract {w vCap eCap : ℕ} {p : Program} {bProj bEmb bOps : ℕ}
    {H : MGraph} {e a b : ℕ} {P : List (ℕ × Bool)} {S : Finset ℕ}
    (hpProj : p.HasAt bProj (projProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bProj + projIdxEdge) (dsProjEdgeContract w vCap eCap H e a b P S) := by
  refine meetsContract_of_runs (hpProj.get (i := projIdxEdge) (by simp [projProcs, projIdxEdge])) ?_
  rintro args mem pos ω hargs ⟨gPtr, wPtr, sBitPtr, scr, out, rfl, hw16, hgB, hwB, hsB, hscrB,
    houtB, dSO, dSG, dSW, dSS, dOG, dOW, dOS, hG, hHv, hVc, hEc, haV, hbV, hPw, hWat, hsBit⟩
  simp only [projProcs, projIdxEdge, List.getElem_cons_zero]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargs
  obtain ⟨hgw, he_w, haw, hbw, hww, hsw, hscrw, houtw⟩ := hargs
  have heCap_w : eCap < 2 ^ w := by
    have : eCap ≤ dynGraphSize vCap eCap := by simp only [dynGraphSize]; omega
    omega
  have hPe : ∀ x ∈ P, x.1 < 2 ^ w := fun x hx =>
    lt_trans (hPw.2.2 x hx) heCap_w
  have hl1 : (prefixWalk H a P S).2.length ≤ P.length := prefixWalk_snd_length_le H S a P
  have hl2 : (prefixWalk H b (walkRev P) S).2.length ≤ P.length := by
    have := prefixWalk_snd_length_le H S b (walkRev P); rwa [walkRev_length] at this
  have hrevn : (walkRev P).length = P.length := walkRev_length P
  have hW₁e : ∀ x ∈ (prefixWalk H a P S).2, x.1 < 2 ^ w := fun x hx =>
    hPe x (prefixWalk_snd_mem H S a P x hx)
  have hW₂e : ∀ x ∈ (prefixWalk H b (walkRev P) S).2, x.1 < 2 ^ w := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_walkRev_fst (prefixWalk_snd_mem H S b (walkRev P) x hx)
    rw [← hxy]; exact hPe y hy
  have hmn : mem wPtr = P.length := MWalkAt_head hWat
  dsimp only [dsProjEdgeStmt]
  refine runs_start_le ?_
  -- Address computations.
  refine runs_seq_assign_le (v := P.length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hmn) ?_
  iterate 7 wram_step
  -- Call 1: `W₁` at `scr`, `â` in register 15.
  refine runs_seq_call_le (mWalkPrefix_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
      (H := H) (uStart := a) (vEnd := b) (W := P) (S := S) hpEmb hpOps)
    (by eval_expr) (by wram_words)
    ⟨gPtr, wPtr, sBitPtr, scr, rfl, hw16, hgB, hwB, hsB, by omega,
      dSW.or_sub (Nat.le_refl _) (by omega), dSS.pts_sub (Nat.le_refl _) (by omega),
      dSG.pts_sub (Nat.le_refl _) (by omega), hG, hHv, hVc, hEc, haV, hPw.1, hWat, hsBit⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨_, _, _, _, hargs₁, hv₁, hW₁at, hfr₁⟩
  simp only [List.cons.injEq, and_true] at hargs₁
  obtain ⟨rfl, -, rfl, rfl, rfl⟩ := hargs₁
  have hG₁ : DynGraphAt mem₁ gPtr vCap eCap H := dynGraphAt_of_agree hG fun addr h1 h2 =>
    hfr₁ addr (dSG.addr_sub (Nat.le_refl _) (by omega) addr h1 h2)
  -- Call 2: `walkRev P` at `scr + B`.
  refine runs_seq_call_le (mWalkRev_meetsContract (w := w) (P := P) hpEmb)
    (by eval_expr) (by wram_words)
    ⟨_, _, rfl, hw16, by omega, by omega, dSW.or_sub (by omega) (by omega), hPe,
      MWalkAt.of_frame hWat hfr₁ (dSW.or_sub (Nat.le_refl _) (by omega))⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨_, _, hargs₂, -, hRevAt, hfr₂⟩
  simp only [List.cons.injEq, and_true] at hargs₂
  obtain ⟨rfl, rfl⟩ := hargs₂
  have hG₂ : DynGraphAt mem₂ gPtr vCap eCap H := dynGraphAt_of_agree hG₁ fun addr h1 h2 =>
    hfr₂ addr (dSG.addr_sub (by omega) (by omega) addr h1 h2)
  have hsBit₂ : ∀ v < vCap, mem₂ (sBitPtr + v) = if v ∈ S then 1 else 0 := fun v hv =>
    (hfr₂ _ (dSS.pts_sub (by omega) (by omega) v hv)).trans
      ((hfr₁ _ (dSS.pts_sub (Nat.le_refl _) (by omega) v hv)).trans (hsBit v hv))
  -- Call 3: `W₂` at `scr + 2B`, `b̂` in register 16.
  refine runs_seq_call_le (mWalkPrefix_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
      (H := H) (uStart := b) (vEnd := a) (W := walkRev P) (S := S) hpEmb hpOps)
    (by eval_expr) (by wram_words)
    ⟨_, _, _, _, rfl, hw16, hgB, by omega, hsB, by omega, Or.inl (by omega),
      dSS.pts_sub (by omega) (by omega), dSG.pts_sub (by omega) (by omega),
      hG₂, hHv, hVc, hEc, hbV, hPw.2.1, hRevAt, hsBit₂⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨_, _, _, _, hargs₃, hv₃, hW₂at, hfr₃⟩
  simp only [List.cons.injEq, and_true] at hargs₃
  obtain ⟨rfl, -, rfl, rfl, rfl⟩ := hargs₃
  -- Call 4: `walkRev W₁` at `scr + 3B`.
  refine runs_seq_call_le (mWalkRev_meetsContract (w := w) (P := (prefixWalk H a P S).2) hpEmb)
    (by eval_expr) (by wram_words)
    ⟨_, _, rfl, hw16, by omega, by omega, Or.inl (by omega), hW₁e,
      MWalkAt.of_frame (MWalkAt.of_frame hW₁at hfr₂ (Or.inl (by omega))) hfr₃
        (Or.inl (by omega))⟩ ?_
  rintro v₄ mem₄ pos₄ ⟨_, _, hargs₄, -, hRW₁at, hfr₄⟩
  simp only [List.cons.injEq, and_true] at hargs₄
  obtain ⟨rfl, rfl⟩ := hargs₄
  -- The one-edge walk `[(e, true)]` at `scr + 4B`.
  iterate 3 wram_step
  -- Call 6: `walkRev W₁ ++ [(e, true)]` at `scr + 4B + 3`.
  have hRW₁e : ∀ x ∈ walkRev (prefixWalk H a P S).2, x.1 < 2 ^ w := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_walkRev_fst hx
    rw [← hxy]; exact hW₁e y hy
  have hRW₁len : (walkRev (prefixWalk H a P S).2).length = (prefixWalk H a P S).2.length :=
    walkRev_length _
  refine runs_seq_call_le (mWalkConcat_meetsContract (w := w)
      (P := walkRev (prefixWalk H a P S).2) (Q := [(e, true)]) hpEmb)
    (by eval_expr) (by wram_words)
    ⟨_, _, _, rfl, hw16, by rw [hRW₁len]; omega,
      by simp only [List.length_cons, List.length_nil]; omega,
      by simp only [List.length_cons, List.length_nil, hRW₁len]; omega,
      Or.inl (by rw [hRW₁len]; omega),
      Or.inl (by simp only [List.length_cons, List.length_nil]; omega),
      hRW₁e, by simpa using he_w,
      hRW₁at.of_agree (fun addr h1 h2 => by
        simp only [Function.update_apply]
        split_ifs <;> first | rfl | omega),
      mWalkAt_single (by simp) (by simp) (by simp)⟩ ?_
  rintro v₆ mem₆ pos₆ ⟨_, _, _, hargs₆, -, hCatAt, hfr₆⟩
  simp only [List.cons.injEq, and_true] at hargs₆
  obtain ⟨rfl, rfl, rfl⟩ := hargs₆
  -- The endpoints `â`, `b̂` at `out`, `out + 1`.
  iterate 2 wram_step
  -- Call 8: the final walk at `out + 2`.
  have hCatLen : (walkRev (prefixWalk H a P S).2 ++ [(e, true)]).length =
      (prefixWalk H a P S).2.length + 1 := by
    simp only [List.length_append, hRW₁len, List.length_cons, List.length_nil]
  have hCatE : ∀ x ∈ walkRev (prefixWalk H a P S).2 ++ [(e, true)], x.1 < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hRW₁e x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; exact he_w
  refine runs_seq_call_le (mWalkConcat_meetsContract (w := w)
      (P := walkRev (prefixWalk H a P S).2 ++ [(e, true)])
      (Q := (prefixWalk H b (walkRev P) S).2) hpEmb)
    (by eval_expr) (by wram_words)
    ⟨_, _, _, rfl, hw16, by rw [hCatLen]; omega, by omega, by rw [hCatLen]; omega,
      by rw [hCatLen]; unfold IvlDisj at dSO; omega,
      by unfold IvlDisj at dSO; omega,
      hCatE, hW₂e,
      hCatAt.of_agree (fun addr h1 h2 => by
        rw [hCatLen] at h2
        unfold IvlDisj at dSO
        simp only [Function.update_apply]
        split_ifs <;> first | rfl | omega),
      hW₂at.of_agree (fun addr h1 h2 => by
        unfold IvlDisj at dSO
        simp only [Function.update_apply]
        split_ifs <;> first | omega | skip
        refine (hfr₆ addr (by simp only [hRW₁len, List.length_cons, List.length_nil]; omega)).trans ?_
        simp only [Function.update_apply]
        split_ifs <;> first | omega | skip
        exact hfr₄ addr (by omega))⟩ ?_
  rintro v₈ mem₈ pos₈ ⟨_, _, _, hargs₈, hret₈, hFinAt, hfr₈⟩
  simp only [List.cons.injEq, and_true] at hargs₈
  obtain ⟨rfl, rfl, rfl⟩ := hargs₈
  rw [hCatLen] at hret₈ hfr₈
  have hWlen := projEdgeWalk_length H e a b P S
  refine runs_ret_le (v := v₈) (Expr.eval_reg_of_eq (by simp))
    ⟨gPtr, wPtr, sBitPtr, scr, out, rfl, ?_, ?_, hFinAt, ?_, ?_⟩ ?_
  · refine (hfr₈ out (Or.inl (by omega))).trans ?_
    simp [hv₁]
  · refine (hfr₈ (out + 1) (Or.inl (by omega))).trans ?_
    simp [hv₃]
  · show v₈ = _
    omega
  · intro addr ha hb
    rw [hWlen] at hb
    unfold IvlDisj at dSO
    refine (hfr₈ addr (by omega)).trans ?_
    simp only [Function.update_apply]
    split_ifs <;> first | omega | skip
    refine (hfr₆ addr (by simp only [hRW₁len, List.length_cons, List.length_nil]; omega)).trans ?_
    simp only [Function.update_apply]
    split_ifs <;> first | omega | skip
    exact (hfr₄ addr (by omega)).trans ((hfr₃ addr (by omega)).trans
      ((hfr₂ addr (by omega)).trans (hfr₁ addr (by omega))))
  · simp only [dsProjEdgeContract, mWalkPrefixContract, mWalkRevContract, mWalkConcatContract,
      Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil,
      List.length_append, List.length_cons, List.length_nil, hRW₁len, hrevn]
    omega

end

end MinCostFlow.DynSpanner.Program
