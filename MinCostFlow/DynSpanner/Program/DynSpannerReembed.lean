module

public import MinCostFlow.DynSpanner.Program.DynSpannerProjDefs
public import MinCostFlow.DynSpanner.Program.EmbPrefix
public import MinCostFlow.DynSpanner.Program.StateLayout
import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
import MinCostFlow.DynSpanner.Walks
import WordRAM.Tactic

/-!
# The re-embedding of one affected edge

Algorithm 6 (line 85) re-embeds an affected edge `e` with old walk `P = Π_{<j}(e)` from
`a = tail e` to `b = head e` as `Π_j(e) = W₁ ++ M ++ walkRev W₂`. Here `W₁ = Π_{<j}(e)[a, â]` and
`W₂` are the two walks of the projection (see `DynSpannerProjDefs.lean`), and `M` is the walk of
the projected edge in the new sparsifier, already mapped back to `H_{<j} ∪ E_affected`
(`embMid e`). The result is `reembedWalk G H embLt embMid S e` when `P = embLt e`,
`M = embMid e`, `a = G.tail e` and `b = G.head e` (`reembedEdgeWalk_eq_reembedWalk`).

The procedure `dsReembedEdgeStmt` computes `W₁` and `W₂` again, by two prefix walks, reverses
`W₂` and concatenates. Its scratch area has `10 · |P| + 2 · |M| + 10` words, computed at run time
from the length words of `P` and `M`. The proof `dsReembedEdge_meetsContract` follows the one of
`dsProjEdge_meetsContract`: each call writes a block of the scratch area that the later calls do
not touch.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- Re-embedding of one edge (`args = [gPtr, a, b, wPtr, midPtr, sBitPtr, scr, out]`). Writes
`W₁ ++ M ++ walkRev W₂` at `out` and returns the first address after it. -/
def dsReembedEdgeStmt (bEmb : ℕ) : Stmt :=
  .assign 8 (.load (.reg 3)) ;;
  .assign 9 (.bin .add (.bin .add (.reg 8) (.reg 8)) (.const 1)) ;;
  .assign 10 (.bin .add (.reg 6) (.reg 9)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 9)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 9)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 9)) ;;
  .call 14 (bEmb + embIdxWalkPrefix) [.reg 0, .reg 1, .reg 3, .reg 5, .reg 6] ;;
  .call 15 (bEmb + embIdxWalkRev) [.reg 3, .reg 10] ;;
  .call 15 (bEmb + embIdxWalkPrefix) [.reg 0, .reg 2, .reg 10, .reg 5, .reg 11] ;;
  .call 15 (bEmb + embIdxWalkRev) [.reg 11, .reg 12] ;;
  .call 15 (bEmb + embIdxWalkConcat) [.reg 6, .reg 4, .reg 13] ;;
  .call 15 (bEmb + embIdxWalkConcat) [.reg 13, .reg 12, .reg 7] ;;
  .ret (.reg 15)

/-- The procedures of the re-embedding module. -/
def reembedProcs (bEmb : ℕ) : List Stmt :=
  [dsReembedEdgeStmt bEmb]

def reembedIdxEdge : ℕ := 0

lemma reembedProcs_noRand (bEmb : ℕ) : ∀ s ∈ reembedProcs bEmb, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The walk `W₁ ++ M ++ walkRev W₂` written by `dsReembedEdgeStmt`. -/
def reembedEdgeWalk (H : MGraph) (a b : ℕ) (P M : List (ℕ × Bool)) (S : Finset ℕ) :
    List (ℕ × Bool) :=
  (prefixWalk H a P S).2 ++ M ++ walkRev (prefixWalk H b (walkRev P) S).2

/-- With `P = embLt e`, `M = embMid e`, `a = G.tail e` and `b = G.head e`, the walk written by
`dsReembedEdgeStmt` is `reembedWalk G H embLt embMid S e` (Algorithm 6, line 85). -/
lemma reembedEdgeWalk_eq_reembedWalk (G H : MGraph) (embLt embMid : Embedding) (S : Finset ℕ)
    (e : ℕ) :
    reembedEdgeWalk H (G.tail e) (G.head e) (embLt e) (embMid e) S =
      reembedWalk G H embLt embMid S e := rfl

/-- Contract of `dsReembedEdgeStmt` for the walk `P` from `a` to `b` in `H`, the middle walk `M`
and the set `S`. The caller gives a scratch area of `10 · |P| + 2 · |M| + 10` words at `scr` and
an output area of `4 · |P| + 2 · |M| + 5` words at `out`. -/
def dsReembedEdgeContract (w vCap eCap : ℕ) (H : MGraph) (a b : ℕ) (P M : List (ℕ × Bool))
    (S : Finset ℕ) : Contract where
  pre args mem := ∃ gPtr wPtr midPtr sBitPtr scr out,
    args = [gPtr, a, b, wPtr, midPtr, sBitPtr, scr, out] ∧ 16 ≤ 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ wPtr + (2 * P.length + 1) < 2 ^ w ∧
    midPtr + (2 * M.length + 1) < 2 ^ w ∧ sBitPtr + vCap < 2 ^ w ∧
    scr + (10 * P.length + 2 * M.length + 10) < 2 ^ w ∧
    out + (4 * P.length + 2 * M.length + 5) < 2 ^ w ∧
    IvlDisj scr (10 * P.length + 2 * M.length + 10) out (4 * P.length + 2 * M.length + 5) ∧
    IvlDisj scr (10 * P.length + 2 * M.length + 10) gPtr (dynGraphSize vCap eCap) ∧
    IvlDisj scr (10 * P.length + 2 * M.length + 10) wPtr (2 * P.length + 1) ∧
    IvlDisj scr (10 * P.length + 2 * M.length + 10) midPtr (2 * M.length + 1) ∧
    IvlDisj scr (10 * P.length + 2 * M.length + 10) sBitPtr vCap ∧
    IvlDisj out (4 * P.length + 2 * M.length + 5) midPtr (2 * M.length + 1) ∧
    DynGraphAt mem gPtr vCap eCap H ∧ H.IsValid ∧ (∀ v ∈ H.V, v < vCap) ∧
    (∀ e ∈ H.E, e < eCap) ∧ a ∈ H.V ∧ b ∈ H.V ∧ PrefixWalksValid H S eCap a b P ∧ MWalkAt mem wPtr P ∧
    MWalkAt mem midPtr M ∧ (∀ x ∈ M, x.1 < eCap) ∧
    (∀ v < vCap, mem (sBitPtr + v) = if v ∈ S then 1 else 0)
  post args mem ret mem' := ∃ gPtr wPtr midPtr sBitPtr scr out,
    args = [gPtr, a, b, wPtr, midPtr, sBitPtr, scr, out] ∧
    MWalkAt mem' out (reembedEdgeWalk H a b P M S) ∧
    ret = out + (2 * (reembedEdgeWalk H a b P M S).length + 1) ∧
    ∀ addr, (addr < scr ∨ scr + (10 * P.length + 2 * M.length + 10) ≤ addr) →
      (addr < out ∨ out + (2 * (reembedEdgeWalk H a b P M S).length + 1) ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 800 * (P.length + M.length) + 800

end

private lemma reembedEdgeWalk_length (H : MGraph) (a b : ℕ) (P M : List (ℕ × Bool))
    (S : Finset ℕ) :
    (reembedEdgeWalk H a b P M S).length =
      (prefixWalk H a P S).2.length + M.length + (prefixWalk H b (walkRev P) S).2.length := by
  simp [reembedEdgeWalk, walkRev_length]; omega

public section

/-- `dsReembedEdgeStmt` meets `dsReembedEdgeContract`: it writes `reembedEdgeWalk H a b P M S`
at `out`, in time `800 · (|P| + |M|) + 800`. -/
theorem dsReembedEdge_meetsContract {w vCap eCap : ℕ} {p : Program} {bRe bEmb bOps : ℕ}
    {H : MGraph} {a b : ℕ} {P M : List (ℕ × Bool)} {S : Finset ℕ}
    (hpRe : p.HasAt bRe (reembedProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bRe + reembedIdxEdge) (dsReembedEdgeContract w vCap eCap H a b P M S) := by
  refine meetsContract_of_runs
    (hpRe.get (i := reembedIdxEdge) (by simp [reembedProcs, reembedIdxEdge])) ?_
  rintro args mem pos ω hargs ⟨gPtr, wPtr, midPtr, sBitPtr, scr, out, rfl, hw16, hgB, hwB, hmB,
    hsB, hscrB, houtB, dSO, dSG, dSW, dSM, dSS, dOM, hG, hHv, hVc, hEc, haV, hbV, hPw, hWat,
    hMat, hMe, hsBit⟩
  simp only [reembedProcs, reembedIdxEdge, List.getElem_cons_zero]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargs
  obtain ⟨hgw, haw, hbw, hww, hmw, hsw, hscrw, houtw⟩ := hargs
  have heCap_w : eCap < 2 ^ w := by
    have : eCap ≤ dynGraphSize vCap eCap := by simp only [dynGraphSize]; omega
    omega
  have hPe : ∀ x ∈ P, x.1 < 2 ^ w := fun x hx =>
    lt_trans (hPw.2.2 x hx) heCap_w
  have hMe' : ∀ x ∈ M, x.1 < 2 ^ w := fun x hx => lt_trans (hMe x hx) heCap_w
  have hl1 : (prefixWalk H a P S).2.length ≤ P.length := prefixWalk_snd_length_le H S a P
  have hl2 : (prefixWalk H b (walkRev P) S).2.length ≤ P.length := by
    have := prefixWalk_snd_length_le H S b (walkRev P); rwa [walkRev_length] at this
  have hrevn : (walkRev P).length = P.length := walkRev_length P
  have hRW₂len : (walkRev (prefixWalk H b (walkRev P) S).2).length =
      (prefixWalk H b (walkRev P) S).2.length := walkRev_length _
  have hW₁e : ∀ x ∈ (prefixWalk H a P S).2, x.1 < 2 ^ w := fun x hx =>
    hPe x (prefixWalk_snd_mem H S a P x hx)
  have hW₂e : ∀ x ∈ (prefixWalk H b (walkRev P) S).2, x.1 < 2 ^ w := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_walkRev_fst (prefixWalk_snd_mem H S b (walkRev P) x hx)
    rw [← hxy]; exact hPe y hy
  have hRW₂e : ∀ x ∈ walkRev (prefixWalk H b (walkRev P) S).2, x.1 < 2 ^ w := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_walkRev_fst hx
    rw [← hxy]; exact hW₂e y hy
  have hmn : mem wPtr = P.length := MWalkAt_head hWat
  dsimp only [dsReembedEdgeStmt]
  refine runs_start_le ?_
  -- Address computations.
  refine runs_seq_assign_le (v := P.length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hmn) ?_
  iterate 5 wram_step
  -- Call 1: `W₁` at `scr`.
  refine runs_seq_call_le (mWalkPrefix_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
      (H := H) (uStart := a) (vEnd := b) (W := P) (S := S) hpEmb hpOps)
    (by eval_expr) (by wram_words)
    ⟨gPtr, wPtr, sBitPtr, scr, rfl, hw16, hgB, hwB, hsB, by omega,
      dSW.or_sub (Nat.le_refl _) (by omega), dSS.pts_sub (Nat.le_refl _) (by omega),
      dSG.pts_sub (Nat.le_refl _) (by omega), hG, hHv, hVc, hEc, haV, hPw.1, hWat, hsBit⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨_, _, _, _, hargs₁, -, hW₁at, hfr₁⟩
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
  -- Call 3: `W₂` at `scr + 2B`.
  refine runs_seq_call_le (mWalkPrefix_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
      (H := H) (uStart := b) (vEnd := a) (W := walkRev P) (S := S) hpEmb hpOps)
    (by eval_expr) (by wram_words)
    ⟨_, _, _, _, rfl, hw16, hgB, by omega, hsB, by omega, Or.inl (by omega),
      dSS.pts_sub (by omega) (by omega), dSG.pts_sub (by omega) (by omega),
      hG₂, hHv, hVc, hEc, hbV, hPw.2.1, hRevAt, hsBit₂⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨_, _, _, _, hargs₃, -, hW₂at, hfr₃⟩
  simp only [List.cons.injEq, and_true] at hargs₃
  obtain ⟨rfl, -, rfl, rfl, rfl⟩ := hargs₃
  -- Call 4: `walkRev W₂` at `scr + 3B`.
  refine runs_seq_call_le (mWalkRev_meetsContract (w := w)
      (P := (prefixWalk H b (walkRev P) S).2) hpEmb)
    (by eval_expr) (by wram_words)
    ⟨_, _, rfl, hw16, by omega, by omega, Or.inl (by omega), hW₂e, hW₂at⟩ ?_
  rintro v₄ mem₄ pos₄ ⟨_, _, hargs₄, -, hRW₂at, hfr₄⟩
  simp only [List.cons.injEq, and_true] at hargs₄
  obtain ⟨rfl, rfl⟩ := hargs₄
  -- Call 5: `W₁ ++ M` at `scr + 4B`.
  have hM₄ : MWalkAt mem₄ midPtr M :=
    MWalkAt.of_frame (MWalkAt.of_frame (MWalkAt.of_frame (MWalkAt.of_frame hMat hfr₁
      (dSM.or_sub (Nat.le_refl _) (by omega))) hfr₂ (dSM.or_sub (by omega) (by omega))) hfr₃
      (dSM.or_sub (by omega) (by omega))) hfr₄ (dSM.or_sub (by omega) (by omega))
  have hW₁₄ : MWalkAt mem₄ scr (prefixWalk H a P S).2 :=
    MWalkAt.of_frame (MWalkAt.of_frame (MWalkAt.of_frame hW₁at hfr₂ (Or.inl (by omega))) hfr₃
      (Or.inl (by omega))) hfr₄ (Or.inl (by omega))
  refine runs_seq_call_le (mWalkConcat_meetsContract (w := w)
      (P := (prefixWalk H a P S).2) (Q := M) hpEmb)
    (by eval_expr) (by wram_words)
    ⟨_, _, _, rfl, hw16, by omega, hmB, by omega, Or.inl (by omega),
      dSM.or_sub (by omega) (by omega), hW₁e, hMe', hW₁₄, hM₄⟩ ?_
  rintro v₅ mem₅ pos₅ ⟨_, _, _, hargs₅, -, hCatAt, hfr₅⟩
  simp only [List.cons.injEq, and_true] at hargs₅
  obtain ⟨rfl, rfl, rfl⟩ := hargs₅
  -- Call 6: the final walk at `out`.
  have hCatLen : ((prefixWalk H a P S).2 ++ M).length = (prefixWalk H a P S).2.length + M.length :=
    List.length_append
  have hCatE : ∀ x ∈ (prefixWalk H a P S).2 ++ M, x.1 < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hW₁e x hx
    · exact hMe' x hx
  refine runs_seq_call_le (mWalkConcat_meetsContract (w := w)
      (P := (prefixWalk H a P S).2 ++ M)
      (Q := walkRev (prefixWalk H b (walkRev P) S).2) hpEmb)
    (by eval_expr) (by wram_words)
    ⟨_, _, _, rfl, hw16, by rw [hCatLen]; omega, by rw [hRW₂len]; omega,
      by rw [hCatLen, hRW₂len]; omega,
      by rw [hCatLen, hRW₂len]; unfold IvlDisj at dSO; omega,
      by rw [hCatLen, hRW₂len]; unfold IvlDisj at dSO; omega,
      hCatE, hRW₂e, hCatAt,
      MWalkAt.of_frame hRW₂at hfr₅ (Or.inl (by rw [hRW₂len]; omega))⟩ ?_
  rintro v₆ mem₆ pos₆ ⟨_, _, _, hargs₆, hret₆, hFinAt, hfr₆⟩
  simp only [List.cons.injEq, and_true] at hargs₆
  obtain ⟨rfl, rfl, rfl⟩ := hargs₆
  rw [hCatLen, hRW₂len] at hret₆ hfr₆
  have hWlen := reembedEdgeWalk_length H a b P M S
  refine runs_ret_le (v := v₆) (Expr.eval_reg_of_eq (by simp))
    ⟨gPtr, wPtr, midPtr, sBitPtr, scr, out, rfl, hFinAt, ?_, ?_⟩ ?_
  · show v₆ = _
    omega
  · intro addr ha hb
    rw [hWlen] at hb
    refine (hfr₆ addr (by omega)).trans ?_
    refine (hfr₅ addr (by omega)).trans ?_
    exact (hfr₄ addr (by omega)).trans ((hfr₃ addr (by omega)).trans
      ((hfr₂ addr (by omega)).trans (hfr₁ addr (by omega))))
  · simp only [dsReembedEdgeContract, mWalkPrefixContract, mWalkRevContract, mWalkConcatContract,
      Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil,
      List.length_append, hRW₂len, hrevn]
    omega

end

end MinCostFlow.DynSpanner.Program
