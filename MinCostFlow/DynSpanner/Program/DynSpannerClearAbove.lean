module

public import MinCostFlow.DynSpanner.Program.DynSpannerZeroRange
public import MinCostFlow.DynSpanner.Program.DynSpannerStepEmpty
import WordRAM.Tactic

/-!
# Emptying the levels above `j`

After a rebuild of level `j`, the levels above `j` are empty, and the set `S_j` is empty too
(`step` sets `S_i := ∅` for `i ≥ j`). The program empties them in `O(L)` time by writing `0` to
the generation words `domGen[i]` for `i > j` and `sGen[i]` for `i ≥ j`: with the generation word
`0`, no edge stamp and no vertex stamp is current, so the level is empty
(`levelDom_of_gen_zero`, `levelS_of_gen_zero` in `DynSpannerStepEmpty.lean`). `dsClearAboveStmt`
makes the two calls of `dsZeroRangeStmt` (`dsClearAbove_meetsContract`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [domGenBase, sGenBase, dLo, sLo, hi]`: write `0` to `domGen[i]` for
`dLo ≤ i < hi` and to `sGen[i]` for `sLo ≤ i < hi`. -/
def dsClearAboveStmt (bZ : ℕ) : Stmt :=
  .call 5 (bZ + zeroRangeIdx) [.reg 0, .reg 2, .reg 4] ;;
  .call 5 (bZ + zeroRangeIdx) [.reg 1, .reg 3, .reg 4] ;;
  .ret (.const 0)

def clearAboveProcs (bZ : ℕ) : List Stmt := [dsClearAboveStmt bZ]

def clearAboveIdx : ℕ := 0

lemma clearAboveProcs_noRand (bZ : ℕ) : ∀ s ∈ clearAboveProcs bZ, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsClearAboveStmt`. -/
def dsClearAboveContract (w dBase sBase dLo sLo hi : ℕ) : Contract where
  pre args _ := args = [dBase, sBase, dLo, sLo, hi] ∧ dLo ≤ hi ∧ sLo ≤ hi ∧
    dBase + hi < 2 ^ w ∧ sBase + hi < 2 ^ w ∧ 2 ≤ 2 ^ w
  post _ mem _ mem' :=
    (∀ i, dLo ≤ i → i < hi → mem' (dBase + i) = 0) ∧
    (∀ i, sLo ≤ i → i < hi → mem' (sBase + i) = 0) ∧
    ∀ addr, (addr < dBase + dLo ∨ dBase + hi ≤ addr) →
      (addr < sBase + sLo ∨ sBase + hi ≤ addr) → mem' addr = mem addr
  cost _ _ := 15 * (hi - dLo) + 15 * (hi - sLo) + 50

end

public section

/-- `dsClearAboveStmt` meets `dsClearAboveContract`. -/
theorem dsClearAbove_meetsContract {w dBase sBase dLo sLo hi : ℕ} {p : Program} {bZ bC : ℕ}
    (hpZ : p.HasAt bZ zeroRangeProcs) (hpC : p.HasAt bC (clearAboveProcs bZ)) :
    MeetsContract w p (bC + clearAboveIdx) (dsClearAboveContract w dBase sBase dLo sLo hi) := by
  refine meetsContract_of_runs
    (hpC.get (i := clearAboveIdx) (by simp [clearAboveProcs, clearAboveIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, hle, hle', hdB, hsB, hw2⟩
  simp only [clearAboveProcs, clearAboveIdx, List.getElem_cons_zero]
  dsimp only [dsClearAboveStmt]
  refine runs_start_le ?_
  refine runs_seq_call_le (vs := [dBase, dLo, hi])
    (dsZeroRange_meetsContract (w := w) (base := dBase) (lo := dLo) (hi := hi) hpZ)
    (by eval_expr)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl) <;> omega)
    ⟨rfl, hle, hdB, hw2⟩ ?_
  rintro r₁ mem₁ pos₁ ⟨hz₁, hfr₁⟩
  refine runs_seq_call_le (vs := [sBase, sLo, hi])
    (dsZeroRange_meetsContract (w := w) (base := sBase) (lo := sLo) (hi := hi) hpZ)
    (by eval_expr)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl) <;> omega)
    ⟨rfl, hle', hsB, hw2⟩ ?_
  rintro r₂ mem₂ pos₂ ⟨hz₂, hfr₂⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
    ⟨fun i h1 h2 => ?_, hz₂, fun addr h1 h2 => ?_⟩ ?_
  · show mem₂ (dBase + i) = 0
    by_cases hs : sBase + sLo ≤ dBase + i ∧ dBase + i < sBase + hi
    · -- The two ranges meet at this word; `sGen` is written last, also with `0`.
      obtain ⟨k, hk⟩ : ∃ k, dBase + i = sBase + k := ⟨dBase + i - sBase, by omega⟩
      rw [hk]
      exact hz₂ k (by omega) (by omega)
    · rw [hfr₂ _ (by omega)]
      exact hz₁ i h1 h2
  · show mem₂ addr = _
    exact (hfr₂ addr h2).trans (hfr₁ addr h1)
  · simp only [Expr.size, argsSize, dsClearAboveContract, dsZeroRangeContract]
    omega

/-- The `S` clause of a level above `j` after the step: once `sGen[i]` is `0` and the vertex
stamps and the generation word are kept, the clause holds with `S_i = ∅` and an empty list. The
bounds on the stamps come from the old clause. -/
theorem levelSAt_clear {L vCap eCap b : ℕ} {mem mem' : ℕ → ℕ} {x x' : DynSpannerMeta L}
    {st st' : DynSpannerState L} {i : Fin (L + 1)} (h : LevelSAt L vCap eCap b mem x st i)
    (hz : mem' (dsSGenBase b L vCap eCap + i.1) = 0)
    (hag : ∀ addr, ((dsVSGenBase b L vCap eCap ≤ addr ∧ addr < dsSHeadBase b L vCap eCap) ∨
      addr = b + dsGenOff) → mem' addr = mem addr)
    (hsx : x'.sLists i = []) (hS : st'.S_level i = ∅) :
    LevelSAt L vCap eCap b mem' x' st' i := by
  obtain ⟨_, _, h3, _⟩ := h
  have hi := i.2
  have hH : dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hgen := hag (b + dsGenOff) (Or.inr rfl)
  refine levelS_of_gen_zero i hz (fun v hv => ?_) hsx hS
  have hlt : i.1 * vCap + v < (L + 1) * vCap := by
    calc i.1 * vCap + v < i.1 * vCap + vCap := by omega
      _ = (i.1 + 1) * vCap := by ring
      _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right _ (by omega)
  rw [show dsVSGenBase b L vCap eCap + i.1 * vCap + v =
      dsVSGenBase b L vCap eCap + (i.1 * vCap + v) by omega]
  rw [hag _ (Or.inl ⟨by omega, by omega⟩), hgen]
  rw [show dsVSGenBase b L vCap eCap + (i.1 * vCap + v) =
      dsVSGenBase b L vCap eCap + i.1 * vCap + v by omega]
  exact (h3 v hv).1

/-- After `dsClearAboveStmt` with `dLo = j + 1` and `sLo = j`, each level above `j` satisfies both
level clauses with an empty domain, empty reverse lists and an empty `S`. The writes of the call
are the generation words only, so the stamps and the word `gen` are kept
(`levelDomAt_clear`, `levelSAt_clear`). -/
theorem levels_above_clear {L vCap eCap b j : ℕ} {mem mem' : ℕ → ℕ} {x x' : DynSpannerMeta L}
    {st st' : DynSpannerState L}
    (hD : ∀ i : Fin (L + 1), LevelDomAt L vCap eCap b mem x st i)
    (hS : ∀ i : Fin (L + 1), LevelSAt L vCap eCap b mem x st i)
    (hzD : ∀ i, j + 1 ≤ i → i < L + 1 → mem' (dsDomGenBase b L vCap eCap + i) = 0)
    (hzS : ∀ i, j ≤ i → i < L + 1 → mem' (dsSGenBase b L vCap eCap + i) = 0)
    (hag : ∀ addr, ((dsEdgeDomGenBase b L vCap eCap ≤ addr ∧ addr < dsSGenBase b L vCap eCap) ∨
      (dsVSGenBase b L vCap eCap ≤ addr ∧ addr < dsSHeadBase b L vCap eCap) ∨
      addr = b + dsGenOff) → mem' addr = mem addr)
    (hdomx : ∀ i : Fin (L + 1), j < i.1 → x'.memInDom i = ∅)
    (hrevx : ∀ i : Fin (L + 1), j < i.1 → ∀ v, x'.revLists i v = [])
    (hdom : ∀ i : Fin (L + 1), j < i.1 → st'.inDom i = ∅)
    (hsx : ∀ i : Fin (L + 1), j < i.1 → x'.sLists i = [])
    (hSl : ∀ i : Fin (L + 1), j < i.1 → st'.S_level i = ∅) :
    ∀ i : Fin (L + 1), j < i.1 →
      LevelDomAt L vCap eCap b mem' x' st' i ∧ LevelSAt L vCap eCap b mem' x' st' i := by
  intro i hi
  refine ⟨levelDomAt_clear (hD i) (hzD i.1 (by omega) i.2) (fun addr h => hag addr ?_)
    (hdomx i hi) (hrevx i hi) (hdom i hi),
    levelSAt_clear (hS i) (hzS i.1 (by omega) i.2) (fun addr h => hag addr ?_) (hsx i hi)
      (hSl i hi)⟩
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end

end MinCostFlow.DynSpanner.Program
