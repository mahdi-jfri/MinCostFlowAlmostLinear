module

public import MinCostFlow.HierPaths.BuildProgWalkFits

/-!
# Storing all walks of one routed matching

Keep one position array and one scratch vertex block. Each routed edge in the
matching gives one shortcut walk in the arena. The directory records the base
of its length-prefixed slot in matching order.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp MinCostFlow.Cited

/-- A consecutive row of walks in a router reply. -/
structure BuildWalkRow where
  count : ℕ
  total : ℕ
  first : ℕ
  u : ℕ → ℕ
  v : ℕ → ℕ
  emb : ℕ → List ℕ

/-- The raw walk of edge `i` of the row. -/
def BuildWalkRow.raw (R : BuildWalkRow) (i : ℕ) : List ℕ := R.emb (R.first + i)

/-- The start of the next slot after writing the first `i` walks. -/
def BuildWalkRow.cursor (R : BuildWalkRow) (out : ℕ) : ℕ → ℕ
  | 0 => out
  | i + 1 => R.cursor out i + 1 + (R.raw i).length

/-- Args are `[table, total, first, source, ends, verts, positions, directory, heap, count]`. -/
def buildWalkRowStep (f : ℕ) : Stmt :=
  .seq (.call 11 f [.reg 0, .reg 1, .bin .add (.reg 2) (.reg 10),
      .bin .add (.reg 3) (.bin .add (.reg 10) (.reg 10)),
      .reg 4, .reg 5, .reg 6, .reg 8])
    (.seq (.store (.bin .add (.reg 7) (.reg 10)) (.reg 8)) (.assign 8 (.reg 11)))

/-- Walks of a matching are written in their original order. -/
def buildWalkRowProc (f : ℕ) : Stmt :=
  .seq (forRange 10 (.const 0) (.reg 9) (buildWalkRowStep f)) (.ret (.reg 8))

theorem buildWalkRowProc_noRand (f : ℕ) : (buildWalkRowProc f).NoRand := by
  simp [buildWalkRowProc, buildWalkRowStep, forRange, forUp, Stmt.NoRand]

/-- Address bounds for the raw matching, graph, scratch and output regions. -/
structure WalkRowFit (w : ℕ) (R : BuildWalkRow) (G : Graph)
    (tb src ends vs P dir out : ℕ) : Prop where
  index : R.first + R.count ≤ R.total
  table : tb + (csrList R.total R.emb).length ≤ dir
  source : src + 2 * R.count ≤ dir
  ends : ends + 2 * G.m ≤ dir
  directory : dir + R.count ≤ vs
  scratch : ∀ i < R.count, vs + (R.raw i).length + 1 ≤ P
  positions : P + G.n ≤ out
  word : R.cursor out R.count < 2 ^ w
  one : 1 < 2 ^ w

/-- Cells kept by a row write, including earlier walk slots in the arena. -/
def WalkRowKept (count vs P dir out a : ℕ) : Prop :=
  a < dir ∨ (dir + count ≤ a ∧ a < vs) ∨ (P ≤ a ∧ a < out)

/-- The matching sources, host edges and raw walk table lie below the directory. -/
def buildWalkRowContract (w : ℕ) (G : Graph) (R : BuildWalkRow) : Contract where
  pre args mem := ∃ tb src ends vs P dir out,
    args = [tb, R.total, R.first, src, ends, vs, P, dir, out, R.count] ∧
    WalkRowFit w R G tb src ends vs P dir out ∧ G.IsValid ∧
    ListAt mem tb (csrList R.total R.emb) ∧
    ListAt mem ends (G.edges.flatMap fun e => [e.1, e.2]) ∧
    (∀ i < R.count, mem (src + 2 * i) = R.u i ∧ R.u i < G.n ∧
      IsEdgeWalk G.edges (R.u i) (R.v i) (R.raw i)) ∧
    ZeroFrom mem out ∧ (∀ a < G.n, mem (P + a) = 0)
  post args mem v mem' := ∃ tb src ends vs P dir out,
    args = [tb, R.total, R.first, src, ends, vs, P, dir, out, R.count] ∧
    v = R.cursor out R.count ∧ ZeroFrom mem' v ∧
    (∀ a, WalkRowKept R.count vs P dir out a → mem' a = mem a) ∧ (∀ a < G.n, mem' (P + a) = 0) ∧
    ∀ i < R.count, mem' (dir + i) = R.cursor out i ∧
      SeqAt mem' (R.cursor out i) (erase G.edges (R.u i) (R.raw i))
  cost _ _ := rangeCost (fun i => 136 * (R.raw i).length + 330) 0 R.count + 9 * R.count + 16

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp MinCostFlow.Cited

/-- Each reserved slot extends the walk arena. -/
theorem BuildWalkRow.cursor_mono (R : BuildWalkRow) (out : ℕ) : Monotone (R.cursor out) := by
  apply monotone_nat_of_le_succ
  intro i
  change R.cursor out i ≤ R.cursor out i + 1 + (R.raw i).length
  omega

/-- A length-prefixed list depends only on the header and its listed words. -/
theorem seqAt_frame {mem mem' : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (hAt : SeqAt mem a xs) (h : ∀ j, a ≤ j → j < a + 1 + xs.length → mem' j = mem j) :
    SeqAt mem' a xs :=
  ⟨(h a le_rfl (by omega)).trans hAt.1,
    WordRAM.ListAt.congr hAt.2 (fun j hj hEnd => h j (by omega) hEnd)⟩

private def walkRowInv (R : BuildWalkRow) (G : Graph) (tb src ends vs P dir out : ℕ)
    (mem : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = tb ∧ st.regs 1 = R.total ∧ st.regs 2 = R.first ∧ st.regs 3 = src ∧
    st.regs 4 = ends ∧ st.regs 5 = vs ∧ st.regs 6 = P ∧ st.regs 7 = dir ∧
    st.regs 8 = R.cursor out i ∧ st.regs 9 = R.count ∧ st.regs 10 = i ∧
    ZeroFrom st.mem (R.cursor out i) ∧ (∀ a, WalkRowKept R.count vs P dir out a → st.mem a = mem a) ∧
    (∀ a < G.n, st.mem (P + a) = 0) ∧
    ∀ j < i, st.mem (dir + j) = R.cursor out j ∧
      SeqAt st.mem (R.cursor out j) (erase G.edges (R.u j) (R.raw j))

private theorem buildWalkRow_step {w tb src ends vs P dir out i f : ℕ} {p : Program}
    {G : Graph} {R : BuildWalkRow} {mem : ℕ → ℕ}
    (hProc : ∀ j < R.count, MeetsContract w p f
      (buildStoreWalkContract w G.edges (R.u j) R.emb R.total (R.first + j)))
    (hf : WalkRowFit w R G tb src ends vs P dir out) (hG : G.IsValid)
    (hArgs : ∀ a ∈ [tb, R.total, R.first, src, ends, vs, P, dir, out, R.count], a < 2 ^ w)
    (hTb : ListAt mem tb (csrList R.total R.emb))
    (hE : ListAt mem ends (G.edges.flatMap fun e => [e.1, e.2]))
    (hWalk : ∀ j < R.count, mem (src + 2 * j) = R.u j ∧ R.u j < G.n ∧
      IsEdgeWalk G.edges (R.u j) (R.v j) (R.raw j))
    (hi : i < R.count) :
    Triple w p (walkRowInv R G tb src ends vs P dir out mem i) (buildWalkRowStep f)
      (normalPost fun st => walkRowInv R G tb src ends vs P dir out mem (i + 1)
        { st with regs := Function.update st.regs 10 (i + 1) } ∧ st.regs 10 = i)
      (fun _ => 136 * (R.raw i).length + 330) := by
  intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,hZero,hFrame,hPos,hPrev⟩
  let top := R.cursor out i
  let len := (R.raw i).length
  let cell := src + 2 * i
  have ht : top + 1 + len = R.cursor out (i + 1) := rfl
  have hNext := (R.cursor_mono out (show i + 1 ≤ R.count by omega)).trans_lt hf.word
  rw [← ht] at hNext
  have hTop : out ≤ top := R.cursor_mono out (Nat.zero_le i)
  have hfInd := hf.index
  have hfDir := hf.directory
  have hfSrc := hf.source
  have hfScratch := hf.scratch i hi
  have hfPos := hf.positions
  change vs + len + 1 ≤ P at hfScratch
  have hBound : R.first + i < R.total := by omega
  have hCell : cell < dir := by dsimp [cell]; omega
  have hRead : st.mem cell = R.u i := (hFrame _ (Or.inl hCell)).trans (hWalk i hi).1
  have hTab' : ListAt st.mem tb (csrList R.total R.emb) :=
    WordRAM.ListAt.congr hTb (fun a _ ha => hFrame a (Or.inl (ha.trans_le hf.table)))
  have hE' : ListAt st.mem ends (G.edges.flatMap fun e => [e.1, e.2]) :=
    WordRAM.ListAt.congr hE (fun a _ ha => hFrame a (Or.inl (by
      have he : (G.edges.flatMap fun e => [e.1, e.2]).length = 2 * G.m := by
        simp [Graph.m, Nat.mul_comm, List.length_flatMap]
      rw [he] at ha
      exact ha.trans_le hf.ends)))
  have hdv : dir ≤ vs := by omega
  have hPath := pathPre_of_routedWalk (emb := R.emb) (i := R.first + i) (tb := tb) (n := R.total) (vs := vs) (P := P) (out := top + 1) hG (hWalk i hi).2.2 (hWalk i hi).2.1
    hBound hTab' hE' (hf.table.trans hdv) (hf.ends.trans hdv)
    hfScratch (by omega) hNext hf.one hPos
  have hTable : tb + (R.total + 1) ≤ vs := by
    have he : R.total + 1 ≤ (csrList R.total R.emb).length := by
      simp [csrList]
    have hfTab := hf.table
    omega
  have hIdxW : R.first + i < 2 ^ w := hBound.trans (hArgs R.total (by simp))
  have hi2 : i + i < 2 ^ w := by omega
  have hCellW : src + (i + i) < 2 ^ w := by dsimp [cell] at hCell; omega
  have hT : top < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildWalkRowStep
  refine runs_seq_call_le (hProc i hi) (vs := [tb, R.total, R.first + i, cell, ends, vs, P, top]) ?_ ?_
    ⟨tb, cell, ends, vs, P, top, rfl, hBound, hTable, by omega, hRead,
      hfScratch.trans (by omega), hTab', hPath⟩ ?_
  · simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h8, h10, hIdxW, hi2, hCellW,
      top, cell, Nat.two_mul]
  · have htb := hArgs tb (by simp)
    have hn := hArgs R.total (by simp)
    have he := hArgs ends (by simp)
    have hv := hArgs vs (by simp)
    have hp := hArgs P (by simp)
    dsimp [cell]
    wram_words
  intro v mem' pos' hPost
  obtain ⟨_, _, _, _, _, _, hEq, hv, hAt, hFrame'⟩ := hPost
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := hEq
  change v = top + 1 + len at hv
  have hv' : v = R.cursor out (i + 1) := hv.trans ht
  change ∀ j, (j < vs ∨ (vs + len + 1 ≤ j ∧ j < top) ∨ v ≤ j) → mem' j = st.mem j at hFrame'
  have hDirW : dir + i < 2 ^ w := by omega
  refine runs_seq_store_le (x := dir + i) (v := top) ?_ ?_ ?_
  · simp [Expr.eval, Function.update, h7, h10, hDirW]
  · simp [Expr.eval, Function.update, h8, top]
  refine runs_assign_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · let next := Function.update mem' (dir + i) top
    have hNoTouch {a : ℕ} (ha : a ≠ dir + i) : next a = mem' a := Function.update_of_ne ha _ _
    refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
      by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7, by simp [hv'],
      by simpa using h9, by simp, ?_, ?_, ?_, ?_⟩, h10⟩
    · intro a ha
      change next a = 0
      have ha' : v ≤ a := hv'.trans_le ha
      exact (hNoTouch (by omega)).trans ((hFrame' a (Or.inr (Or.inr ha'))).trans
        (hZero a (by omega)))
    · intro a ha
      have hk := ha
      change a < dir ∨ (dir + R.count ≤ a ∧ a < vs) ∨ (P ≤ a ∧ a < out) at hk
      have hCell : a ≠ dir + i := by omega
      have hStore : a < vs ∨ (vs + len + 1 ≤ a ∧ a < top) ∨ v ≤ a := by omega
      exact (hNoTouch hCell).trans ((hFrame' a hStore).trans (hFrame a ha))
    · intro a ha
      exact (hNoTouch (by omega)).trans ((hFrame' _ (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans
        (hPos a ha))
    · intro j hj
      change next (dir + j) = R.cursor out j ∧ SeqAt next _ _
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hOldDir,hOldAt⟩ := hPrev j hj
        have hOldLe := R.cursor_mono out (show j + 1 ≤ i by omega)
        have hOldOut : out ≤ R.cursor out j := R.cursor_mono out (Nat.zero_le j)
        change R.cursor out j + 1 + (R.raw j).length ≤ top at hOldLe
        have hLen := (erase_spec (R.raw j).length _ _ _ le_rfl (hWalk j (hj.trans hi)).2.2).2.1.length_le
        refine ⟨(hNoTouch (by omega)).trans ((hFrame' _ (Or.inl (by omega))).trans hOldDir), ?_⟩
        exact seqAt_frame hOldAt fun a ha hb => (hNoTouch (by omega)).trans
          (hFrame' a (Or.inr (Or.inl ⟨by omega, by omega⟩)))
      · refine ⟨by simp [next, top], ?_⟩
        exact seqAt_frame hAt fun a ha _ => hNoTouch (by omega)
  · simp [buildStoreWalkContract, argsSize, Expr.size, BuildWalkRow.raw]
    omega

/-- Store a whole row with cost linear in the number of raw edge occurrences. -/
theorem buildWalkRowProc_meetsContract {w f fWalk : ℕ} {p : Program} {G : Graph}
    {R : BuildWalkRow} (hf : p.procs[f]? = some (buildWalkRowProc fWalk))
    (hWalkP : ∀ i < R.count, MeetsContract w p fWalk
      (buildStoreWalkContract w G.edges (R.u i) R.emb R.total (R.first + i))) :
    MeetsContract w p f (buildWalkRowContract w G R) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨tb, src, ends, vs, P, dir, out, rfl, hFit, hG, hTb, hE, hWalk, hZero, hPos⟩ := hPre
  let st0 := startState [tb, R.total, R.first, src, ends, vs, P, dir, out, R.count] mem pos
  have hLoop := Triple.forRange_le (p := p) (r := 10) (lo := .const 0) (hi := .reg 9)
    (body := buildWalkRowStep fWalk) (P := fun st => st = st0)
    (Inv := walkRowInv R G tb src ends vs P dir out mem)
    (fun i => 136 * (R.raw i).length + 330) 0 R.count (Nat.zero_le _) hFit.one
    (fun _ => hArgs R.count (by simp))
    (fun st he => by
      subst st
      exact ⟨Expr.eval_const (Nat.two_pow_pos _), rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
        hZero, fun _ _ => rfl, hPos, fun j hj => False.elim (Nat.not_lt_zero j hj)⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ hi => buildWalkRow_step hWalkP hFit hG hArgs hTb hE hWalk hi)
  refine runs_start_le ?_
  unfold buildWalkRowProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_,_,_,_,_,_,_,_,hTop,_,_,hZ,hF,hP,hD⟩
  refine runs_ret_le (Expr.eval_reg_of_eq hTop)
    ⟨tb, src, ends, vs, P, dir, out, rfl, rfl, hZ, hF, hP, hD⟩ ?_
  simp [buildWalkRowContract, Expr.size]
  omega

end MinCostFlow.HierPaths
