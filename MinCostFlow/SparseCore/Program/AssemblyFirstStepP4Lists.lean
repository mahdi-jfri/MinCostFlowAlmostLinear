module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutEnds
public import MinCostFlow.SparseCore.Program.AssemblyFirstOutIns
public import MinCostFlow.SparseCore.Program.AssemblyFirstEmbCopyIns

import WordRAM.Tactic

/-!
# The output lists of Phase 4 (`AssemblyFirstStepP4Lists`)

After the selectors (`AssemblyFirstStepP4Sel.lean`), Phase 4 writes the two lists of the output
step: the leaving edges with their flags (`OutDelAt`) and the entering edges with the new roots
of their ends (`OutInsAt`). It also writes the self-walks of the entering edges into the
embedding table. The procedure `asmFirstP4ListsStmt fEnds fDel fIns fCopy`, with arguments
`[tourH, insSupPtr, insLen, selInsPtr, delSupPtr, delLen, selDelPtr, inE'Ptr, eCap, embH, h]`,
keeps the two words `[h, h + 2)` for the places of the two lists and then runs four procedures
from `h + 2` on:
1. `asmFirstQueryInsEndsStmt` asks the tour for the new roots of the ends of each entering edge;
2. `asmFirstBuildDelStmt` writes the sorted leaving edges with their flags; the procedure stores
   their place at `h`;
3. `asmFirstBuildInsStmt` writes the sorted entering edges with the roots of their ends; the
   procedure stores their place at `h + 1`;
4. `asmFirstCopyInsStmt` writes the self-walk `[(e, true)]` of each entering edge `e` into the
   embedding table.

The run lemma `asmFirstP4Lists_runs` is stated on abstract sets: `Sdel` and `Sins` are the sets
that the selectors decide, the lists `Ld` and `Li` contain them, and `E'` is the set of the
flags of the leaving edges. The tour changes only in its own cells, and the lists lie outside its
cells and outside the cells `avoid₀` below `h`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

/-! ## The procedure -/

@[expose] public section

/-- **The output lists of Phase 4**, `[tourH, insSupPtr, insLen, selInsPtr, delSupPtr, delLen,
selDelPtr, inE'Ptr, eCap, embH, h]`. Register `11` holds `h + 2`, where the ends of the entering
edges go; registers `12` to `15` hold the heap pointers that the four calls return. -/
def asmFirstP4ListsStmt (fEnds fDel fIns fCopy : ℕ) : Stmt :=
  .assign 11 (.bin .add (.reg 10) (.const 2)) ;;
  .call 12 fEnds [.reg 0, .reg 1, .reg 2, .reg 3, .reg 8, .reg 11] ;;
  .call 13 fDel [.reg 4, .reg 5, .reg 6, .reg 7, .reg 12] ;;
  .store (.reg 10) (.load (.reg 12)) ;;
  .call 14 fIns [.reg 1, .reg 2, .reg 3, .reg 11, .bin .add (.reg 11) (.reg 8), .reg 13] ;;
  .store (.bin .add (.reg 10) (.const 1)) (.load (.reg 13)) ;;
  .call 15 fCopy [.reg 9, .load (.reg 13), .reg 14] ;;
  .ret (.reg 15)

/-- The cells that `asmFirstP4ListsStmt` allocates from `h` on, besides the scratch cells of the
tour queries: the two places, the ends (`2 eCap`), the cells of the queries (`2` per entering
edge), the two lists with their scratch (`2 + 5 |Ld|` and `2 + 6 |Li|`), and the self-walks of the
entering edges (`3` each). -/
def p4ListsSpace (eCap nIns nLd nLi : ℕ) : ℕ := 6 + 2 * eCap + 5 * nIns + 5 * nLd + 6 * nLi

/-- What `asmFirstP4ListsStmt` leaves, from the tour `a` (concrete state `tx₀`) and the
embedding view `v` (concrete state `y`). The sets `Sdel` and `Sins` are those of the selectors,
`Ld` and `Li` the candidate lists, `mul` the cost factor of a tour query. At `h` lies the place
of the sorted leaving edges with their flags of `E'`, at `h + 1` the place of the sorted entering
edges with the roots of their ends in the tour. Both lists lie below the returned pointer and
outside `avoid₀` and the cells of the tour. The tour keeps its state, and the embedding table
holds the self-walks of the entering edges. Every cell below `h` outside the tour and the
embedding table is kept, the cells of the tour and of the table grow only into `[h + 2, o)`, and
the cost is paid against the potential of the tour. -/
def P4ListsPost (TR : ℕ → ℕ → DSRep AsmTourAbs) (vCap eCap tourH embH h : ℕ) (a : AsmTourAbs)
    (tx₀ : (TR vCap eCap).τ) (Sdel Sins E' : Finset ℕ) (Ld Li : List ℕ) (v : EmbView)
    (y : EmbConc) (avoid₀ : ℕ → Prop) (mul : ℕ) (mem₀ : ℕ → ℕ) (o : Outcome) (st' : State)
    (cost : ℕ) : Prop :=
  ∃ (tx' : (TR vCap eCap).τ) (y' : EmbConc),
    (TR vCap eCap).rep tourH a tx' st'.mem ∧
    OutDelAt st'.mem (st'.mem h) (Sdel.sort (· ≤ ·)) E' ∧
    OutCellsFree (st'.mem h) (1 + 2 * Sdel.card) o.value
      (fun x => avoid₀ x ∨ (TR vCap eCap).foot tourH tx' x) ∧
    OutInsAt st'.mem (st'.mem (h + 1)) (Sins.sort (· ≤ ·))
      (fun e => if e ∈ Sins then a.rf.root (ordSrc a.ord (e, true)) else 0)
      (fun e => if e ∈ Sins then a.rf.root (ordSrc a.ord (e, false)) else 0) ∧
    OutCellsFree (st'.mem (h + 1)) (1 + 3 * Sins.card) o.value
      (fun x => avoid₀ x ∨ (TR vCap eCap).foot tourH tx' x) ∧
    h + 2 ≤ st'.mem h ∧ h + 2 ≤ st'.mem (h + 1) ∧
    (embRep eCap).rep embH (v.apply (insSelfChange (Sins.sort (· ≤ ·)))) y' st'.mem ∧
    h + 2 ≤ o.value ∧ o.value ≤ h + p4ListsSpace eCap Sins.card Ld.length Li.length ∧
    ZeroFrom st'.mem o.value ∧
    (∀ x < h, ¬ (TR vCap eCap).foot tourH tx₀ x → ¬ embFoot eCap embH y x →
      st'.mem x = mem₀ x) ∧
    (∀ x, (TR vCap eCap).foot tourH tx' x →
      (TR vCap eCap).foot tourH tx₀ x ∨ (h + 2 ≤ x ∧ x < o.value)) ∧
    (∀ x, embFoot eCap embH y' x → embFoot eCap embH y x ∨ (h + 2 ≤ x ∧ x < o.value)) ∧
    (∀ x, embFoot eCap embH y' x → ¬ (TR vCap eCap).foot tourH tx' x) ∧
    cost + (TR vCap eCap).phi tourH tx' st'.mem ≤
      2 * Sins.card * (mul * ordStoreLog eCap + 45) + 35 * Li.length + outBuildCost Ld.length +
        outBuildCost Li.length + 60 * Sins.card + 300 + (TR vCap eCap).phi tourH tx₀ mem₀

end

/-! ## Facts on the output lists -/

public section

theorem asmFirstP4ListsStmt_noRand (fEnds fDel fIns fCopy : ℕ) :
    (asmFirstP4ListsStmt fEnds fDel fIns fCopy).NoRand := by
  simp [asmFirstP4ListsStmt, Stmt.NoRand]

/-- The leaving edges at `a` depend only on the cells `[a, a + 1 + 2 |delL|)`. -/
theorem outDelAt_of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {delL : List ℕ} {E' : Finset ℕ}
    (h : OutDelAt mem a delL E') (hag : ∀ x, a ≤ x → x < a + 1 + 2 * delL.length → mem' x = mem x) :
    OutDelAt mem' a delL E' := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨by rw [hag a le_rfl (by omega)]; exact h0, fun i hi => ?_⟩
  rw [hag _ (by omega) (by omega), hag _ (by omega) (by omega)]
  exact h1 i hi

/-- The entering edges at `a` depend only on the cells `[a, a + 1 + 3 |insL|)`. -/
theorem outInsAt_of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {insL : List ℕ} {tl hd : ℕ → ℕ}
    (h : OutInsAt mem a insL tl hd)
    (hag : ∀ x, a ≤ x → x < a + 1 + 3 * insL.length → mem' x = mem x) :
    OutInsAt mem' a insL tl hd := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨by rw [hag a le_rfl (by omega)]; exact h0, fun i hi => ?_⟩
  rw [hag _ (by omega) (by omega), hag _ (by omega) (by omega), hag _ (by omega) (by omega)]
  exact h1 i hi

/-- Free cells stay free below a larger top and outside a smaller set. -/
theorem outCellsFree_mono {a len top top' : ℕ} {avoid avoid' : ℕ → Prop}
    (h : OutCellsFree a len top avoid) (htop : top ≤ top')
    (hav : ∀ i < len, avoid' (a + i) → avoid (a + i)) : OutCellsFree a len top' avoid' :=
  ⟨le_trans h.1 htop, fun i hi ha => h.2 i hi (hav i hi ha)⟩

/-- The flags of the leaving edges may be read on a larger set that agrees with `E'` on the
listed edges. -/
theorem outDelAt_inter {mem : ℕ → ℕ} {a : ℕ} {delL : List ℕ} {E' S : Finset ℕ}
    (h : OutDelAt mem a delL (E' ∩ S)) (hS : ∀ e ∈ delL, e ∈ S) : OutDelAt mem a delL E' := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨h0, fun i hi => ⟨(h1 i hi).1, ?_⟩⟩
  have hmem : delL.getD i 0 ∈ S := by
    rw [List.getD_eq_getElem _ _ hi]; exact hS _ (List.getElem_mem hi)
  rw [(h1 i hi).2]
  by_cases hE : delL.getD i 0 ∈ E'
  · simp only [Finset.mem_inter, hE, hmem, and_self, ↓reduceIte]
  · simp only [Finset.mem_inter, hE, false_and, ↓reduceIte]

end

/-! ## The run -/

/-- A call followed by a statement, with the cost bound carried along. -/
private theorem lists_runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ}
    (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

/-- The run of the statement from the runs of its four calls. -/
private theorem asmFirstP4Lists_run_of {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {fEnds fDel fIns fCopy : ℕ} {bEnds bDel bIns bCopy : Stmt}
    (hfEnds : p.procs[fEnds]? = some bEnds) (hfDel : p.procs[fDel]? = some bDel)
    (hfIns : p.procs[fIns]? = some bIns) (hfCopy : p.procs[fCopy]? = some bCopy)
    {tourH insSupPtr insLen selInsPtr delSupPtr delLen selDelPtr inE'Ptr eCap embH h pos : ℕ}
    {mem₀ : ℕ → ℕ} (hw16 : 16 ≤ 2 ^ w) (hsz : h + 2 + eCap < 2 ^ w)
    {o₁ o₂ o₃ o₄ : Outcome} {st₁ st₂ st₃ st₄ : State} {c₁ c₂ c₃ c₄ : ℕ}
    (hr₁ : Runs w p ω bEnds (startState [tourH, insSupPtr, insLen, selInsPtr, eCap, h + 2] mem₀
      pos) o₁ st₁ c₁)
    (hr₂ : Runs w p ω bDel (startState [delSupPtr, delLen, selDelPtr, inE'Ptr, o₁.value] st₁.mem
      st₁.pos) o₂ st₂ c₂)
    (hr₃ : Runs w p ω bIns (startState [insSupPtr, insLen, selInsPtr, h + 2, h + 2 + eCap,
      o₂.value] (Function.update st₂.mem h (st₂.mem o₁.value)) st₂.pos) o₃ st₃ c₃)
    (hr₄ : Runs w p ω bCopy (startState [embH, st₃.mem o₂.value, o₃.value]
      (Function.update st₃.mem (h + 1) (st₃.mem o₂.value)) st₃.pos) o₄ st₄ c₄)
    (hne : o₂.value ≠ h + 1) :
    ∃ st' c, Runs w p ω (asmFirstP4ListsStmt fEnds fDel fIns fCopy)
        (startState [tourH, insSupPtr, insLen, selInsPtr, delSupPtr, delLen, selDelPtr, inE'Ptr,
          eCap, embH, h] mem₀ pos) (.returned o₄.value) st' c ∧ st'.mem = st₄.mem ∧
      c ≤ c₁ + c₂ + c₃ + c₄ + 100 := by
  have key : ∃ o st' c, Runs w p ω (asmFirstP4ListsStmt fEnds fDel fIns fCopy)
      (startState [tourH, insSupPtr, insLen, selInsPtr, delSupPtr, delLen, selDelPtr, inE'Ptr,
        eCap, embH, h] mem₀ pos) o st' c ∧ (o = .returned o₄.value ∧ st'.mem = st₄.mem) ∧
      0 + c ≤ c₁ + c₂ + c₃ + c₄ + 100 := by
    unfold asmFirstP4ListsStmt
    refine runs_seq_assign_le (v := h + 2) (by eval_expr) ?_
    refine lists_runs_seq_callRuns_le (by eval_expr) hfEnds hr₁ ?_
    refine lists_runs_seq_callRuns_le (by eval_expr) hfDel hr₂ ?_
    refine runs_seq_store_le (x := h) (v := st₂.mem o₁.value) (by eval_expr) (by eval_expr) ?_
    refine lists_runs_seq_callRuns_le (by eval_expr) hfIns hr₃ ?_
    refine runs_seq_store_le (x := h + 1) (v := st₃.mem o₂.value) (by eval_expr) (by eval_expr) ?_
    have hv : Function.update st₃.mem (h + 1) (st₃.mem o₂.value) o₂.value = st₃.mem o₂.value :=
      Function.update_of_ne hne _ _
    refine lists_runs_seq_callRuns_le (by eval_expr) hfCopy hr₄ ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o, st', c, hr, ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c, hr, hm, by omega⟩

public section

set_option maxHeartbeats 1600000 in
/-- **The run of the output lists of Phase 4.** The lists `Li` and `Ld` contain the sets `Sins`
and `Sdel` that the selectors decide, the ends of the entering edges are in the order of the
tour, the inputs lie below `h` outside the cells of the tour, and the embedding table lies below
`h` apart from the tour. Then `asmFirstP4ListsStmt` ends in `P4ListsPost`. -/
theorem asmFirstP4Lists_runs {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w fEndRoot fEnds fDel fIns fCopy bSort vCap eCap tourH insSupPtr selInsPtr delSupPtr
      selDelPtr inE'Ptr embH h pos : ℕ} {p : Program}
    (H : AsmFirstTourEndRootAt TR w p fEndRoot) (hTR_loc : ∀ v e, (TR v e).Local)
    (hfEnds : p.procs[fEnds]? = some (asmFirstQueryInsEndsStmt fEndRoot))
    (hfDel : p.procs[fDel]? = some (asmFirstBuildDelStmt bSort))
    (hfIns : p.procs[fIns]? = some (asmFirstBuildInsStmt bSort))
    (hfCopy : p.procs[fCopy]? = some asmFirstCopyInsStmt)
    (hpS : p.HasAt bSort (sortProcs bSort))
    {a : AsmTourAbs} {tx₀ : (TR vCap eCap).τ} {Ld Li : List ℕ} {Sdel Sins E' : Finset ℕ}
    {v : EmbView} {y : EmbConc} {avoid₀ : ℕ → Prop} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (htour_w : tourH < 2 ^ w)
    (hrep : (TR vCap eCap).rep tourH a tx₀ mem₀)
    (hfootT : ∀ x, (TR vCap eCap).foot tourH tx₀ x → x < h)
    (hIS : ListAt mem₀ insSupPtr Li) (hIS_le : insSupPtr + Li.length ≤ h) (hIS_nd : Li.Nodup)
    (hIS_cap : ∀ e ∈ Li, e < eCap) (hIS_cov : ∀ e ∈ Sins, e ∈ Li)
    (hSelI : OutSelFlagsAt mem₀ selInsPtr eCap Sins) (hSelI_le : selInsPtr + eCap ≤ h)
    (hAct : ∀ e ∈ Sins, (∃ u, (e, true) ∈ a.ord u) ∧ (∃ u, (e, false) ∈ a.ord u))
    (hDS : ListAt mem₀ delSupPtr Ld) (hDS_le : delSupPtr + Ld.length ≤ h)
    (hDS_cap : ∀ e ∈ Ld, e < eCap) (hDS_cov : ∀ e ∈ Sdel, e ∈ Ld)
    (hSelD : OutSelFlagsAt mem₀ selDelPtr eCap Sdel) (hSelD_le : selDelPtr + eCap ≤ h)
    (hE' : OutDelFlagsAt mem₀ inE'Ptr eCap E') (hE'_le : inE'Ptr + eCap ≤ h)
    (hIn : ∀ x, (TR vCap eCap).foot tourH tx₀ x →
      (x < insSupPtr ∨ insSupPtr + Li.length ≤ x) ∧ (x < selInsPtr ∨ selInsPtr + eCap ≤ x) ∧
      (x < delSupPtr ∨ delSupPtr + Ld.length ≤ x) ∧ (x < selDelPtr ∨ selDelPtr + eCap ≤ x) ∧
      (x < inE'Ptr ∨ inE'Ptr + eCap ≤ x))
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hEmbF : ∀ x, embFoot eCap embH y x → x < h)
    (hET : ∀ x, embFoot eCap embH y x → ¬ (TR vCap eCap).foot tourH tx₀ x)
    (havoid : ∀ x, avoid₀ x → x < h)
    (heCap_w : eCap < 2 ^ w)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + p4ListsSpace eCap Sins.card Ld.length Li.length + H.querySpace < 2 ^ w) :
    ∃ o st' cost,
      Runs w p ω (asmFirstP4ListsStmt fEnds fDel fIns fCopy)
        (startState [tourH, insSupPtr, Li.length, selInsPtr, delSupPtr, Ld.length, selDelPtr,
          inE'Ptr, eCap, embH, h] mem₀ pos) o st' cost ∧
      P4ListsPost TR vCap eCap tourH embH h a tx₀ Sdel Sins E' Ld Li v y avoid₀ H.mul mem₀ o st'
        cost := by
  classical
  have hsz : p4ListsSpace eCap Sins.card Ld.length Li.length =
      6 + 2 * eCap + 5 * Sins.card + 5 * Ld.length + 6 * Li.length := rfl
  have hq1 : 1 ≤ H.querySpace := H.querySpace_ge
  have hdelLen : (Sdel.sort (· ≤ ·)).length = Sdel.card := Finset.length_sort _
  have hinsLen : (Sins.sort (· ≤ ·)).length = Sins.card := Finset.length_sort _
  -- 1. The ends of the entering edges, at `h + 2`.
  obtain ⟨hE, st₁, c₁, tx₁, hr₁, hrep₁, hends₁, hE_lo, hE_hi, hz₁, hfr₁, hft₁, hc₁⟩ :=
    asmFirstQueryInsEnds_runs (h := h + 2) (pos := pos) (ω := ω) H hTR_loc hw16 htour_w hrep
      (fun x hx => by have := hfootT x hx; omega) hIS (by omega)
      (fun x h1 h2 hf => by rcases (hIn x hf).1 with h3 | h3 <;> omega) hIS_nd hIS_cap hIS_cov
      hSelI (by omega) (fun x h1 h2 hf => by rcases (hIn x hf).2.1 with h3 | h3 <;> omega) hAct
      (fun x hx => hz x (by omega)) (by omega)
  have hk₁ : ∀ x, x < h → ¬ (TR vCap eCap).foot tourH tx₀ x → st₁.mem x = mem₀ x :=
    fun x hx hf => hfr₁ x (by omega) hf
  have hDS₁ : ListAt st₁.mem delSupPtr Ld := hDS.congr fun k h1 h2 => hk₁ k (by omega)
    fun hf => by rcases (hIn k hf).2.2.1 with h3 | h3 <;> omega
  have hIS₁ : ListAt st₁.mem insSupPtr Li := hIS.congr fun k h1 h2 => hk₁ k (by omega)
    fun hf => by rcases (hIn k hf).1 with h3 | h3 <;> omega
  have hSelD₁ : OutSelFlagsAt st₁.mem selDelPtr eCap Sdel := fun e he => by
    rw [hk₁ _ (by omega) fun hf => by rcases (hIn _ hf).2.2.2.1 with h3 | h3 <;> omega]
    exact hSelD e he
  have hSelI₁ : OutSelFlagsAt st₁.mem selInsPtr eCap Sins := fun e he => by
    rw [hk₁ _ (by omega) fun hf => by rcases (hIn _ hf).2.1 with h3 | h3 <;> omega]
    exact hSelI e he
  have hE'₁ : OutDelFlagsAt st₁.mem inE'Ptr eCap E' := fun e he => by
    rw [hk₁ _ (by omega) fun hf => by rcases (hIn _ hf).2.2.2.2 with h3 | h3 <;> omega]
    exact hE' e he
  have hEmb₁ : (embRep eCap).rep embH v y st₁.mem :=
    (embRep_local eCap embH v y mem₀ st₁.mem fun x hx =>
      (hk₁ x (hEmbF x hx) (hET x hx)).symm).1 hEmb
  set avoid : ℕ → Prop := fun x => avoid₀ x ∨ (TR vCap eCap).foot tourH tx₁ x with havd
  have havoid₁ : ∀ x, avoid x → x < hE := fun x hx => by
    rcases hx with hx | hx
    · have := havoid x hx; omega
    · rcases hft₁ x hx with hx' | ⟨_, hx'⟩
      · have := hfootT x hx'; omega
      · exact hx'
  -- 2. The leaving edges, at `hE`.
  obtain ⟨o₂, st₂, c₂, hr₂, hDel₂, hFree₂, hp₂lo, hp₂hi, ho₂lo, ho₂hi, hz₂, hfr₂, hc₂⟩ :=
    asmFirstBuildDel_runs (avoid := avoid) (pos := st₁.pos) (ω := ω) hpS hw16 hDS₁ (by omega)
      hDS_cap hDS_cov hSelD₁ (by omega) hE'₁ (by omega) havoid₁ heCap_w hz₁ (by omega)
  set m₂ := Function.update st₂.mem h (st₂.mem hE) with hm₂
  have hk₂ : ∀ x, x < hE → x ≠ h → m₂ x = st₁.mem x := fun x h1 h2 => by
    rw [hm₂, Function.update_of_ne h2]; exact hfr₂ x h1
  have hIS₂ : ListAt m₂ insSupPtr Li := hIS₁.congr fun k h1 h2 => hk₂ k (by omega) (by omega)
  have hSelI₂ : OutSelFlagsAt m₂ selInsPtr eCap Sins := fun e he => by
    rw [hk₂ _ (by omega) (by omega)]; exact hSelI₁ e he
  have hends₂ : OutInsEndsAt m₂ (h + 2) (h + 2 + eCap) eCap
      (fun e => if e ∈ Sins then a.rf.root (ordSrc a.ord (e, true)) else 0)
      (fun e => if e ∈ Sins then a.rf.root (ordSrc a.ord (e, false)) else 0) := fun e he => by
    rw [hk₂ _ (by omega) (by omega), hk₂ _ (by omega) (by omega)]; exact hends₁ e he
  have hz₂' : ZeroFrom m₂ o₂.value := fun x hx => by
    rw [hm₂, Function.update_of_ne (by omega)]; exact hz₂ x hx
  -- 3. The entering edges, at `o₂.value`.
  obtain ⟨o₃, st₃, c₃, hr₃, hIns₃, hFree₃, hp₃lo, hp₃hi, ho₃lo, ho₃hi, hz₃, hfr₃, hc₃⟩ :=
    asmFirstBuildIns_runs (avoid := avoid) (pos := st₂.pos) (ω := ω) hpS hw16 hIS₂ (by omega)
      hIS_cap hIS_cov hSelI₂ (by omega) hends₂ (by omega) (by omega)
      (fun x hx => by have := havoid₁ x hx; omega) heCap_w hz₂' (by omega)
  set m₃ := Function.update st₃.mem (h + 1) (st₃.mem o₂.value) with hm₃
  have hk₃ : ∀ x, x < o₂.value → x ≠ h + 1 → m₃ x = m₂ x := fun x h1 h2 => by
    rw [hm₃, Function.update_of_ne h2]; exact hfr₃ x h1
  have hEmb₃ : (embRep eCap).rep embH v y m₃ :=
    (embRep_local eCap embH v y st₁.mem m₃ fun x hx => by
      have := hEmbF x hx
      rw [hk₃ x (by omega) (by omega), hk₂ x (by omega) (by omega)]).1 hEmb₁
  have hInsAt₃ : OutInsAt m₃ (st₃.mem o₂.value) (Sins.sort (· ≤ ·))
      (fun e => if e ∈ Sins then a.rf.root (ordSrc a.ord (e, true)) else 0)
      (fun e => if e ∈ Sins then a.rf.root (ordSrc a.ord (e, false)) else 0) :=
    outInsAt_of_agree hIns₃ fun x h1 _ => by
      rw [hm₃, Function.update_of_ne (by omega)]
  have hz₃' : ZeroFrom m₃ o₃.value := fun x hx => by
    rw [hm₃, Function.update_of_ne (by omega)]; exact hz₃ x hx
  -- 4. The self-walks of the entering edges, at `o₃.value`.
  obtain ⟨o₄, st₄, c₄, y', hr₄, hEmb₄, ho₄, hz₄, hfr₄, hef₄, hc₄⟩ :=
    asmFirstCopyIns_runs (pos := st₃.pos) (ω := ω) hw16 hEmb₃ hInsAt₃
      (by have := hFree₃.1; omega)
      (fun e he => hIS_cap e (hIS_cov e ((Finset.mem_sort _).mp he)))
      (fun x hx => by have := hEmbF x hx; omega)
      (fun x h1 _ hx => by have := hEmbF x hx; omega) hz₃' (by rw [hinsLen]; omega)
  -- The run of the whole statement.
  obtain ⟨st', cost, hrun, hm, hcost⟩ :=
    asmFirstP4Lists_run_of hfEnds hfDel hfIns hfCopy hw16 (by omega) hr₁ hr₂ hr₃ hr₄ (by omega)
  -- The cells kept by the last call.
  have hk₄ : ∀ x, x < o₃.value → ¬ embFoot eCap embH y x → st'.mem x = m₃ x := fun x h1 h2 => by
    rw [hm]; exact hfr₄ x h1 h2
  have hnE : ∀ x, h ≤ x → ¬ embFoot eCap embH y x := fun x h1 hx => by
    have := hEmbF x hx; omega
  have hdelP : st'.mem h = st₂.mem hE := by
    rw [hk₄ h (by omega) (hnE h le_rfl), hk₃ h (by omega) (by omega), hm₂, Function.update_self]
  have hinsP : st'.mem (h + 1) = st₃.mem o₂.value := by
    rw [hk₄ (h + 1) (by omega) (hnE _ (by omega)), hm₃, Function.update_self]
  have htk : ∀ x, (TR vCap eCap).foot tourH tx₁ x → st'.mem x = st₁.mem x := fun x hx => by
    rcases hft₁ x hx with hx' | ⟨h1, h2⟩
    · have := hfootT x hx'
      rw [hk₄ x (by omega) fun he => hET x he hx', hk₃ x (by omega) (by omega),
        hk₂ x (by omega) (by omega)]
    · rw [hk₄ x (by omega) (hnE x (by omega)), hk₃ x (by omega) (by omega),
        hk₂ x (by omega) (by omega)]
  have hloc := hTR_loc vCap eCap tourH a tx₁ st₁.mem st'.mem fun x hx => (htk x hx).symm
  refine ⟨_, st', cost, hrun, tx₁, y', hloc.1 hrep₁, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hm]; exact hEmb₄, by show h + 2 ≤ o₄.value; omega,
    by show o₄.value ≤ _; rw [ho₄, hinsLen]; omega, by rw [hm]; exact hz₄,
    fun x hx h1 h2 => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx hxt => ?_, ?_⟩
  · rw [hdelP]
    refine outDelAt_of_agree hDel₂ fun x h1 h2 => ?_
    have := hFree₂.1
    rw [hk₄ x (by omega) (hnE x (by omega)), hk₃ x (by omega) (by omega), hm₂,
      Function.update_of_ne (by omega)]
  · rw [hdelP, ← hdelLen]
    exact outCellsFree_mono hFree₂ (by show o₂.value ≤ o₄.value; omega) fun _ _ h => h
  · rw [hinsP]
    refine outInsAt_of_agree hIns₃ fun x h1 h2 => ?_
    have := hFree₃.1
    rw [hk₄ x (by omega) (hnE x (by omega)), hm₃, Function.update_of_ne (by omega)]
  · rw [hinsP, ← hinsLen]
    exact outCellsFree_mono hFree₃ (by show o₃.value ≤ o₄.value; omega) fun _ _ h => h
  · rw [hdelP]; omega
  · rw [hinsP]; omega
  · rw [hk₄ x (by omega) h2, hk₃ x (by omega) (by omega), hk₂ x (by omega) (by omega)]
    exact hk₁ x hx h1
  · rcases hft₁ x hx with hx' | ⟨h1, h2⟩
    · exact Or.inl hx'
    · exact Or.inr ⟨by omega, by show x < o₄.value; omega⟩
  · rcases hef₄ x hx with hx' | ⟨h1, h2⟩
    · exact Or.inl hx'
    · exact Or.inr ⟨by omega, h2⟩
  · rcases hef₄ x hx with hx' | ⟨h1, _⟩ <;> rcases hft₁ x hxt with hxt' | ⟨_, h4⟩
    · exact hET x hx' hxt'
    · have := hEmbF x hx'; omega
    · have := hfootT x hxt'; omega
    · omega
  · rw [← hloc.2]
    have h4 : c₄ ≤ 60 * Sins.card + 30 := by rw [← hinsLen]; exact hc₄
    omega

end

end MinCostFlow.SparseCore.Program
