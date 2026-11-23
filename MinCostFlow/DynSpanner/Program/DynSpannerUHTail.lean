module

public import MinCostFlow.DynSpanner.Program.DynSpannerDelAll
public import MinCostFlow.DynSpanner.Program.DynSpannerInsRecords
public import MinCostFlow.DynSpanner.Program.DynSpannerStepHelpers
import WordRAM.Tactic

/-!
# The last records of `U_H`: deletions, then insertions

After the rebuild of level `j`, the batch `U_H` ends with the deletions of the edges of `H` that
left (the bucket edges of the levels `j..L` outside `J̃`) and then the insertions of the edges of
`J̃` that `H` does not have. `dsDelAllStmt` writes the deletions and `dsInsRecordsStmt` the
insertions. `dsUHTailStmt` calls both, so that the insertions follow the deletions in memory, and
returns the number of records. `dsUHTail_meetsContract` proves that the words form one batch
(`BatchBodyAt`, by `batchBodyAt_append`), for any graph, since the records of deletions and
insertions do not depend on the graph.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [nextBase, headBase, lenBase, lo, hi, presX, out, esPtr, esLen, presY, gPtr]`;
returns the number of records written. -/
def dsUHTailStmt (bA bI : ℕ) : Stmt :=
  .call 11 (bA + delAllIdx) [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6] ;;
  .call 12 (bI + insRecordsIdx)
    [.reg 7, .reg 8, .reg 9, .reg 10, .bin .add (.reg 6) (.bin .mul (.const 2) (.reg 11))] ;;
  .ret (.bin .add (.reg 11) (.reg 12))

def uhTailProcs (bA bI : ℕ) : List Stmt := [dsUHTailStmt bA bI]

def uhTailIdx : ℕ := 0

lemma uhTailProcs_noRand (bA bI : ℕ) : ∀ s ∈ uhTailProcs bA bI, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The data of `dsUHTailStmt`: the data `da` of the deletions, and the data of the insertions
(the edges `es` of `G`, outside the set `Y`). -/
structure UTCtx where
  da : DACtx
  vCap : ℕ
  G : MGraph
  Y : Finset ℕ
  es : List ℕ
  esPtr : ℕ
  presY : ℕ
  gPtr : ℕ
  hesB : esPtr + es.length < 2 ^ da.w
  hpB : presY + da.eCap < 2 ^ da.w
  hgB : gPtr + dynGraphSize vCap da.eCap < 2 ^ da.w
  hoB : da.out + 2 * (bucketsCat da.B da.lo (da.hi - da.lo)).length + 4 * es.length < 2 ^ da.w
  dOE : IvlDisj da.out (2 * (bucketsCat da.B da.lo (da.hi - da.lo)).length + 4 * es.length)
    esPtr es.length
  dOP : IvlDisj da.out (2 * (bucketsCat da.B da.lo (da.hi - da.lo)).length + 4 * es.length)
    presY da.eCap
  dOG : IvlDisj da.out (2 * (bucketsCat da.B da.lo (da.hi - da.lo)).length + 4 * es.length)
    gPtr (dynGraphSize vCap da.eCap)
  hes : ListAt da.mem0 esPtr es
  hesG : ∀ e ∈ es, e ∈ G.E
  hG : DynGraphAt da.mem0 gPtr vCap da.eCap G
  hpres : ∀ e < da.eCap, da.mem0 (presY + e) = if e ∈ Y then 1 else 0
  hGcap : G.IsValid

/-- The number of words of the whole output region. -/
def UTCtx.size (c : UTCtx) : ℕ :=
  2 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length + 4 * c.es.length

/-- The records written: deletions, then insertions. -/
def UTCtx.recs (c : UTCtx) : List Update :=
  (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).map Update.delete ++
    insRecs c.G c.Y c.es

/-- Contract of `dsUHTailStmt`. -/
def dsUHTailContract (c : UTCtx) : Contract where
  pre args mem :=
    args = [c.da.nextBase, c.da.headBase, c.da.lenBase, c.da.lo, c.da.hi, c.da.pres, c.da.out,
      c.esPtr, c.es.length, c.presY, c.gPtr] ∧ mem = c.da.mem0
  post _ mem ret mem' :=
    ret = c.recs.length ∧
    (∀ K : MGraph, BatchBodyAt mem' c.da.out K c.recs
      (2 * (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).length +
        4 * (insList c.Y c.es).length)) ∧
    (∀ i < 2 * (delList c.da.X (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))).length +
        4 * (insList c.Y c.es).length, mem' (c.da.out + i) < 2 ^ c.da.w) ∧
    ∀ addr, (addr < c.da.out ∨ c.da.out + c.size ≤ addr) → mem' addr = mem addr
  cost _ _ := 60 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length +
    60 * (c.da.hi - c.da.lo) + 210 * c.es.length + 100

end

public section

lemma mem_delWords {X : Finset ℕ} {L : List ℕ} {x : ℕ} (hx : x ∈ delWords X L) :
    x = 1 ∨ x ∈ L := by
  simp only [delWords, delList, List.mem_flatMap, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨e, ⟨he, _⟩, rfl | rfl⟩ := hx
  · exact Or.inl rfl
  · exact Or.inr he

lemma mem_insWords {G : MGraph} {X : Finset ℕ} {es : List ℕ} {x : ℕ} (hx : x ∈ insWords G X es) :
    x = 0 ∨ ∃ e ∈ es, x = e ∨ x = G.tail e ∨ x = G.head e := by
  simp only [insWords, insList, List.mem_flatMap, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨e, ⟨he, _⟩, h⟩ := hx
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨e, he, Or.inl h⟩
  · exact Or.inr ⟨e, he, Or.inr (Or.inl h)⟩
  · exact Or.inr ⟨e, he, Or.inr (Or.inr h)⟩

lemma listAt_words_lt {mem : ℕ → ℕ} {a B : ℕ} {l : List ℕ} (h : ListAt mem a l)
    (hb : ∀ x ∈ l, x < B) : ∀ i < l.length, mem (a + i) < B := fun i hi => by
  rw [h i hi]; exact hb _ (List.getElem_mem hi)

/-- `dsUHTailStmt` meets `dsUHTailContract`. -/
theorem dsUHTail_meetsContract (c : UTCtx) {p : Program} {bT bA bR bI bOps : ℕ}
    (hpR : p.HasAt bR delRecordsProcs) (hpA : p.HasAt bA (delAllProcs bR))
    (hpOps : p.HasAt bOps dgOpsProcs) (hpI : p.HasAt bI (insRecordsProcs bOps))
    (hpT : p.HasAt bT (uhTailProcs bA bI)) :
    MeetsContract c.da.w p (bT + uhTailIdx) (dsUHTailContract c) := by
  refine meetsContract_of_runs
    (hpT.get (i := uhTailIdx) (by simp [uhTailProcs, uhTailIdx])) ?_
  rintro args mem pos ω hargsW ⟨rfl, hmem⟩
  subst hmem
  simp only [uhTailProcs, uhTailIdx, List.getElem_cons_zero]
  dsimp only [dsUHTailStmt]
  have hw16 := c.da.hw16
  have hoB := c.hoB
  have hesB := c.hesB
  have hpB := c.hpB
  have hgB := c.hgB
  have dOE := c.dOE
  have dOP := c.dOP
  have dOG := c.dOG
  unfold IvlDisj at dOE dOP dOG
  set cat := bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo) with hcat
  have hdl : (delList c.da.X cat).length ≤ cat.length := List.length_filter_le _ _
  have hcatC' : ∀ x ∈ cat, x < c.da.eCap := by
    intro x hx
    simp only [hcat, bucketsCat, List.mem_flatMap, List.mem_range'] at hx
    obtain ⟨i, ⟨k, hk, rfl⟩, hi⟩ := hx
    exact (c.da.hB _ (by omega) (by omega)).1.2.1 x hi
  refine runs_start_le ?_
  -- Call 1: the deletions.
  refine runs_seq_call_le (vs := [c.da.nextBase, c.da.headBase, c.da.lenBase, c.da.lo, c.da.hi,
      c.da.pres, c.da.out])
    (dsDelAll_meetsContract c.da hpR hpA) (by eval_expr)
    (fun v hv => hargsW v (by simp only [List.mem_cons] at hv ⊢; tauto)) ⟨rfl, rfl⟩ ?_
  rintro r₁ mem₁ pos₁ ⟨hr₁, hL₁, hfr₁⟩
  rw [← hcat] at hr₁ hL₁ hfr₁
  set nd := (delList c.da.X cat).length with hnd
  have hnd_le : nd ≤ cat.length := hdl
  -- The data of the insertions, in the memory after the deletions.
  have hag : ∀ addr, (addr < c.da.out ∨ c.da.out + 2 * cat.length ≤ addr) →
      mem₁ addr = c.da.mem0 addr := hfr₁
  let ci : IRCtx :=
    { w := c.da.w, vCap := c.vCap, eCap := c.da.eCap, G := c.G, X := c.Y, es := c.es,
      esPtr := c.esPtr, pres := c.presY, gPtr := c.gPtr, out := c.da.out + 2 * nd,
      mem0 := mem₁, hw16 := hw16, hesB := hesB, hpB := hpB, hgB := hgB,
      hoB := by omega,
      dOE := by unfold IvlDisj; omega, dOP := by unfold IvlDisj; omega,
      dOG := by unfold IvlDisj; omega,
      hes := c.hes.congr fun k h1 h2 => hag k (by omega),
      hesG := c.hesG,
      hG := dynGraphAt_of_agree c.hG fun addr h1 h2 => hag addr (by omega),
      hpres := fun e he => (hag _ (by omega)).trans (c.hpres e he) }
  have hr₁' : r₁ = nd := hr₁
  subst hr₁'
  refine runs_seq_call_le (vs := [c.esPtr, c.es.length, c.presY, c.gPtr, c.da.out + 2 * nd])
    (dsInsRecords_meetsContract ci hpOps hpI)
    (by
      simp only [evalArgs, Expr.eval, BinOp.eval]
      simp [startState, show (2 : ℕ) < 2 ^ c.da.w by omega, show 2 * nd < 2 ^ c.da.w by omega,
        show c.da.out + 2 * nd < 2 ^ c.da.w by omega])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl|rfl|rfl)
      · exact hargsW _ (by simp)
      · omega
      · exact hargsW _ (by simp)
      · exact hargsW _ (by simp)
      · omega)
    ⟨rfl, rfl⟩ ?_
  rintro r₂ mem₂ pos₂ ⟨hr₂, hL₂, hfr₂⟩
  simp only [ci] at hr₂ hL₂ hfr₂
  have hr₂' : r₂ = (insList c.Y c.es).length := hr₂
  subst hr₂'
  have hil := insList_length_le c.Y c.es
  refine runs_ret_le (v := nd + (insList c.Y c.es).length)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (by omega))
    ⟨by simp [UTCtx.recs, insRecs, hnd, hcat, Outcome.value], fun K => ?_, fun i hi => ?_,
      fun addr h => ?_⟩ ?_
  all_goals
    have hdwl : (delWords c.da.X cat).length = 2 * nd := by
      simp only [delWords, hnd]
      induction delList c.da.X cat with
      | nil => simp
      | cons a t ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
          List.length_nil, ih]; omega
    have h1 : ListAt mem₂ c.da.out (delWords c.da.X cat) := hL₁.congr fun k h1 h2 =>
      hfr₂ k (by omega)
  · -- Deletions, then insertions.
    have hb1 := delRecs_batchBodyAt (mem := mem₂) K c.da.X cat c.da.out h1
    have hb2 := insRecs_batchBodyAt (mem := mem₂) c.G
      (K.applyBatch ((delList c.da.X cat).map Update.delete)) c.Y c.es (c.da.out + 2 * nd) hL₂
    exact batchBodyAt_append hb1 hb2
  · -- The words are below `2 ^ w`.
    simp only [← hcat] at hi
    have heC : c.da.eCap < 2 ^ c.da.w := by omega
    have hvC : c.vCap < 2 ^ c.da.w := by simp only [dynGraphSize] at hgB; omega
    have hiwl := insWords_length c.G c.Y c.es
    by_cases hi1 : i < 2 * nd
    · refine listAt_words_lt h1 (fun x hx => ?_) i (by omega)
      rcases mem_delWords hx with rfl | hx
      · omega
      · have := hcatC' x hx; omega
    · have := listAt_words_lt (B := 2 ^ c.da.w) hL₂ (fun x hx => ?_) (i - 2 * nd) (by omega)
      · rwa [show c.da.out + 2 * nd + (i - 2 * nd) = c.da.out + i by omega] at this
      · rcases mem_insWords hx with h | ⟨e, he, h | h | h⟩ <;> rw [h]
        · omega
        · have := c.hG.2.2.1 e (c.hesG e he); omega
        · have := c.hG.2.1 _ (c.hGcap e (c.hesG e he)).1; omega
        · have := c.hG.2.1 _ (c.hGcap e (c.hesG e he)).2; omega
  · show mem₂ addr = _
    simp only [UTCtx.size, ← hcat] at h
    exact (hfr₂ addr (by omega)).trans (hfr₁ addr (by omega))
  · simp only [Expr.size, argsSize, dsUHTailContract, dsDelAllContract, dsInsRecordsContract, ci,
      ← hcat]
    omega

end

end MinCostFlow.DynSpanner.Program
