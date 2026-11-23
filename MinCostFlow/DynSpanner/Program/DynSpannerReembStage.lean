module

public import MinCostFlow.DynSpanner.Program.DynSpannerCompAll
public import MinCostFlow.DynSpanner.Program.DynSpannerReembedAll
import WordRAM.Tactic

/-!
# The re-embedding stage of a step

After the call of `Sparsify` and the shortcut of its walks, Algorithm 6 composes the walks
(`embMid = Embedding.comp embJH outEmb`) and re-embeds every affected edge (line 85). The
procedure `dsReembStageStmt` calls `dsCompAllStmt` and then `dsReembedAllStmt`. The heap area
`[heap, heap + reembStageNeed)` holds, in this order, the pointers to the walks `embMid e`, these
walks, and the new walks `Π_j(e)` with their scratch space.

`dsReembStage_meetsContract` proves the contract. The inputs (the graph, `sBit`, the tables, the
lists and all input walks) are outside the heap area, and the pointer table `piTab` of level `j`
is disjoint from the heap area and from the inputs that the second call reads.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The re-embedding stage
(`args = [gPtr, sBitPtr, tab, piTab, esPtr, esLen, wpPtr, qTab, heap]`); returns the final heap
pointer. -/
def dsReembStageStmt (bA bR : ℕ) : Stmt :=
  .call 9 (bA + compAllIdx) [.reg 7, .reg 2, .reg 4, .reg 5, .reg 8, .bin .add (.reg 8) (.reg 5)] ;;
  .call 10 (bR + reembedAllIdx) [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6, .reg 8, .reg 3, .reg 9] ;;
  .ret (.reg 10)

def reembStageProcs (bA bR : ℕ) : List Stmt := [dsReembStageStmt bA bR]

def reembStageIdx : ℕ := 0

lemma reembStageProcs_noRand (bA bR : ℕ) : ∀ s ∈ reembStageProcs bA bR, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Heap words used by the stage. -/
def reembStageNeed (embLt embJH outEmb : Embedding) (es : List ℕ) : ℕ :=
  es.length + compHeapNeed embJH outEmb es +
    reembHeapNeed embLt (Embedding.comp embJH outEmb) es

/-- The data and the precondition of the stage. -/
structure RSCtx where
  w : ℕ
  vCap : ℕ
  eCap : ℕ
  G : MGraph
  embLt : Embedding
  embJH : Embedding
  outEmb : Embedding
  S : Finset ℕ
  es : List ℕ
  gPtr : ℕ
  sBitPtr : ℕ
  tab : ℕ
  piTab : ℕ
  esPtr : ℕ
  wpPtr : ℕ
  qTab : ℕ
  heap : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hgB : gPtr + dynGraphSize vCap eCap < 2 ^ w
  hsB : sBitPtr + vCap < 2 ^ w
  htB : tab + eCap < 2 ^ w
  hpB : piTab + eCap < 2 ^ w
  hesB : esPtr + es.length < 2 ^ w
  hwpB : wpPtr + es.length < 2 ^ w
  hqB : qTab + eCap < 2 ^ w
  hhB : heap + reembStageNeed embLt embJH outEmb es < 2 ^ w
  dRG : IvlDisj heap (reembStageNeed embLt embJH outEmb es) gPtr (dynGraphSize vCap eCap)
  dRS : IvlDisj heap (reembStageNeed embLt embJH outEmb es) sBitPtr vCap
  dRT : IvlDisj heap (reembStageNeed embLt embJH outEmb es) tab eCap
  dRP : IvlDisj heap (reembStageNeed embLt embJH outEmb es) piTab eCap
  dRE : IvlDisj heap (reembStageNeed embLt embJH outEmb es) esPtr es.length
  dRW : IvlDisj heap (reembStageNeed embLt embJH outEmb es) wpPtr es.length
  dRQ : IvlDisj heap (reembStageNeed embLt embJH outEmb es) qTab eCap
  dPG : IvlDisj piTab eCap gPtr (dynGraphSize vCap eCap)
  dPS : IvlDisj piTab eCap sBitPtr vCap
  dPE : IvlDisj piTab eCap esPtr es.length
  dPW : IvlDisj piTab eCap wpPtr es.length
  hwalk : ∀ k (hk : k < es.length),
    MWalkAt mem0 (mem0 (wpPtr + k)) (embLt es[k]) ∧
    mem0 (wpPtr + k) + (2 * (embLt es[k]).length + 1) < 2 ^ w ∧
    IvlDisj heap (reembStageNeed embLt embJH outEmb es) (mem0 (wpPtr + k))
      (2 * (embLt es[k]).length + 1) ∧
    IvlDisj piTab eCap (mem0 (wpPtr + k)) (2 * (embLt es[k]).length + 1) ∧
    MWalkAt mem0 (mem0 (qTab + es[k])) (outEmb es[k]) ∧
    mem0 (qTab + es[k]) + (2 * (outEmb es[k]).length + 1) < 2 ^ w ∧
    IvlDisj heap (reembStageNeed embLt embJH outEmb es) (mem0 (qTab + es[k]))
      (2 * (outEmb es[k]).length + 1) ∧
    ∀ x ∈ outEmb es[k], x.1 < eCap ∧ MWalkAt mem0 (mem0 (tab + x.1)) (embJH x.1) ∧
      mem0 (tab + x.1) + (2 * (embJH x.1).length + 1) < 2 ^ w ∧
      IvlDisj heap (reembStageNeed embLt embJH outEmb es) (mem0 (tab + x.1))
        (2 * (embJH x.1).length + 1) ∧
      ∀ y ∈ embJH x.1, y.1 < eCap
  hG : DynGraphAt mem0 gPtr vCap eCap G
  hGv : G.IsValid
  hVc : ∀ v ∈ G.V, v < vCap
  hEc : ∀ e ∈ G.E, e < eCap
  hes : ListAt mem0 esPtr es
  hnd : es.Nodup
  hesG : ∀ e ∈ es, e ∈ G.E
  hPw : ∀ e ∈ es, PrefixWalksValid G S eCap (G.tail e) (G.head e) (embLt e)
  hsBit : ∀ v < vCap, mem0 (sBitPtr + v) = if v ∈ S then 1 else 0

/-- Contract of `dsReembStageStmt`. -/
def dsReembStageContract (c : RSCtx) : Contract where
  pre args mem :=
    args = [c.gPtr, c.sBitPtr, c.tab, c.piTab, c.esPtr, c.es.length, c.wpPtr, c.qTab, c.heap] ∧
    mem = c.mem0
  post _ mem ret mem' :=
    (∀ e ∈ c.es,
      c.heap + c.es.length + compHeapNeed c.embJH c.outEmb c.es ≤ mem' (c.piTab + e) ∧
      mem' (c.piTab + e) +
        reembOutLen c.G c.embLt (Embedding.comp c.embJH c.outEmb) c.S e ≤ ret ∧
      MWalkAt mem' (mem' (c.piTab + e))
        (reembedWalk c.G c.G c.embLt (Embedding.comp c.embJH c.outEmb) c.S e)) ∧
    ret = reembHeapAt c.G c.embLt (Embedding.comp c.embJH c.outEmb) c.S c.es
      (c.heap + c.es.length + compHeapNeed c.embJH c.outEmb c.es) c.es.length ∧
    ∀ addr, (addr < c.heap ∨ c.heap + reembStageNeed c.embLt c.embJH c.outEmb c.es ≤ addr) →
      (∀ e ∈ c.es, addr ≠ c.piTab + e) → mem' addr = mem addr
  cost _ _ := compAllCost c.embJH c.outEmb c.es +
    reembedAllCost c.embLt (Embedding.comp c.embJH c.outEmb) c.es + 40

end

/-- The edges of a composed walk are edges of the pieces. -/
private lemma comp_edge_lt {T Q : Embedding} {eCap e : ℕ}
    (hQ : ∀ x ∈ Q e, ∀ y ∈ T x.1, y.1 < eCap) :
    ∀ x ∈ Embedding.comp T Q e, x.1 < eCap := by
  intro x hx
  rw [comp_eq_flatMap, List.mem_flatMap] at hx
  obtain ⟨y, hy, hx⟩ := hx
  unfold compPiece at hx
  split_ifs at hx
  · exact hQ y hy x hx
  · obtain ⟨z, hz, hzx⟩ := mem_walkRev_fst hx
    rw [← hzx]; exact hQ y hy z hz

public section

/-- `dsReembStageStmt` meets `dsReembStageContract`. -/
theorem dsReembStage_meetsContract (c : RSCtx) {p : Program}
    {bS bA bR bC bOps bRe bEmb : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpRe : p.HasAt bRe (reembedProcs bEmb))
    (hpEmb : p.HasAt bEmb (embOpsProcs bOps)) (hpC : p.HasAt bC (compProcs bEmb))
    (hpA : p.HasAt bA (compAllProcs bC)) (hpR : p.HasAt bR (reembedAllProcs bOps bRe))
    (hpS : p.HasAt bS (reembStageProcs bA bR)) :
    MeetsContract c.w p (bS + reembStageIdx) (dsReembStageContract c) := by
  refine meetsContract_of_runs
    (hpS.get (i := reembStageIdx) (by simp [reembStageProcs, reembStageIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem⟩
  subst hmem
  simp only [reembStageProcs, reembStageIdx, List.getElem_cons_zero]
  dsimp only [dsReembStageStmt]
  have hw16 := c.hw16
  have hgB := c.hgB
  have hsB := c.hsB
  have htB := c.htB
  have hpB := c.hpB
  have hesB := c.hesB
  have hwpB := c.hwpB
  have hqB := c.hqB
  have hhB := c.hhB
  have heCap : c.eCap ≤ dynGraphSize c.vCap c.eCap := by simp only [dynGraphSize]; omega
  set CN := compHeapNeed c.embJH c.outEmb c.es with hCN
  set RN := reembHeapNeed c.embLt (Embedding.comp c.embJH c.outEmb) c.es with hRN
  have hneed : reembStageNeed c.embLt c.embJH c.outEmb c.es = c.es.length + CN + RN := rfl
  have dRG := c.dRG; have dRS := c.dRS; have dRT := c.dRT; have dRP := c.dRP
  have dRE := c.dRE; have dRW := c.dRW; have dRQ := c.dRQ
  rw [hneed] at dRG dRS dRT dRP dRE dRW dRQ hhB
  have toC : ∀ {y ly}, IvlDisj c.heap (c.es.length + CN + RN) y ly →
      IvlDisj (c.heap + c.es.length) CN y ly := fun h => h.sub_left (by omega) (by omega)
  have toM : ∀ {y ly}, IvlDisj c.heap (c.es.length + CN + RN) y ly →
      IvlDisj c.heap c.es.length y ly := fun h => h.sub_left (by omega) (by omega)
  have toR : ∀ {y ly}, IvlDisj c.heap (c.es.length + CN + RN) y ly →
      IvlDisj (c.heap + c.es.length + CN) RN y ly := fun h => h.sub_left (by omega) (by omega)
  -- Compose the walks.
  refine runs_start_le ?_
  refine runs_seq_call_le (dsCompAll_meetsContract (w := c.w) (eCap := c.eCap) (T := c.embJH)
      (outEmb := c.outEmb) (es := c.es) hpC hpEmb hpA) (by eval_expr)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨c.qTab, c.tab, c.esPtr, c.heap, c.heap + c.es.length, rfl, hw16, hqB, htB, hesB, by omega,
      by omega, toC dRQ, toC dRT, toC dRE, Or.inr (by omega), toM dRQ, toM dRT, toM dRE, c.hes,
      fun k hk => by
        obtain ⟨_, _, _, _, hQ, hQb, dQ, hxs⟩ := c.hwalk k hk
        refine ⟨c.hEc _ (c.hesG _ (List.getElem_mem hk)), hQ, hQb,
          toC dQ, toM dQ, fun x hx => ?_⟩
        obtain ⟨h1, h2, h3, h4, h5⟩ := hxs x hx
        exact ⟨h1, h2, h3, toC h4, toM h4, h5⟩⟩ ?_
  rintro r₉ mem₁ pos₁ ⟨_, _, _, _, _, hargs₁, hmp, hret₁, hfr₁⟩
  simp only [List.cons.injEq, and_true] at hargs₁
  obtain ⟨rfl, rfl, rfl, -, rfl, rfl⟩ := hargs₁
  have hall := compHeapAt_all c.embJH c.outEmb c.es (c.heap + c.es.length)
  rw [← hCN] at hall
  -- Memory outside the first heap part is unchanged.
  have hrd : ∀ addr, (addr < c.heap ∨ c.heap + (c.es.length + CN + RN) ≤ addr) →
      mem₁ addr = c.mem0 addr := fun addr h => hfr₁ addr (by omega) (by omega)
  have hG₁ : DynGraphAt mem₁ c.gPtr c.vCap c.eCap c.G :=
    dynGraphAt_of_agree c.hG fun addr h1 h2 =>
      hrd addr (dRG.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr h1 h2)
  have hes₁ : ListAt mem₁ c.esPtr c.es :=
    c.hes.congr fun k h1 h2 => hrd k (dRE.addr_sub (Nat.le_refl _) (Nat.le_refl _) k h1 h2)
  have hS₁ : ∀ v < c.vCap, mem₁ (c.sBitPtr + v) = if v ∈ c.S then 1 else 0 := fun v hv =>
    (hrd _ (dRS.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hsBit v hv)
  have hwalk₁ : ∀ k (hk : k < c.es.length),
      MWalkAt mem₁ (mem₁ (c.wpPtr + k)) (c.embLt c.es[k]) ∧
      mem₁ (c.wpPtr + k) + (2 * (c.embLt c.es[k]).length + 1) < 2 ^ c.w ∧
      IvlDisj (c.heap + c.es.length + CN) RN (mem₁ (c.wpPtr + k))
        (2 * (c.embLt c.es[k]).length + 1) ∧
      IvlDisj c.piTab c.eCap (mem₁ (c.wpPtr + k)) (2 * (c.embLt c.es[k]).length + 1) ∧
      MWalkAt mem₁ (mem₁ (c.heap + k)) (Embedding.comp c.embJH c.outEmb c.es[k]) ∧
      mem₁ (c.heap + k) + (2 * (Embedding.comp c.embJH c.outEmb c.es[k]).length + 1) <
        2 ^ c.w ∧
      IvlDisj (c.heap + c.es.length + CN) RN (mem₁ (c.heap + k))
        (2 * (Embedding.comp c.embJH c.outEmb c.es[k]).length + 1) ∧
      IvlDisj c.piTab c.eCap (mem₁ (c.heap + k))
        (2 * (Embedding.comp c.embJH c.outEmb c.es[k]).length + 1) := by
    intro k hk
    obtain ⟨hW, hWb, dW, dWP, _⟩ := c.hwalk k hk
    have hwp₁ : mem₁ (c.wpPtr + k) = c.mem0 (c.wpPtr + k) :=
      hrd _ (dRW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
    obtain ⟨hmk, hMk⟩ := hmp k hk
    have hsk := compHeapAt_succ c.embJH c.outEmb c.es (c.heap + c.es.length) k hk
    have hmono := compHeapAt_mono c.embJH c.outEmb c.es (c.heap + c.es.length)
      (show k + 1 ≤ c.es.length by omega)
    have hlo : c.heap + c.es.length ≤ compHeapAt c.embJH c.outEmb c.es (c.heap + c.es.length) k := by
      simp only [compHeapAt]; omega
    simp only [compOutLen, ← comp_eq_flatMap] at hsk
    rw [hwp₁, hmk]
    refine ⟨hW.of_agree fun addr h1 h2 => hrd addr (dW.addr_sub (Nat.le_refl _) (Nat.le_refl _)
        addr h1 (by omega)), hWb, toR dW, dWP, hMk, by omega,
      Or.inr (by omega), ?_⟩
    exact (dRP.sub_left (x' := compHeapAt c.embJH c.outEmb c.es (c.heap + c.es.length) k)
      (lx' := 2 * (Embedding.comp c.embJH c.outEmb c.es[k]).length + 1)
      (by omega) (by omega)).symm
  -- Re-embed.
  refine runs_seq_call_le (dsReembedAll_meetsContract (w := c.w) (vCap := c.vCap)
      (eCap := c.eCap) (G := c.G) (embLt := c.embLt) (embMid := Embedding.comp c.embJH c.outEmb)
      (S := c.S) (es := c.es) hpOps hpRe hpEmb hpR) (by eval_expr)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨c.gPtr, c.sBitPtr, c.esPtr, c.wpPtr, c.heap, c.piTab, c.heap + c.es.length + CN,
      by rw [hall], hw16, hgB, hsB, hesB, hwpB, by omega, hpB, by omega,
      toR dRG, toR dRS, toR dRE, toR dRW, Or.inr (by omega), toR dRP,
      c.dPG, c.dPS, c.dPE, c.dPW, (toM dRP).symm,
      hwalk₁, hG₁, c.hGv, c.hVc, c.hEc, hes₁, c.hnd, c.hesG, c.hPw,
      fun e he => comp_edge_lt (fun x hx y hy => by
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
        exact ((c.hwalk k hk).2.2.2.2.2.2.2 x hx).2.2.2.2 y hy), hS₁⟩ ?_
  rintro r₁₀ mem₂ pos₂ ⟨_, _, _, _, _, _, _, hargs₂, hT₂, hret₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at hargs₂
  obtain ⟨rfl, rfl, rfl, -, rfl, rfl, rfl, hh₂⟩ := hargs₂
  rw [hall] at hh₂
  subst hh₂
  refine runs_ret_le (v := r₁₀) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · refine ⟨hT₂, hret₂, fun addr hH hP => ?_⟩
    rw [hneed] at hH
    show mem₂ _ = _
    rw [hfr₂ addr (by omega) hP]
    exact hrd addr hH
  · simp only [dsCompAllContract, dsReembedAllContract, dsReembStageContract,
      Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
    omega

end

end MinCostFlow.DynSpanner.Program
