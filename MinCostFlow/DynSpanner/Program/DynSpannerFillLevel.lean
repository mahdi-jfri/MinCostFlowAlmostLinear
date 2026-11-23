module

public import MinCostFlow.DynSpanner.Program.DynSpannerPhase
public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
import WordRAM.Tactic

/-!
# Filling the bucket of level `j`

After a rebuild of level `j` the buckets of the levels `j ≤ i ≤ L` are emptied
(`dsClearBucketsStmt`), which sets `minH[e] := 0` for their edges. Then the edges of `J̃` whose
smallest level is now `j` are exactly those with `minH[e] = 0`: an edge of `J̃` with
`minH[e] ≠ 0` lies in a level below `j`. `dsFillLevelStmt` walks over a list `es` (the edges of
`J̃`) and puts each edge with `minH[e] = 0` into bucket `j` with `hBucketConsStmt`, which also sets
`minH[e] := j + 1`. `dsFillLevel_meetsContract` proves that bucket `j` becomes
`A.reverse ++ B₀`, where `A` is the list of these edges and `B₀` the old bucket.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- One edge `e = es[r5]`. -/
def dsFillLevelBodyStmt (bPhase : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 2) (.reg 5))) ;;
  .assign 7 (.load (.bin .add (.reg 4) (.reg 6))) ;;
  .cond (.reg 7) .nop (.call 8 (bPhase + phaseIdxHBucketCons) [.reg 0, .reg 1, .reg 6])

/-- `args = [b, j, esPtr, esLen, minHBase]`. -/
def dsFillLevelStmt (bPhase : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 3) (dsFillLevelBodyStmt bPhase) ;;
  .ret (.const 0)

def fillLevelProcs (bPhase : ℕ) : List Stmt := [dsFillLevelStmt bPhase]

def fillLevelIdx : ℕ := 0

lemma fillLevelProcs_noRand (bPhase : ℕ) : ∀ s ∈ fillLevelProcs bPhase, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The data and the precondition of `dsFillLevelStmt`. -/
structure FLCtx where
  w : ℕ
  L : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  j : ℕ
  es : List ℕ
  esPtr : ℕ
  B₀ : List ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hbound : b + dsFixedSize L vCap eCap < 2 ^ w
  hjL : j ≤ L
  hLw : mem0 (b + dsLOff) = L
  hvw : mem0 (b + dsVCapOff) = vCap
  hew : mem0 (b + dsECapOff) = eCap
  hesB : esPtr + es.length < 2 ^ w
  dEB : IvlDisj esPtr es.length b (dsFixedSize L vCap eCap)
  hes : ListAt mem0 esPtr es
  hnd : es.Nodup
  hesC : ∀ e ∈ es, e < eCap
  hdll : IsDoublyLinkedList mem0 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
    (dsHHeadBase b vCap eCap + j) eCap B₀
  hdeg : mem0 (dsHDegDummyBase b L vCap eCap + j) = B₀.length
  hB₀ : ∀ x ∈ B₀, mem0 (dsMinHBase b vCap eCap + x) ≠ 0

/-- The edges of `es` with `minH[e] = 0` at the start. -/
def FLCtx.added (c : FLCtx) (es : List ℕ) : List ℕ :=
  es.filter fun e => decide (c.mem0 (dsMinHBase c.b c.vCap c.eCap + e) = 0)

/-- The bucket facts and the frame after the edges `A` were added. -/
def FLMem (c : FLCtx) (A : List ℕ) (mem : ℕ → ℕ) : Prop :=
  IsDoublyLinkedList mem (dsHPrevBase c.b c.vCap c.eCap) (dsHNextBase c.b c.vCap c.eCap)
    (dsHHeadBase c.b c.vCap c.eCap + c.j) c.eCap (A.reverse ++ c.B₀) ∧
  mem (dsHDegDummyBase c.b c.L c.vCap c.eCap + c.j) = A.length + c.B₀.length ∧
  (∀ e ∈ A, mem (dsMinHBase c.b c.vCap c.eCap + e) = c.j + 1) ∧
  ∀ addr, (∀ e ∈ A, addr ≠ dsMinHBase c.b c.vCap c.eCap + e) →
    addr ≠ dsHHeadBase c.b c.vCap c.eCap + c.j →
    addr ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + c.j →
    (∀ x, addr = dsHPrevBase c.b c.vCap c.eCap + x → x ∉ A.reverse ++ c.B₀) →
    (∀ x, addr = dsHNextBase c.b c.vCap c.eCap + x → x ∉ A.reverse ++ c.B₀) →
    mem addr = c.mem0 addr

/-- Contract of `dsFillLevelStmt`. -/
def dsFillLevelContract (c : FLCtx) : Contract where
  pre args mem :=
    args = [c.b, c.j, c.esPtr, c.es.length, dsMinHBase c.b c.vCap c.eCap] ∧ mem = c.mem0
  post _ _ _ mem' := FLMem c (c.added c.es) mem'
  cost _ _ := 210 * c.es.length + 20

/-- The loop invariant after the first `k` edges. -/
def FLInv (c : FLCtx) (k : ℕ) (st : State) : Prop :=
  st.regs 0 = c.b ∧ st.regs 1 = c.j ∧ st.regs 2 = c.esPtr ∧ st.regs 3 = c.es.length ∧
  st.regs 4 = dsMinHBase c.b c.vCap c.eCap ∧ st.regs 5 = k ∧
  FLMem c (c.added (c.es.take k)) st.mem

end

private lemma block_facts (b L vCap eCap : ℕ) :
    b + 6 ≤ dsMinHBase b vCap eCap ∧
    dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap ∧
    dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap ∧
    dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap ∧
    dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) ≤ b + dsFixedSize L vCap eCap := by
  refine ⟨by simp only [dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr, dsHdrSize]; omega, rfl, rfl, rfl,
    rfl, ?_⟩
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
    dsEdgeDomGenBase, dsDomGenBase]
  omega

private lemma added_succ (c : FLCtx) (k : ℕ) (hk : k < c.es.length) :
    c.added (c.es.take (k + 1)) = c.added (c.es.take k) ++
      if c.mem0 (dsMinHBase c.b c.vCap c.eCap + c.es[k]) = 0 then [c.es[k]] else [] := by
  simp only [FLCtx.added, List.take_succ_eq_append_getElem hk, List.filter_append]
  split_ifs with h <;> simp [h]

private lemma getElem_not_mem_take {l : List ℕ} (hnd : l.Nodup) {k : ℕ} (hk : k < l.length) :
    l[k] ∉ l.take k := by
  intro h
  obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem h
  rw [List.getElem_take] at hieq
  have := (List.Nodup.getElem_inj_iff hnd).mp hieq
  simp only [List.length_take] at hi
  omega

public section

/-- One iteration of the loop of `dsFillLevelStmt`. -/
theorem dsFillLevel_step_triple (c : FLCtx) {p : Program} {bPhase bOps bEdge : ℕ}
    (hpP : p.HasAt bPhase (phaseProcs bOps bEdge)) (hpOps : p.HasAt bOps dgOpsProcs)
    {k : ℕ} (hk : k < c.es.length) :
    Triple c.w p (FLInv c k) (dsFillLevelBodyStmt bPhase)
      (normalPost fun st₁ =>
        FLInv c (k + 1) { st₁ with regs := Function.update st₁.regs 5 (k + 1) } ∧
          st₁.regs 5 = k)
      (fun _ => 200) := by
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r4, r5, hdll, hdeg, hmin, hfr⟩ := hI
  have hw16 := c.hw16
  have hbound := c.hbound
  have hesB := c.hesB
  have hjL := c.hjL
  obtain ⟨hb, hn, hp, hh, hd, hfix⟩ := block_facts c.b c.L c.vCap c.eCap
  set A := c.added (c.es.take k) with hA
  set e := c.es[k] with he
  have heC : e < c.eCap := c.hesC e (List.getElem_mem hk)
  have hcap := hdll.2.1
  have heA : e ∉ A := by
    intro h
    have h' := List.mem_of_mem_filter h
    exact getElem_not_mem_take c.hnd hk h'
  -- Reading outside the bucket block.
  have hout : ∀ addr, (addr < c.b ∨ c.b + dsFixedSize c.L c.vCap c.eCap ≤ addr) →
      st.mem addr = c.mem0 addr := fun addr h =>
    hfr addr (fun e' he' => by
      have := c.hesC e' (List.mem_of_mem_take (List.mem_of_mem_filter he')); omega)
      (by omega) (by omega)
      (fun x hx hxL => by have := hcap x hxL; omega)
      (fun x hx hxL => by have := hcap x hxL; omega)
  have hes_rd : st.mem (c.esPtr + k) = e :=
    (hout _ (c.dEB.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hes k hk)
  have hmin_rd : st.mem (dsMinHBase c.b c.vCap c.eCap + e) =
      c.mem0 (dsMinHBase c.b c.vCap c.eCap + e) :=
    hfr _ (fun e' he' h => heA (by
        have : e = e' := by omega
        rw [this]; exact he'))
      (by omega) (by omega) (fun x hx => by omega) (fun x hx => by omega)
  have hsucc := added_succ c k hk
  rw [← hA, ← he] at hsucc
  dsimp only [dsFillLevelBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r2) (Expr.eval_reg_of_eq r5)
      (by omega)) hes_rd) ?_
  refine runs_seq_assign_le (v := c.mem0 (dsMinHBase c.b c.vCap c.eCap + e))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) hmin_rd) ?_
  refine runs_cond_le (v := c.mem0 (dsMinHBase c.b c.vCap c.eCap + e))
    (Expr.eval_reg_of_eq (by simp)) (fun hne => ?_) (fun hz => ?_)
  · -- `minH[e] ≠ 0`: `e` stays where it is.
    simp only [hne, ite_false, List.append_nil] at hsucc
    refine runs_nop_le ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
      by simp, ?_⟩, by simp [r5]⟩ (by simp [Expr.size])
    rw [hsucc]
    exact ⟨hdll, hdeg, hmin, hfr⟩
  · -- `minH[e] = 0`: put `e` into bucket `j`.
    simp only [hz, ite_true] at hsucc
    have heB₀ : e ∉ c.B₀ := fun h => c.hB₀ e h hz
    have heL : e ∉ A.reverse ++ c.B₀ := by
      simp only [List.mem_append, List.mem_reverse, not_or]; exact ⟨heA, heB₀⟩
    have hvw : st.mem (c.b + dsVCapOff) = c.vCap :=
      (hfr _ (fun e' he' => by
        have := c.hesC e' (List.mem_of_mem_take (List.mem_of_mem_filter he'))
        simp only [dsVCapOff]; omega) (by simp only [dsVCapOff]; omega)
        (by simp only [dsVCapOff]; omega) (fun x hx => by simp only [dsVCapOff] at hx; omega)
        (fun x hx => by simp only [dsVCapOff] at hx; omega)).trans c.hvw
    have hew : st.mem (c.b + dsECapOff) = c.eCap :=
      (hfr _ (fun e' he' => by
        have := c.hesC e' (List.mem_of_mem_take (List.mem_of_mem_filter he'))
        simp only [dsECapOff]; omega) (by simp only [dsECapOff]; omega)
        (by simp only [dsECapOff]; omega) (fun x hx => by simp only [dsECapOff] at hx; omega)
        (fun x hx => by simp only [dsECapOff] at hx; omega)).trans c.hew
    have hLw : st.mem (c.b + dsLOff) = c.L :=
      (hfr _ (fun e' he' => by
        have := c.hesC e' (List.mem_of_mem_take (List.mem_of_mem_filter he'))
        simp only [dsLOff]; omega) (by simp only [dsLOff]; omega)
        (by simp only [dsLOff]; omega) (fun x hx => by simp only [dsLOff] at hx; omega)
        (fun x hx => by simp only [dsLOff] at hx; omega)).trans c.hLw
    refine runs_call_le (hBucketCons_meetsContract (w := c.w) (L := c.L) (vCap := c.vCap)
        (eCap := c.eCap) (b := c.b) (L_buck := A.reverse ++ c.B₀) (i := c.j) (e := e) hpP hpOps)
      (by eval_expr)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
      ⟨by simp [he], hw16, hbound, hjL, heC, heL, hLw, hvw, hew, hdll,
        by rw [hdeg]; simp⟩
      (fun v mem' pos' hpost => ?_)
    obtain ⟨_, _, hmin', hdll', hdeg', hfr'⟩ := hpost
    have hrev : (A ++ [e]).reverse ++ c.B₀ = e :: (A.reverse ++ c.B₀) := by simp
    refine ⟨⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp, ?_⟩,
      by simp [r5]⟩, ?_⟩
    · rw [hsucc]
      show FLMem c (A ++ [e]) mem'
      refine ⟨by rw [hrev]; exact hdll', by rw [hdeg']; simp; omega, fun e' he' => ?_,
        fun addr h1 h2 h3 h4 h5 => ?_⟩
      · rcases List.mem_append.mp he' with he' | he'
        · have hne : e' ≠ e := fun h => heA (h ▸ he')
          have := c.hesC e' (List.mem_of_mem_take (List.mem_of_mem_filter he'))
          rw [hfr' _ (by omega) (by omega) (by omega) (fun x hx => by omega) (fun x hx => by omega)]
          exact hmin e' he'
        · rw [List.mem_singleton.mp he']; exact hmin'
      · rw [hrev] at h4 h5
        rw [hfr' addr (h1 e (List.mem_append.mpr (Or.inr (List.mem_singleton_self e)))) h2 h3 h4 h5]
        exact hfr addr (fun e' he' => h1 e' (List.mem_append.mpr (Or.inl he'))) h2 h3
          (fun x hx hxL => h4 x hx (List.mem_cons_of_mem _ hxL))
          (fun x hx hxL => h5 x hx (List.mem_cons_of_mem _ hxL))
    · simp only [hBucketConsContract, Expr.size_reg, Expr.size_load,
        Expr.size_bin, argsSize_cons, argsSize_nil]
      omega


/-- `dsFillLevelStmt` meets `dsFillLevelContract`. -/
theorem dsFillLevel_meetsContract (c : FLCtx) {p : Program} {bF bPhase bOps bEdge : ℕ}
    (hpP : p.HasAt bPhase (phaseProcs bOps bEdge)) (hpOps : p.HasAt bOps dgOpsProcs)
    (hpF : p.HasAt bF (fillLevelProcs bPhase)) :
    MeetsContract c.w p (bF + fillLevelIdx) (dsFillLevelContract c) := by
  refine meetsContract_of_runs
    (hpF.get (i := fillLevelIdx) (by simp [fillLevelProcs, fillLevelIdx])) ?_
  rintro args mem pos ω hwords ⟨rfl, hmem⟩
  subst hmem
  simp only [fillLevelProcs, fillLevelIdx, List.getElem_cons_zero]
  dsimp only [dsFillLevelStmt]
  have hw16 := c.hw16
  have hesB := c.hesB
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st' => st' = startState [c.b, c.j, c.esPtr, c.es.length,
      dsMinHBase c.b c.vCap c.eCap] c.mem0 pos)
    (r := 5) (lo := .const 0) (hi := .reg 3) (body := dsFillLevelBodyStmt bPhase)
    (Inv := FLInv c) 200 0 c.es.length (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st' h => by
      subst h
      refine ⟨Expr.eval_const (by omega), by simp [startState], by simp [startState],
        by simp [startState], by simp [startState], by simp [startState], by simp, ?_⟩
      show FLMem c (c.added (c.es.take 0)) c.mem0
      rw [List.take_zero]
      refine ⟨by simpa [FLCtx.added] using c.hdll, by simpa [FLCtx.added] using c.hdeg,
        fun e he => by simp [FLCtx.added] at he, fun _ _ _ _ _ _ => rfl⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
    (fun k _ hk => dsFillLevel_step_triple c hpP hpOps hk)
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl ?_
  intro st hI
  obtain ⟨_, _, _, _, _, _, hM⟩ := hI
  rw [List.take_of_length_le (Nat.le_refl _)] at hM
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) hM ?_
  simp only [Expr.size, dsFillLevelContract]
  omega

end

end MinCostFlow.DynSpanner.Program
