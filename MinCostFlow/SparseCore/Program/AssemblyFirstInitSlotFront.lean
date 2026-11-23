module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotWalk
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The slots of the active pairs at the init: the front of the procedure (`AssemblyFirstInitSlotFront`)

The front of `slotListBody` is the setup of the registers and the first three loops: the count of
the edges of each component, the active flags, and the marks of the forest edges. This file proves
that the front runs and says what it leaves (`slotListFront_runs`). The rest of the procedure is in
`AssemblyFirstInitSlotRun.lean`.

The component of an edge `e` is the word `cmpH + tail e` of the memory before the call. We write it
`slotCOf mem cmpH G e`. The number of edges of component `c` is `slotCnt`, and the flag of `c` is on
when this number `x` has `1 ≤ x` and `k ≤ 4 x` (`SlotFlagOn`), as in `largeComps`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-! ## The objects of the procedure -/

/-- The component of edge `e`: the word at `cmpH + tail e`. -/
def slotCOf (mem : ℕ → ℕ) (cmpH : ℕ) (G : MGraph) (e : ℕ) : ℕ := mem (cmpH + G.tail e)

/-- The number of edges of `G` in component `c`. -/
noncomputable def slotCnt (G : MGraph) (cOf : ℕ → ℕ) (c : ℕ) : ℕ :=
  open Classical in (G.E.filter fun e => cOf e = c).card

/-- The flag of a component with `x` edges is on: `1 ≤ x` and `k ≤ 4 x`. -/
abbrev SlotFlagOn (k x : ℕ) : Prop := 1 ≤ x ∧ k ≤ 4 * x

/-- The forest edges in P4's export: the first words of the `nF` triples at `fTrip`. -/
def slotForestEdges (mem : ℕ → ℕ) (fTrip nF : ℕ) : List ℕ :=
  (List.range nF).map fun t => mem (fTrip + 3 * t)

/-- The registers after the setup of `slotListBody`. -/
def SlotRegs (regs : ℕ → ℕ) (graph cmpH bktH nComp k B ctH heap vCap eCap m nF fTrip : ℕ) :
    Prop :=
  regs 2 = cmpH ∧ regs 3 = bktH ∧ regs 4 = nComp ∧ regs 5 = k ∧ regs 6 = B ∧ regs 7 = ctH ∧
  regs 8 = heap ∧ regs 11 = m ∧ regs 12 = dgEListBase graph vCap eCap ∧
  regs 13 = dgETailSlotBase graph vCap eCap ∧ regs 14 = dgIntToExtBase graph vCap ∧
  regs 15 = nF ∧ regs 16 = fTrip ∧ regs 17 = heap + 2 ∧ regs 18 = heap + 2 + eCap ∧
  regs 19 = heap + 2 + eCap + m ∧ regs 20 = heap + 2 + eCap + 2 * m ∧
  regs 21 = heap + 2 + eCap + 3 * m ∧ regs 22 = heap + 2 + eCap + 5 * m ∧
  regs 23 = heap + 3 + eCap + 6 * m ∧ regs 24 = heap + 3 + eCap + 8 * m

/-- The number of edges of component `c` in a list `eL` of the edges without repeats. -/
theorem slotCnt_eq_length {G : MGraph} {eL : List ℕ} (hnd : eL.Nodup)
    (hmem : ∀ e, e ∈ eL ↔ e ∈ G.E) (cOf : ℕ → ℕ) (c : ℕ) :
    (eL.filter fun e => cOf e = c).length = slotCnt G cOf c := by
  classical
  unfold slotCnt
  have h2 : (G.E.filter fun e => cOf e = c) = (eL.filter fun e => cOf e = c).toFinset := by
    ext e; simp [hmem]
  rw [h2, List.toFinset_card_of_nodup (hnd.filter _)]

/-! ## The setup -/

/-- A run with cost bound `K' + c ≤ T` is a run with `K + c ≤ T` when `K ≤ K'`. -/
theorem runs_le_of_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {Q : Outcome → State → Prop} {K K' T : ℕ}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ K' + c ≤ T) (hK : K ≤ K') :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ K + c ≤ T := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := h
  exact ⟨o, st', c, hr, hq, by omega⟩


/-- **The setup** of `slotListBody` sets the registers of `SlotRegs` and changes no memory. -/
theorem slotListSetup_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {pos graph expPtr cmpH bktH nComp k B ctH heap vCap eCap fD nF fTrip : ℕ} {G : MGraph}
    {mem : ℕ → ℕ} {s : Stmt} {K T : ℕ} {Q : Outcome → State → Prop}
    (hV : mem graph = vCap) (hE : mem (graph + 1) = eCap) (hM : mem (graph + 3) = G.m)
    (hexp : mem (expPtr + 1) = fD) (hnF : mem (fD + 2) = nF) (hfT : mem (fD + 3) = fTrip)
    (hGle : graph + dynGraphSize vCap eCap ≤ heap)
    (hw : heap + slotListSpace eCap G.m < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hexpw : expPtr + 1 < 2 ^ w) (hfDw : fD + 3 < 2 ^ w)
    (hrest : ∀ st : State, st.mem = mem →
      SlotRegs st.regs graph cmpH bktH nComp k B ctH heap vCap eCap G.m nF fTrip →
      ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ (K + 150) + c ≤ T) :
    ∃ o st' c, Runs w p ω (slotListSetupThen s)
        (startState [graph, expPtr, cmpH, bktH, nComp, k, B, ctH, heap] mem pos) o st' c ∧
      Q o st' ∧ K + c ≤ T := by
  have hsz : graph + (4 + 7 * vCap + 9 * eCap) ≤ heap := hGle
  have hsp : heap + (eCap + 10 * G.m + 3) < 2 ^ w := hw
  unfold slotListSetupThen
  refine runs_seq_assign_le (v := vCap) (Expr.eval_load_of_eq (by eval_expr) hV) ?_
  refine runs_seq_assign_le (v := eCap) (Expr.eval_load_of_eq (by eval_expr) hE) ?_
  refine runs_seq_assign_le (v := G.m) (Expr.eval_load_of_eq (by eval_expr) hM) ?_
  clear hV hE hM
  refine runs_seq_assign_le (v := graph + 4 + 7 * vCap + eCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := graph + 4 + 7 * vCap + 3 * eCap)
    (Expr.eval_eq_of_eq (v₁ := graph + 4 + 7 * vCap + eCap + 2 * eCap) (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := graph + 4 + 4 * vCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := nF) (Expr.eval_load_of_eq (Expr.eval_add
    (Expr.eval_load_of_eq (by eval_expr) hexp) (Expr.eval_const (by omega)) (by omega)) hnF) ?_
  refine runs_seq_assign_le (v := fTrip) (Expr.eval_load_of_eq (Expr.eval_add
    (Expr.eval_load_of_eq (by eval_expr) hexp) (Expr.eval_const (by omega)) (by omega)) hfT) ?_
  clear hexp hnF hfT
  refine runs_seq_assign_le (v := heap + 2) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 2 + eCap) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 2 + eCap + G.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 2 + eCap + 2 * G.m)
    (Expr.eval_eq_of_eq (v₁ := heap + 2 + eCap + G.m + G.m) (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 2 + eCap + 3 * G.m)
    (Expr.eval_eq_of_eq (v₁ := heap + 2 + eCap + 2 * G.m + G.m) (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 2 + eCap + 5 * G.m)
    (Expr.eval_eq_of_eq (v₁ := heap + 2 + eCap + 3 * G.m + 2 * G.m) (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 3 + eCap + 6 * G.m)
    (Expr.eval_eq_of_eq (v₁ := heap + 2 + eCap + 5 * G.m + G.m + 1) (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 3 + eCap + 8 * G.m)
    (Expr.eval_eq_of_eq (v₁ := heap + 3 + eCap + 6 * G.m + 2 * G.m) (by eval_expr) (by omega)) ?_
  refine runs_le_of_le (hrest _ rfl ?_) ?_
  · simp only [SlotRegs, Function.update_apply, startState, dgEListBase, dgETailSlotBase,
      dgIntToExtBase]
    simp
  · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
    omega

/-- The registers below `25` decide `SlotRegs`. -/
theorem SlotRegs.congr {regs regs' : ℕ → ℕ}
    {graph cmpH bktH nComp k B ctH heap vCap eCap m nF fTrip : ℕ}
    (h : ∀ r, r < 25 → regs' r = regs r)
    (hR : SlotRegs regs graph cmpH bktH nComp k B ctH heap vCap eCap m nF fTrip) :
    SlotRegs regs' graph cmpH bktH nComp k B ctH heap vCap eCap m nF fTrip := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24⟩ := hR
  exact ⟨(h 2 (by norm_num)).trans h2, (h 3 (by norm_num)).trans h3, (h 4 (by norm_num)).trans h4,
    (h 5 (by norm_num)).trans h5, (h 6 (by norm_num)).trans h6, (h 7 (by norm_num)).trans h7,
    (h 8 (by norm_num)).trans h8, (h 11 (by norm_num)).trans h11,
    (h 12 (by norm_num)).trans h12, (h 13 (by norm_num)).trans h13,
    (h 14 (by norm_num)).trans h14, (h 15 (by norm_num)).trans h15,
    (h 16 (by norm_num)).trans h16, (h 17 (by norm_num)).trans h17,
    (h 18 (by norm_num)).trans h18, (h 19 (by norm_num)).trans h19,
    (h 20 (by norm_num)).trans h20, (h 21 (by norm_num)).trans h21,
    (h 22 (by norm_num)).trans h22, (h 23 (by norm_num)).trans h23,
    (h 24 (by norm_num)).trans h24⟩

/-! ## The first three loops -/

/-- The cost of the front: the setup and the first three loops. -/
def slotFrontCost (m nComp nF : ℕ) : ℕ := 60 * m + 40 * nComp + 21 * nF + 200

/-- The number of edges of a component is at most the number of edges. -/
theorem slotCnt_le (G : MGraph) (cOf : ℕ → ℕ) (c : ℕ) : slotCnt G cOf c ≤ G.m := by
  classical
  unfold slotCnt MGraph.m
  exact Finset.card_filter_le _ _

/-- **The front of `slotListBody`.** After the setup and the first three loops, the registers are
those of `SlotRegs`; the word `ctH + 3 c` holds the flag of component `c`; the word
`heap + 2 + e` marks the forest edges; and the other memory is as before. -/
theorem slotListFront_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {pos graph expPtr cmpH bktH nComp k B ctH heap vCap eCap fD nF fTrip : ℕ} {G : MGraph}
    {mem : ℕ → ℕ} {s : Stmt} {K T : ℕ} {Q : Outcome → State → Prop}
    (hG : DynGraphAt mem graph vCap eCap G) (hGle : graph + dynGraphSize vCap eCap ≤ ctH)
    (hexp : mem (expPtr + 1) = fD) (hnF : mem (fD + 2) = nF) (hfT : mem (fD + 3) = fTrip)
    (hfe : ∀ e ∈ slotForestEdges mem fTrip nF, e ∈ G.E) (hfeL : fTrip + 3 * nF ≤ ctH)
    (hcmp : ∀ e ∈ G.E, cmpH + G.tail e < ctH ∧ slotCOf mem cmpH G e < nComp)
    (hct : ctH + 3 * nComp ≤ heap) (hz : ZeroFrom mem ctH)
    (hw : heap + slotListSpace eCap G.m < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hexpw : expPtr + 1 < 2 ^ w) (hfDw : fD + 3 < 2 ^ w)
    (hrest : ∀ st : State,
      SlotRegs st.regs graph cmpH bktH nComp k B ctH heap vCap eCap G.m nF fTrip →
      (∀ a, ¬ SlotCtCell ctH nComp a → (a < heap + 2 ∨ heap + 2 + eCap ≤ a) →
        st.mem a = mem a) →
      (∀ c < nComp, st.mem (ctH + 3 * c) =
        if SlotFlagOn k (slotCnt G (slotCOf mem cmpH G) c) then 1 else 0) →
      (∀ e < eCap, st.mem (heap + 2 + e) =
        if e ∈ slotForestEdges mem fTrip nF then 1 else 0) →
      ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧
        (K + slotFrontCost G.m nComp nF) + c ≤ T) :
    ∃ o st' c, Runs w p ω (slotListSetupThen
        (forRange 25 (.const 0) (.reg 11) slotCountStep ;;
         forRange 25 (.const 0) (.reg 4) slotFlagStep ;;
         forRange 25 (.const 0) (.reg 15) slotMarkStep ;; s))
        (startState [graph, expPtr, cmpH, bktH, nComp, k, B, ctH, heap] mem pos) o st' c ∧
      Q o st' ∧ K + c ≤ T := by
  obtain ⟨hGval, hVlt, hElt, hmVCap, hmECap, -, hmM, -, -, hext, -, -,
    ⟨eL, heLen, heNd, heMem, heLA, -⟩, hslot, -⟩ := hG
  have hmV' : mem graph = vCap := by simpa [dgVCapOff] using hmVCap
  have hmE' : mem (graph + 1) = eCap := by simpa [dgECapOff] using hmECap
  have hmM' : mem (graph + 3) = G.m := by simpa [dgMOff] using hmM
  have hsz : graph + (4 + 7 * vCap + 9 * eCap) ≤ ctH := hGle
  have hsp : heap + (eCap + 10 * G.m + 3) < 2 ^ w := hw
  have hfeLen : (slotForestEdges mem fTrip nF).length = nF := by simp [slotForestEdges]
  have hmE : G.m ≤ eCap := by
    unfold MGraph.m
    calc G.E.card ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hElt e he)
      _ = eCap := Finset.card_range eCap
  -- the facts on the edges that loop 1 reads
  have hE1 : ∀ e ∈ eL, graph + 4 + 7 * vCap + 3 * eCap + e < ctH ∧
      graph + 4 + 4 * vCap + mem (graph + 4 + 7 * vCap + 3 * eCap + e) < ctH ∧
      mem (graph + 4 + 4 * vCap + mem (graph + 4 + 7 * vCap + 3 * eCap + e)) = G.tail e ∧
      cmpH + G.tail e < ctH ∧ mem (cmpH + G.tail e) < nComp := by
    intro e he
    have heE : e ∈ G.E := (heMem e).mp he
    have helt := hElt e heE
    have htV : G.tail e ∈ G.V := (hGval e heE).1
    obtain ⟨hsV, hback⟩ := hext _ htV
    have hts : mem (graph + 4 + 7 * vCap + 3 * eCap + e) =
        mem (graph + 4 + 3 * vCap + G.tail e) := (hslot e heE).1
    have hsV' : mem (graph + 4 + 3 * vCap + G.tail e) < vCap := hVlt _ hsV
    obtain ⟨hc1, hc2⟩ := hcmp e heE
    refine ⟨by omega, by rw [hts]; omega, by rw [hts]; exact hback, hc1, hc2⟩
  refine slotListSetup_runs hmV' hmE' hmM' hexp hnF hfT (by omega) hw hw16 hexpw hfDw
    (fun st₁ hm₁ hR₁ => ?_)
  have hR₁' := hR₁
  obtain ⟨r2, -, r4, r5, -, r7, -, r11, r12, r13, r14, r15, r16, r17, -⟩ := hR₁'
  -- loop 1
  refine runs_seq_triple_le (slotCount_loop (mem := mem) (G := G) (eL := eL) (ctH := ctH)
    (nComp := nComp) (eLB := graph + 4 + 7 * vCap + eCap)
    (tsB := graph + 4 + 7 * vCap + 3 * eCap) (iteB := graph + 4 + 4 * vCap) (cmpH := cmpH)
    st₁.regs heLA (by omega) hE1 (fun c hc => hz _ (by omega)) (by omega) hw16 r2 r7
    (r11.trans heLen.symm) r12 r13 r14) ⟨hm₁, fun r _ => rfl⟩ (fun st₂ h₂ => ?_)
  obtain ⟨hR₂, hfr₂, hcnt₂⟩ := h₂
  have hcnt₂' : ∀ c < nComp, st₂.mem (ctH + 3 * c) = slotCnt G (slotCOf mem cmpH G) c :=
    fun c hc => (hcnt₂ c hc).trans (slotCnt_eq_length heNd heMem (slotCOf mem cmpH G) c)
  -- loop 2
  refine runs_seq_triple_le (slotFlag_loop (mem := st₂.mem) (ctH := ctH) (nComp := nComp)
    (k := k) st₁.regs (fun c => slotCnt G (slotCOf mem cmpH G) c) hcnt₂'
    (fun c _ => by have := slotCnt_le G (slotCOf mem cmpH G) c; omega) (by omega) hw16
    r4 r5 r7) ⟨rfl, hR₂⟩ (fun st₃ h₃ => ?_)
  obtain ⟨hR₃, hfr₃, hflag₃⟩ := h₃
  -- loop 3
  have hlow₃ : ∀ a, a < ctH → st₃.mem a = mem a := fun a ha => by
    have hn : ¬ SlotCtCell ctH nComp a := fun ⟨c, _, hc⟩ => by omega
    rw [hfr₃ a hn, hfr₂ a hn]
  refine runs_seq_triple_le (slotMark_loop (mem := st₃.mem) (fTrip := fTrip) (markH := heap + 2)
    (eCap := eCap) (fe := slotForestEdges mem fTrip nF) st₁.regs
    (fun t ht => by
      rw [hfeLen] at ht
      rw [hlow₃ _ (by omega)]
      simp [slotForestEdges])
    (fun e he => hElt e (hfe e he)) (by omega)
    (fun e he => by
      have hn : ¬ SlotCtCell ctH nComp (heap + 2 + e) := fun ⟨c, hc, h⟩ => by omega
      rw [hfr₃ _ hn, hfr₂ _ hn]
      exact hz _ (by omega)) (by omega) hw16 (r15.trans hfeLen.symm) r16 r17)
    ⟨rfl, hR₃⟩ (fun st₄ h₄ => ?_)
  obtain ⟨hR₄, hfr₄, hmark₄⟩ := h₄
  obtain ⟨o, st', c, hr, hq, hc⟩ := hrest st₄
    (SlotRegs.congr (fun r hr => hR₄ r (Or.inl hr)) hR₁)
    (fun a hn ha => by rw [hfr₄ a ha, hfr₃ a hn, hfr₂ a hn])
    (fun c hc => by
      rw [hfr₄ _ (Or.inl (by omega)), hflag₃ c hc])
    hmark₄
  refine ⟨o, st', c, hr, hq, ?_⟩
  simp only [slotFrontCost] at hc
  rw [hfeLen, heLen] at *
  omega

end MinCostFlow.SparseCore.Program
