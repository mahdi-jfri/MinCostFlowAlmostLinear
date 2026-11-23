module

public import MinCostFlow.LSF.Program.TTrack

/-!
# The dynamic graph of the forest `F`

`fGraphProc` builds `F` as a dynamic graph (`DynGraphAt`). It starts from an empty graph, adds the
vertices of `vList`, and inserts the tree edge `fid i` with ends `vList[tl i]` and `vList[hd i]`
for each tree-edge index `i` with `own i = 0` (the edges that the roots pass keeps,
`forest_E_eq` in `FForestMath.lean`). The result is `fGraph` (`fGraph_meetsContract`), at cost
`O(n0 + tM)`. `fGraph_V`, `fGraph_E` and `fGraph_ends` give its vertices, edges and ends.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## The graph -/

/-- One insertion, as `dgInsertEdgeStmt` does it: only a new edge below the capacity. -/
def fGraphStep (eCap : ℕ) (G : MGraph) (e u v : ℕ) : MGraph :=
  if e < eCap ∧ e ∉ G.E then G.applyUpdate (.insert e u v) else G

/-- The graph after the first `k` tree-edge indices. -/
def fGraph (V : Finset ℕ) (eCap : ℕ) (fe tE hE own : ℕ → ℕ) : ℕ → MGraph
  | 0 => { V := V, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  | k + 1 => if own k = 0 then fGraphStep eCap (fGraph V eCap fe tE hE own k) (fe k) (tE k) (hE k)
      else fGraph V eCap fe tE hE own k

variable {V : Finset ℕ} {eCap : ℕ} {fe tE hE own : ℕ → ℕ}

lemma fGraph_V (k : ℕ) : (fGraph V eCap fe tE hE own k).V = V := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [fGraph, fGraphStep]
    split_ifs <;> simp [MGraph.applyUpdate, ih]

/-- The edges and their ends, for distinct edge IDs below the capacity. -/
lemma fGraph_spec (k : ℕ) (hfe : ∀ i < k, fe i < eCap)
    (hinj : ∀ i < k, ∀ j < k, fe i = fe j → i = j) :
    (fGraph V eCap fe tE hE own k).E = ((Finset.range k).filter (fun i => own i = 0)).image fe ∧
    ∀ i < k, own i = 0 → (fGraph V eCap fe tE hE own k).tail (fe i) = tE i ∧
      (fGraph V eCap fe tE hE own k).head (fe i) = hE i := by
  induction k with
  | zero => exact ⟨by simp [fGraph], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨hE', hends⟩ := ih (fun i hi => hfe i (by omega))
      (fun i hi j hj => hinj i (by omega) j (by omega))
    have hnot : fe k ∉ (fGraph V eCap fe tE hE own k).E := by
      rw [hE', Finset.mem_image]
      rintro ⟨i, hi, heq⟩
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      have := hinj i (by omega) k (by omega) heq
      omega
    by_cases hk : own k = 0
    · simp only [fGraph, if_pos hk, fGraphStep, if_pos (And.intro (hfe k (by omega)) hnot),
        MGraph.applyUpdate]
      refine ⟨?_, fun i hi hi0 => ?_⟩
      · rw [hE', Finset.range_add_one, Finset.filter_insert, if_pos hk, Finset.image_insert]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · have hne : fe i ≠ fe k := fun he => by have := hinj i (by omega) k (by omega) he; omega
          rw [Function.update_of_ne hne, Function.update_of_ne hne]
          exact hends i hi hi0
        · simp
    · simp only [fGraph, if_neg hk]
      refine ⟨?_, fun i hi hi0 => ?_⟩
      · rw [hE', Finset.range_add_one, Finset.filter_insert, if_neg hk]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hends i hi hi0
        · exact absurd hi0 hk

/-! ## The procedure -/

/-- Args: `[dgPtr, vCap, eCap, n0, vListPtr, tM, tlPtr, hdPtr, fidPtr, ownPtr]`. Register `10`
is the loop index. -/
def fGraphProc (bDg : ℕ) : Stmt :=
  .call 10 (bDg + dgIdxInitEmpty) [.reg 0, .reg 1, .reg 2] ;;
  forRange 10 (.const 0) (.reg 3)
    (.assign 11 (.load (.bin .add (.reg 4) (.reg 10))) ;;
     .call 12 (bDg + dgIdxAddVertex) [.reg 0, .reg 11]) ;;
  forRange 10 (.const 0) (.reg 5)
    (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 10))) (.const 0))
      (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 10))))) ;;
       .assign 12 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 10))))) ;;
       .call 13 (bDg + 7 + dgIdxInsertEdge)
         [.reg 0, .load (.bin .add (.reg 8) (.reg 10)), .reg 11, .reg 12])
      .nop) ;;
  .ret (.const 0)

lemma fGraphProc_noRand (bDg : ℕ) : (fGraphProc bDg).NoRand := by
  simp [fGraphProc, forRange, forUp, Stmt.NoRand]

/-- An input array of length `len` at `a` lies outside the graph block and below `2 ^ w`. -/
def OutsideBlock (w dgPtr size a len : ℕ) : Prop :=
  (a + len ≤ dgPtr ∨ dgPtr + size ≤ a) ∧ a + len < 2 ^ w

/-- The contract of `fGraphProc`. -/
def fGraphContract (w : ℕ) : Contract where
  pre args mem := ∃ (dgPtr vCap eCap n0 vListPtr tM tlPtr hdPtr fidPtr ownPtr : ℕ),
    args = [dgPtr, vCap, eCap, n0, vListPtr, tM, tlPtr, hdPtr, fidPtr, ownPtr] ∧
    16 ≤ 2 ^ w ∧ dgPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    (∀ i < dynGraphSize vCap eCap, mem (dgPtr + i) = 0) ∧
    OutsideBlock w dgPtr (dynGraphSize vCap eCap) vListPtr n0 ∧
    OutsideBlock w dgPtr (dynGraphSize vCap eCap) tlPtr tM ∧
    OutsideBlock w dgPtr (dynGraphSize vCap eCap) hdPtr tM ∧
    OutsideBlock w dgPtr (dynGraphSize vCap eCap) fidPtr tM ∧
    OutsideBlock w dgPtr (dynGraphSize vCap eCap) ownPtr tM ∧
    (∀ i < n0, mem (vListPtr + i) < vCap) ∧
    (∀ i < tM, mem (tlPtr + i) < n0 ∧ mem (hdPtr + i) < n0 ∧ mem (fidPtr + i) < eCap)
  post args mem ret mem' := ∃ (dgPtr vCap eCap n0 vListPtr tM tlPtr hdPtr fidPtr ownPtr : ℕ),
    args = [dgPtr, vCap, eCap, n0, vListPtr, tM, tlPtr, hdPtr, fidPtr, ownPtr] ∧ ret = 0 ∧
    DynGraphAt mem' dgPtr vCap eCap
      (fGraph (memSlice mem vListPtr n0).toFinset eCap (fun i => mem (fidPtr + i))
        (fun i => mem (vListPtr + mem (tlPtr + i))) (fun i => mem (vListPtr + mem (hdPtr + i)))
        (fun i => mem (ownPtr + i)) tM) ∧
    ∀ a, a < dgPtr ∨ dgPtr + dynGraphSize vCap eCap ≤ a → mem' a = mem a
  cost args _ := 150 * args.getD 3 0 + 620 * args.getD 5 0 + 100

set_option maxHeartbeats 800000 in
theorem fGraph_meetsContract {w : ℕ} {p : Program} {b bDg : ℕ}
    (hp : p.procs[b]? = some (fGraphProc bDg)) (hpDg : p.HasAt bDg (dgRelocProcs bDg)) :
    MeetsContract w p b (fGraphContract w) := by
  have hpOps : p.HasAt bDg dgOpsProcs := dgReloc_hasAt_ops hpDg
  have hpEdge : p.HasAt (bDg + 7) (dgEdgeProcs bDg) := dgReloc_hasAt_edge hpDg
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨dgPtr, vCap, eCap, n0, vListPtr, tM, tlPtr, hdPtr, fidPtr, ownPtr, rfl, h16, hbd,
    hzero, ⟨hvD, hvW⟩, ⟨htD, htW⟩, ⟨hhD, hhW⟩, ⟨hfD, hfW⟩, ⟨hoD, hoW⟩, hvC, hidx⟩ := hpre
  set args := [dgPtr, vCap, eCap, n0, vListPtr, tM, tlPtr, hdPtr, fidPtr, ownPtr] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hvCw : vCap < 2 ^ w := hwords _ (by simp [hargs])
  have heCw : eCap < 2 ^ w := hwords _ (by simp [hargs])
  have hn0w : n0 < 2 ^ w := hwords _ (by simp [hargs])
  have htMw : tM < 2 ^ w := hwords _ (by simp [hargs])
  set vs := memSlice mem vListPtr n0 with hvs
  set fe : ℕ → ℕ := fun i => mem (fidPtr + i) with hfe
  set tE : ℕ → ℕ := fun i => mem (vListPtr + mem (tlPtr + i)) with htE
  set hE : ℕ → ℕ := fun i => mem (vListPtr + mem (hdPtr + i)) with hhE
  set ow : ℕ → ℕ := fun i => mem (ownPtr + i) with how
  have hvslen : vs.length = n0 := memSlice_length _ _ _
  have hvsget : ∀ i (hi : i < vs.length), vs[i] = mem (vListPtr + i) := fun i hi =>
    memSlice_getElem _ _ _ _ hi
  have hvsmem : ∀ i < n0, mem (vListPtr + i) ∈ vs.toFinset := fun i hi => by
    rw [List.mem_toFinset, ← hvsget i (by omega)]; exact List.getElem_mem _
  let Fr : (ℕ → ℕ) → Prop := fun m =>
    ∀ a, a < dgPtr ∨ dgPtr + dynGraphSize vCap eCap ≤ a → m a = mem a
  let Rg : State → Prop := fun st => ∀ i < 10, st.regs i = args.getD i 0
  have hRd : ∀ {a len : ℕ}, (a + len ≤ dgPtr ∨ dgPtr + dynGraphSize vCap eCap ≤ a) →
      ∀ m, Fr m → ∀ i < len, m (a + i) = mem (a + i) := fun hD m hm i hi =>
    hm _ (by rcases hD with h | h <;> [left; right] <;> omega)
  -- the vertex loop
  let InvV : ℕ → State → Prop := fun i st =>
    Rg st ∧ st.regs 10 = i ∧ DynGraphAt st.mem dgPtr vCap eCap (tVGraph vs i) ∧ Fr st.mem
  have hloopV : Triple w p
      (fun st => Rg st ∧ DynGraphAt st.mem dgPtr vCap eCap (tVGraph vs 0) ∧ Fr st.mem)
      (forRange 10 (.const 0) (.reg 3)
        (.assign 11 (.load (.bin .add (.reg 4) (.reg 10))) ;;
         .call 12 (bDg + dgIdxAddVertex) [.reg 0, .reg 11]))
      (normalPost (InvV n0))
      (fun _ => (n0 - 0) * (130 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    refine Triple.forRange_const 130 0 n0 (Nat.zero_le _) hw1 (fun _ => hn0w) ?_ ?_ ?_ ?_
    · rintro st ⟨hR, hdg, hfr⟩
      refine ⟨by eval_expr, fun i hi => ?_, by simp, hdg, hfr⟩
      simp only [Function.update_of_ne (show i ≠ 10 by omega)]; exact hR i hi
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h
      have r3 : st.regs 3 = n0 := h.1 3 (by omega)
      eval_expr
    · intro i _ hi st ω' hI
      obtain ⟨hR, h10, hdg, hfr⟩ := hI
      have r0 : st.regs 0 = dgPtr := hR 0 (by omega)
      have r4 : st.regs 4 = vListPtr := hR 4 (by omega)
      have hvi : st.mem (vListPtr + i) = mem (vListPtr + i) := hRd hvD _ hfr i hi
      have hlen : i < vs.length := by omega
      have hxw : mem (vListPtr + i) < 2 ^ w := lt_trans (hvC i hi) hvCw
      have hdw : dgPtr < 2 ^ w := hwords _ (by simp [hargs])
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := mem (vListPtr + i)) (by rw [← hvi]; eval_expr) ?_
      refine runs_call_le (vs := [dgPtr, mem (vListPtr + i)])
        (dgAddVertex_meetsContract (G := tVGraph vs i) hpOps)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> assumption)
        ⟨dgPtr, _, rfl, h16, hbd, hvC i hi, hdg⟩ ?_
      rintro v₂ mem₂ pos₂ ⟨g₂, x₂, heq₂, -, hdg₂, hfr₂⟩
      simp only [List.cons.injEq, and_true] at heq₂
      obtain ⟨rfl, rfl⟩ := heq₂
      refine ⟨⟨⟨fun k hk => ?_, by simp, ?_, fun a ha => ?_⟩, by simpa using h10⟩, ?_⟩
      · simp only [Function.update_of_ne (show k ≠ 10 by omega),
          Function.update_of_ne (show k ≠ 12 by omega), Function.update_of_ne (show k ≠ 11 by omega)]
        exact hR k hk
      · rw [← tVGraph_succ hlen, hvsget i hlen]; exact hdg₂
      · show mem₂ a = mem a
        rw [hfr₂ a ha]; exact hfr a ha
      · simp [argsSize, Expr.size, dgAddVertexContract]
  -- the edge loop
  let InvE : ℕ → State → Prop := fun i st =>
    Rg st ∧ st.regs 10 = i ∧
      DynGraphAt st.mem dgPtr vCap eCap (fGraph vs.toFinset eCap fe tE hE ow i) ∧ Fr st.mem
  have hloopE : Triple w p
      (fun st => Rg st ∧ DynGraphAt st.mem dgPtr vCap eCap (fGraph vs.toFinset eCap fe tE hE ow 0) ∧
        Fr st.mem)
      (forRange 10 (.const 0) (.reg 5)
        (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 10))) (.const 0))
          (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 10))))) ;;
           .assign 12 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 10))))) ;;
           .call 13 (bDg + 7 + dgIdxInsertEdge)
             [.reg 0, .load (.bin .add (.reg 8) (.reg 10)), .reg 11, .reg 12])
          .nop))
      (normalPost (InvE tM))
      (fun _ => (tM - 0) * (600 + (Expr.reg 5).size + 8) +
        ((Expr.const 0).size + (Expr.reg 5).size + 5)) := by
    refine Triple.forRange_const 600 0 tM (Nat.zero_le _) hw1 (fun _ => htMw) ?_ ?_ ?_ ?_
    · rintro st ⟨hR, hdg, hfr⟩
      refine ⟨by eval_expr, fun i hi => ?_, by simp, hdg, hfr⟩
      simp only [Function.update_of_ne (show i ≠ 10 by omega)]; exact hR i hi
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h
      have r5 : st.regs 5 = tM := h.1 5 (by omega)
      eval_expr
    · intro i _ hi st ω' hI
      obtain ⟨hR, h10, hdg, hfr⟩ := hI
      have r0 : st.regs 0 = dgPtr := hR 0 (by omega)
      have r4 : st.regs 4 = vListPtr := hR 4 (by omega)
      have r6 : st.regs 6 = tlPtr := hR 6 (by omega)
      have r7 : st.regs 7 = hdPtr := hR 7 (by omega)
      have r8 : st.regs 8 = fidPtr := hR 8 (by omega)
      have r9 : st.regs 9 = ownPtr := hR 9 (by omega)
      have hdw : dgPtr < 2 ^ w := hwords _ (by simp [hargs])
      obtain ⟨hti, hhi, hfi⟩ := hidx i hi
      have hO : st.mem (ownPtr + i) = ow i := hRd hoD _ hfr i hi
      have hF : st.mem (fidPtr + i) = fe i := hRd hfD _ hfr i hi
      have hT1 : st.mem (tlPtr + i) = mem (tlPtr + i) := hRd htD _ hfr i hi
      have hH1 : st.mem (hdPtr + i) = mem (hdPtr + i) := hRd hhD _ hfr i hi
      have hx : st.mem (vListPtr + st.mem (tlPtr + i)) = tE i := by
        rw [hT1, hRd hvD _ hfr _ hti]
      have hy : st.mem (vListPtr + st.mem (hdPtr + i)) = hE i := by
        rw [hH1, hRd hvD _ hfr _ hhi]
      have hxV : tE i ∈ vs.toFinset := hvsmem _ hti
      have hyV : hE i ∈ vs.toFinset := hvsmem _ hhi
      have hxw : tE i < 2 ^ w := lt_trans (hvC _ hti) hvCw
      have hyw : hE i < 2 ^ w := lt_trans (hvC _ hhi) hvCw
      have hfw : fe i < 2 ^ w := lt_trans hfi heCw
      refine runs_start_le ?_
      refine WordRAM.runs_cond_le (v := if ow i = 0 then 1 else 0) (by rw [← hO]; eval_expr)
        (fun hv => ?_) (fun hv => ?_)
      · have h0 : ow i = 0 := by by_contra hne; exact hv (if_neg hne)
        refine runs_seq_assign_le (v := tE i) (by rw [← hx]; eval_expr) ?_
        refine runs_seq_assign_le (v := hE i) (by rw [← hy]; eval_expr) ?_
        have hVf : (fGraph vs.toFinset eCap fe tE hE ow i).V = vs.toFinset := fGraph_V i
        refine runs_call_le (vs := [dgPtr, fe i, tE i, hE i])
          (dgInsertEdge_meetsContract (G := fGraph vs.toFinset eCap fe tE hE ow i) hpEdge hpOps)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by rw [← hF]; eval_expr)
            (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
          (by
            intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> omega)
          ⟨dgPtr, _, _, _, rfl, h16, hbd, by rw [hVf]; exact hxV, by rw [hVf]; exact hyV, hdg⟩ ?_
        rintro v₃ mem₃ pos₃ ⟨g₃, e₃, u₃, x₃, heq₃, -, hdg₃, hfr₃⟩
        simp only [List.cons.injEq, and_true] at heq₃
        obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₃
        have hG : fGraph vs.toFinset eCap fe tE hE ow (i + 1) =
            fGraphStep eCap (fGraph vs.toFinset eCap fe tE hE ow i) (fe i) (tE i) (hE i) := by
          simp only [fGraph, if_pos h0]
        refine ⟨⟨⟨fun k hk => ?_, by simp, ?_, fun a ha => ?_⟩, by simpa using h10⟩, ?_⟩
        · simp only [Function.update_of_ne (show k ≠ 10 by omega),
            Function.update_of_ne (show k ≠ 13 by omega),
            Function.update_of_ne (show k ≠ 12 by omega), Function.update_of_ne (show k ≠ 11 by omega)]
          exact hR k hk
        · rw [hG]; exact hdg₃
        · show mem₃ a = mem a
          rw [hfr₃ a ha]; exact hfr a ha
        · simp [argsSize, Expr.size, dgInsertEdgeContract]
      · have h0 : ow i ≠ 0 := by intro he; exact absurd hv (by simp [he])
        have hG : fGraph vs.toFinset eCap fe tE hE ow (i + 1) =
            fGraph vs.toFinset eCap fe tE hE ow i := by
          simp only [fGraph, if_neg h0]
        refine runs_nop_le ⟨⟨fun k hk => ?_, by simp, ?_, fun a ha => hfr a ha⟩,
          by simpa using h10⟩ (by simp [Expr.size])
        · simp only [Function.update_of_ne (show k ≠ 10 by omega)]
          exact hR k hk
        · dsimp only; rw [hG]; exact hdg
  -- the run
  refine runs_start_le ?_
  unfold fGraphProc
  refine runs_seq_call_le (vs := [dgPtr, vCap, eCap]) (dgInitEmptyLocal_meetsContract hpOps)
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> first | assumption | exact hwords _ (by simp [hargs]))
    ⟨dgPtr, vCap, eCap, rfl, h16, hbd, hzero⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨g₁, vc₁, ec₁, heq₁, -, hdg₁, hfr₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  refine runs_seq_triple_le hloopV ⟨fun i hi => ?_, ?_, fun a ha => ?_⟩ ?_
  · simp only [Function.update_of_ne (show i ≠ 10 by omega)]
    interval_cases i <;> simp [startState, hargs]
  · have h0 : tVGraph vs 0 = { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 } := by
      simp [tVGraph]
    rw [h0]; exact hdg₁
  · refine hfr₁ a ?_
    rcases ha with ha | ha
    · left; exact ha
    · right; simp only [dynGraphSize] at ha; omega
  rintro st₂ ⟨hR₂, -, hdg₂, hfr₂⟩
  have hP2 : Rg st₂ ∧ DynGraphAt st₂.mem dgPtr vCap eCap (fGraph vs.toFinset eCap fe tE hE ow 0) ∧
      Fr st₂.mem := by
    refine ⟨hR₂, ?_, hfr₂⟩
    have h0 : fGraph vs.toFinset eCap fe tE hE ow 0 = tVGraph vs vs.length := by
      simp only [fGraph, tVGraph, List.take_length]
    rw [h0, hvslen]; exact hdg₂
  refine runs_seq_triple_le hloopE hP2 ?_
  rintro st₃ ⟨-, -, hdg₃, hfr₃⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨dgPtr, vCap, eCap, n0, vListPtr, tM, tlPtr,
    hdPtr, fidPtr, ownPtr, rfl, rfl, hdg₃, hfr₃⟩ ?_
  simp only [fGraphContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg, Nat.sub_zero, dgInitEmptyLocalContract, argsSize]
  omega

end

end MinCostFlow.LSF.Program
