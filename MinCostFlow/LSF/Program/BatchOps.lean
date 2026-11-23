module

public import MinCostFlow.LSF.Program.BatchSplitOp
import Mathlib.Tactic.Linarith

/-!
# Full Batch Update Procedure (`op 0`) for Dynamic LSF (`BatchOps`)

Implements and verifies `lsfApplyBatchProc` (`[b, batchPtr, heap]`, returning `heap`), matching the
`op 0` clause of `DSRep.Implements` for `lsfDataStructure` (`Lemma 5.4`, `arXiv:2309.16629v1`
page 17 and Appendix A.1 page 48):

* Dispatches each encoded update in the batch at `batchPtr` to `lsfInsertUpdateProc`,
  `lsfDeleteUpdateProc`, or `lsfSplitUpdateProc`.
* Canonicalizes the batch via `canonBatch S.G U`, preserving `BatchAt`, `BatchIsValid`, and
  `BatchWithinCaps`.
* Proves `lsfApplyBatch_runs`: preserves `(LSFRep h).rep`, achieves `lsfBatchPost`, respects the
  heap discipline with `space = 0` (returning `heap`), and satisfies the amortized cost bound
  `c + lsfPhi b x' mem' ≤ lsfBatchCost [b, batchPtr, heap] mem + lsfPhi b x mem`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Procedure definition -/

/-- Apply an encoded update batch at `batchPtr` to LSF handle `b` (`[b, batchPtr, heap]`),
returning `heap` (`space = 0`). -/
def lsfApplyBatchProc (idxInsUpd idxDelUpd idxSplitUpd : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .assign 4 (.const 0) ;;
  .assign 5 (.bin .add (.reg 1) (.const 1)) ;;
  .loop (.bin .lt (.reg 4) (.reg 3))
    (.assign 6 (.load (.reg 5)) ;;
     .cond (.bin .eq (.reg 6) (.const 0))
       (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
        .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
        .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
        .call 10 idxInsUpd [.reg 0, .reg 7, .reg 8, .reg 9])
       (.cond (.bin .eq (.reg 6) (.const 1))
         (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
          .call 10 idxDelUpd [.reg 0, .reg 7])
         (.call 10 idxSplitUpd [.reg 0, .reg 5])) ;;
     .assign 5 (.bin .add (.reg 5) (.reg 10)) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  .ret (.reg 2)

lemma lsfApplyBatchProc_noRand (idxInsUpd idxDelUpd idxSplitUpd : ℕ) :
    (lsfApplyBatchProc idxInsUpd idxDelUpd idxSplitUpd).NoRand := by
  dsimp [lsfApplyBatchProc]; trivial

/-! ## Canonical-update properties -/

private def IsCanonSplit (G : MGraph) : Update → Prop
  | .insert _ _ _ => True
  | .delete _ => True
  | .split v _ St Sh => (∀ e ∈ St, e ∈ G.E ∧ G.tail e = v) ∧ (∀ e ∈ Sh, e ∈ G.E ∧ G.head e = v)

private lemma canonUpdate_isCanon (G : MGraph) (u : Update) : IsCanonSplit G (canonUpdate G u) := by
  cases u with
  | insert _ _ _ => trivial
  | delete _ => trivial
  | split v v' St Sh =>
    exact ⟨fun e he => (Finset.mem_filter.mp he).2, fun e he => (Finset.mem_filter.mp he).2⟩

private def IsCanonBatch : MGraph → List Update → Prop
  | _, [] => True
  | H, u :: us => IsCanonSplit H u ∧ IsCanonBatch (H.applyUpdate u) us

private lemma isCanonBatch_of_canonBatch (G : MGraph) (U : List Update) :
    G.BatchIsValid U → IsCanonBatch G (canonBatch G U) := by
  induction U generalizing G with
  | nil => intro _; trivial
  | cons u us ih =>
    intro ⟨hu, hus⟩
    refine ⟨canonUpdate_isCanon G u, ?_⟩
    rw [canonUpdate_apply hu]
    exact ih (G.applyUpdate u) hus

private lemma sameStatic_endAddr_batch {b : ℕ} {x x' : LSFConcrete} (hs : SameStaticConcrete x x') :
    x'.endAddr b = x.endAddr b := by
  dsimp only [LSFConcrete.endAddr]
  rw [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1]

private lemma batchBodyAt_of_agree {mem mem' : ℕ → ℕ} {p : ℕ} {G : MGraph} {U : List Update}
    {words : ℕ} (h : BatchBodyAt mem p G U words)
    (hag : ∀ a, p ≤ a → a < p + words → mem' a = mem a) :
    BatchBodyAt mem' p G U words := by
  induction U generalizing p G words with
  | nil => exact h
  | cons u us ih =>
    rcases h with ⟨len, hlen, hu, hrest⟩
    refine ⟨len, hlen, UpdateAt.of_agree hu fun i hi => hag (p + i) (by omega) (by omega),
      ih hrest fun a ha1 ha2 => hag a (by omega) (by omega)⟩

/-! ## Loop verification for `lsfApplyBatchProc` -/

private lemma lsfApplyBatchLoop_runs
    {w h b heap numUpd idxInsUpd idxDelUpd idxSplitUpd idxAddRoot idxMinUp idxDgDelF
     idxDgInsG idxDgDelG idxDgUpd idxBFS idxTIns idxTDel idxTSplit idxSetWstr : ℕ}
    {p : Program} {ω : ℕ → Bool} {x0 : LSFConcrete} {mem0 : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x0.endAddr b < 2 ^ w) (hheap_ltw : heap < 2 ^ w)
    (hpIns : p.procs[idxInsUpd]? = some (lsfInsertUpdateProc idxAddRoot idxDgInsG idxTIns idxSetWstr))
    (hpDel : p.procs[idxDelUpd]? = some (lsfDeleteUpdateProc idxAddRoot idxDgDelG idxTDel))
    (hpSplit : p.procs[idxSplitUpd]? = some (lsfSplitUpdateProc idxAddRoot idxDgUpd idxBFS idxTSplit))
    (hpAdd : p.procs[idxAddRoot]? = some (addOrigRootProc idxMinUp idxDgDelF idxBFS))
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x0.vList x0.tOrigList))
    (hDgDelF : ∀ F, MeetsContract w p idxDgDelF (dgDeleteEdgeContract w x0.vCap (fECap x0.eCap x0.n0) F))
    (hDgInsG : ∀ G, MeetsContract w p idxDgInsG (dgInsertEdgeContract w x0.vCap x0.eCap G))
    (hDgDelG : ∀ G, MeetsContract w p idxDgDelG (dgDeleteEdgeContract w x0.vCap x0.eCap G))
    (hDgUpdF : ∀ G H v v' St Sh len, MeetsContract w p idxDgUpd
      (dgApplyUpdateContract w x0.vCap (fECap x0.eCap x0.n0) G H (.split v v' St Sh) len))
    (hDgUpdG : ∀ G v v' St Sh len, MeetsContract w p idxDgUpd
      (dgApplyUpdateContract w x0.vCap x0.eCap G G (.split v v' St Sh) len))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F))
    (hTIns : ∀ G T_cur T₀ π, MeetsContract w p idxTIns
      (lsfTBlockInsertContract w x0.vCap x0.eCap x0.tM G T_cur T₀ π x0.tOrigList))
    (hTDel : ∀ G T_cur T₀ π, MeetsContract w p idxTDel
      (lsfTBlockDeleteContract w x0.vCap x0.eCap x0.tM G T_cur T₀ π x0.tOrigList))
    (hTSplit : ∀ G T_cur T₀ π v v' St Sh len, MeetsContract w p idxTSplit
      (lsfTBlockSplitContract w x0.vCap x0.eCap x0.tM G T_cur T₀ π x0.tOrigList v v' St Sh len))
    (hSetWstr : MeetsContract w p idxSetWstr (lsfSetWstrOneContract w h)) :
    ∀ (U : List Update) (curPtr remWords i : ℕ) (S : LSFState) (x : LSFConcrete) (st : State),
      i + U.length = numUpd →
      numUpd < 2 ^ w →
      curPtr + remWords ≤ heap →
      (∀ k < remWords, curPtr + k < b ∨ x0.endAddr b ≤ curPtr + k) →
      (∀ k < remWords, st.mem (curPtr + k) < 2 ^ w) →
      SameStaticConcrete x0 x →
      (LSFRep h).rep b S x st.mem →
      (∀ a, a < b ∨ x0.endAddr b ≤ a → st.mem a = mem0 a) →
      BatchBodyAt st.mem curPtr S.G U remWords →
      S.G.BatchIsValid U →
      BatchWithinCaps x0.vCap x0.eCap U →
      IsCanonBatch S.G U →
      st.regs 0 = b → st.regs 2 = heap → st.regs 3 = numUpd → st.regs 4 = i → st.regs 5 = curPtr →
      ∃ st' c x',
        Runs w p ω
          (.loop (.bin .lt (.reg 4) (.reg 3))
            (.assign 6 (.load (.reg 5)) ;;
             .cond (.bin .eq (.reg 6) (.const 0))
               (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
                .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
                .call 10 idxInsUpd [.reg 0, .reg 7, .reg 8, .reg 9])
               (.cond (.bin .eq (.reg 6) (.const 1))
                 (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                  .call 10 idxDelUpd [.reg 0, .reg 7])
                 (.call 10 idxSplitUpd [.reg 0, .reg 5])) ;;
             .assign 5 (.bin .add (.reg 5) (.reg 10)) ;;
             .assign 4 (.bin .add (.reg 4) (.const 1))))
          st .normal st' c ∧
        st'.regs 2 = heap ∧
        SameStaticConcrete x0 x' ∧
        (LSFRep h).rep b (applyLSFBatch S U) x' st'.mem ∧
        (∀ a, a < b ∨ x0.endAddr b ≤ a → st'.mem a = mem0 a) ∧
        c + lsfPhi b x' st'.mem ≤ 4000 * remWords * x0.L_w + 15 + lsfPhi b x st.mem := by
  intro U
  induction U with
  | nil =>
    intro curPtr remWords i S x st hi hnum hcur hdisj hword hsame hrep hfr hbody _ _ _ hr0 hr2 hr3 hr4 hr5
    have hi_eq : i = numUpd := by simp at hi; omega
    have hcond : (Expr.bin .lt (.reg 4) (.reg 3)).eval w st = some 0 := by
      rw [show (0 : ℕ) = BinOp.lt.eval i numUpd by dsimp [BinOp.eval]; rw [ite_eq_right (by omega)]]
      exact Expr.eval_bin (by eval_expr) (by eval_expr)
        (by dsimp [BinOp.eval]; rw [ite_eq_right (by omega)]; omega)
    refine ⟨st, 4, x, ?_, hr2, hsame, hrep, hfr, by omega⟩
    rw [runs_loop_iff]
    exact Or.inl ⟨hcond, rfl, rfl, by decide⟩
  | cons u us ih =>
    intro curPtr remWords i S x st hi hnum hcur hdisj hword hsame hrep hfr hbody hval hcaps hcan
      hr0 hr2 hr3 hr4 hr5
    rcases hbody with ⟨len, hlen_le, hUpdAt, hrest_body⟩
    obtain ⟨hu_val, hus_val⟩ := hval
    have hu_cap : UpdateWithinCaps x0.vCap x0.eCap u := hcaps u List.mem_cons_self
    have hus_cap : BatchWithinCaps x0.vCap x0.eCap us := fun y hy => hcaps y (List.mem_cons_of_mem u hy)
    obtain ⟨hu_can, hus_can⟩ := hcan
    have hi_lt : i < numUpd := by simp at hi; omega
    have hi_ltw : i < 2 ^ w := by omega
    have hi1_ltw : i + 1 < 2 ^ w := by omega
    have hcur_ltw : curPtr < 2 ^ w := by omega
    have hcur_len_ltw : curPtr + len < 2 ^ w := by omega
    have hlen_ltw : len < 2 ^ w := by omega
    have hb_ltw : b < 2 ^ w := by
      have : b < x0.endAddr b := by dsimp [LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, lsfHdrSize]; omega
      omega
    have hx_vc : x.vCap = x0.vCap := hsame.1
    have hx_ec : x.eCap = x0.eCap := hsame.2.1
    have hx_n0 : x.n0 = x0.n0 := hsame.2.2.1
    have hx_tM : x.tM = x0.tM := hsame.2.2.2.2.1
    have hx_Lw : x.L_w = x0.L_w := hsame.2.2.2.2.2.2.2.2.1
    have hx_tL : x.tOrigList = x0.tOrigList := hsame.2.2.2.2.2.2.2.2.2.2.1
    have hx_vL : x.vList = x0.vList := hsame.2.2.2.2.2.2.2.2.2.2.2.1
    have hx_end : x.endAddr b = x0.endAddr b := sameStatic_endAddr_batch hsame
    have hLw1 : 1 ≤ x0.L_w := hx_Lw ▸ hrep.2.2.2.1
    have hMinUp' : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList) := by
      rw [hx_vL, hx_tL]; exact hMinUp
    have hDgDelF' : ∀ F, MeetsContract w p idxDgDelF (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F) := by
      rw [hx_vc, hx_ec, hx_n0]; exact hDgDelF
    have hcond : (Expr.bin .lt (.reg 4) (.reg 3)).eval w st = some 1 := by
      rw [show (1 : ℕ) = BinOp.lt.eval i numUpd by dsimp [BinOp.eval]; rw [ite_eq_left hi_lt]]
      exact Expr.eval_bin (by eval_expr) (by eval_expr)
        (by dsimp [BinOp.eval]; rw [ite_eq_left hi_lt]; omega)
    -- Execute one iteration body producing `(st1, c_b, x1)`
    have hstep : ∃ st1 c_b x1,
        Runs w p ω
          (.assign 6 (.load (.reg 5)) ;;
           .cond (.bin .eq (.reg 6) (.const 0))
             (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
              .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
              .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
              .call 10 idxInsUpd [.reg 0, .reg 7, .reg 8, .reg 9])
             (.cond (.bin .eq (.reg 6) (.const 1))
               (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                .call 10 idxDelUpd [.reg 0, .reg 7])
               (.call 10 idxSplitUpd [.reg 0, .reg 5])) ;;
           .assign 5 (.bin .add (.reg 5) (.reg 10)) ;;
           .assign 4 (.bin .add (.reg 4) (.const 1)))
          st .normal st1 c_b ∧
        st1.regs 0 = b ∧ st1.regs 2 = heap ∧ st1.regs 3 = numUpd ∧
        st1.regs 4 = i + 1 ∧ st1.regs 5 = curPtr + len ∧
        SameStaticConcrete x0 x1 ∧
        (LSFRep h).rep b (applyLSFUpdate S u) x1 st1.mem ∧
        (∀ a, a < b ∨ x0.endAddr b ≤ a → st1.mem a = mem0 a) ∧
        c_b + lsfPhi b x1 st1.mem ≤ 3900 * len * x0.L_w + lsfPhi b x st.mem := by
      cases u with
      | insert e a1 a2 =>
        rcases hUpdAt with ⟨rfl, hLA⟩
        have hm0 : st.mem curPtr = 0 := by simpa using hLA 0 (by simp)
        have hm1 : st.mem (curPtr + 1) = e := hLA 1 (by simp)
        have hm2 : st.mem (curPtr + 2) = a1 := hLA 2 (by simp)
        have hm3 : st.mem (curPtr + 3) = a2 := hLA 3 (by simp)
        have he_ltw : e < 2 ^ w := hm1 ▸ hword 1 (by omega)
        have ha1_ltw : a1 < 2 ^ w := hm2 ▸ hword 2 (by omega)
        have ha2_ltw : a2 < 2 ^ w := hm3 ▸ hword 3 (by omega)
        have hDgIns' : ∀ G, MeetsContract w p idxDgInsG (dgInsertEdgeContract w x.vCap x.eCap G) := by
          rw [hx_vc, hx_ec]; exact hDgInsG
        have hTIns' : ∀ G T_cur, MeetsContract w p idxTIns
            (lsfTBlockInsertContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList) := by
          rw [hx_vc, hx_ec, hx_tM, hx_tL]; exact fun G T_cur => hTIns G T_cur S.T₀ S.π
        obtain ⟨st_c, c_c, x1, hrun_c, hsame_x1, hrep1, hfr_c, hc_c⟩ :=
          lsfInsertUpdate_runs (pos := st.pos) hw16 (hx_end ▸ hend_ltw) hrep hu_val (hx_ec.symm ▸ hu_cap)
            hpAdd hMinUp' hDgDelF' hBFS hDgIns' hTIns' hSetWstr
        suffices hgoal : ∃ o st1 c_b,
            Runs w p ω
              (.assign 6 (.load (.reg 5)) ;;
               .cond (.bin .eq (.reg 6) (.const 0))
                 (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                  .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
                  .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
                  .call 10 idxInsUpd [.reg 0, .reg 7, .reg 8, .reg 9])
                 (.cond (.bin .eq (.reg 6) (.const 1))
                   (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                    .call 10 idxDelUpd [.reg 0, .reg 7])
                   (.call 10 idxSplitUpd [.reg 0, .reg 5])) ;;
               .assign 5 (.bin .add (.reg 5) (.reg 10)) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)))
              st o st1 c_b ∧
            (o = .normal ∧ st1.regs 0 = b ∧ st1.regs 2 = heap ∧ st1.regs 3 = numUpd ∧
              st1.regs 4 = i + 1 ∧ st1.regs 5 = curPtr + 4 ∧ st1.mem = st_c.mem) ∧
            0 + c_b ≤ c_c + 100 by
          rcases hgoal with ⟨_, st1, c_b, hrun_b, ⟨rfl, g0, g2, g3, g4, g5, gmem⟩, hcb⟩
          refine ⟨st1, c_b, x1, hrun_b, g0, g2, g3, g4, g5, hsame.trans hsame_x1,
            gmem ▸ hrep1, fun a ha => by rw [gmem, hfr_c a (hx_end ▸ ha), hfr a ha], ?_⟩
          rw [gmem]; rw [hx_Lw] at hc_c; clear * - hcb hc_c hLw1; omega
        refine runs_seq_assign_le (v := 0) (Expr.eval_load_of_eq (by eval_expr) hm0) ?_
        refine runs_seq_cond_le (v := 1)
          (by simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega])
          ?_ (fun h => by omega)
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq (by eval_expr) hm1) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_le (v := a1) (Expr.eval_load_of_eq (by eval_expr) hm2) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_le (v := a2) (Expr.eval_load_of_eq (by eval_expr) hm3) ?_
        have hcall : Runs w p ω (.call 10 idxInsUpd [.reg 0, .reg 7, .reg 8, .reg 9])
            { mem := st.mem, regs := Function.update (Function.update (Function.update (Function.update st.regs 6 0) 7 e) 8 a1) 9 a2, pos := st.pos }
            .normal { st_c with regs := Function.update (Function.update (Function.update (Function.update (Function.update st.regs 6 0) 7 e) 8 a1) 9 a2) 10 4 }
            (argsSize [.reg 0, .reg 7, .reg 8, .reg 9] + c_c + 1) :=
          runs_call_iff.mpr ⟨[b, e, a1, a2], _, .returned 4, st_c, c_c, by eval_expr, hpIns, hrun_c, rfl, rfl, rfl⟩
        refine runs_seq_of_runs_le hcall ?_
        refine runs_seq_assign_le (v := curPtr + 4) (by eval_expr) ?_
        refine runs_assign_le (v := i + 1) (by eval_expr) ?_ ?_
        · refine ⟨rfl, by simp [hr0], by simp [hr2], by simp [hr3], by simp, by simp, rfl⟩
        · dsimp only [argsSize, Expr.size]; omega
      | delete e =>
        rcases hUpdAt with ⟨rfl, hLA⟩
        have hm0 : st.mem curPtr = 1 := by simpa using hLA 0 (by simp)
        have hm1 : st.mem (curPtr + 1) = e := hLA 1 (by simp)
        have he_ltw : e < 2 ^ w := hm1 ▸ hword 1 (by omega)
        have hDgDelG' : ∀ G, MeetsContract w p idxDgDelG (dgDeleteEdgeContract w x.vCap x.eCap G) := by
          rw [hx_vc, hx_ec]; exact hDgDelG
        have hTDel' : ∀ G T_cur, MeetsContract w p idxTDel
            (lsfTBlockDeleteContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList) := by
          rw [hx_vc, hx_ec, hx_tM, hx_tL]; exact fun G T_cur => hTDel G T_cur S.T₀ S.π
        obtain ⟨st_c, c_c, x1, hrun_c, hsame_x1, hrep1, hfr_c, hc_c⟩ :=
          lsfDeleteUpdate_runs (pos := st.pos) hw16 (hx_end ▸ hend_ltw) hrep hu_val
            hpAdd hMinUp' hDgDelF' hBFS hDgDelG' hTDel'
        suffices hgoal : ∃ o st1 c_b,
            Runs w p ω
              (.assign 6 (.load (.reg 5)) ;;
               .cond (.bin .eq (.reg 6) (.const 0))
                 (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                  .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
                  .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
                  .call 10 idxInsUpd [.reg 0, .reg 7, .reg 8, .reg 9])
                 (.cond (.bin .eq (.reg 6) (.const 1))
                   (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                    .call 10 idxDelUpd [.reg 0, .reg 7])
                   (.call 10 idxSplitUpd [.reg 0, .reg 5])) ;;
               .assign 5 (.bin .add (.reg 5) (.reg 10)) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)))
              st o st1 c_b ∧
            (o = .normal ∧ st1.regs 0 = b ∧ st1.regs 2 = heap ∧ st1.regs 3 = numUpd ∧
              st1.regs 4 = i + 1 ∧ st1.regs 5 = curPtr + 2 ∧ st1.mem = st_c.mem) ∧
            0 + c_b ≤ c_c + 100 by
          rcases hgoal with ⟨_, st1, c_b, hrun_b, ⟨rfl, g0, g2, g3, g4, g5, gmem⟩, hcb⟩
          refine ⟨st1, c_b, x1, hrun_b, g0, g2, g3, g4, g5, hsame.trans hsame_x1,
            gmem ▸ hrep1, fun a ha => by rw [gmem, hfr_c a (hx_end ▸ ha), hfr a ha], ?_⟩
          rw [gmem]; clear * - hcb hc_c hLw1; omega
        refine runs_seq_assign_le (v := 1) (Expr.eval_load_of_eq (by eval_expr) hm0) ?_
        refine runs_seq_cond_le (v := 0)
          (by simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega])
          (fun h => by omega) ?_
        intro _
        refine runs_seq_cond_le (v := 1)
          (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega])
          ?_ (fun h => by omega)
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq (by eval_expr) hm1) ?_
        have hcall : Runs w p ω (.call 10 idxDelUpd [.reg 0, .reg 7])
            { mem := st.mem, regs := Function.update (Function.update st.regs 6 1) 7 e, pos := st.pos }
            .normal { st_c with regs := Function.update (Function.update (Function.update st.regs 6 1) 7 e) 10 2 }
            (argsSize [.reg 0, .reg 7] + c_c + 1) :=
          runs_call_iff.mpr ⟨[b, e], _, .returned 2, st_c, c_c, by eval_expr, hpDel, hrun_c, rfl, rfl, rfl⟩
        refine runs_seq_of_runs_le hcall ?_
        refine runs_seq_assign_le (v := curPtr + 2) (by eval_expr) ?_
        refine runs_assign_le (v := i + 1) (by eval_expr) ?_ ?_
        · refine ⟨rfl, by simp [hr0], by simp [hr2], by simp [hr3], by simp, by simp, rfl⟩
        · dsimp only [argsSize, Expr.size]; omega
      | split v v' St Sh =>
        have htag : st.mem curPtr = 2 ∨ st.mem curPtr = 3 := by
          rcases hUpdAt with ⟨Lt, Lh, _, _, _, _, hlen, hLA⟩ | ⟨Lt, Lh, _, _, _, _, hlen, hLA⟩
          · left; simpa using hLA 0 (by simp)
          · right; simpa using hLA 0 (by simp)
        have hlen_ge5 : 5 ≤ len := by
          rcases hUpdAt with ⟨Lt, Lh, _, _, _, _, hlen, _⟩ | ⟨Lt, Lh, _, _, _, _, hlen, _⟩ <;> omega
        set tag := st.mem curPtr
        have htag_ltw : tag < 2 ^ w := by rcases htag with h | h <;> omega
        have htag_ne0 : tag ≠ 0 := by rcases htag with h | h <;> omega
        have htag_ne1 : tag ≠ 1 := by rcases htag with h | h <;> omega
        have hDgUpdF' : ∀ G H, MeetsContract w p idxDgUpd
            (dgApplyUpdateContract w x.vCap (fECap x.eCap x.n0) G H (.split v v' St Sh) len) := by
          rw [hx_vc, hx_ec, hx_n0]; exact fun G H => hDgUpdF G H v v' St Sh len
        have hDgUpdG' : ∀ G, MeetsContract w p idxDgUpd
            (dgApplyUpdateContract w x.vCap x.eCap G G (.split v v' St Sh) len) := by
          rw [hx_vc, hx_ec]; exact fun G => hDgUpdG G v v' St Sh len
        have hTSplit' : ∀ G T_cur, MeetsContract w p idxTSplit
            (lsfTBlockSplitContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList v v' St Sh len) := by
          rw [hx_vc, hx_ec, hx_tM, hx_tL]; exact fun G T_cur => hTSplit G T_cur S.T₀ S.π v v' St Sh len
        obtain ⟨st_c, c_c, x1, hrun_c, hsame_x1, hrep1, hfr_c, hc_c⟩ :=
          lsfSplitUpdate_runs (pos := st.pos) hw16 (hx_end ▸ hend_ltw) hcur_len_ltw
            (fun k hk => hx_end ▸ hdisj k (by omega)) (fun k hk => hword k (by omega))
            hrep hu_val (hx_vc.symm ▸ hu_cap) hu_can.1 hu_can.2 hUpdAt
            hpAdd hMinUp' hDgDelF' hDgUpdF' hDgUpdG' hBFS hTSplit'
        suffices hgoal : ∃ o st1 c_b,
            Runs w p ω
              (.assign 6 (.load (.reg 5)) ;;
               .cond (.bin .eq (.reg 6) (.const 0))
                 (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                  .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
                  .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
                  .call 10 idxInsUpd [.reg 0, .reg 7, .reg 8, .reg 9])
                 (.cond (.bin .eq (.reg 6) (.const 1))
                   (.assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
                    .call 10 idxDelUpd [.reg 0, .reg 7])
                   (.call 10 idxSplitUpd [.reg 0, .reg 5])) ;;
               .assign 5 (.bin .add (.reg 5) (.reg 10)) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)))
              st o st1 c_b ∧
            (o = .normal ∧ st1.regs 0 = b ∧ st1.regs 2 = heap ∧ st1.regs 3 = numUpd ∧
              st1.regs 4 = i + 1 ∧ st1.regs 5 = curPtr + len ∧ st1.mem = st_c.mem) ∧
            0 + c_b ≤ c_c + 100 by
          rcases hgoal with ⟨_, st1, c_b, hrun_b, ⟨rfl, g0, g2, g3, g4, g5, gmem⟩, hcb⟩
          refine ⟨st1, c_b, x1, hrun_b, g0, g2, g3, g4, g5, hsame.trans hsame_x1,
            gmem ▸ hrep1, fun a ha => by rw [gmem, hfr_c a (hx_end ▸ ha), hfr a ha], ?_⟩
          rw [gmem]
          have h1 : 3000 * len + 100 ≤ 3900 * len := by omega
          have h2 : 3900 * len ≤ 3900 * len * x0.L_w := Nat.le_mul_of_pos_right _ hLw1
          clear * - hcb hc_c h1 h2; omega
        refine runs_seq_assign_le (v := tag) (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
        have heq0 : (Expr.bin .eq (.reg 6) (.const 0)).eval w
            { mem := st.mem, regs := Function.update st.regs 6 tag, pos := st.pos } = some 0 := by
          simp [Expr.eval, BinOp.eval, htag_ne0, show 0 < 2 ^ w by omega]
        refine runs_seq_cond_le heq0 (fun h => by omega) ?_
        intro _
        have heq1 : (Expr.bin .eq (.reg 6) (.const 1)).eval w
            { mem := st.mem, regs := Function.update st.regs 6 tag, pos := st.pos } = some 0 := by
          simp [Expr.eval, BinOp.eval, htag_ne1, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega]
        refine runs_seq_cond_le heq1 (fun h => by omega) ?_
        intro _
        have hcall : Runs w p ω (.call 10 idxSplitUpd [.reg 0, .reg 5])
            { mem := st.mem, regs := Function.update st.regs 6 tag, pos := st.pos }
            .normal { st_c with regs := Function.update (Function.update st.regs 6 tag) 10 len }
            (argsSize [.reg 0, .reg 5] + c_c + 1) :=
          runs_call_iff.mpr ⟨[b, curPtr], _, .returned len, st_c, c_c, by eval_expr, hpSplit, hrun_c, rfl, rfl, rfl⟩
        refine runs_seq_of_runs_le hcall ?_
        refine runs_seq_assign_le (v := curPtr + len) (by eval_expr) ?_
        refine runs_assign_le (v := i + 1) (by eval_expr) ?_ ?_
        · refine ⟨rfl, by simp [hr0], by simp [hr2], by simp [hr3], by simp, by simp, rfl⟩
        · dsimp only [argsSize, Expr.size]; omega
    rcases hstep with ⟨st1, c_b, x1, hrun_b, hr1_0, hr1_2, hr1_3, hr1_4, hr1_5,
      hsame1, hrep1, hfr1, hc_b⟩
    have hmem1_rest : ∀ k < remWords - len, st1.mem (curPtr + len + k) = st.mem (curPtr + len + k) := by
      intro k hk
      have ha : curPtr + len + k < b ∨ x0.endAddr b ≤ curPtr + len + k := by
        simpa [Nat.add_assoc] using hdisj (len + k) (by omega)
      exact (hfr1 _ ha).trans (hfr _ ha).symm
    have hrest_body1 : BatchBodyAt st1.mem (curPtr + len) (applyLSFUpdate S u).G us (remWords - len) := by
      have hG_eq : (applyLSFUpdate S u).G = S.G.applyUpdate u := by cases u <;> rfl
      rw [hG_eq]
      exact batchBodyAt_of_agree hrest_body fun a ha1 ha2 => by
        have := hmem1_rest (a - (curPtr + len)) (by omega)
        rwa [Nat.add_sub_cancel' ha1] at this
    have hG_eq' : (applyLSFUpdate S u).G = S.G.applyUpdate u := by cases u <;> rfl
    obtain ⟨st', c_r, x', hrun_r, hr'_2, hsame', hrep', hfr', hc_r⟩ :=
      ih (curPtr + len) (remWords - len) (i + 1) (applyLSFUpdate S u) x1 st1
        (by simp at hi; omega) hnum (by omega)
        (fun k hk => by simpa [Nat.add_assoc] using hdisj (len + k) (by omega))
        (fun k hk => by rw [hmem1_rest k hk, Nat.add_assoc]; exact hword (len + k) (by omega))
        hsame1 hrep1 hfr1 hrest_body1 (hG_eq'.symm ▸ hus_val) hus_cap (hG_eq'.symm ▸ hus_can)
        hr1_0 hr1_2 hr1_3 hr1_4 hr1_5
    have hlen_pos : 1 ≤ len := by
      cases u with
      | insert _ _ _ => exact hUpdAt.1 ▸ by decide
      | delete _ => exact hUpdAt.1 ▸ by decide
      | split _ _ _ _ => rcases hUpdAt with ⟨_, _, _, _, _, _, hlen, _⟩ | ⟨_, _, _, _, _, _, hlen, _⟩ <;> omega
    refine ⟨st', 3 + c_b + c_r + 1, x', ?_, hr'_2, hsame', hrep', hfr', ?_⟩
    · rw [runs_loop_iff]
      exact Or.inr (Or.inr ⟨1, st1, c_b, c_r, hcond, by decide, hrun_b, hrun_r, rfl⟩)
    · have hsum_w : len * x0.L_w + (remWords - len) * x0.L_w = remWords * x0.L_w := by
        rw [← Nat.add_mul, Nat.add_sub_cancel' hlen_le]
      have h100 : 4 ≤ 100 * (len * x0.L_w) := by
        have : 1 ≤ len * x0.L_w := Nat.mul_le_mul hlen_pos hLw1
        omega
      rw [Nat.mul_assoc] at hc_b hc_r ⊢
      clear * - hc_b hc_r hsum_w h100
      omega

/-! ## Top-level `op 0` theorem for `DSRep.Implements` -/

/-- Complete `op 0` (`applyLSFBatch`) verification matching the operation clause of `DSRep.Implements`
for `lsfDataStructure` with `space = 0`. -/
theorem lsfApplyBatch_runs
    {w h b idxInsUpd idxDelUpd idxSplitUpd idxAddRoot idxMinUp idxDgDelF
     idxDgInsG idxDgDelG idxDgUpd idxBFS idxTIns idxTDel idxTSplit idxSetWstr : ℕ}
    {p : Program} {S : LSFState} {x : LSFConcrete} {args : List ℕ} {mem : ℕ → ℕ}
    (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some b)
    (hrep : (LSFRep h).rep b S x mem)
    (hpre : lsfBatchPre w S args mem)
    (hfoot : ∀ a, (LSFRep h).foot b x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + 0 < 2 ^ w)
    (hpIns : p.procs[idxInsUpd]? = some (lsfInsertUpdateProc idxAddRoot idxDgInsG idxTIns idxSetWstr))
    (hpDel : p.procs[idxDelUpd]? = some (lsfDeleteUpdateProc idxAddRoot idxDgDelG idxTDel))
    (hpSplit : p.procs[idxSplitUpd]? = some (lsfSplitUpdateProc idxAddRoot idxDgUpd idxBFS idxTSplit))
    (hpAdd : p.procs[idxAddRoot]? = some (addOrigRootProc idxMinUp idxDgDelF idxBFS))
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList))
    (hDgDelF : ∀ F, MeetsContract w p idxDgDelF (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F))
    (hDgInsG : ∀ G, MeetsContract w p idxDgInsG (dgInsertEdgeContract w x.vCap x.eCap G))
    (hDgDelG : ∀ G, MeetsContract w p idxDgDelG (dgDeleteEdgeContract w x.vCap x.eCap G))
    (hDgUpdF : ∀ G H v v' St Sh len, MeetsContract w p idxDgUpd
      (dgApplyUpdateContract w x.vCap (fECap x.eCap x.n0) G H (.split v v' St Sh) len))
    (hDgUpdG : ∀ G v v' St Sh len, MeetsContract w p idxDgUpd
      (dgApplyUpdateContract w x.vCap x.eCap G G (.split v v' St Sh) len))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F))
    (hTIns : ∀ G T_cur T₀ π, MeetsContract w p idxTIns
      (lsfTBlockInsertContract w x.vCap x.eCap x.tM G T_cur T₀ π x.tOrigList))
    (hTDel : ∀ G T_cur T₀ π, MeetsContract w p idxTDel
      (lsfTBlockDeleteContract w x.vCap x.eCap x.tM G T_cur T₀ π x.tOrigList))
    (hTSplit : ∀ G T_cur T₀ π v v' St Sh len, MeetsContract w p idxTSplit
      (lsfTBlockSplitContract w x.vCap x.eCap x.tM G T_cur T₀ π x.tOrigList v v' St Sh len))
    (hSetWstr : MeetsContract w p idxSetWstr (lsfSetWstrOneContract w h)) :
    ∃ o st' c, Runs w p ω (lsfApplyBatchProc idxInsUpd idxDelUpd idxSplitUpd)
        (startState args mem pos) o st' c ∧
      ∃ s' x', (LSFRep h).rep b s' x' st'.mem ∧
        lsfBatchPost S args mem s' st'.mem ∧
        (LSFRep h).Respects ((LSFRep h).foot b x) (heapArg args) 0 mem o.value b x' st'.mem ∧
        c + (LSFRep h).phi b x' st'.mem ≤ lsfBatchCost args mem + (LSFRep h).phi b x mem := by
  rcases hpre with ⟨b', batchPtr, heap, U, totalWords, rfl, hw16, hBatchAt, hU_val, hU_caps,
    hbatch_word, hbatch_le, hbatch_disj⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst b'
  have hheap_eq : heapArg [b, batchPtr, heap] = heap := rfl
  rw [hheap_eq] at hfoot hz hsp
  have hhdr := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvCap_m : mem (b + lsfOffVCap) = x.vCap := hhdr.1
  have heCap_m : mem (b + lsfOffECap) = x.eCap := hhdr.2.1
  have hLw_m : mem (b + lsfOffLW) = x.L_w := hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have hend_m : mem (b + lsfOffEnd) = x.endAddr b := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hvCap_m, heCap_m] at hU_caps
  rw [hend_m] at hbatch_disj
  have hb_lt_end : b < x.endAddr b := by dsimp [LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, lsfHdrSize]; omega
  have hend_le_heap : x.endAddr b ≤ heap := by
    have := hfoot (x.endAddr b - 1) ⟨by omega, by omega⟩
    omega
  have hend_ltw : x.endAddr b < 2 ^ w := by omega
  have hheap_ltw : heap < 2 ^ w := by omega
  have hb_ltw : b < 2 ^ w := by omega
  have hbp_ltw : batchPtr < 2 ^ w := hwords batchPtr (by simp)
  -- Canonicalize `U` into `U' := canonBatch S.G U`
  set U' := canonBatch S.G U
  have hBatchAt' : BatchAt mem batchPtr S.G U' totalWords := (canonBatch_batchAt hU_val).mpr hBatchAt
  have hU'_val : S.G.BatchIsValid U' := canonBatch_valid hU_val
  have hU'_caps : BatchWithinCaps x.vCap x.eCap U' := canonBatch_withinCaps hU_caps
  have hU'_can := isCanonBatch_of_canonBatch S.G U hU_val
  obtain ⟨htw_ge1, hnum_m, hbody'⟩ := hBatchAt'
  have hbp1_ltw : batchPtr + 1 < 2 ^ w := by omega
  have hnum_ltw : U'.length < 2 ^ w := by
    have h0 := hbatch_word 0 (by omega)
    rw [Nat.add_zero, hnum_m] at h0; exact h0
  have hst0_r : (startState [b, batchPtr, heap] mem pos).regs 0 = b ∧
      (startState [b, batchPtr, heap] mem pos).regs 1 = batchPtr ∧
      (startState [b, batchPtr, heap] mem pos).regs 2 = heap := by simp [startState]
  rcases hst0_r with ⟨hr0, hr1, hr2⟩
  -- Execute prefix (3 assigns) + loop + `.ret (.reg 2)`
  let st_l0 : State :=
    { mem := mem
      regs := Function.update (Function.update (Function.update
        (startState [b, batchPtr, heap] mem pos).regs 3 U'.length) 4 0) 5 (batchPtr + 1)
      pos := pos }
  obtain ⟨st_l1, c_loop, x', hrun_loop, hr_l1_2, hsame', hrep', hfr', hc_loop⟩ :=
    lsfApplyBatchLoop_runs (numUpd := U'.length) (mem0 := mem) (p := p) (ω := ω)
      hw16 hend_ltw hheap_ltw hpIns hpDel hpSplit hpAdd hMinUp hDgDelF hDgInsG hDgDelG
      hDgUpdF hDgUpdG hBFS hTIns hTDel hTSplit hSetWstr
      U' (batchPtr + 1) (totalWords - 1) 0 S x st_l0
      (by omega) hnum_ltw (by omega)
      (fun k hk => by simpa [Nat.add_assoc] using hbatch_disj (1 + k) (by omega))
      (fun k hk => by
        change mem (batchPtr + 1 + k) < 2 ^ w
        rw [Nat.add_assoc]; exact hbatch_word (1 + k) (by omega))
      (SameStaticConcrete.refl x) hrep (fun _ _ => rfl)
      hbody' hU'_val hU'_caps hU'_can
      (by dsimp [st_l0]; simp [hr0]) (by dsimp [st_l0]; simp [hr2])
      (by dsimp [st_l0]; simp) (by dsimp [st_l0]; simp) (by dsimp [st_l0]; simp)
  have hfull : ∃ c_all,
      Runs w p ω (lsfApplyBatchProc idxInsUpd idxDelUpd idxSplitUpd)
        (startState [b, batchPtr, heap] mem pos) (.returned heap) st_l1 c_all ∧
      c_all ≤ c_loop + 30 := by
    suffices h : ∃ o st' c_all,
        Runs w p ω (lsfApplyBatchProc idxInsUpd idxDelUpd idxSplitUpd)
          (startState [b, batchPtr, heap] mem pos) o st' c_all ∧
        (o = .returned heap ∧ st' = st_l1) ∧ 0 + c_all ≤ c_loop + 30 by
      rcases h with ⟨_, _, c_all, hr, ⟨rfl, rfl⟩, hc⟩; exact ⟨c_all, hr, by omega⟩
    dsimp only [lsfApplyBatchProc]
    refine runs_seq_assign_le (v := U'.length) (Expr.eval_load_of_eq (by eval_expr) hnum_m) ?_
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    refine runs_seq_assign_le (v := batchPtr + 1) (by eval_expr) ?_
    refine runs_seq_of_runs_le hrun_loop ?_
    refine runs_ret_le (v := heap) (by eval_expr) ⟨rfl, rfl⟩ ?_
    dsimp only [Expr.size]; omega
  rcases hfull with ⟨c_all, hrun_all, hc_all⟩
  have hpost : lsfBatchPost S [b, batchPtr, heap] mem (applyLSFBatch S U') st_l1.mem :=
    ⟨b, batchPtr, heap, U', totalWords, rfl, ⟨htw_ge1, hnum_m, hbody'⟩, rfl⟩
  have hresp : (LSFRep h).Respects ((LSFRep h).foot b x) heap 0 mem (Outcome.returned heap).value b x' st_l1.mem := by
    dsimp only [Outcome.value]
    refine ⟨le_rfl, by omega, fun a ha => ?_, fun a _ hnot => ?_, fun a ha => ?_⟩
    · rw [hfr' a (Or.inr (by omega))]; exact hz a ha
    · exact hfr' a (by dsimp [LSFRep] at hnot; omega)
    · left; dsimp [LSFRep] at ha ⊢; rwa [← sameStatic_endAddr_batch hsame']
  have hcost_eq : lsfBatchCost [b, batchPtr, heap] mem = lsfBatchCostFactor * (totalWords * x.L_w + 1) := by
    dsimp only [lsfBatchCost]
    simp only [List.getD_cons_zero, List.getD_cons_succ, hLw_m, batchMemLen_eq hBatchAt]
  refine ⟨.returned heap, st_l1, c_all, hrun_all, applyLSFBatch S U', x', hrep', hpost, hresp, ?_⟩
  change c_all + lsfPhi b x' st_l1.mem ≤ lsfBatchCost [b, batchPtr, heap] mem + lsfPhi b x mem
  rw [hcost_eq]
  dsimp only [lsfBatchCostFactor]
  dsimp only [st_l0] at hc_loop
  rw [Nat.mul_assoc] at hc_loop
  have htw_le : (totalWords - 1) * x.L_w ≤ totalWords * x.L_w :=
    Nat.mul_le_mul_right x.L_w (Nat.sub_le totalWords 1)
  clear * - hc_all hc_loop htw_le
  omega

end

end MinCostFlow.LSF.Program
