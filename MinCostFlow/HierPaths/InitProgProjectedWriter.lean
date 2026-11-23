module

public import MinCostFlow.HierPaths.InitProgProjectedRows
public import MinCostFlow.HierPaths.InitStore

/-!
# The projected walk section entry

The entry makes the two connector address columns and a small header in
scratch. The compressed row writer uses this header to project each
connector in order. The finished section is moved down over the scratch.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The continuation after writing the projection context. -/
def initProjectedFinish (csr move : ℕ) : Stmt :=
  .assign 20 (.bin .add (.reg 6) (.const 12)) ;;
  .call 21 csr [.reg 6, .reg 10, .reg 20] ;;
  .call 22 move [.reg 7, .reg 20, .reg 21] ;;
  .ret (.reg 22)

def initProjectedWriter (slots indices root csr move : ℕ) : Stmt :=
  .assign 7 (.reg 6) ;;
  .call 8 slots secArgs ;;
  .call 9 indices [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 8] ;;
  .assign 10 (.bin .sub (.reg 8) (.reg 6)) ;;
  .assign 11 (.load (.bin .add (.reg 4) (.const 7))) ;;
  .assign 12 (.load (.bin .add (.reg 4) (.const 8))) ;;
  .assign 13 (.bin .shiftLeft (.const 1) (.reg 11)) ;;
  .assign 14 (.bin .shiftLeft (.const 1) (.reg 12)) ;;
  .assign 15 depthExpr ;;
  .assign 16 numPairsExpr ;;
  .call 17 root [.reg 4, .reg 13, .bin .add (.reg 15) (.const 1), .const 0, .const 0] ;;
  .assign 18 (.bin .add (.bin .add (.reg 4) (.const 7)) (.load (.bin .add (.reg 4) (.const 2)))) ;;
  .assign 19 (.bin .add (.reg 4) (.const 10)) ;;
  .assign 6 (.reg 9) ;;
  storeSeq [4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 7, 8] 0
    (initProjectedFinish csr move)

def initProjectedWriterScratch (S : StaticData) (verts : Bool) : ℕ :=
  2 * S.numConn + 12 + initProjectedScratch S verts

def initProjectedWriterCost (S : StaticData) (G : Graph) (verts : Bool) : ℕ :=
  2 * initEndpointSectionCost S +
    rangeCost (initProjectedRowCost S G verts) 0 S.numConn +
    70 * S.numConn + 17 * (initProjectedSection S verts).length + 1000

/-- Writes above the destination of the compressed table leave the context valid. -/
theorem initProjectedContext_stable {w ctx : ℕ} {S : StaticData} {G : Graph}
    {data : ℕ} {mem mem' : ℕ → ℕ} (h : initProjectedContext w ctx S G data mem)
    (hf : ∀ y < data, mem' y = mem y) :
    initProjectedContext w ctx S G data mem' := by
  obtain ⟨h, host, L, O, slots, indices, hh, hS, hsep, hRoot, hslots, hindices,
    hctx, hsl, hin, hb, hH, hB, hk, hD⟩ := h
  obtain ⟨hg, hgB, hL, hO, hLAt, hOAt, hproj, hGm⟩ := hRoot
  have hslotsLen : (initEndpointWords S 2).length = S.numConn := by
    rw [← initConnLocs_slots, List.length_map, initConnLocs_length]
  have hindLen : (initEndpointWords S 3).length = S.numConn := by
    rw [← initConnLocs_indices, List.length_map, initConnLocs_length]
  refine ⟨h, host, L, O, slots, indices,
    listAt_congr (fun i hi => (hf _ (by simp at hi; omega)).symm) hh,
    listAt_congr (fun i hi => (hf _ (by omega)).symm) hS, hsep,
    ⟨listAt_congr (fun i hi => (hf _ (by omega)).symm) hg, hgB, hL, hO,
      fun e he => (hf _ (by omega)).trans (hLAt e he),
      fun i hi => ⟨(hf _ (by omega)).trans (hOAt i hi).1, (hOAt i hi).2⟩, hproj, hGm⟩,
    listAt_congr (fun i hi => (hf _ (by rw [hslotsLen] at hi; omega)).symm) hslots,
    listAt_congr (fun i hi => (hf _ (by rw [hindLen] at hi; omega)).symm) hindices,
    hctx, hsl, hin, hb, hH, hB, hk, hD⟩

theorem initProjectedCSR_meetsContract {w f row project ctx : ℕ}
    {S : StaticData} {G : Graph} {verts : Bool} {p : Program}
    (hp : p.procs[f]? = some (initCSRWrite row))
    (hRow : p.procs[row]? = some (initProjectedRowProc project))
    (hProj : ∀ q, MeetsContract w p project (initProjectAtContract w S G verts q)) :
    MeetsContract w p f (initCSRWriteContract w ctx S.numConn (initProjectedRow S verts)
      (initProjectedRowCost S G verts) (initProjectedContext w ctx S G)
      (initProjectedScratch S verts)) :=
  initCSRWrite_meetsContract hp (fun _ hi => initProjectedRowProc_meetsContract hi hRow hProj)
    (fun _ _ _ hi hfr => initProjectedContext_stable hi hfr)

private theorem initProjectedFinish_triple {w csr move ctx dst : ℕ}
    {S : StaticData} {G : Graph} {verts : Bool} {p : Program} {s : State}
    (hCSR : MeetsContract w p csr (initCSRWriteContract w ctx S.numConn
      (initProjectedRow S verts) (initProjectedRowCost S G verts) (initProjectedContext w ctx S G)
      (initProjectedScratch S verts)))
    (hMove : MeetsContract w p move (moveDownContract w))
    (r6 : s.regs 6 = ctx) (r7 : s.regs 7 = dst) (r10 : s.regs 10 = S.numConn)
    (hsep : dst ≤ ctx) (h1 : 1 < 2 ^ w)
    (hCtx : initProjectedContext w ctx S G (ctx + 12) s.mem)
    (hz : ZeroFrom s.mem (ctx + 12))
    (hw : ctx + 12 + (initProjectedSection S verts).length + initProjectedScratch S verts < 2 ^ w) :
    Triple w p (fun t => t = s) (initProjectedFinish csr move)
      (fun o t => ∃ r, o = .returned r ∧ r = dst + (initProjectedSection S verts).length ∧
        ListAt t.mem dst (initProjectedSection S verts) ∧ ZeroFrom t.mem r ∧
        ∀ y < dst, t.mem y = s.mem y)
      (fun _ => rangeCost (initProjectedRowCost S G verts) 0 S.numConn +
        30 * S.numConn + 17 * (ctx + 12 + (initProjectedSection S verts).length - dst) + 150) := by
  let data := ctx + 12
  let len := (initProjectedSection S verts).length
  have hdata : data < 2 ^ w := by omega
  have hn : S.numConn + 1 ≤ len := by
    unfold len initProjectedSection
    rw [csrList, List.length_append, length_csrOffsets]
    omega
  have hEnd : data + len < 2 ^ w := by omega
  intro st ω hs
  subst st
  refine runs_start_le ?_
  unfold initProjectedFinish
  refine runs_seq_assign_le (v := data) (Expr.eval_add (Expr.eval_reg_of_eq r6)
    (Expr.eval_const (by dsimp [data] at hdata; omega)) hdata) ?_
  refine runs_seq_call_le hCSR (vs := [ctx, S.numConn, data])
    (by simp [evalArgs, Expr.eval, r6, r10]) ?_
    ⟨data, rfl, hCtx, hz, hw, h1⟩ ?_
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · dsimp [data] at hdata; omega
    · omega
    · exact hdata
  intro r mem₁ pos₁ hp₁
  obtain ⟨d', ha, hr, hmem, hz₁, hf₁⟩ := hp₁
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, hd⟩ := ha
  subst d'
  change r = data + len at hr
  subst r
  have hd : dst ≤ data := hsep.trans (Nat.le_add_right _ _)
  refine runs_seq_call_le hMove (vs := [dst, data, data + len])
    (by simp [evalArgs, Expr.eval, r7]) ?_
    ⟨dst, data, data + len, rfl, hd, Nat.le_add_right _ _, hEnd, h1⟩ ?_
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · omega
    · exact hdata
    · exact hEnd
  intro r mem₂ pos₂ hp₂
  obtain ⟨dst', data', end', ha, hr, hout, hbelow, hzero, hf₂⟩ := hp₂
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hd', hs', he'⟩ := ha
  subst dst' data' end'
  have hlen : data + len - data = len := Nat.add_sub_cancel_left _ _
  rw [hlen] at hr hout hzero
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ⟨r, rfl, hr, ?_, ?_, ?_⟩ ?_
  · intro i hi
    exact (hout i hi).trans (hmem i hi)
  · intro y hy
    rcases Nat.lt_or_ge y (data + len) with hl | hh
    · exact hzero _ (hr ▸ hy) hl
    · exact (hf₂ _ hh).trans (hz₁ _ hh)
  · intro y hy
    exact (hbelow _ hy).trans (hf₁ _ (hy.trans_le hd))
  · simp [initCSRWriteContract, moveDownContract, Expr.size, argsSize, data, len]
    omega

set_option maxHeartbeats 800000 in
theorem initProjectedWriter_meetsContract {w a f slots indices root csr move : ℕ}
    {S : StaticData} {G : Graph} {verts : Bool} {p : Program}
    (hp : p.procs[f]? = some (initProjectedWriter slots indices root csr move))
    (hSlots : MeetsContract w p slots (SecContract w (buildInv w S a G)
      ⟨slots, fun _ => initEndpointWords S 2, fun _ => initEndpointSectionCost S, fun _ => 0⟩))
    (hIdx : MeetsContract w p indices (SecContract w (buildInv w S a G)
      ⟨indices, fun _ => initEndpointWords S 3, fun _ => initEndpointSectionCost S, fun _ => 0⟩))
    (hRoot : MeetsContract w p root
      (initFlatSeekContract w 3 S (leafDepth S.x S.b + 1) (initHostRow S)))
    (hCSR : ∀ ctx, MeetsContract w p csr (initCSRWriteContract w ctx S.numConn
      (initProjectedRow S verts) (initProjectedRowCost S G verts) (initProjectedContext w ctx S G)
      (initProjectedScratch S verts)))
    (hMove : MeetsContract w p move (moveDownContract w)) :
    MeetsContract w p f (SecContract w (buildInv w S a G)
      ⟨f, fun _ => initProjectedSection S verts, fun _ => initProjectedWriterCost S G verts,
        fun _ => initProjectedWriterScratch S verts⟩) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, dst, rfl, hbl, hInv, hzero, hdst, hroom⟩ := hpre
  have ⟨h', hh', hx, hb, hh8, hxw, hb0, hkw⟩ := header_facts hInv hw
  obtain ⟨ga, pn, pd, M, h, h₁, hbase, hS, hs, hG, hgh, hnum, hden, hgood, hbw, hxi, hlam⟩ := hInv
  have hInv := (show buildInv w S a G base mem from
    ⟨ga, pn, pd, M, h, h₁, hbase, hS, hs, hG, hgh, hnum, hden, hgood, hbw, hxi, hlam⟩)
  subst base
  change h = h' at hh'
  subst h'
  change h₁ + 25 ≤ dst at hdst
  let base := [ga, pn, pd, M, h, h₁]
  let N := S.numConn
  let P := S.numTerm
  let B := 2 ^ S.b
  let D := leafDepth S.x S.b
  let K := numPairsOf S.x S.b
  let idx := dst + N
  let ctx := idx + N
  let len := (initProjectedSection S verts).length
  have hRoom : ctx + 12 + len + initProjectedScratch S verts < 2 ^ w := by
    change dst + len + (2 * N + 12 + initProjectedScratch S verts) < 2 ^ w at hroom
    dsimp [ctx, idx]
    omega
  have hctx : ctx < 2 ^ w := by omega
  have hidx : idx < 2 ^ w := by dsimp [ctx] at hctx; omega
  have h1 : 1 < 2 ^ w := by omega
  have hP : P < 2 ^ w := by
    obtain ⟨_, _, hp⟩ := staticOut_owner_facts hS
    change 10 + P ≤ S.encode.length at hp
    omega
  have hB : B < 2 ^ w := by
    have hpos : 0 < depthOf G.m := (by decide : 0 < 2).trans_le (two_le_depthOf _)
    have h1 := Nat.le_self_pow (a := branchOf G.m) (n := 2) (by decide)
    have h2 := Nat.le_mul_of_pos_left (branchOf G.m ^ 2) hpos
    have h3 := Nat.le_mul_of_pos_right (depthOf G.m * branchOf G.m ^ 2)
      (one_le_lamOf a (dOf pn pd) G.m)
    exact (hgood.branch.trans (h1.trans (h2.trans h3))).trans_lt hxi
  have hSlotsLen : (initEndpointWords S 2).length = N := by
    rw [← initConnLocs_slots, List.length_map, initConnLocs_length]
  have hIdxLen : (initEndpointWords S 3).length = N := by
    rw [← initConnLocs_indices, List.length_map, initConnLocs_length]
  have hSw : h + S.encode.length < 2 ^ w := by omega
  have hD : D + 1 < 2 ^ w := by
    have hsec := hS.section_end_le (i := 3) (by decide)
    rw [staticHostSection] at hsec
    have hs : (D + 1) * P + 1 ≤ (csrList ((D + 1) * P) (initHostRow S)).length := by
      rw [length_csrList]; omega
    have hp : D + 1 ≤ (D + 1) * P := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos S.x)
    exact (hp.trans (Nat.le_trans (Nat.le_add_right _ _) (hs.trans
      ((Nat.le_add_left _ _).trans hsec)))).trans_lt hSw
  have hN : N < 2 ^ w := by dsimp [ctx, idx] at hctx; omega
  have hGraph := graph_encode_length G
  have hGn : G.n < 2 ^ w := by have := hgood.verts; omega
  have hGm : G.m < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold initProjectedWriter
  refine runs_seq_assign_le (v := dst) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_call_le hSlots (vs := base ++ [dst]) rfl hw
    ⟨base, dst, rfl, hbl, hInv, hzero, hdst, by simpa only [hSlotsLen, Nat.add_zero] using hidx⟩ ?_
  intro r mem₁ pos₁ hp₁
  obtain ⟨_, dst', ha, hr, hSlotsAt, hz₁, hf₁⟩ := hp₁
  have he : dst' = dst := List.singleton_inj.mp (List.append_inj_right' ha.symm rfl)
  subst dst'
  change r = dst + (initEndpointWords S 2).length at hr
  rw [hSlotsLen] at hr
  change r = idx at hr
  subst r
  have hInv₁ := buildInv_stable w S a G base mem mem₁ hInv (fun y hy =>
    hf₁ y (by change y < h₁ at hy; omega))
  refine runs_seq_call_le hIdx (vs := base ++ [idx]) rfl ?_
    ⟨base, idx, rfl, hbl, hInv₁, hz₁,
      by change h₁ + 25 ≤ idx; exact hdst.trans (Nat.le_add_right _ _),
      by simpa only [hIdxLen, Nat.add_zero] using hctx⟩ ?_
  · intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hw v (List.mem_append_left _ hv)
    · exact hidx
  intro r mem₂ pos₂ hp₂
  obtain ⟨_, idx', ha, hr, hIdxAt, hz₂, hf₂⟩ := hp₂
  have he : idx' = idx := List.singleton_inj.mp (List.append_inj_right' ha.symm rfl)
  subst idx'
  change r = idx + (initEndpointWords S 3).length at hr
  rw [hIdxLen] at hr
  change r = ctx at hr
  subst r
  have hf (y : ℕ) (hy : y < dst) : mem₂ y = mem y :=
    (hf₂ y (hy.trans_le (Nat.le_add_right _ _))).trans (hf₁ y hy)
  have hStatic : StaticOut mem₂ h S :=
    listAt_congr (fun i hi => (hf _ (by omega)).symm) hS
  have hSlot₂ : ListAt mem₂ dst (initEndpointWords S 2) :=
    listAt_congr (fun i hi => (hf₂ _ (by rw [hSlotsLen] at hi; dsimp [idx]; omega)).symm) hSlotsAt
  have hSub : idx - dst = N := Nat.add_sub_cancel_left _ _
  have hx₂ : mem₂ (h + 7) = S.x := (hf _ (by omega)).trans hx
  have hb₂ : mem₂ (h + 8) = S.b := (hf _ (by omega)).trans hb
  refine runs_seq_assign_le (v := N) (Expr.eval_eq_of_eq
    (Expr.eval_sub (Expr.eval_reg_of_eq (v := idx) rfl) (Expr.eval_reg_of_eq (v := dst) rfl)
      hidx) hSub) ?_
  refine runs_seq_assign_le (v := S.x) (eval_xExpr rfl hx₂ hh8) ?_
  refine runs_seq_assign_le (v := S.b) (eval_bExpr rfl hb₂ hh8) ?_
  refine runs_seq_assign_le (v := P) ?_ ?_
  · have he : (1 : ℕ) <<< S.x = P := by simp [Nat.shiftLeft_eq, P, StaticData.numTerm]
    exact Expr.eval_eq_of_eq
      (Expr.eval_shiftLeft (Expr.eval_const h1) (Expr.eval_reg_of_eq (v := S.x) rfl) (he ▸ hP)) he
  refine runs_seq_assign_le (v := B) ?_ ?_
  · have he : (1 : ℕ) <<< S.b = B := by simp [Nat.shiftLeft_eq, B]
    exact Expr.eval_eq_of_eq
      (Expr.eval_shiftLeft (Expr.eval_const h1) (Expr.eval_reg_of_eq (v := S.b) rfl) (he ▸ hB)) he
  refine runs_seq_assign_le (v := D) (eval_depthExpr rfl hx₂ hb₂ hh8 hxw hb0) ?_
  refine runs_seq_assign_le (v := K) (eval_numPairsExpr rfl hx₂ hb₂ hh8 hxw hb0 hkw) ?_
  refine runs_seq_call_le hRoot (vs := [h, P, D + 1, 0, 0]) ?_ ?_
    ⟨h, 0, 0, rfl, hStatic, hSw, by decide, Nat.succ_pos _, Nat.two_pow_pos _,
      staticHostSection S⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, P, D, h1, hD]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hP
    · exact hD
    all_goals exact Nat.two_pow_pos _
  intro host mem₃ pos₃ hp₃
  obtain ⟨h', j', g', ha, hh, hm₃⟩ := hp₃
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hh', _, _, hj', hg'⟩ := ha
  subst h' j' g' mem₃
  let hostAddr := initCSRAddr (h + 7 + mem₂ (h + 3)) ((D + 1) * P) (initHostRow S) 0
  have hh' : host = hostAddr := by simpa [hostAddr, D, P] using hh
  clear hh
  subst host
  let L := h + 7 + mem₂ (h + 2)
  let O := h + 10
  let data := ctx + 12
  have hRoot₂ : InitRootAt w S G mem₂ hostAddr L O (ctx + 12) :=
    staticOut_initRootAt hStatic hgood (by dsimp [ctx, idx]; omega) hGn hGm
  have hL : L < 2 ^ w := by
    have hh := hRoot₂.2.2.1
    change L + _ ≤ ctx + 12 at hh
    omega
  have hO : O < 2 ^ w := by dsimp [O]; omega
  refine runs_seq_assign_le (v := L) ?_ ?_
  · have hl := Nat.le_add_right (h + 7) (mem₂ (h + 2))
    exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
        (Expr.eval_const (by omega)) (by omega)) rfl) hL
  refine runs_seq_assign_le (v := O) (Expr.eval_add (Expr.eval_reg_of_eq rfl)
    (Expr.eval_const (by dsimp [O] at hO; omega)) hO) ?_
  refine runs_seq_assign_le (v := ctx) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_storeSeq [4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 7, 8] 0 _ _ _ rfl
    (by simp; omega) ?_
  intro mem₄ hWords hFrame
  have hhAt : ListAt mem₄ ctx [h, S.x, S.b, P, B, D, K, hostAddr, L, O, dst, idx] := by
    intro i hi
    change i < 12 at hi
    interval_cases i <;> first
      | exact hWords 0 (by decide)
      | exact hWords 1 (by decide)
      | exact hWords 2 (by decide)
      | exact hWords 3 (by decide)
      | exact hWords 4 (by decide)
      | exact hWords 5 (by decide)
      | exact hWords 6 (by decide)
      | exact hWords 7 (by decide)
      | exact hWords 8 (by decide)
      | exact hWords 9 (by decide)
      | exact hWords 10 (by decide)
      | exact hWords 11 (by decide)
  obtain ⟨hGraphAt, hGraphBound, hLBound, hOBound, hLabels, hOwners, hProj, hGword⟩ := hRoot₂
  have hsCtx : h + S.encode.length ≤ ctx := by dsimp [ctx, idx]; omega
  have hRctx := staticOut_initRootAt (w := w) hStatic hgood hsCtx hGn hGm
  obtain ⟨_, hGB, hLB, hOB, _, _, _, _⟩ := hRctx
  have hbefore (y : ℕ) (hy : y < ctx) : mem₄ y = mem₂ y :=
    hFrame y (.inl (show y < ctx from hy))
  change hostAddr + (S.H.host 0 0).encode.length ≤ ctx at hGB
  change L + (S.H.host 0 0).m ≤ ctx at hLB
  change O + P ≤ ctx at hOB
  have hCtx : initProjectedContext w ctx S G data mem₄ := by
    refine ⟨h, hostAddr, L, O, dst, idx, hhAt,
      listAt_congr (fun i hi => (hbefore _ (by omega)).symm) hStatic,
      hsCtx.trans (Nat.le_add_right _ _), ?_,
      listAt_congr (fun i hi => (hbefore _ (by rw [hSlotsLen] at hi; dsimp [ctx, idx]; omega)).symm)
        hSlot₂,
      listAt_congr (fun i hi => (hbefore _ (by rw [hIdxLen] at hi; dsimp [ctx]; omega)).symm)
        hIdxAt,
      le_rfl, by dsimp [data, ctx, idx]; omega, by dsimp [data, ctx]; omega,
      hb0, hgood.valid, hB, hkw, hD⟩
    exact ⟨listAt_congr (fun i hi => (hbefore _ (by omega)).symm) hGraphAt,
      hGraphBound, hLBound, hOBound, fun e he => (hbefore _ (by omega)).trans (hLabels e he),
      fun i hi => ⟨(hbefore _ (by omega)).trans (hOwners i hi).1, (hOwners i hi).2⟩, hProj, hGword⟩
  have hz₄ : ZeroFrom mem₄ data := fun y hy => (hFrame y (.inr (by simpa [data] using hy))).trans
    (hz₂ y (by dsimp [data] at hy; omega))
  have hdctx : dst ≤ ctx := by dsimp [ctx, idx]; omega
  let regs :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update ((startState (base ++
      [dst]) mem pos).regs) 7 dst) 8 idx) 9 ctx) 10 N) 11 S.x) 12 S.b) 13 P) 14 B) 15 D) 16 K)
      17 hostAddr) 18 L) 19 O) 6 ctx
  let st : State := ⟨mem₄, regs, pos₃⟩
  obtain ⟨o, t, c, hrun, ⟨r, ho, hr, hTable, hz, hfr⟩, hc⟩ :=
    initProjectedFinish_triple (s := st) (hCSR ctx) hMove rfl rfl rfl hdctx h1 hCtx hz₄ hRoom st ω rfl
  subst o
  refine ⟨.returned r, t, c, hrun, ⟨base, dst, rfl, hr, hTable, hz, ?_⟩, ?_⟩
  · intro y hy
    exact (hfr _ hy).trans ((hbefore _ (hy.trans_le hdctx)).trans (hf _ hy))
  · have hd : ctx + 12 + len - dst = 2 * N + 12 + len := by dsimp [ctx, idx]; omega
    change c ≤ rangeCost (initProjectedRowCost S G verts) 0 N + 30 * N +
      17 * (ctx + 12 + len - dst) + 150 at hc
    rw [hd] at hc
    simp [SecContract, initProjectedWriterCost, initFlatSeekContract, numPairsExpr, depthExpr,
      Expr.size, argsSize, secArgs]
    dsimp only [N, len] at hc
    omega


end MinCostFlow.HierPaths

end
