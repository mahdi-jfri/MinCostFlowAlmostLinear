module

public import MinCostFlow.HierPaths.BuildProgWalkCollectRound
import MinCostFlow.HierPaths.InitLayout

/-!
# Collecting all per-child walk pointers across the round directory and final injection

Proves `buildCollectWalksProc_meetsContract`, combining per-round collection
(`buildCollectRoundProc_meetsContract`) with the final injection archive scan.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- `buildCollectWalksProc` meets `buildCollectWalksContract`. -/
theorem buildCollectWalksProc_meetsContract {w f fRound fAppend : ℕ} {p : Program}
    {D : ChoiceLoopData} {slot slotWords heap₁ injEnd : ℕ}
    {sts : ℕ → ChildState} {F : ℕ → List ((ℕ × ℕ) × List ℕ)}
    (hf : p.procs[f]? = some (buildCollectWalksProc fRound fAppend))
    (hfR : p.procs[fRound]? = some (buildCollectRoundProc fAppend))
    (hfA : p.procs[fAppend]? = some buildAppendRowWalksProc) :
    MeetsContract w p f (buildCollectWalksContract w D slot slotWords heap₁ injEnd sts F) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨cap, rfl, hs1, hDirLe, hTrace, hInj, hCapF, htop, hstW, hw4⟩ := hPre
  obtain ⟨_, bounds, walks, holes, hb0, hbt, hbMono, hArch, hWalksEq⟩ := hTrace
  obtain ⟨Ms, emb, routedEnd, hMlen, hRowLe, hloRep, hMemHeap, hRepEndLe, hEndInj, hRepAt,
    hHeapLeP, hPInj, _, _, hWalksInj, hFsplit, _, hZFinit⟩ := hInj
  have hBoundsLe (r : ℕ) (hr : r ≤ D.limit) : bounds r ≤ heap₁ := by
    have hgen : ∀ d, r + d ≤ D.limit → bounds r ≤ bounds (r + d) := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih => intro hle; exact (ih (by omega)).trans (hbMono (r + d) (by omega))
    have h1 := hgen (D.limit - r) (by omega)
    rw [Nat.add_sub_of_le hr, hbt] at h1
    exact h1
  have hHeapLeInj : heap₁ ≤ injEnd := by omega
  have hPrefixLeCap (r c : ℕ) (hr : r ≤ D.limit) (hc : c < D.count) :
      ((List.range r).flatMap fun i => walks i c).length ≤ cap := by
    have h1 : ((List.range r).flatMap fun i => walks i c).length ≤
        ((List.range D.limit).flatMap fun i => walks i c).length := by
      have hsp : List.range D.limit = List.range r ++ (List.range D.limit).drop r := by
        conv_lhs => rw [← List.take_append_drop r (List.range D.limit)]
        rw [List.take_range, Nat.min_eq_left hr]
      conv_rhs => rw [hsp, List.flatMap_append, List.length_append]
      omega
    have h2 : ((List.range D.limit).flatMap fun i => walks i c).length ≤ (F c).length := by
      have := congrArg List.length (hFsplit c hc)
      dsimp only at this
      rw [hWalksEq c hc, List.length_map, List.length_append] at this
      omega
    exact h1.trans (h2.trans (hCapF c hc))
  let prefixWalks : ℕ → ℕ → List (List ℕ) := fun r c => (List.range r).flatMap fun i => walks i c
  have hWT0 : WalkTableAt D.count injEnd (injEnd + D.count) cap (prefixWalks 0) mem := by
    refine ⟨le_rfl, fun c hc => ?_⟩
    simp only [prefixWalks, List.range_zero, List.flatMap_nil, List.length_nil]
    exact ⟨Nat.zero_le _, hZFinit _ (Nat.le_add_right _ _), fun _ he => (Nat.not_lt_zero _ he).elim⟩
  have hloop1 := Triple.forRange_const (w := w) (p := p) (r := 9) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 10 (.load (.bin .add (.reg 0) (.reg 9))) ;;
      .cond (.reg 10)
        (.call 11 fRound [.reg 10, .reg 2, .reg 3, .reg 6, .reg 7, .reg 8])
        .nop)
    (P := fun st =>
      st.regs 0 = D.directory ∧ st.regs 1 = D.limit ∧ st.regs 2 = D.first ∧
      st.regs 3 = D.base.childSize ∧ st.regs 4 = D.count ∧ st.regs 5 = heap₁ ∧
      st.regs 6 = injEnd ∧ st.regs 7 = injEnd + D.count ∧ st.regs 8 = cap ∧ st.mem = mem)
    (Inv := fun r st =>
      st.regs 0 = D.directory ∧ st.regs 1 = D.limit ∧ st.regs 2 = D.first ∧
      st.regs 3 = D.base.childSize ∧ st.regs 4 = D.count ∧ st.regs 5 = heap₁ ∧
      st.regs 6 = injEnd ∧ st.regs 7 = injEnd + D.count ∧ st.regs 8 = cap ∧ st.regs 9 = r ∧
      WalkTableAt D.count injEnd (injEnd + D.count) cap (prefixWalks r) st.mem ∧
      (∀ a < injEnd, st.mem a = mem a) ∧ ZeroFrom st.mem (injEnd + D.count + D.count * cap))
    (32 * (D.base.childSize * D.count) + 140 * D.count + 225) 0 D.limit (Nat.zero_le _)
    (by omega) (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
        by simpa using h8, by simp, hm ▸ hWT0, fun _ _ => hm ▸ rfl,
        fun a ha => hm ▸ hZFinit a (by omega)⟩)
    (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi' => by simp [Expr.eval, hi'.2.1])
    (fun r _ hr => by
      intro st ω' ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hWTr, hPresR, hZFr⟩
      set rec := mem (D.directory + r)
      have hMrec : st.mem (D.directory + r) = rec := hPresR _ (by omega)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := rec)
        (show Expr.eval w st (.load (.bin .add (.reg 0) (.reg 9))) = some rec by
          rw [← hMrec]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h0)
            (Expr.eval_reg_of_eq h9) (by omega))) ?_
      have hNextEq : (fun c => prefixWalks r c ++ walks r c) = prefixWalks (r + 1) := by
        funext c; simp [prefixWalks, List.range_succ, List.flatMap_append]
      refine runs_cond_le (v := rec) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
      · intro hrec0
        have hRoundSpec := buildCollectRoundProc_meetsContract (w := w)
          (G := D.base.host) (start := D.first) (s := D.base.childSize) (k := D.count)
          (d := D.base.pathBound) (coreCap := roundCoreCap D + roundRouteCap D)
          (lo := bounds r) (hi := bounds (r + 1)) (rec := rec)
          (walks := walks r) (hole := holes r) (preWalks := prefixWalks r) hfR hfA
        have hBndLe : bounds (r + 1) ≤ injEnd := (hBoundsLe (r + 1) hr).trans hHeapLeInj
        have hArchSt : RoundArchive D.base.host D.first D.base.childSize D.count D.base.pathBound
            (roundCoreCap D + roundRouteCap D) st.mem (bounds r) (bounds (r + 1)) rec (walks r) (holes r) :=
          (hArch r hr).frame fun a _ ha2 => hPresR a (ha2.trans_le hBndLe)
        have hRecLt : rec < injEnd := by
          have hA' := hArch r hr
          unfold RoundArchive at hA'; rw [ite_eq_right hrec0] at hA'
          obtain ⟨_, _, _, _, _, _, _, hhiEq, _, _, _⟩ := hA'; omega
        have hkPos : 1 ≤ D.count := by
          have hA' := hArch r hr; unfold RoundArchive at hA'; rw [ite_eq_right hrec0] at hA'
          obtain ⟨_, _, _, _, _, _, _, _, ho1, hok, _⟩ := hA'; omega
        have hRoundPre : (buildCollectRoundContract w D.base.host D.first D.base.childSize
            D.count D.base.pathBound (roundCoreCap D + roundRouteCap D) (bounds r) (bounds (r + 1)) rec (walks r)
            (holes r) (prefixWalks r)).pre
            [rec, D.first, D.base.childSize, injEnd, injEnd + D.count, cap] st.mem := by
          refine ⟨injEnd, injEnd + D.count, cap, rfl, hrec0, hs1, hBndLe, hArchSt, hWTr,
            fun c hc => ?_, htop, hZFr, hstW, hw4⟩
          have := hPrefixLeCap (r + 1) c hr hc
          have hStep : prefixWalks (r + 1) c = prefixWalks r c ++ walks r c := by
            simp [prefixWalks, List.range_succ, List.flatMap_append]
          change (prefixWalks (r + 1) c).length ≤ cap at this
          rw [hStep, List.length_append] at this
          exact this
        refine runs_call_le hRoundSpec
          (vs := [rec, D.first, D.base.childSize, injEnd, injEnd + D.count, cap])
          (by simp [evalArgs, Expr.eval, h2, h3, h6, h7, h8])
          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl | rfl | rfl | hx
              · omega
              · omega
              · have : 1 * D.base.childSize ≤ D.count * D.base.childSize :=
                  Nat.mul_le_mul_right _ hkPos; omega
              · omega
              · omega
              · rw [hx]; have : 1 * cap ≤ D.count * cap := Nat.mul_le_mul_right _ hkPos; omega)
          hRoundPre ?_
        intro rv mNext posNext hPostR
        obtain ⟨_, _, _, heqR, hWTnext, hPresNext, hZFnext⟩ := hPostR
        simp only [List.cons.injEq, and_true, true_and] at heqR
        obtain ⟨rfl, rfl, rfl⟩ := heqR
        refine ⟨⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
          by simpa using h8, by simp, by rwa [← hNextEq],
          fun a ha => (hPresNext a ha).trans (hPresR a ha), hZFnext⟩, by simp [h9]⟩, ?_⟩
        simp only [buildCollectRoundContract, Expr.size, argsSize]
        omega
      · intro hrec0
        have hArchR := hArch r hr
        unfold RoundArchive at hArchR
        rw [ite_eq_left hrec0] at hArchR
        refine runs_nop_le ?_ (by simp [Expr.size])
        have hPEq : prefixWalks (r + 1) = prefixWalks r := by
          rw [← hNextEq]; funext c; simp [hArchR.1 c]
        exact ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
          by simpa using h8, by simp, by rwa [hPEq], hPresR, hZFr⟩, by simp [h9]⟩)
  refine runs_start_le ?_
  unfold buildCollectWalksProc
  refine runs_seq_triple_le hloop1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  intro st1 ⟨_, _, _, h3, h4, h5, h6, h7, h8, _, hWT1, hPres1, hZF1⟩
  let rep := injectReplyBase heap₁ D.count D.base.childSize
  let walkDir := routedEnd + 4
  obtain ⟨hRep1, hMtOff, hTwoFlatLe⟩ := routeMatched_mt_offsets hRepAt
  have hRoW : routedEnd < 2 ^ w := by omega
  have hRepW : rep < 2 ^ w := by omega
  have hWdW : walkDir < 2 ^ w := by dsimp [walkDir]; omega
  have hMrep1 : st1.mem (rep + 1) = 1 :=
    (hPres1 _ (by dsimp [rep]; omega)).trans hRep1
  have hMheap : st1.mem heap₁ = routedEnd :=
    (hPres1 _ (by dsimp [rep, injectReplyBase, buildBatchEnd] at hRepEndLe hEndInj; omega)).trans hMemHeap
  refine runs_seq_assign_le (v := rep)
    (by have h1 : heap₁ + D.base.childSize < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h2 : D.count + D.count < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h3' : heap₁ + D.base.childSize + (D.count + D.count) < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h4' : heap₁ + D.base.childSize + (D.count + D.count) + 1 < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h5' : D.count * D.base.childSize < 2 ^ w := by
          dsimp [rep, injectReplyBase, buildBatchEnd] at hRepW; omega
        have h6' : heap₁ + D.base.childSize + (D.count + D.count) + 1 +
            D.count * D.base.childSize = rep := by
          dsimp [rep, injectReplyBase, buildBatchEnd]; omega
        rw [← h6']
        exact Expr.eval_add (Expr.eval_add (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq h3) h1)
          (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq h4) h2) h3')
          (Expr.eval_const (by omega)) h4')
          (Expr.eval_mul (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq h3) h5')
          (by rw [h6']; exact hRepW)) ?_
  refine runs_seq_assign_le (v := rep + 5)
    (by have h1 : rep + 4 + st1.mem (rep + 1) = rep + 5 := by rw [hMrep1]
        rw [← h1]
        exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_const (by omega)) (by omega)))
          (by rw [h1]; omega)) ?_
  refine runs_seq_assign_le (v := walkDir)
    (by have h1 : st1.mem heap₁ + 4 = walkDir := by rw [hMheap]
        rw [← h1]
        exact Expr.eval_add (Expr.eval_load (Expr.eval_reg_of_eq (by simpa using h5)))
          (Expr.eval_const (by omega)) (by rw [h1]; exact hWdW)) ?_
  let injRowWalks : ℕ → List (List ℕ) := fun c =>
    (List.range (Ms.getD c []).length).map fun e =>
      let row := matchingWalkRow Ms emb c
      erase D.base.host.edges (row.u e) (row.raw e)
  let curAfterInj : ℕ → ℕ → List (List ℕ) := fun n c =>
    if c < n then (F c).map Prod.snd else prefixWalks D.limit c
  have hloop2 := Triple.forRange_const (w := w) (p := p) (r := 9) (lo := .const 0) (hi := .reg 4)
    (body :=
      .assign 13 (.bin .div (.load (.bin .add (.reg 11) (.reg 9))) (.const 2)) ;;
      .assign 14 (.bin .div (.load (.bin .add (.bin .add (.reg 11) (.reg 9)) (.const 1))) (.const 2)) ;;
      .call 15 fAppend [.reg 12, .reg 13, .reg 14, .reg 6, .reg 7, .reg 8, .reg 9])
    (P := fun st =>
      st.regs 4 = D.count ∧ st.regs 6 = injEnd ∧ st.regs 7 = injEnd + D.count ∧
      st.regs 8 = cap ∧ st.regs 11 = rep + 5 ∧ st.regs 12 = walkDir ∧ st.mem = st1.mem)
    (Inv := fun n st =>
      st.regs 4 = D.count ∧ st.regs 6 = injEnd ∧ st.regs 7 = injEnd + D.count ∧
      st.regs 8 = cap ∧ st.regs 9 = n ∧ st.regs 11 = rep + 5 ∧ st.regs 12 = walkDir ∧
      WalkTableAt D.count injEnd (injEnd + D.count) cap (curAfterInj n) st.mem ∧
      (∀ a < injEnd, st.mem a = mem a) ∧ ZeroFrom st.mem (injEnd + D.count + D.count * cap))
    (32 * D.base.childSize + 90) 0 D.count (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st ⟨h4', h6', h7', h8', h11', h12', hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      have h0eq : curAfterInj 0 = prefixWalks D.limit := by funext c; simp [curAfterInj]
      refine ⟨by simpa using h4', by simpa using h6', by simpa using h7', by simpa using h8',
        by simp, by simpa using h11', by simpa using h12',
        by simpa [hm, h0eq] using hWT1, hm ▸ hPres1, hm ▸ hZF1⟩)
    (fun _ st _ _ hi' => hi'.2.2.2.2.1)
    (fun _ st _ _ hi' => by simp [Expr.eval, hi'.1])
    (fun c _ hc => by
      intro st ω' ⟨h4', h6', h7', h8', h9', h11', h12', hWTc, hPresC, hZFc⟩
      have hcM : c < Ms.length := hMlen.symm ▸ hc
      have hloE : flatIndex Ms c 0 ≤ flatIndex Ms (c + 1) 0 := by
        rw [flatIndex_succ_eq Ms hcM]; omega
      have hhiE : flatIndex Ms (c + 1) 0 ≤ Ms.flatten.length :=
        flatIndex_le_flatten Ms (Nat.succ_le_of_lt hcM)
      have hLenEq : flatIndex Ms (c + 1) 0 - flatIndex Ms c 0 = (Ms.getD c []).length := by
        rw [flatIndex_succ_eq Ms hcM]; omega
      have hMmt0 : st.mem (rep + 5 + c) = 2 * flatIndex Ms c 0 :=
        (hPresC _ (by dsimp [rep] at hPInj ⊢; omega)).trans (hMtOff c (Nat.le_of_lt hcM))
      have hMmt1 : st.mem (rep + 5 + c + 1) = 2 * flatIndex Ms (c + 1) 0 := by
        rw [show rep + 5 + c + 1 = rep + 5 + (c + 1) by omega]
        exact (hPresC _ (by dsimp [rep] at hPInj ⊢; omega)).trans
          (hMtOff (c + 1) (Nat.succ_le_of_lt hcM))
      have h2loW : 2 * flatIndex Ms c 0 < 2 ^ w := by omega
      have h2hiW : 2 * flatIndex Ms (c + 1) 0 < 2 ^ w := by omega
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := flatIndex Ms c 0)
        (by have hdiv : 2 * flatIndex Ms c 0 / 2 = flatIndex Ms c 0 :=
              Nat.mul_div_right _ (by omega : 0 < 2)
            rw [← hdiv]
            exact Expr.eval_div
              (by rw [← hMmt0]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h11')
                    (Expr.eval_reg_of_eq h9') (by dsimp [rep] at hPInj ⊢; omega)))
              (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (v := flatIndex Ms (c + 1) 0)
        (by have hdiv : 2 * flatIndex Ms (c + 1) 0 / 2 = flatIndex Ms (c + 1) 0 :=
              Nat.mul_div_right _ (by omega : 0 < 2)
            rw [← hdiv]
            exact Expr.eval_div
              (by rw [← hMmt1]; exact Expr.eval_load (Expr.eval_add
                    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h11'))
                      (Expr.eval_reg_of_eq (by simpa using h9'))
                      (by dsimp [rep] at hPInj ⊢; omega))
                    (Expr.eval_const (by omega))
                    (by dsimp [rep] at hPInj ⊢; omega)))
              (Expr.eval_const (by omega)) (by omega)) ?_
      have hCurC : curAfterInj c c = prefixWalks D.limit c := by simp [curAfterInj]
      have hJoinC : curAfterInj c c ++ injRowWalks c = (F c).map Prod.snd := by
        rw [hCurC, hFsplit c hc]
        change (List.range D.limit).flatMap (fun i => walks i c) ++ injRowWalks c =
          (sts c).rounds.flatten.map Prod.snd ++ injRowWalks c
        rw [hWalksEq c hc]
      have hCapC : (curAfterInj c c).length + (injRowWalks c).length ≤ cap := by
        have hlen := congrArg List.length hJoinC
        rw [List.length_append] at hlen
        rw [hlen, List.length_map]; exact hCapF c hc
      have hck : (c + 1) * cap ≤ D.count * cap := Nat.mul_le_mul_right cap hc
      rw [Nat.succ_mul] at hck
      have hIL : (injRowWalks c).length = (Ms.getD c []).length := by simp [injRowWalks]
      have hAppSpec := buildAppendRowWalksProc_meetsContract (w := w)
        (oldCnt := (curAfterInj c c).length) (ptrs := fun r => mem (walkDir + r)) hfA
      have hAppPre : (buildAppendRowWalksContract w (curAfterInj c c).length
          (fun r => mem (walkDir + r))).pre
          [walkDir, flatIndex Ms c 0, flatIndex Ms (c + 1) 0, injEnd, injEnd + D.count, cap, c]
          st.mem := by
        refine ⟨walkDir, flatIndex Ms c 0, flatIndex Ms (c + 1) 0, injEnd, injEnd + D.count,
          cap, c, rfl, hloE, (hWTc.2 c hc).2.1,
          fun r _ hr => hPresC _ (by dsimp [walkDir]; omega),
          by dsimp [walkDir]; omega, by omega, by omega, by omega⟩
      refine runs_call_le hAppSpec
        (vs := [walkDir, flatIndex Ms c 0, flatIndex Ms (c + 1) 0, injEnd, injEnd + D.count, cap, c])
        (by simp [evalArgs, Expr.eval, h12', h6', h7', h8', h9'])
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | hx | rfl
            · exact hWdW
            · omega
            · omega
            · omega
            · omega
            · rw [hx]; have : 1 * cap ≤ D.count * cap := Nat.mul_le_mul_right cap (by omega); omega
            · omega)
        hAppPre ?_
      intro rv mNext posNext hPostApp
      obtain ⟨_, _, _, _, _, _, _, heqA, hCntA, hWrA, hFrA⟩ := hPostApp
      simp only [List.cons.injEq, and_true] at heqA
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqA
      have hStepWT := walkTable_append (c := c) (extra := injRowWalks c) hWTc hc hCapC
        (by rw [hCntA, hLenEq, hIL])
        (fun e he => by
          have he' : e < (Ms.getD c []).length := hIL ▸ he
          have hwr := hWrA e (hLenEq.symm ▸ he')
          dsimp only; rw [hwr]; dsimp only; rw [← Nat.add_assoc]
          obtain ⟨_, hAInj, hSeq⟩ := hWalksInj c hc e he'
          have hGetW : (injRowWalks c).getD e [] =
              erase D.base.host.edges ((matchingWalkRow Ms emb c).u e)
                ((matchingWalkRow Ms emb c).raw e) := by
            simp only [injRowWalks]
            rw [List.getD_eq_getElem _ _ (by simp; exact he'), List.getElem_map, List.getElem_range]
          rw [hGetW]
          exact ⟨by dsimp [walkDir]; omega,
            seqAt_frame hSeq fun a ha hb => hPresC a (by dsimp [walkDir] at hb ⊢; omega)⟩)
        (fun a hne ha => hFrA a hne (by rw [hLenEq, ← hIL]; exact ha))
      have hCurEq : (fun c' => if c' = c then curAfterInj c c' ++ injRowWalks c else curAfterInj c c') =
          curAfterInj (c + 1) := by
        funext c'
        by_cases hcc' : c' = c
        · rw [hcc']
          simp only [↓reduceIte, hJoinC, curAfterInj, Nat.lt_succ_self]
        · simp only [hcc', ↓reduceIte, curAfterInj]
          have hiff : c' < c + 1 ↔ c' < c := by omega
          simp only [hiff]
      refine ⟨⟨⟨by simpa using h4', by simpa using h6', by simpa using h7', by simpa using h8',
        by simp, by simpa using h11', by simpa using h12',
        by rw [hCurEq] at hStepWT; exact hStepWT.1,
        fun a ha => (hStepWT.2.1 a ha).trans (hPresC a ha),
        fun a ha => (hStepWT.2.2 a ha).trans (hZFc a ha)⟩, by simp [h9']⟩, ?_⟩
      simp only [buildAppendRowWalksContract, List.getD_cons_succ, List.getD_cons_zero,
        Expr.size, argsSize]
      have hrl := hRowLe c hc
      omega)
  refine runs_seq_triple_le hloop2
    ⟨by simpa using h4, by simpa using h6, by simpa using h7, by simpa using h8,
     by simp, by simp, rfl⟩ ?_
  intro st5 ⟨_, _, _, _, _, _, _, hWTfinal, hPresFinal, hZFfinal⟩
  refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
  · refine ⟨cap, rfl, ?_, hPresFinal, hZFfinal⟩
    refine ⟨hWTfinal.1, fun c hc => ?_⟩
    simpa only [curAfterInj, hc, ↓reduceIte] using hWTfinal.2 c hc
  · simp only [buildCollectWalksContract, Expr.size, Nat.sub_zero]
    have hnorm1 : 32 * (D.base.childSize * D.count) + 140 * D.count + 225 + 1 + 8 =
        32 * (D.base.childSize * D.count) + 140 * D.count + 234 := by omega
    have hnorm2 : 32 * D.base.childSize + 90 + 1 + 8 = 32 * D.base.childSize + 99 := by omega
    rw [hnorm1, hnorm2]
    have h2mul : D.count * (32 * D.base.childSize + 99) =
        32 * (D.base.childSize * D.count) + 99 * D.count := by ring
    have h1mul : (D.limit + 1) * (32 * (D.base.childSize * D.count) + 170 * D.count + 260) =
        D.limit * (32 * (D.base.childSize * D.count) + 170 * D.count + 260) +
          (32 * (D.base.childSize * D.count) + 170 * D.count + 260) := by ring
    have h1le : D.limit * (32 * (D.base.childSize * D.count) + 140 * D.count + 234) ≤
        D.limit * (32 * (D.base.childSize * D.count) + 170 * D.count + 260) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end MinCostFlow.HierPaths
