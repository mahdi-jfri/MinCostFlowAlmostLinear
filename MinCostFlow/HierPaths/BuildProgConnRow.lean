module

public import MinCostFlow.HierPaths.BuildProgWalkRow
public import MinCostFlow.HierPaths.BuildProgCopy
public import MinCostFlow.HierPaths.InitProgCSRWrite

/-!
# Packing connector records

A routed sibling matching has a contiguous endpoint table and a pointer
to each cleaned walk. The output for one edge consists of its two
endpoints and the shortcut's edge numbers. The generic CSR loop packs
all the records with their offsets.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The writer's two source tables and the shortened walks they describe. -/
def ConnectorRowsAt (ctx n : ℕ) (source : ℕ → ℕ × ℕ) (wk : ℕ → List ℕ)
    (limit : ℕ) (mem : ℕ → ℕ) : Prop :=
  ctx+2 ≤ limit ∧
  let endpoints := mem ctx
  let dir := mem (ctx+1)
  endpoints+2*n ≤ limit ∧ dir+n ≤ limit ∧
  ∀ i < n, mem (endpoints+2*i) = (source i).1 ∧
    mem (endpoints+2*i+1) = (source i).2 ∧
    let addr := mem (dir+i)
    addr+1+(wk i).length ≤ limit ∧ SeqAt mem addr (wk i)

/-- The full connector record at index i. -/
def buildConnectorRowWords (source : ℕ → ℕ × ℕ) (wk : ℕ → List ℕ) (i : ℕ) : List ℕ :=
  (source i).1 :: (source i).2 :: wk i

/-- Write both endpoint words and copy the shortcut from its prefixed slot. -/
def buildConnectorRowProc (fCopy : ℕ) : Stmt :=
  .assign 3 (.bin .add (.load (.reg 0)) (.bin .add (.reg 1) (.reg 1))) ;;
  .assign 4 (.load (.bin .add (.load (.bin .add (.reg 0) (.const 1))) (.reg 1))) ;;
  .assign 5 (.load (.reg 4)) ;;
  .store (.reg 2) (.load (.reg 3)) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.load (.bin .add (.reg 3) (.const 1))) ;;
  .call 6 fCopy [.bin .add (.reg 4) (.const 1),.reg 5,.bin .add (.reg 2) (.const 2)] ;;
  .ret (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 5))

theorem buildConnectorRowProc_noRand (fCopy : ℕ) : (buildConnectorRowProc fCopy).NoRand := by
  simp [buildConnectorRowProc,Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Packing rows above the source tables preserves all of their views. -/
theorem ConnectorRowsAt.frame {ctx n lim : ℕ} {source : ℕ → ℕ × ℕ} {wk : ℕ → List ℕ}
    {mem after : ℕ → ℕ} (h : ConnectorRowsAt ctx n source wk lim mem)
    (hFrame : ∀ a < lim, after a = mem a) :
    ConnectorRowsAt ctx n source wk lim after := by
  obtain ⟨hCtx,hEnds,hDir,hRows⟩ := h
  refine ⟨hCtx,?_⟩
  simp only [hFrame ctx (by omega),hFrame (ctx+1) (by omega)]
  refine ⟨hEnds,hDir,fun i hi => ?_⟩
  obtain ⟨ha,hb,hSpan,hAt⟩ := hRows i hi
  have hp := hFrame (mem (ctx+1)+i) (by omega)
  refine ⟨(hFrame _ (by omega)).trans ha,(hFrame _ (by omega)).trans hb,?_⟩
  rw [hp]
  exact ⟨hSpan,seqAt_frame hAt (fun a _ ha => hFrame a (ha.trans_le hSpan))⟩

/-- One connector record is written with a linear-time copy of its walk. -/
theorem buildConnectorRowProc_meetsContract {w f fCopy ctx n i : ℕ} {p : Program}
    {source : ℕ → ℕ × ℕ} {wk : ℕ → List ℕ}
    (hf : p.procs[f]? = some (buildConnectorRowProc fCopy))
    (hc : p.procs[fCopy]? = some buildCopyProc) (hi : i < n) :
    MeetsContract w p f (initCSRWriteRowContract ctx i (buildConnectorRowWords source wk i)
      (fun dst mem => ∃ lim, ConnectorRowsAt ctx n source wk lim mem ∧ lim ≤ dst ∧
        dst+(buildConnectorRowWords source wk i).length < 2^w)
      (17*(wk i).length+100)) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨dst,rfl,⟨lim,hRows,hLe,hRoom⟩,hZero⟩ := hPre
  obtain ⟨hCtx,hEnds,hDir,hRows⟩ := hRows
  let endpoints := mem ctx
  let dir := mem (ctx+1)
  let cell := endpoints+2*i
  let addr := mem (dir+i)
  let len := (wk i).length
  let u := (source i).1
  let v := (source i).2
  have hEnd : dst+2+len < 2^w := by simpa [buildConnectorRowWords,len,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hRoom
  obtain ⟨hu,hv,hSpan,hList⟩ := hRows i hi
  change mem cell = u at hu
  change mem (cell+1) = v at hv
  change addr+1+len ≤ lim at hSpan
  change SeqAt mem addr (wk i) at hList
  have hOne : 1 < 2^w := by omega
  have hTwo : 2 < 2^w := by omega
  have hCell : cell < 2^w := by dsimp [cell,endpoints]; omega
  have hCell1 : cell+1 < 2^w := by dsimp [cell,endpoints]; omega
  have hCtx1 : ctx+1 < 2^w := by omega
  have hDirI : dir+i < 2^w := by dsimp [dir]; omega
  have hI : i+i < 2^w := by omega
  have hAddr : addr+1 < 2^w := by omega
  have hDst1 : dst+1 < 2^w := by omega
  have hDst2 : dst+2 < 2^w := by omega
  refine runs_start_le ?_
  unfold buildConnectorRowProc
  refine runs_seq_assign_le (v := cell) ?_ ?_
  · have hh : endpoints+(i+i) < 2^w := by dsimp [cell] at hCell; omega
    simp [startState,Expr.eval,hI,hh,cell,endpoints,Nat.two_mul]
  refine runs_seq_assign_le (v := addr) ?_ ?_
  · simp [startState,Expr.eval,Function.update,hOne,hCtx1,hDirI,dir,addr]
  refine runs_seq_assign_le (v := len) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hList.1) ?_
  refine runs_seq_store_le (x := dst) (v := u) (Expr.eval_reg_of_eq (by simp [startState])) ?_ ?_
  · exact Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hu
  refine runs_seq_store_le (x := dst+1) (v := v) ?_ ?_ ?_
  · exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const hOne) hDst1
  · have hNo : cell+1 ≠ dst := by dsimp [cell,endpoints]; omega
    exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const hOne) hCell1)
      ((Function.update_of_ne hNo ..).trans hv)
  let mid := Function.update (Function.update mem dst u) (dst+1) v
  refine runs_seq_call_le (buildCopyProc_meetsContract hc) (vs := [addr+1,len,dst+2]) ?_ ?_
    ⟨addr+1,len,dst+2,rfl,by omega,hEnd,hOne⟩ ?_
  · simp [evalArgs,Expr.eval,Function.update,startState,hOne,hTwo,hAddr,hDst2]
  · wram_words
  intro _ after pos₂ hPost
  obtain ⟨_,_,_,he,hCopy,hFrame⟩ := hPost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl⟩ := he
  have hC : ∀ j < len, after (dst+2+j) = mid (addr+1+j) := hCopy
  have hFr : ∀ j, j < dst+2 ∨ dst+2+len ≤ j → after j = mid j := hFrame
  have hKeepMid (j : ℕ) (h0 : j ≠ dst) (h1 : j ≠ dst+1) : mid j = mem j := by
    simp only [mid,Function.update_of_ne h0,Function.update_of_ne h1]
  refine runs_ret_le (v := dst+2+len) ?_ ?_ ?_
  · exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const hTwo) hDst2)
      (Expr.eval_reg_of_eq (by simp)) hEnd
  · refine ⟨dst,rfl,by change dst+2+len = _; simp [buildConnectorRowWords,len]; omega,?_,?_,?_⟩
    · change ListAt after dst ([u,v]++wk i)
      apply listAt_append.mpr
      constructor
      · intro j hj
        have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
        rcases hj' with rfl|rfl
        · change after dst = u
          rw [hFr _ (Or.inl (by omega))]
          simp [mid]
        · change after (dst+1) = v
          rw [hFr _ (Or.inl (by omega))]
          simp [mid]
      · intro j hj
        change j < len at hj
        change after (dst+2+j) = (wk i)[j]
        exact (hC j hj).trans ((hKeepMid _ (by omega) (by omega)).trans (hList.2 j hj))
    · intro j hj
      change dst+2+len ≤ j at hj
      exact (hFr j (Or.inr hj)).trans ((hKeepMid j (by omega) (by omega)).trans (hZero j (by omega)))
    · intro j hj
      exact (hFr j (Or.inl (by omega))).trans (hKeepMid j (by omega) (by omega))
  · simp [initCSRWriteRowContract,buildCopyContract,Expr.size,argsSize,len]
    omega

/-- The generic CSR loop packs the endpoints and shortcut of each matching
edge in order, writing the connector section in linear time. -/
theorem buildConnectorGather_meetsContract {w f fRow fCopy ctx n lim : ℕ} {p : Program}
    {source : ℕ → ℕ × ℕ} {wk : ℕ → List ℕ}
    (hf : p.procs[f]? = some (initCSRWrite fRow))
    (hr : p.procs[fRow]? = some (buildConnectorRowProc fCopy))
    (hc : p.procs[fCopy]? = some buildCopyProc) :
    MeetsContract w p f (initCSRWriteContract w ctx n (buildConnectorRowWords source wk)
      (fun i => 17*(wk i).length+100)
      (fun dst mem => lim ≤ dst ∧ ConnectorRowsAt ctx n source wk lim mem) 0) := by
  apply initCSRWrite_meetsContract hf
  · intro i hi args mem pos ω hWords hPre
    obtain ⟨addr,rfl,⟨dst,⟨hLim,hAt⟩,hLo,hRoom⟩,hZ⟩ := hPre
    exact buildConnectorRowProc_meetsContract hr hc hi _ _ _ _ hWords
      ⟨addr,rfl,⟨lim,hAt,by omega,by simpa using hRoom⟩,hZ⟩
  · intro dst mem after hp hFrame
    exact ⟨hp.1,hp.2.frame fun a ha => hFrame a (ha.trans_le hp.1)⟩

end MinCostFlow.HierPaths
