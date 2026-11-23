module

public import MinCostFlow.SparseCore.Program.ReadUpdOne
public import MinCostFlow.SparseCore.Program.ReadLoopPot

import WordRAM.Tactic

/-!
# The walk over the input batch

`walkStmt` (`[r, batch, out]`) applies the entries of the input batch at `batch`, one by one, to
the data with handle `r` (`updOneStmt`). Afterwards the representation holds
`U.foldl walkView v`. The loop carries the potential `readPotMul · treePot` of the current data
(`runs_loop_pot`): an entry may cost more than its words pay, if the potential drops by the
excess. So the walk costs at most `readWalkMul · words · (L_w + 1)` plus the drop of the potential
(`walk_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## Facts on the batch -/

/-- The rest of a valid batch is valid on the graph after its first `k` updates. -/
theorem batchIsValid_drop : ∀ (k : ℕ) (G : MGraph) (U : List Update),
    G.BatchIsValid U → (G.applyBatch (U.take k)).BatchIsValid (U.drop k)
  | 0, _, _, h => by simpa [MGraph.applyBatch] using h
  | k + 1, G, [], h => by simpa [MGraph.applyBatch] using h
  | k + 1, G, u :: us, ⟨_, hus⟩ => by
    simpa [MGraph.applyBatch] using batchIsValid_drop k (G.applyUpdate u) us hus

/-- The data after the first `k` entries of the batch. -/
noncomputable def walkAt (v : ReadView) (U : List Update) (k : ℕ) : ReadView :=
  (U.take k).foldl walkView v

theorem walkAt_succ (v : ReadView) (U : List Update) {k : ℕ} (hk : k < U.length) :
    walkAt v U (k + 1) = walkView (walkAt v U k) U[k] := by
  simp only [walkAt, List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The walk never adds edges to the tree. -/
theorem walkView_T_E_subset (U : List Update) (v : ReadView) :
    (U.foldl walkView v).lsf.T.E ⊆ v.lsf.T.E := by
  induction U generalizing v with
  | nil => exact Finset.Subset.rfl
  | cons u U ih => exact (ih (walkView v u)).trans (tViewUpdate_E_subset _ _)

/-- An entry has at least two words. -/
theorem UpdateAt.two_le {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (h : UpdateAt mem a G u len) : 2 ≤ len := by
  cases u with
  | insert e x z => have := h.1; omega
  | delete e => have := h.1; omega
  | split v v' St Sh =>
    rcases h with ⟨_, _, _, _, _, _, hl, _⟩ | ⟨_, _, _, _, _, _, hl, _⟩ <;> omega

/-- One entry of `len` words raises the potential by at most `len`. -/
theorem walkView_pot_le {mem : ℕ → ℕ} {a len : ℕ} {v : ReadView} {u : Update}
    (hag : TreeAgree v.G v.lsf.T) (hu : v.G.UpdateIsValid u)
    (hins : ∀ e x z, u = .insert e x z → e ∉ v.lsf.T.E) (hU : UpdateAt mem a v.G u len) :
    treePot (walkView v u).G (walkView v u).lsf.T ≤ treePot v.G v.lsf.T + len := by
  cases u with
  | insert e x z => rw [walkView_pot_insert (hins e x z rfl)]; omega
  | delete e => have := walkView_pot_delete (v := v) hu; have := hU.1; omega
  | split v1 v2 St Sh =>
    have := walkView_pot_split hag hu hU
    show treePot (v.G.applyUpdate _) (tViewUpdate _ _) ≤ _
    omega

/-! ## The procedure -/

/-- `[r, batch, out]`: apply the entries of the batch at `batch` with `updOneStmt` at `fUpd`.
Registers: `3` the number of entries, `4` the index, `5` the address of the next entry. -/
def walkStmt (fUpd : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .assign 4 (.const 0) ;;
  .assign 5 (.bin .add (.reg 1) (.const 1)) ;;
  .loop (.bin .lt (.reg 4) (.reg 3))
    (.call 6 fUpd [.reg 0, .reg 5, .reg 2] ;;
     .assign 5 (.bin .add (.reg 5) (.reg 6)) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  .ret (.const 0)

theorem walkStmt_noRand (fUpd : ℕ) : (walkStmt fUpd).NoRand := by
  simp [walkStmt, Stmt.NoRand]

/-- The cost factor of the walk, per word and limb. -/
def readWalkMul : ℕ := 5100

/-- Contract of `walkStmt` for the data `v` held as `y` and the batch `U` of `words` words. The
batch lies outside the data and below the scratch `out`, which lies above the data. -/
noncomputable def walkContract (w vCap eCap tCap L_w P : ℕ) (v : ReadView) (y : ReadConc)
    (U : List Update) (words : ℕ) : Contract where
  pre args mem := ∃ r batch out, args = [r, batch, out] ∧ 16 ≤ 2 ^ w ∧ 1 ≤ L_w ∧ eCap ≤ tCap ∧
    ReadRepAt vCap eCap tCap L_w P r v y mem ∧
    (∀ x, readFoot vCap eCap tCap L_w r y x → x < out) ∧
    BatchAt mem batch v.G U words ∧
    (∀ i < words, mem (batch + i) < 2 ^ w ∧ ¬ readFoot vCap eCap tCap L_w r y (batch + i)) ∧
    batch + words ≤ out ∧ out + words + 2 * tCap < 2 ^ w ∧
    v.G.BatchIsValid U ∧ BatchWithinCaps vCap eCap U ∧
    (∀ k (hk : k < U.length), ∀ e x z, U[k] = .insert e x z →
      e ∉ ((U.take k).foldl tViewUpdate v.lsf.T).E)
  post args mem ret mem' := ∃ r batch out, args = [r, batch, out] ∧ ret = 0 ∧
    ReadRepAt vCap eCap tCap L_w P r (U.foldl walkView v) { y with view := U.foldl walkView v }
      mem' ∧
    (∀ x, ¬ readFoot vCap eCap tCap L_w r y x → (x < out ∨ out + words + 2 * tCap ≤ x) →
      mem' x = mem x) ∧
    treePot (U.foldl walkView v).G (U.foldl walkView v).lsf.T ≤ treePot v.G v.lsf.T + words
  cost _ _ := readWalkMul * (words * (L_w + 1)) + readPotMul * treePot v.G v.lsf.T -
    readPotMul * treePot (U.foldl walkView v).G (U.foldl walkView v).lsf.T

/-- `walkStmt` meets `walkContract`. -/
theorem walk_meetsContract {w : ℕ} {p : Program} {f fUpd vCap eCap tCap L_w P : ℕ}
    {v : ReadView} {y : ReadConc} {U : List Update} {words : ℕ}
    (hp : p.procs[f]? = some (walkStmt fUpd))
    (hUpd : ∀ (v : ReadView) (y : ReadConc) (u : Update) (len : ℕ),
      MeetsContract w p fUpd (updOneContract w vCap eCap tCap L_w P v y u len)) :
    MeetsContract w p f (walkContract w vCap eCap tCap L_w P v y U words) := by
  refine meetsContract_of_runs hp ?_
  rintro args mem pos ω hargs ⟨r, batch, out, rfl, hw16, hLw, heT, hrep, hfoot, hB, hBw, hb1,
    hout, hval, hcaps, hins⟩
  have hrw : r < 2 ^ w := hargs _ (by simp)
  obtain ⟨hw1, hlen0, hbody⟩ := hB
  have h2len := BatchBodyAt.two_mul_length_le hbody
  have hyv : ({ y with view := v } : ReadConc) = y := by
    obtain ⟨hv, -⟩ := hrep
    cases y
    cases hv
    rfl
  -- the loop
  let Inv : State → Prop := fun st => ∃ idx rw', idx ≤ U.length ∧ rw' ≤ words - 1 ∧
    st.regs 0 = r ∧ st.regs 2 = out ∧ st.regs 3 = U.length ∧ st.regs 4 = idx ∧
    st.regs 5 + rw' = batch + words ∧
    BatchBodyAt st.mem (st.regs 5) (walkAt v U idx).G (U.drop idx) rw' ∧
    (∀ i < words, st.mem (batch + i) = mem (batch + i)) ∧
    ReadRepAt vCap eCap tCap L_w P r (walkAt v U idx) { y with view := walkAt v U idx } st.mem ∧
    (∀ x, ¬ readFoot vCap eCap tCap L_w r y x → (x < out ∨ out + words + 2 * tCap ≤ x) →
      st.mem x = mem x) ∧
    treePot (walkAt v U idx).G (walkAt v U idx).lsf.T + (batch + 1) ≤
      treePot v.G v.lsf.T + st.regs 5
  let Q : State → Prop := fun st => st.regs 4 = U.length ∧
    ReadRepAt vCap eCap tCap L_w P r (U.foldl walkView v) { y with view := U.foldl walkView v }
      st.mem ∧
    (∀ x, ¬ readFoot vCap eCap tCap L_w r y x → (x < out ∨ out + words + 2 * tCap ≤ x) →
      st.mem x = mem x) ∧
    treePot (U.foldl walkView v).G (U.foldl walkView v).lsf.T ≤ treePot v.G v.lsf.T + words
  let rem : State → ℕ := fun st => readWalkMul * ((batch + words - st.regs 5) * (L_w + 1)) + 20
  let pot : State → ℕ := fun st =>
    readPotMul * treePot (walkAt v U (st.regs 4)).G (walkAt v U (st.regs 4)).lsf.T
  have hloop := runs_loop_pot (w := w) (p := p) (ω := ω) (e := .bin .lt (.reg 4) (.reg 3))
    (body := .call 6 fUpd [.reg 0, .reg 5, .reg 2] ;;
      .assign 5 (.bin .add (.reg 5) (.reg 6)) ;; .assign 4 (.bin .add (.reg 4) (.const 1)))
    (Inv := Inv) (Q := Q) (m := fun st => U.length - st.regs 4) (rem := rem) (pot := pot)
    (condVal := fun st => if st.regs 4 < st.regs 3 then 1 else 0)
    (fun st _ => by eval_expr)
    (fun st hInv hv => by
      obtain ⟨idx, rw', hidx, -, -, -, hr3, hr4, hr5, -, -, hrepI, hfrI, hpI⟩ := hInv
      have hidx' : idx = U.length := by
        rw [hr3, hr4] at hv
        by_contra hc
        simp [show idx < U.length by omega] at hv
      subst hidx'
      have hfin : walkAt v U U.length = U.foldl walkView v := by simp [walkAt]
      refine ⟨⟨hr4, hfin ▸ hrepI, hfrI, by rw [← hfin]; omega⟩, ?_⟩
      simp only [Expr.size, rem]
      omega)
    (fun st hInv hv => by
      obtain ⟨idx, rw', hidx, hrw', hr0, hr2, hr3, hr4, hr5, hbodyI, hmemI, hrepI, hfrI, hpI⟩ :=
        hInv
      have hlt : idx < U.length := by
        rw [hr3, hr4] at hv
        by_contra hc
        simp [hc] at hv
      have hdrop : U.drop idx = U[idx] :: U.drop (idx + 1) :=
        (List.cons_getElem_drop_succ (h := hlt)).symm
      rw [hdrop] at hbodyI
      obtain ⟨len, hlen, hUi, hrest⟩ := hbodyI
      have hlen2 := UpdateAt.two_le hUi
      have hGi : (walkAt v U idx).G = v.G.applyBatch (U.take idx) := (walkView_fold _ _).1
      have hvalid : (walkAt v U idx).G.UpdateIsValid U[idx] := by
        have := batchIsValid_drop idx v.G U hval
        rw [hdrop] at this
        rw [hGi]; exact this.1
      have hcapI : UpdateWithinCaps vCap eCap U[idx] := hcaps _ (List.getElem_mem hlt)
      have hinsI : ∀ e x z, U[idx] = .insert e x z → e ∉ (walkAt v U idx).lsf.T.E :=
        fun e x z h => by
          rw [walkAt, (walkView_fold (U.take idx) v).2.1]
          exact hins idx hlt e x z h
      have hagI : TreeAgree (walkAt v U idx).G (walkAt v U idx).lsf.T :=
        hrepI.2.2.1.treeAgree hrepI.2.2.2.1.gGraph.1 hrepI.2.2.2.1.2.2.2.2.2.2.2.2.2.1.1
      have hpotI := walkView_pot_le hagI hvalid hinsI hUi
      have hcur : batch + 1 ≤ st.regs 5 := by omega
      have hwordsI : ∀ i < len, st.mem (st.regs 5 + i) < 2 ^ w ∧
          ¬ readFoot vCap eCap tCap L_w r y (st.regs 5 + i) := fun i hi => by
        have hi' : st.regs 5 - batch + i < words := by omega
        have := hBw _ hi'
        rw [show batch + (st.regs 5 - batch + i) = st.regs 5 + i by omega] at this
        have hm := hmemI _ hi'
        rw [show batch + (st.regs 5 - batch + i) = st.regs 5 + i by omega] at hm
        exact ⟨hm ▸ this.1, this.2⟩
      have hLL : len ≤ len * (L_w + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have hsplit : rw' * (L_w + 1) = (rw' - len) * (L_w + 1) + len * (L_w + 1) := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hlen]
      have hrw'w : batch + words < 2 ^ w := by omega
      -- the body
      obtain ⟨o, st', c, hrun, ⟨rfl, hInv', hm', hpot'⟩, hc⟩ :
          ∃ o st' c, Runs w p ω (.call 6 fUpd [.reg 0, .reg 5, .reg 2] ;;
            .assign 5 (.bin .add (.reg 5) (.reg 6)) ;; .assign 4 (.bin .add (.reg 4) (.const 1)))
            st o st' c ∧
          (o = .normal ∧ Inv st' ∧ U.length - st'.regs 4 < U.length - st.regs 4 ∧
            rem st' + pot st' = readWalkMul * ((rw' - len) * (L_w + 1)) + 20 +
              readPotMul * treePot (walkAt v U (idx + 1)).G (walkAt v U (idx + 1)).lsf.T) ∧
          0 + c ≤ 20 + (readUpdMul * (len * (L_w + 1)) +
            readPotMul * treePot (walkAt v U idx).G (walkAt v U idx).lsf.T -
            readPotMul * treePot (walkAt v U (idx + 1)).G (walkAt v U (idx + 1)).lsf.T) := by
        refine runs_seq_call_le (hUpd (walkAt v U idx) { y with view := walkAt v U idx } U[idx] len)
          (vs := [r, st.regs 5, out]) (by eval_expr) (by wram_words)
          ⟨r, st.regs 5, out, rfl, hw16, hLw, heT, hrepI, hfoot, hUi, hwordsI, by omega,
            by omega, hvalid, hcapI, hinsI⟩ ?_
        rintro r1 mem1 pos1 ⟨_, _, _, hEq1, hr1, hrep1, hfr1⟩
        simp only [List.cons.injEq, and_true] at hEq1
        obtain ⟨rfl, rfl, rfl⟩ := hEq1
        replace hfr1 : ∀ x, ¬ readFoot vCap eCap tCap L_w r y x →
            (x < out ∨ out + len + 2 * tCap ≤ x) → mem1 x = st.mem x := hfr1
        have hbatch1 : ∀ i < words, mem1 (batch + i) = mem (batch + i) := fun i hi =>
          (hfr1 _ (hBw i hi).2 (Or.inl (by omega))).trans (hmemI i hi)
        refine runs_seq_assign_le (v := st.regs 5 + len) (by eval_expr) ?_
        refine runs_assign_le (v := idx + 1) (by eval_expr) ⟨rfl, ⟨idx + 1, rw' - len, hlt, by omega,
          ?_, ?_, ?_, ?_, ?_, ?_, hbatch1, ?_, ?_, ?_⟩, ?_, ?_⟩ ?_
        · simp [hr0]
        · simp [hr2]
        · simp [hr3]
        · simp
        · simp; omega
        · simp only [Function.update_self, ne_eq, not_false_eq_true,
            Function.update_of_ne, Nat.reduceEqDiff]
          rw [walkAt_succ v U hlt]
          refine hrest.of_agree fun i hi => ?_
          have hi' : st.regs 5 - batch + len + i < words := by omega
          have h1 := hfr1 _ (hBw _ hi').2 (Or.inl (by omega))
          rw [show batch + (st.regs 5 - batch + len + i) = st.regs 5 + len + i by omega] at h1
          exact h1
        · rw [walkAt_succ v U hlt]; exact hrep1
        · intro x hx hs
          exact (hfr1 x hx (by omega)).trans (hfrI x hx hs)
        · dsimp only
          rw [walkAt_succ v U hlt]
          have h5 : Function.update (Function.update (Function.update st.regs 6 r1) 5
              (st.regs 5 + len)) 4 (idx + 1) 5 = st.regs 5 + len := by simp
          rw [h5]
          omega
        · simp; omega
        · simp only [rem, pot, Function.update_self, ne_eq, Function.update_of_ne,
            Nat.reduceEqDiff, not_false_eq_true]
          rw [show batch + words - (st.regs 5 + len) = rw' - len by omega]
        · simp only [updOneContract, argsSize, Expr.size, walkAt_succ v U hlt]
          omega
      refine ⟨st', c, hrun, hInv', hm', ?_⟩
      have hmono : readPotMul * treePot (walkAt v U (idx + 1)).G (walkAt v U (idx + 1)).lsf.T ≤
          readUpdMul * (len * (L_w + 1)) +
            readPotMul * treePot (walkAt v U idx).G (walkAt v U idx).lsf.T := by
        rw [walkAt_succ v U hlt]
        simp only [readPotMul, readUpdMul]
        omega
      have hremst : rem st + pot st = readWalkMul * (rw' * (L_w + 1)) + 20 +
          readPotMul * treePot (walkAt v U idx).G (walkAt v U idx).lsf.T := by
        simp only [rem, pot, hr4]
        rw [show batch + words - st.regs 5 = rw' by omega]
      rw [hremst, hsplit]
      simp only [Expr.size, readWalkMul, readUpdMul] at hc hpot' hmono ⊢
      omega)
  -- the code before and after the loop
  apply runs_start_le
  refine runs_seq_assign_le (v := U.length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := batch + 1) (by eval_expr) ?_
  refine runs_seq_loop_pot_le hloop ⟨0, words - 1, Nat.zero_le _, le_refl _, ?_, ?_, ?_, ?_,
    ?_, ?_, fun _ _ => rfl, ?_, fun _ _ _ => rfl, ?_⟩ ?_
  · simp [startState]
  · simp [startState]
  · simp
  · simp
  · simp; omega
  · simpa [walkAt, startState] using hbody
  · simpa [walkAt, startState, hyv] using hrep
  · simp [walkAt]
  · rintro st₁ c₁ ⟨hr4, hrepF, hfrF, hpF⟩ hc₁
    refine runs_ret_le (v := 0) (by eval_expr) ⟨r, batch, out, rfl, rfl, hrepF, hfrF, hpF⟩ ?_
    have hW : words * (L_w + 1) = (words - 1) * (L_w + 1) + (L_w + 1) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hw1]
    simp only [rem, pot, hr4, Function.update_self, ne_eq, Function.update_of_ne,
      Nat.reduceEqDiff, not_false_eq_true, walkAt, List.take_zero, List.foldl_nil,
      List.take_length] at hc₁
    simp only [walkContract, Expr.size, readWalkMul] at hc₁ ⊢
    rw [show batch + words - (batch + 1) = words - 1 by omega] at hc₁
    rw [hW]
    omega

end MinCostFlow.SparseCore.Program.Read
