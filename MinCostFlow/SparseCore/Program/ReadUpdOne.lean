module

public import MinCostFlow.SparseCore.Program.ReadUpdAux
public import MinCostFlow.SparseCore.Program.ReadWalkView
public import MinCostFlow.SparseCore.Program.ReadSplitT
public import MinCostFlow.SparseCore.Program.ReadDelFrz

import WordRAM.Tactic

/-!
# The update of the data for one entry of the input batch

`updOneStmt` (`[r, a, out]`) applies the update `u` encoded at `a` to the data with handle `r`, so
that the representation holds `walkView v u` afterwards. It loads the pointers of the blocks from
the record and does the following.

* It applies `u` to the copy of `G`, and, restricted, to the forest `F` and to the live part
  (`dgApplyUpdate`). The live part follows the restricted update (`liveT_step`).
* An insertion gives the new edge the pair `(1, 1)` (`lsfSetWstrOneProc`).
* A deletion of a tree edge moves the edge to the frozen part (`delFrzStmt`).
* A split splits the tree (`splitTStmt`) and adds the new vertex to the frozen part.

It returns the number `len` of words of the entry. It writes only in the blocks of the data and in
the scratch `[out, out + len + 2 tCap)`. Its cost plus `readPotMul` times the new potential is at
most `readUpdMul · len · (L_w + 1)` plus `readPotMul` times the old potential
(`updOne_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.LSF.Program

/-- `[r, a, out]`: apply the entry at `a` of the input batch to the data with handle `r`.
Registers: `3` the tag, `4` to `8` the blocks of `T`, `F`, `G`, the live and the frozen part,
`9` the length of the entry. -/
def updOneStmt (L : ReadLib) (fSplitT fDelFrz : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .call 9 (L.batch + dgIdxApplyUpdate) [.reg 6, .reg 1, .const 1] ;;
  .call 10 (L.batch + dgIdxApplyUpdate) [.reg 5, .reg 1, .const 0] ;;
  .call 10 (L.batch + dgIdxApplyUpdate) [.reg 7, .reg 1, .const 0] ;;
  .cond (.bin .eq (.reg 3) (.const 0))
    (.call 10 L.setOne [.load (.bin .add (.reg 0) (.const 7)),
      .load (.bin .add (.reg 0) (.const 8)), .load (.bin .add (.reg 1) (.const 1)),
      .load (.bin .add (.reg 0) (.const 4))])
    (.cond (.bin .eq (.reg 3) (.const 1))
      (.call 10 fDelFrz [.reg 4, .reg 8, .load (.bin .add (.reg 1) (.const 1))])
      (.call 10 fSplitT [.reg 4, .reg 7, .reg 8, .reg 1, .reg 2] ;;
       .call 10 (L.ops + dgIdxAddVertex) [.reg 8, .load (.bin .add (.reg 1) (.const 2))])) ;;
  .ret (.reg 9)

theorem updOneStmt_noRand (L : ReadLib) (fSplitT fDelFrz : ℕ) :
    (updOneStmt L fSplitT fDelFrz).NoRand := by
  simp [updOneStmt, Stmt.NoRand]

/-- The cost factor of one entry of the batch, per word and limb. -/
def readUpdMul : ℕ := 5000

/-- Contract of `updOneStmt` for the data `v` held as `y`, and the entry `u` of `len` words. The
entry lies outside the data and below the scratch `out`, which lies above the data. -/
noncomputable def updOneContract (w vCap eCap tCap L_w P : ℕ) (v : ReadView) (y : ReadConc) (u : Update)
    (len : ℕ) : Contract where
  pre args mem := ∃ r a out, args = [r, a, out] ∧ 16 ≤ 2 ^ w ∧ 1 ≤ L_w ∧ eCap ≤ tCap ∧
    ReadRepAt vCap eCap tCap L_w P r v y mem ∧
    (∀ x, readFoot vCap eCap tCap L_w r y x → x < out) ∧
    UpdateAt mem a v.G u len ∧
    (∀ i < len, mem (a + i) < 2 ^ w ∧ ¬ readFoot vCap eCap tCap L_w r y (a + i)) ∧
    a + len ≤ out ∧ out + len + 2 * tCap < 2 ^ w ∧
    v.G.UpdateIsValid u ∧ UpdateWithinCaps vCap eCap u ∧
    (∀ e x z, u = .insert e x z → e ∉ v.lsf.T.E)
  post args mem ret mem' := ∃ r a out, args = [r, a, out] ∧ ret = len ∧
    ReadRepAt vCap eCap tCap L_w P r (walkView v u) { y with view := walkView v u } mem' ∧
    ∀ x, ¬ readFoot vCap eCap tCap L_w r y x → (x < out ∨ out + len + 2 * tCap ≤ x) →
      mem' x = mem x
  cost _ _ := readUpdMul * (len * (L_w + 1)) + readPotMul * treePot v.G v.lsf.T -
    readPotMul * treePot (walkView v u).G (walkView v u).lsf.T

/-- `updOneStmt` meets `updOneContract`. -/
theorem updOne_meetsContract {w : ℕ} {p : Program} {L : ReadLib}
    {f fSplitT fMove fKeep fDelFrz vCap eCap tCap L_w P : ℕ} {v : ReadView} {y : ReadConc}
    {u : Update} {len : ℕ} (hL : L.Has p)
    (hp : p.procs[f]? = some (updOneStmt L fSplitT fDelFrz))
    (hpS : p.procs[fSplitT]? = some (splitTStmt L fMove fKeep))
    (hpM : p.procs[fMove]? = some (splitMoveStmt L))
    (hpK : p.procs[fKeep]? = some (splitKeepStmt L))
    (hpD : p.procs[fDelFrz]? = some (delFrzStmt L)) :
    MeetsContract w p f (updOneContract w vCap eCap tCap L_w P v y u len) := by
  refine meetsContract_of_runs hp ?_
  rintro args mem pos ω hargs ⟨r, a, out, rfl, hw16, hLw, heT, hrep, hfoot, hU, hUw, ha1, hout,
    hu, hcap, hins⟩
  have hrep0 := hrep
  obtain ⟨-, hlay, hk, hrec, h9, h10, hlive, hfrz⟩ := hrep
  obtain ⟨h0, h1, -, -, h4, -, h6, h7, h8, hT, hF, -, hSV, hSP, -, hG⟩ := hrec
  have hlay' := hlay
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := hlay'
  simp only [readFullWords] at l1
  set Dt := dynGraphSize vCap tCap with hDt
  set De := dynGraphSize vCap eCap with hDe
  have hDt4 : 4 ≤ Dt := by rw [hDt]; simp only [dynGraphSize]; omega
  have hDe4 : 4 ≤ De := by rw [hDe]; simp only [dynGraphSize]; omega
  have hvDt : vCap < Dt := by rw [hDt]; simp only [dynGraphSize]; omega
  have hend : y.frz + Dt ≤ out := by
    have := hfoot (y.frz + Dt - 1) (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    omega
  have haw : a < 2 ^ w := hargs _ (by simp)
  have hrw : r + 11 < 2 ^ w := by omega
  have hag : TreeAgree v.G v.lsf.T := hk.treeAgree hG.1 hT.1
  obtain ⟨hag', hk'⟩ := walkView_agree hag hk hu hins
  have hUd : ∀ i < len, outBlocks vCap eCap tCap L_w y (a + i) :=
    fun i hi => outBlocks_of_notFoot (hUw i hi).2
  have hLL : len ≤ len * (L_w + 1) := Nat.le_mul_of_pos_right _ (by omega)
  apply runs_start_le
  refine runs_seq_assign_le (v := mem a) (by eval_expr) ?_
  refine runs_seq_assign_le (v := y.q.t) (by eval_expr) ?_
  refine runs_seq_assign_le (v := y.q.f) (by eval_expr) ?_
  refine runs_seq_assign_le (v := y.q.g) (by eval_expr) ?_
  refine runs_seq_assign_le (v := y.live) (by eval_expr) ?_
  refine runs_seq_assign_le (v := y.frz) (by eval_expr) ?_
  -- `u` on the copy of `G`
  refine runs_seq_call_le (hL.applyUpdate vCap eCap v.G v.G u len) (vs := [y.q.g, a, 1])
    (by eval_expr) (by wram_words) ⟨y.q.g, a, 1, rfl, hw16, by omega, by omega,
      fun i hi => (hUd i hi).2.2.1, fun i hi => (hUw i hi).1, hU, hu, hcap, hG,
      Or.inl ⟨one_ne_zero, rfl⟩⟩ ?_
  rintro r1 mem1 pos1 ⟨_, _, _, hEq1, hr1, hG1, hfr1⟩
  simp only [List.cons.injEq, and_true] at hEq1
  obtain ⟨rfl, rfl, rfl⟩ := hEq1
  replace hfr1 : ∀ x, x < y.q.g ∨ y.q.g + De ≤ x → mem1 x = mem x := hfr1
  have hlen0 : dgUpdateMemLen mem a = len := dgUpdateMemLen_eq hU
  have hU1 : UpdateAt mem1 a v.G u len := hU.of_agree fun i hi => hfr1 _ (hUd i hi).2.2.1
  -- `u`, restricted, on the forest
  refine runs_seq_call_le (hL.applyUpdate vCap tCap v.G v.lsf.F.F u len) (vs := [y.q.f, a, 0])
    (by eval_expr) (by wram_words) ⟨y.q.f, a, 0, rfl, hw16, by omega, by omega,
      fun i hi => (hUd i hi).2.1, fun i hi => (hfr1 _ (hUd i hi).2.2.1).trans_lt (hUw i hi).1,
      hU1, hu, UpdateWithinCaps.mono hcap heT, hF.of_agree fun x _ hx => hfr1 x (Or.inl (by omega)),
      Or.inr ⟨rfl, hk.2.2.2, hk.2.2.1⟩⟩ ?_
  rintro r2 mem2 pos2 ⟨_, _, _, hEq2, -, hF2, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEq2
  obtain ⟨rfl, rfl, rfl⟩ := hEq2
  replace hfr2 : ∀ x, x < y.q.f ∨ y.q.f + Dt ≤ x → mem2 x = mem1 x := hfr2
  have hlen1 : dgUpdateMemLen mem1 a = len := dgUpdateMemLen_eq hU1
  have hU2 : UpdateAt mem2 a v.G u len := hU1.of_agree fun i hi => hfr2 _ (hUd i hi).2.1
  -- `u`, restricted, on the live part
  refine runs_seq_call_le (hL.applyUpdate vCap eCap v.G (liveT v.G v.lsf.T) u len)
    (vs := [y.live, a, 0]) (by eval_expr) (by wram_words) ⟨y.live, a, 0, rfl, hw16, by omega,
      by omega, fun i hi => (hUd i hi).2.2.2.2.2.1,
      fun i hi => ((hfr2 _ (hUd i hi).2.1).trans (hfr1 _ (hUd i hi).2.2.1)).trans_lt (hUw i hi).1,
      hU2, hu, hcap, hlive.of_agree fun x hx _ =>
        (hfr2 x (Or.inr (by omega))).trans (hfr1 x (Or.inr (by omega))),
      Or.inr ⟨rfl, (liveT_sub _ _).1, (liveT_sub _ _).2⟩⟩ ?_
  rintro r3 mem3 pos3 ⟨_, _, _, hEq3, -, hl3, hfr3'⟩
  simp only [List.cons.injEq, and_true] at hEq3
  obtain ⟨rfl, rfl, rfl⟩ := hEq3
  replace hfr3' : ∀ x, x < y.live ∨ y.live + De ≤ x → mem3 x = mem2 x := hfr3'
  have hlen2 : dgUpdateMemLen mem2 a = len := dgUpdateMemLen_eq hU2
  have hfr3 : ∀ x, (x < y.q.g ∨ y.q.g + De ≤ x) → (x < y.q.f ∨ y.q.f + Dt ≤ x) →
      (x < y.live ∨ y.live + De ≤ x) → mem3 x = mem x := fun x hg hf hl => by
    rw [hfr3' x hl, hfr2 x hf, hfr1 x hg]
  have hfr3o : ∀ x, outBlocks vCap eCap tCap L_w y x → mem3 x = mem x := fun x hx =>
    hfr3 x hx.2.2.1 hx.2.1 hx.2.2.2.2.2.1
  have hU3 : UpdateAt mem3 a v.G u len := hU.of_agree fun i hi => hfr3o _ (hUd i hi)
  have hG3 : DynGraphAt mem3 y.q.g vCap eCap (v.G.applyUpdate u) := by
    have : dgBatchTarget 1 v.G u = v.G.applyUpdate u := by simp [dgBatchTarget]
    rw [← this]
    exact hG1.of_agree fun x hx _ => by rw [hfr3' x (Or.inl (by omega)), hfr2 x (Or.inr (by omega))]
  have hF3 : DynGraphAt mem3 y.q.f vCap tCap (dgBatchTarget 0 v.lsf.F.F u) :=
    hF2.of_agree fun x _ hx => hfr3' x (Or.inl (by omega))
  have hl3' : DynGraphAt mem3 y.live vCap eCap
      (liveT (v.G.applyUpdate u) (tViewUpdate v.lsf.T u)) :=
    DynGraphAt.of_same hl3 (liveT_step hins)
  have hT3 : DynGraphAt mem3 y.q.t vCap tCap v.lsf.T :=
    hT.of_agree fun x _ hx => hfr3 x (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have hfrz3 : DynGraphAt mem3 y.frz vCap tCap (frozenT v.G v.lsf.T) :=
    hfrz.of_agree fun x hx _ => hfr3 x (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hrecw : ∀ i < 11, outBlocks vCap eCap tCap L_w y (r + i) := fun i hi =>
    ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
      Or.inl (by omega), Or.inl (by omega)⟩
  have h7' : mem3 (r + 7) = y.q.num := (hfr3o _ (hrecw 7 (by norm_num))).trans h7
  have h8' : mem3 (r + 8) = y.q.den := (hfr3o _ (hrecw 8 (by norm_num))).trans h8
  have h4' : mem3 (r + 4) = L_w := (hfr3o _ (hrecw 4 (by norm_num))).trans h4
  have h78 : mem (r + 7 + 1) = y.q.den := h8
  cases u with
  | insert e x z =>
    obtain ⟨rfl, hAt⟩ := hU
    have hma : mem a = 0 := by simpa using hAt 0 (by simp)
    have hma1 : mem3 (a + 1) = e := by
      rw [hfr3o _ (hUd 1 (by norm_num))]; simpa using hAt 1 (by simp)
    have heT' : e ∉ v.lsf.T.E := hins e x z rfl
    have he : e < eCap := hcap
    have heL : e * L_w + L_w ≤ eCap * L_w := cell_in_table he
    have hE1 : (e + 1) * L_w = e * L_w + L_w := by ring
    refine runs_seq_cond_le (by eval_expr) (fun _ => ?_) (fun h => by simp at h)
    refine runs_seq_call_le hL.setOne (vs := [y.q.num, y.q.den, e, L_w]) (by eval_expr)
      (by wram_words) ⟨y.q.num, y.q.den, e, L_w, rfl, hw16, by norm_num, hLw, by omega,
        by rw [hE1]; omega, by rw [hE1]; omega, Or.inl (by rw [hE1]; omega)⟩ ?_
    rintro r4 mem4 pos4 ⟨_, _, _, _, hEq4, -, hVN, hVD, hIN, hID, hfr4⟩
    simp only [List.cons.injEq, and_true] at hEq4
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq4
    replace hfr4 : ∀ x, ¬ (y.q.num + e * L_w ≤ x ∧ x < y.q.num + (e + 1) * L_w) →
        ¬ (y.q.den + e * L_w ≤ x ∧ x < y.q.den + (e + 1) * L_w) → mem4 x = mem3 x := hfr4
    rw [hE1] at hfr4
    have hfin : ∀ x, (x < y.q.num ∨ y.q.den + eCap * L_w ≤ x) → mem4 x = mem3 x :=
      fun x hx => hfr4 x (by omega) (by omega)
    have hfo : ∀ x, outBlocks vCap eCap tCap L_w y x → mem4 x = mem x := fun x hx =>
      (hfr4 x (by have := hx.2.2.2.1; omega) (by have := hx.2.2.2.2.1; omega)).trans (hfr3o x hx)
    obtain ⟨hval', hpair'⟩ := stretch_step (E' := insert e v.G.E)
      (wstr' := Function.update v.lsf.wstr e 1) (num' := Function.update v.num e 1)
      (den' := Function.update v.den e 1) (mem' := mem4) hSV hSP
      (hfo _ (hrecw 7 (by norm_num))) (hfo _ (hrecw 8 (by norm_num))) (fun f hf => by
        rw [h7, h78]
        by_cases hfe : f = e
        · subst hfe
          exact Or.inr ⟨⟨hVN, hVD, hIN, hID⟩, by simp, by simp, by simp⟩
        · have hfG : f ∈ v.G.E := (Finset.mem_insert.mp hf).resolve_left hfe
          have hfL : f * L_w + L_w ≤ eCap * L_w := cell_in_table (hG.2.2.1 f hfG)
          refine Or.inl ⟨hfG, by simp [hfe], by simp [hfe], by simp [hfe], fun i hi => ?_⟩
          have hc := cell_kept hfe hi
          constructor
          · rw [hfr4 _ (by omega) (by omega)]
            exact hfr3 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
          · rw [hfr4 _ (by omega) (by omega)]
            exact hfr3 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))
    refine runs_ret_le (v := 4) (by eval_expr) ⟨r, a, out, rfl, rfl, ?_,
      fun x hx _ => hfo x (outBlocks_of_notFoot hx)⟩ ?_
    · refine ReadRepAt.change hrep0 hk' rfl rfl (fun x hx => hfo x (outBlocks_of_fixed hlay hx).2)
        (hT3.of_agree fun x _ hx => hfin x (Or.inl (by omega)))
        (hF3.of_agree fun x _ hx => hfin x (Or.inl (by omega)))
        (hG3.of_agree fun x _ hx => hfin x (Or.inl (by omega)))
        (hl3'.of_agree fun x hx _ => hfin x (Or.inr (by omega)))
        ((DynGraphAt.of_same hfrz3 (frozenT_step_insert heT')).of_agree
          fun x hx _ => hfin x (Or.inr (by omega))) hval' hpair'
    · simp only [updOneContract, dgApplyUpdateContract, lsfSetWstrOneContract, readUpdMul,
        readPotMul, startState, hlen0, hlen1, hlen2, walkView_pot_insert heT', argsSize, Expr.size,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
        List.getD_cons_succ, List.getD_cons_zero]
      omega
  | delete e =>
    obtain ⟨rfl, hAt⟩ := hU
    have hma : mem a = 1 := by simpa using hAt 0 (by simp)
    have hma1 : mem3 (a + 1) = e := by
      rw [hfr3o _ (hUd 1 (by norm_num))]; simpa using hAt 1 (by simp)
    have heG : e ∈ v.G.E := hu
    have he : e < eCap := hG.2.2.1 e heG
    refine runs_seq_cond_le (by eval_expr) (fun h => by simp at h) (fun _ => ?_)
    refine runs_seq_cond_le (by eval_expr) (fun _ => ?_) (fun h => by simp at h)
    refine runs_seq_call_le (delFrz_meetsContract (vCap := vCap) (tCap := tCap) (T := v.lsf.T)
      hL hpD) (vs := [y.q.t, y.frz, e]) (by eval_expr)
      (by wram_words) ⟨y.q.t, y.frz, e, rfl, hw16, by omega, hT3⟩ ?_
    rintro r4 mem4 pos4 ⟨_, _, _, hEq4, -, hT4, hfr4⟩
    simp only [List.cons.injEq, and_true] at hEq4
    obtain ⟨rfl, rfl, rfl⟩ := hEq4
    replace hfr4 : ∀ x, x < y.q.t ∨ y.q.t + Dt ≤ x → mem4 x = mem3 x := hfr4
    have hfz' : DynGraphAt mem4 y.frz vCap tCap
        (frozenT (v.G.applyUpdate (.delete e)) (tViewUpdate v.lsf.T (.delete e))) :=
      (DynGraphAt.of_same hfrz3 (frozenT_step_delete heG)).of_agree fun x hx _ =>
        hfr4 x (Or.inr (by omega))
    have hfo : ∀ x, outBlocks vCap eCap tCap L_w y x → mem4 x = mem x := fun x hx =>
      (hfr4 x hx.1).trans (hfr3o x hx)
    obtain ⟨hval', hpair'⟩ := stretch_step (E' := v.G.E.erase e) (wstr' := v.lsf.wstr)
      (num' := v.num) (den' := v.den) (mem' := mem4) hSV hSP
      (hfo _ (hrecw 7 (by norm_num))) (hfo _ (hrecw 8 (by norm_num))) (fun f hf => by
        rw [h7, h78]
        have hfG : f ∈ v.G.E := Finset.mem_of_mem_erase hf
        have hfL : f * L_w + L_w ≤ eCap * L_w := cell_in_table (hG.2.2.1 f hfG)
        refine Or.inl ⟨hfG, rfl, rfl, rfl, fun i hi => ⟨?_, ?_⟩⟩
        · rw [hfr4 _ (Or.inr (by omega))]
          exact hfr3 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
        · rw [hfr4 _ (Or.inr (by omega))]
          exact hfr3 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))
    refine runs_ret_le (v := 2) (by eval_expr) ⟨r, a, out, rfl, rfl, ?_,
      fun x hx _ => hfo x (outBlocks_of_notFoot hx)⟩ ?_
    · refine ReadRepAt.change hrep0 hk' rfl rfl (fun x hx => hfo x (outBlocks_of_fixed hlay hx).2)
        hT4
        (hF3.of_agree fun x hx _ => hfr4 x (Or.inr (by omega)))
        (hG3.of_agree fun x hx _ => hfr4 x (Or.inr (by omega)))
        (hl3'.of_agree fun x hx _ => hfr4 x (Or.inr (by omega))) hfz' hval' hpair'
    · have hpot := walkView_pot_delete (v := v) heG
      simp only [updOneContract, dgApplyUpdateContract, delFrzContract, readUpdMul,
        readPotMul, startState, hlen0, hlen1, hlen2, argsSize, Expr.size,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      omega
  | split v1 v2 St Sh =>
    have hU0 := hU
    have hhd : mem a ≠ 0 ∧ mem a ≠ 1 ∧ mem (a + 2) = v2 ∧ 5 ≤ len := by
      rcases hU with ⟨Lt, Lh, -, -, -, -, hlen, hAt⟩ | ⟨Lt, Lh, -, -, -, -, hlen, hAt⟩
      · have hHd := (listAt_append.mp (listAt_append.mp hAt).1).1
        have h0 : mem a = 2 := hHd 0 (by simp)
        have h2 : mem (a + 2) = v2 := hHd 2 (by simp)
        exact ⟨by omega, by omega, h2, by omega⟩
      · have hHd := (listAt_append.mp (listAt_append.mp hAt).1).1
        have h0 : mem a = 3 := hHd 0 (by simp)
        have h2 : mem (a + 2) = v2 := hHd 2 (by simp)
        exact ⟨by omega, by omega, h2, by omega⟩
    obtain ⟨hma0, hma1, hma2, hlen5⟩ := hhd
    have hma2' : mem3 (a + 2) = v2 := by rw [hfr3o _ (hUd 2 (by omega))]; exact hma2
    have hv2c : v2 < vCap := hcap
    refine runs_seq_cond_le (by eval_expr) (fun h => by simp [hma0] at h) (fun _ => ?_)
    refine runs_seq_cond_le (by eval_expr) (fun h => by simp [hma1] at h) (fun _ => ?_)
    refine WordRAM.runs_seq_assoc_le ?_
    refine runs_seq_call_le (splitT_meetsContract (vCap := vCap) (eCap := eCap) (tCap := tCap)
      (G := v.G) (T := v.lsf.T) (v := v1) (v' := v2) (St := St) (Sh := Sh) (len := len) hL hpS
      hpM hpK) (vs := [y.q.t, y.live, y.frz, a, out]) (by eval_expr) (by wram_words)
      ⟨y.q.t, y.live, y.frz, a, out, rfl, hw16, hU3,
        fun i hi => (hfr3o _ (hUd i hi)).trans_lt (hUw i hi).1, fun i hi => (hUd i hi).1, hag,
        hu, hv2c, heT, by omega, by omega, by omega, ha1, hout, hT3, hl3', hfrz3⟩ ?_
    rintro r4 mem4 pos4 ⟨_, _, _, _, _, hEq4, -, hT4, hfr4⟩
    simp only [List.cons.injEq, and_true] at hEq4
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hEq4
    replace hfr4 : ∀ x, (x < y.q.t ∨ y.q.t + Dt ≤ x) → (x < out ∨ out + len + 2 * tCap ≤ x) →
        mem4 x = mem3 x := hfr4
    have hma2'' : mem4 (a + 2) = v2 := by
      rw [hfr4 _ (hUd 2 (by omega)).1 (Or.inl (by omega))]; exact hma2'
    refine runs_seq_call_le (hL.addVertex vCap tCap (frozenT v.G v.lsf.T)) (vs := [y.frz, v2])
      (by eval_expr) (by wram_words) ⟨y.frz, v2, rfl, hw16, by omega, hv2c,
        hfrz3.of_agree fun x hx _ => hfr4 x (Or.inr (by omega)) (Or.inl (by omega))⟩ ?_
    rintro r5 mem5 pos5 ⟨_, _, hEq5, -, hfz5, hfr5⟩
    simp only [List.cons.injEq, and_true] at hEq5
    obtain ⟨rfl, rfl⟩ := hEq5
    replace hfr5 : ∀ x, x < y.frz ∨ y.frz + Dt ≤ x → mem5 x = mem4 x := hfr5
    have hbelow : ∀ x, y.q.t + Dt ≤ x → x < y.frz → mem5 x = mem3 x := fun x h1 h2 =>
      (hfr5 x (Or.inl h2)).trans (hfr4 x (Or.inr h1) (Or.inl (by omega)))
    have hfo : ∀ x, outBlocks vCap eCap tCap L_w y x → (x < out ∨ out + len + 2 * tCap ≤ x) →
        mem5 x = mem x := fun x hx hs =>
      ((hfr5 x hx.2.2.2.2.2.2).trans (hfr4 x hx.1 hs)).trans (hfr3o x hx)
    obtain ⟨hval', hpair'⟩ := stretch_step (E' := v.G.E) (wstr' := v.lsf.wstr)
      (num' := v.num) (den' := v.den) (mem' := mem5) hSV hSP
      (hfo _ (hrecw 7 (by norm_num)) (Or.inl (by omega)))
      (hfo _ (hrecw 8 (by norm_num)) (Or.inl (by omega))) (fun f hf => by
        rw [h7, h78]
        have hfL : f * L_w + L_w ≤ eCap * L_w := cell_in_table (hG.2.2.1 f hf)
        refine Or.inl ⟨hf, rfl, rfl, rfl, fun i hi => ⟨?_, ?_⟩⟩
        · rw [hbelow _ (by omega) (by omega)]
          exact hfr3 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
        · rw [hbelow _ (by omega) (by omega)]
          exact hfr3 _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))
    have hr1' : r1 = len := hr1
    refine runs_ret_le (v := len) (by eval_expr) ⟨r, a, out, rfl, rfl, ?_,
      fun x hx hs => hfo x (outBlocks_of_notFoot hx) hs⟩ ?_
    · refine ReadRepAt.change hrep0 hk' rfl rfl
        (fun x hx => hfo x (outBlocks_of_fixed hlay hx).2
          (Or.inl (hfoot x (outBlocks_of_fixed hlay hx).1)))
        (hT4.of_agree fun x _ hx => hfr5 x (Or.inl (by omega)))
        (hF3.of_agree fun x hx1 hx2 => hbelow x (by omega) (by omega))
        (hG3.of_agree fun x hx1 hx2 => hbelow x (by omega) (by omega))
        (hl3'.of_agree fun x hx1 hx2 => hbelow x (by omega) (by omega))
        (DynGraphAt.of_same hfz5 (frozenT_step_split hu)) hval' hpair'
    · have hpot := walkView_pot_split hag hu hU0
      have hwv : treePot (walkView v (.split v1 v2 St Sh)).G
          (walkView v (.split v1 v2 St Sh)).lsf.T =
          treePot (v.G.applyUpdate (.split v1 v2 St Sh)) (tViewUpdate v.lsf.T (.split v1 v2 St Sh)) :=
        rfl
      simp only [updOneContract, dgApplyUpdateContract, splitTContract, dgAddVertexContract,
        readUpdMul, readPotMul, startState, hlen0, hlen1, hlen2, hwv, argsSize, Expr.size,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      omega

end MinCostFlow.SparseCore.Program.Read
