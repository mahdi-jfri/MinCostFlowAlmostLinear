module

public import MinCostFlow.SparseCore.Program.ReadWalk

import WordRAM.Tactic

/-!
# The update of the readout data (operation `2` of a branch)

`readStepStmt` (`[r, batch, words, chg, us, usWords, h]`) is the update of `ReadBranchAt`.

* It walks over the input batch (`walkStmt`), with scratch at `h`. Then the representation holds
  `U.foldl walkView v`.
* It sets the root bits of the new roots of the change record (`setRootsStmt`), and deletes the
  forest edges of the record from `F` (`delEdgesStmt`).
* It applies the output batch `U_S` to `S` (`dgApplyBatch`).

The result is `v.step U c U_S`: `walkView_fold` gives the parts of the walk, and the last two
steps give the new `F`, roots and `S`. The procedure returns the end
`h + words + 2 tCap` of the scratch, and writes nothing above it. `readRep_step` proves the
update clause of `ReadBranchAt` for `readRep`, for every `mul ≥ readStepMul`. The seven
procedures of the update sit in one block (`readStepProcs`); `readStepProcs_step` and
`readStepProcs_walk` give the two facts on the program that `readRep_step` asks.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## The model -/

/-- The full update with allowed insertions applies the batch. -/
theorem foldl_dgBatchTarget_one (U : List Update) (H : MGraph) :
    U.foldl (dgBatchTarget 1) H = H.applyBatch U := by
  induction U generalizing H with
  | nil => rfl
  | cons u U ih =>
    simp only [List.foldl_cons, MGraph.applyBatch] at ih ⊢
    rw [ih]
    simp [dgBatchTarget]

/-! ## The representation after a rebuild of the blocks -/

/-- **The representation after new blocks.** If the eleven words of the record keep their
values, the new data `v'` meets `ReadKeep`, and each block holds its part of `v'`, the
representation holds `v'`. -/
theorem ReadRepAt.rebuild {vCap eCap tCap L_w P r : ℕ} {v v' : ReadView} {y : ReadConc}
    {mem mem' : ℕ → ℕ} (hrep : ReadRepAt vCap eCap tCap L_w P r v { y with view := v } mem)
    (hkeep : ReadKeep v')
    (hw : ∀ i < readFullWords, mem' (r + i) = mem (r + i))
    (hT : DynGraphAt mem' y.q.t vCap tCap v'.lsf.T)
    (hF : DynGraphAt mem' y.q.f vCap tCap v'.lsf.F.F)
    (hR : RootsAt mem' y.q.roots vCap v'.lsf.F.R)
    (hS : DynGraphAt mem' y.q.s vCap eCap v'.S)
    (hG : DynGraphAt mem' y.q.g vCap eCap v'.G)
    (hlive : DynGraphAt mem' y.live vCap eCap (liveT v'.G v'.lsf.T))
    (hfrz : DynGraphAt mem' y.frz vCap tCap (frozenT v'.G v'.lsf.T))
    (hval : StretchValuesAt mem' (r + 7) 4 L_w P v'.G.E v'.lsf.wstr)
    (hpairs : StretchPairsAt mem' (r + 7) L_w v'.G.E v'.num v'.den) :
    ReadRepAt vCap eCap tCap L_w P r v' { y with view := v' } mem' := by
  obtain ⟨-, hlay, -, hrec, h9, h10, -, -⟩ := hrep
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hrec
  refine ⟨rfl, hlay, hkeep, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT, hF, hR, hval, hpairs, hS, hG⟩,
    ?_, ?_, hlive, hfrz⟩
  · rw [show r = r + 0 from rfl, hw 0 (by decide)]; exact h0
  · rw [hw 1 (by decide)]; exact h1
  · rw [hw 2 (by decide)]; exact h2
  · rw [hw 3 (by decide)]; exact h3
  · rw [hw 4 (by decide)]; exact h4
  · rw [hw 5 (by decide)]; exact h5
  · rw [hw 6 (by decide)]; exact h6
  · rw [hw 7 (by decide)]; exact h7
  · rw [hw 8 (by decide)]; exact h8
  · rw [hw 9 (by decide)]; exact h9
  · rw [hw 10 (by decide)]; exact h10

/-! ## The procedure -/

/-- `[r, batch, words, chg, us, usWords, h]`: walk over the batch with `walkStmt` at `fWalk`,
apply the change record and the output batch, and return `h + words + 2 tCap` (`tCap` read from
the block of `T`). Register `8` holds the number of new roots. -/
def readStepStmt (L : ReadLib) (fWalk : ℕ) : Stmt :=
  .call 7 fWalk [.reg 0, .reg 1, .reg 6] ;;
  .assign 8 (.load (.reg 3)) ;;
  .call 9 (L.loops + readIdxSetRoots)
    [.load (.bin .add (.reg 0) (.const 2)), .bin .add (.reg 3) (.const 1), .reg 8] ;;
  .call 9 (L.loops + readIdxDelEdges)
    [.load (.bin .add (.reg 0) (.const 1)), .bin .add (.bin .add (.reg 3) (.const 2)) (.reg 8),
      .load (.bin .add (.bin .add (.reg 3) (.const 1)) (.reg 8))] ;;
  .call 9 (L.batch + dgIdxApplyBatch) [.load (.bin .add (.reg 0) (.const 5)), .reg 4, .const 1] ;;
  .ret (.bin .add (.bin .add (.reg 6) (.reg 2))
    (.bin .mul (.const 2) (.load (.bin .add (.load (.reg 0)) (.const 1)))))

theorem readStepStmt_noRand (L : ReadLib) (fWalk : ℕ) : (readStepStmt L fWalk).NoRand := by
  simp [readStepStmt, Stmt.NoRand]

/-- The cost factor of the update. -/
def readStepMul : ℕ := 5300

/-- **The update clause for `readRep`.** If `p` has `readStepStmt` at `f`, the walk at `fWalk`
and the procedures of `L`, and `readStepMul ≤ mul`, the update meets its clause of
`ReadBranchAt`. -/
theorem readRep_step {w vCap eCap tCap L_w P mul f fWalk : ℕ} {p : Program} {L : ReadLib}
    (hL : L.Has p) (hp : p.procs[f]? = some (readStepStmt L fWalk))
    (hWalk : ∀ (v : ReadView) (y : ReadConc) (U : List Update) (words : ℕ),
      MeetsContract w p fWalk (walkContract w vCap eCap tCap L_w P v y U words))
    (hmul : readStepMul ≤ mul) (hLw : 1 ≤ L_w) (hw16 : 16 ≤ 2 ^ w)
    (r batch words chg us usWords h : ℕ) (v : ReadView) (y : ReadConc) (U U_S : List Update)
    (c : LSFChange) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hargs : ∀ a ∈ [r, batch, words, chg, us, usWords, h], a < 2 ^ w)
    (hrep : (readRep vCap eCap tCap L_w P).rep r v y mem)
    (hfoot : ∀ a, (readRep vCap eCap tCap L_w P).foot r y a → a < h) (hz : ZeroFrom mem h)
    (hB : BatchAt mem batch v.G U words) (hval : v.G.BatchIsValid U)
    (hcaps : BatchWithinCaps vCap eCap U)
    (hBin : InputAt w mem ((readRep vCap eCap tCap L_w P).foot r y) batch words h)
    (hC : LSFChangeAt mem chg c)
    (hCin : InputAt w mem ((readRep vCap eCap tCap L_w P).foot r y) chg c.words h)
    (hBS : BatchAt mem us v.S U_S usWords) (hvalS : v.S.BatchIsValid U_S)
    (hcapsS : BatchWithinCaps vCap eCap U_S)
    (hBSin : InputAt w mem ((readRep vCap eCap tCap L_w P).foot r y) us usWords h)
    (hins : ∀ k (hk : k < U.length), ∀ e x z, U[k] = .insert e x z →
      e ∉ ((U.take k).foldl tViewUpdate v.lsf.T).E)
    (hInv : (v.step U c U_S).Inv vCap eCap tCap)
    (hroom : h + readSpace mul vCap tCap L_w (words + c.words + usWords) < 2 ^ w) :
    ReadCallEnds (readRep vCap eCap tCap L_w P) w p f [r, batch, words, chg, us, usWords, h] mem
      pos ω r y h (v.step U c U_S) (fun _ => True)
      (readSpace mul vCap tCap L_w (words + c.words + usWords))
      (mul * ((words + usWords + 1) * (L_w + 1) + c.size))
      ((readRep vCap eCap tCap L_w P).phi r y mem) := by
  simp only [readRep_rep] at hrep
  have hrep0 := hrep
  have hyv : y.view = v := hrep.1
  simp only [readRep_foot] at hfoot hBin hCin hBSin
  set W := U.foldl walkView v with hWdef
  obtain ⟨hWG, hWT, hWF, hWR, hWw, hWS, hWn, hWd⟩ := walkView_fold U v
  rw [← hWdef] at hWG hWT hWF hWR hWw hWS hWn hWd
  obtain ⟨-, hlay, -, hrec, -, -, -, -⟩ := hrep
  have hlay' := hlay
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := hlay'
  simp only [readFullWords] at l1
  have heT : eCap ≤ tCap := hInv.2.2.2.1
  have hrw : r < 2 ^ w := hargs _ (by simp)
  have hhw : h < 2 ^ w := hargs _ (by simp)
  have hmulX : ∀ X, 2 * X ≤ mul * X * (L_w + 1) := fun X => by
    have h1 : X ≤ X * (L_w + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : 2 * (X * (L_w + 1)) ≤ mul * (X * (L_w + 1)) :=
      Nat.mul_le_mul_right _ (by simp only [readStepMul] at hmul; omega)
    rw [Nat.mul_assoc]; omega
  have hsp := hmulX (vCap + tCap + (words + c.words + usWords) + 1)
  simp only [readSpace] at hroom
  have hDt : dynGraphSize vCap tCap = 4 + 7 * vCap + 9 * tCap := rfl
  have hDe : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hnb : ∀ x, ¬ readFoot vCap eCap tCap L_w r y x →
      (x < y.q.roots ∨ y.q.roots + vCap ≤ x) ∧
      (x < y.q.f ∨ y.q.f + dynGraphSize vCap tCap ≤ x) ∧
      (x < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ x) := by
    intro x hx
    simp only [readFoot, ReadRecFoot, not_or, not_and, not_lt] at hx
    obtain ⟨-, ⟨-, -, hf, hro, hs, -, -, -⟩, -, -⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · by_cases h1 : y.q.roots ≤ x
      · exact Or.inr (hro h1)
      · exact Or.inl (by omega)
    · by_cases h1 : y.q.f ≤ x
      · exact Or.inr (hf h1)
      · exact Or.inl (by omega)
    · by_cases h1 : y.q.s ≤ x
      · exact Or.inr (hs h1)
      · exact Or.inl (by omega)
  obtain ⟨hcR, hcRL, hcF, hcFL⟩ := hC
  have hBin1 : batch + words ≤ h := hBin.1
  have hCin1 : chg + c.words ≤ h := hCin.1
  have hBSin1 : us + usWords ≤ h := hBSin.1
  have hend : y.frz + dynGraphSize vCap tCap ≤ h := by
    have := hfoot (y.frz + dynGraphSize vCap tCap - 1)
      (Or.inr (Or.inr (Or.inr ⟨by rw [hDt]; omega, by rw [hDt]; omega⟩)))
    omega
  have hcw : c.words = 2 + c.roots.length + c.fDel.length := by
    simp only [LSFChange.words, LSFChange.size]; omega
  obtain ⟨o, st', cst, hrun, ⟨hoval, hrepF, hfrF, hpotF⟩, hcst⟩ :
      ∃ o st' cst, Runs w p ω (readStepStmt L fWalk)
        (startState [r, batch, words, chg, us, usWords, h] mem pos) o st' cst ∧
      (o.value = h + words + 2 * tCap ∧
        ReadRepAt vCap eCap tCap L_w P r (v.step U c U_S) { y with view := v.step U c U_S }
          st'.mem ∧
        (∀ x, ¬ readFoot vCap eCap tCap L_w r y x → (x < h ∨ h + words + 2 * tCap ≤ x) →
          st'.mem x = mem x) ∧
        treePot W.G W.lsf.T ≤ treePot v.G v.lsf.T + words) ∧
      cst ≤ readWalkMul * (words * (L_w + 1)) + readPotMul * treePot v.G v.lsf.T -
        readPotMul * treePot W.G W.lsf.T + 30 * c.roots.length + 490 * c.fDel.length +
        670 * usWords + 200 := by
    apply runs_start_le
    -- the walk
    refine runs_seq_call_le (hWalk v y U words) (vs := [r, batch, h]) (by eval_expr)
      (by wram_words) ⟨r, batch, h, rfl, hw16, hLw, heT, hrep0, hfoot, hB, hBin.2, hBin.1,
        by omega, hval, hcaps, hins⟩ ?_
    rintro r1 mem1 pos1 ⟨_, _, _, hEq1, -, hW1, hfr1, hpot1⟩
    simp only [List.cons.injEq, and_true] at hEq1
    obtain ⟨rfl, rfl, rfl⟩ := hEq1
    replace hfr1 : ∀ x, ¬ readFoot vCap eCap tCap L_w r y x →
        (x < h ∨ h + words + 2 * tCap ≤ x) → mem1 x = mem x := hfr1
    rw [← hWdef] at hW1 hpot1
    have hW1c := hW1
    obtain ⟨-, -, -, hrec1, -, -, hlive1, hfrz1⟩ := hW1
    obtain ⟨g0, g1, g2, -, -, g5, -, g7, g8, hT1, hF1, hR1, hSV1, hSP1, hS1, hG1⟩ := hrec1
    dsimp only at g0 g1 g2 g5 g7 g8 hT1 hF1 hR1 hS1 hG1 hlive1 hfrz1
    have hchg : ∀ i < c.words, mem1 (chg + i) = mem (chg + i) := fun i hi =>
      hfr1 _ (hCin.2 i hi).2 (Or.inl (by omega))
    have hm1c : mem1 chg = c.roots.length := by
      rw [show chg = chg + 0 from rfl, hchg 0 (by omega)]; exact hcR
    refine runs_seq_assign_le (v := c.roots.length) (by eval_expr) ?_
    -- the new roots
    have hRL1 : ListAt mem1 (chg + 1) c.roots := fun i hi => by
      rw [show chg + 1 + i = chg + (1 + i) by omega, hchg _ (by omega),
        show chg + (1 + i) = chg + 1 + i by omega]
      exact hcRL i hi
    refine runs_seq_call_le (hL.setRoots vCap W.lsf.F.R c.roots)
      (vs := [y.q.roots, chg + 1, c.roots.length]) (by eval_expr) (by wram_words)
      ⟨y.q.roots, chg + 1, rfl, hw16, by omega, by omega, hRL1, fun u hu =>
        hInv.2.1 u (hInv.2.2.2.2.2.2.2.2.2.2.1
          (Finset.mem_union_right _ (List.mem_toFinset.mpr hu))),
        fun i hi => (hnb _ (hCin.2 (1 + i) (by omega)).2).1 |>.imp
          (fun h' => by omega) (fun h' => by omega), hR1⟩ ?_
    rintro r2 mem2 pos2 ⟨_, _, hEq2, -, hR2, hfr2⟩
    simp only [List.cons.injEq, and_true] at hEq2
    obtain ⟨rfl, rfl⟩ := hEq2
    replace hfr2 : ∀ x, x < y.q.roots ∨ y.q.roots + vCap ≤ x → mem2 x = mem1 x := hfr2
    -- the forest edges that leave
    have hm2f : mem2 (r + 1) = y.q.f := (hfr2 _ (Or.inl (by omega))).trans g1
    have hm2n : mem2 (chg + 1 + c.roots.length) = c.fDel.length := by
      have hx := (hCin.2 (1 + c.roots.length) (by omega)).2
      have hc := hchg (1 + c.roots.length) (by omega)
      rw [show chg + (1 + c.roots.length) = chg + 1 + c.roots.length by omega] at hx hc
      rw [hfr2 _ (hnb _ hx).1, hc]
      exact hcF
    have hFL2 : ListAt mem2 (chg + 2 + c.roots.length) c.fDel := fun i hi => by
      have hx := (hCin.2 (2 + c.roots.length + i) (by omega)).2
      have hc := hchg (2 + c.roots.length + i) (by omega)
      rw [show chg + (2 + c.roots.length + i) = chg + 2 + c.roots.length + i by omega] at hx hc
      rw [hfr2 _ (hnb _ hx).1, hc]
      exact hcFL i hi
    have hFw : ∀ e ∈ c.fDel, e < 2 ^ w := fun e he => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      have hw' := (hCin.2 (2 + c.roots.length + i) (by omega)).1
      rw [show chg + (2 + c.roots.length + i) = chg + 2 + c.roots.length + i by omega,
        hcFL i hi] at hw'
      exact hw'
    have hF2 : DynGraphAt mem2 y.q.f vCap tCap W.lsf.F.F :=
      hF1.of_agree fun x _ hx2 => hfr2 x (Or.inl (by omega))
    refine runs_seq_call_le (hL.delEdges vCap tCap W.lsf.F.F c.fDel)
      (vs := [y.q.f, chg + 2 + c.roots.length, c.fDel.length]) (by eval_expr) (by wram_words)
      ⟨y.q.f, chg + 2 + c.roots.length, rfl, hw16, by omega, by omega, hFL2, hFw,
        fun i hi => by
          have hx := (hCin.2 (2 + c.roots.length + i) (by omega)).2
          rw [show chg + (2 + c.roots.length + i) = chg + 2 + c.roots.length + i by omega] at hx
          exact (hnb _ hx).2.1, hF2⟩ ?_
    rintro r3 mem3 pos3 ⟨_, _, hEq3, -, hF3, hfr3⟩
    simp only [List.cons.injEq, and_true] at hEq3
    obtain ⟨rfl, rfl⟩ := hEq3
    replace hfr3 : ∀ x, x < y.q.f ∨ y.q.f + dynGraphSize vCap tCap ≤ x → mem3 x = mem2 x := hfr3
    -- the output batch on `S`
    have hm3s : mem3 (r + 5) = y.q.s := by
      rw [hfr3 _ (Or.inl (by omega)), hfr2 _ (Or.inl (by omega))]; exact g5
    have hus : ∀ i < usWords, mem3 (us + i) = mem (us + i) := fun i hi => by
      have hx := (hBSin.2 i hi).2
      rw [hfr3 _ (hnb _ hx).2.1, hfr2 _ (hnb _ hx).1, hfr1 _ hx (Or.inl (by omega))]
    have hBS3 : BatchAt mem3 us v.S U_S usWords := by
      refine ⟨hBS.1, ?_, hBS.2.2.of_agree fun i hi => ?_⟩
      · rw [show us = us + 0 from rfl, hus 0 (by have := hBS.1; omega)]; exact hBS.2.1
      · rw [show us + 1 + i = us + (1 + i) by omega, hus _ (by omega)]
    have hS3 : DynGraphAt mem3 y.q.s vCap eCap v.S := by
      rw [← hWS]
      exact hS1.of_agree fun x hx1 _ => by
        rw [hfr3 _ (Or.inr (by omega)), hfr2 _ (Or.inr (by omega))]
    refine runs_seq_call_le (hL.applyBatch vCap eCap v.S v.S U_S usWords)
      (vs := [y.q.s, us, 1]) (by eval_expr) (by wram_words)
      ⟨y.q.s, us, 1, rfl, hw16, by omega, by omega, fun i hi => (hnb _ (hBSin.2 i hi).2).2.2,
        fun i hi => (hus i hi).trans_lt (hBSin.2 i hi).1, hBS3, hvalS, hcapsS, hS3,
        Or.inl ⟨one_ne_zero, rfl⟩⟩ ?_
    rintro r4 mem4 pos4 ⟨_, _, _, hEq4, -, hS4, hfr4⟩
    simp only [List.cons.injEq, and_true] at hEq4
    obtain ⟨rfl, rfl, rfl⟩ := hEq4
    replace hfr4 : ∀ x, x < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ x → mem4 x = mem3 x := hfr4
    have hfin : ∀ x, (x < y.q.roots ∨ y.q.roots + vCap ≤ x) →
        (x < y.q.f ∨ y.q.f + dynGraphSize vCap tCap ≤ x) →
        (x < y.q.s ∨ y.q.s + dynGraphSize vCap eCap ≤ x) → mem4 x = mem1 x :=
      fun x hro hf hs => by rw [hfr4 x hs, hfr3 x hf, hfr2 x hro]
    have hlow : ∀ x, x < y.q.f → mem4 x = mem1 x := fun x hx =>
      hfin x (Or.inl (by omega)) (Or.inl hx) (Or.inl (by omega))
    have hhigh : ∀ x, y.q.s + dynGraphSize vCap eCap ≤ x → mem4 x = mem1 x := fun x hx =>
      hfin x (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr hx)
    have hm4t : mem4 r = y.q.t := (hlow r (by omega)).trans g0
    have hm4tc : mem4 (y.q.t + 1) = tCap := by
      rw [hlow _ (by omega)]
      simpa [dgECapOff] using hT1.2.2.2.2.1
    have h2t : 2 * tCap < 2 ^ w := by omega
    have hm4tc' : mem4 (mem4 r + 1) = tCap := by rw [hm4t]; exact hm4tc
    refine runs_ret_le (v := h + words + 2 * tCap) (by eval_expr) ⟨rfl, ?_, ?_, hpot1⟩ ?_
    · -- the data after the update
      have hstepT : (v.step U c U_S).lsf.T = W.lsf.T := hWT.symm
      have hstepG : (v.step U c U_S).G = W.G := hWG.symm
      have hstepF : (v.step U c U_S).lsf.F.F =
          { W.lsf.F.F with E := W.lsf.F.F.E \ c.fDel.toFinset } := by rw [hWF]; rfl
      have hstepR : (v.step U c U_S).lsf.F.R = W.lsf.F.R ∪ c.roots.toFinset := by rw [hWR]; rfl
      have hstepS : (v.step U c U_S).S = U_S.foldl (dgBatchTarget 1) v.S := by
        rw [foldl_dgBatchTarget_one]; rfl
      have hstepw : (v.step U c U_S).lsf.wstr = W.lsf.wstr := hWw.symm
      have hstepn : (v.step U c U_S).num = W.num := hWn.symm
      have hstepd : (v.step U c U_S).den = W.den := hWd.symm
      have hGcap : ∀ e ∈ W.G.E, e < eCap := hG1.2.2.1
      obtain ⟨hval4, hpair4⟩ := stretch_step (E' := W.G.E) (wstr' := W.lsf.wstr) (num' := W.num)
        (den' := W.den) (mem' := mem4) hSV1 hSP1 (hlow _ (by omega)) (hlow _ (by omega))
        (fun e he => by
          rw [g7, g8]
          have heL : e * L_w + L_w ≤ eCap * L_w := cell_in_table (hGcap e he)
          exact Or.inl ⟨he, rfl, rfl, rfl, fun i hi =>
            ⟨hhigh _ (by omega), hhigh _ (by omega)⟩⟩)
      show ReadRepAt vCap eCap tCap L_w P r (v.step U c U_S) { y with view := v.step U c U_S } mem4
      refine ReadRepAt.rebuild hW1c hInv.keep (fun i hi => hlow _ (by
          simp only [readFullWords] at hi; omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hstepT]; exact hT1.of_agree fun x _ hx => hlow x (by omega)
      · rw [hstepF]; exact hF3.of_agree fun x hx _ =>
          (hfr4 x (Or.inl (by omega))).trans rfl
      · rw [hstepR]
        refine ⟨hR2.1, fun x hx => ?_⟩
        rw [hfr4 _ (Or.inl (by omega)), hfr3 _ (Or.inr (by omega))]
        exact hR2.2 x hx
      · rw [hstepS]; exact hS4
      · rw [hstepG]; exact hG1.of_agree fun x hx _ => hhigh x (by omega)
      · rw [hstepG, hstepT]; exact hlive1.of_agree fun x hx _ => hhigh x (by omega)
      · rw [hstepG, hstepT]; exact hfrz1.of_agree fun x hx _ => hhigh x (by omega)
      · rw [hstepG, hstepw]; exact hval4
      · rw [hstepG, hstepn, hstepd]; exact hpair4
    · intro x hx hs
      exact (hfin x (hnb x hx).1 (hnb x hx).2.1 (hnb x hx).2.2).trans (hfr1 x hx hs)
    · simp only [walkContract, setRootsContract, delEdgesContract, dgApplyBatchContract,
        argsSize, Expr.size]
      rw [← hWdef]
      omega
  have hφ : treePot (v.step U c U_S).G (v.step U c U_S).lsf.T = treePot W.G W.lsf.T := by
    have h1 : (v.step U c U_S).G = W.G := hWG.symm
    have h2 : (v.step U c U_S).lsf.T = W.lsf.T := hWT.symm
    rw [h1, h2]
  refine ⟨readStepStmt L fWalk, hp, o, st', cst, { y with view := v.step U c U_S }, hrun, hrepF,
    trivial, ?_, ?_, ?_, ?_, fun a ha => Or.inl ha, ?_⟩
  · omega
  · simp only [readSpace]
    omega
  · intro a ha
    rw [hfrF a (fun hf => by have := hfoot a hf; omega) (Or.inr (by omega))]
    exact hz a (by omega)
  · intro a ha hf
    exact hfrF a hf (Or.inl ha)
  · simp only [readRep_phi, hyv, hφ]
    have hm' : 5300 ≤ mul := hmul
    have hK : 1 ≤ L_w + 1 := by omega
    set K := L_w + 1 with hKdef
    have e1 : words ≤ words * K := Nat.le_mul_of_pos_right _ hK
    have e4 : usWords ≤ usWords * K := Nat.le_mul_of_pos_right _ hK
    have hsz : c.size = c.roots.length + c.fDel.length := rfl
    have hexp : (words + usWords + 1) * K + c.size =
        words * K + usWords * K + K + c.roots.length + c.fDel.length := by
      rw [hsz]; ring
    have hm : 5300 * ((words + usWords + 1) * K + c.size) ≤
        mul * ((words + usWords + 1) * K + c.size) :=
      Nat.mul_le_mul_right _ hm'
    have hW5 : readWalkMul = 5100 := rfl
    have hP : readPotMul = 1000 := rfl
    rw [hW5, hP] at hcst
    rw [hP]
    omega

/-! ## The procedures of the update in one block -/

/-- The seven procedures of the update, at `b, …, b + 6`: the update, the walk, one entry of the
batch, the split of `T`, the two kinds of split, and the copy of a deleted tree edge into the
frozen part. -/
def readStepProcs (L : ReadLib) (b : ℕ) : List Stmt :=
  [readStepStmt L (b + 1), walkStmt (b + 2), updOneStmt L (b + 3) (b + 6),
    splitTStmt L (b + 4) (b + 5), splitMoveStmt L, splitKeepStmt L, delFrzStmt L]

/-- The update is at `b`. -/
theorem readStepProcs_step {p : Program} {L : ReadLib} {b : ℕ}
    (hp : p.HasAt b (readStepProcs L b)) : p.procs[b]? = some (readStepStmt L (b + 1)) :=
  hp.get (i := 0) (by simp [readStepProcs])

/-- The walk at `b + 1` meets its contract. -/
theorem readStepProcs_walk {w vCap eCap tCap L_w P : ℕ} {p : Program} {L : ReadLib} {b : ℕ}
    (hL : L.Has p) (hp : p.HasAt b (readStepProcs L b)) (v : ReadView) (y : ReadConc)
    (U : List Update) (words : ℕ) :
    MeetsContract w p (b + 1) (walkContract w vCap eCap tCap L_w P v y U words) :=
  walk_meetsContract (hp.get (i := 1) (by simp [readStepProcs])) fun _ _ _ _ =>
    updOne_meetsContract hL (hp.get (i := 2) (by simp [readStepProcs]))
      (hp.get (i := 3) (by simp [readStepProcs])) (hp.get (i := 4) (by simp [readStepProcs]))
      (hp.get (i := 5) (by simp [readStepProcs])) (hp.get (i := 6) (by simp [readStepProcs]))

end MinCostFlow.SparseCore.Program.Read
