module

public import MinCostFlow.LowStretch.ProgBodyNodeEnd
public import MinCostFlow.LowStretch.ProgBodyNodePre
public import MinCostFlow.LowStretch.ProgBodyNodeCt0
import MinCostFlow.LowStretch.ProgBodyNodeAct
import MinCostFlow.LowStretch.ProgChildRec

/-!
# The tail of the node part

After the loop of the regular petals returns, the node part writes the center `CC[0] = x0` and
the target `CT[0]` of child `0`, stores the petal block of `16` words at `hS`, and runs
`nodeEnd` (the child step and the four words of `wr4`). `PW.nodeTail_runs` shows that this tail
ends with `BodyPost`.

The memory `M1` that the child step sees is fixed in advance (`tailMem`): the memory after the
loop with the two stores and the block. So the run of the child step, and with it the cost, is
known before the run of the tail is built step by step.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The tail of the node part, after the loop of the regular petals. -/
def nodeTail (bK : ℕ) : Stmt :=
  .seq (.store (.reg 36) (.load (.bin .add (.reg 61) (.const 5))))
    (.seq ct0 (stR 57 petRegs 0 (nodeEnd bK)))

theorem nodeMid_eq (bP bC bR bK : ℕ) : nodeMid bP bC bR bK =
    .seq (.assign 13 (.const 1)) (.seq (.cond (.reg 53) (spPet bP bC) .nop)
      (.seq (.call 58 bR (rgs (List.range 43))) (nodeTail bK))) := rfl

/-- The center of child `0` is the center of the cluster. -/
theorem Cl.raw_zero_x0 {G : PG} {c : Cl} {D : Cl.Dec} : (c.raw G D 0).x0 = c.x0 := by
  unfold Cl.raw; split_ifs <;> rfl

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

/-- The values of the petal block, in the order of `petRegs`. -/
noncomputable def blkVals (W : PW) (A : TA) (Q : LA) (nP : ℕ) (sp : Bool) (ACT : ℕ) : List ℕ :=
  [nP, if sp then 1 else 0, Q.PL, Q.PO, W.L.OK, W.L.os, Q.CT, Q.CC, W.NXT, A.PP, A.PF, A.PA, A.PB,
    W.nA, ACT, W.c.Δ W.G]

/-- The memory that the child step sees: `M` with `CC[0]`, `CT[0]` and the block at `hS`. -/
noncomputable def tailMem (W : PW) (A : TA) (Q : LA) (M : ℕ → ℕ) (hS nP : ℕ) (sp : Bool)
    (ACT e : ℕ) : ℕ → ℕ := fun y =>
  if hS ≤ y ∧ y < hS + 16 then (blkVals W A Q nP sp ACT).getD (y - hS) 0
  else Function.update (Function.update M Q.CC W.c.x0) Q.CT e y

open Classical in
set_option maxHeartbeats 1000000 in
/-- **The tail of the node part.** From the state after the loop (memory of the end `LInv` at
`stE`, registers of the loop, the block registers `52 … 58` and the arguments in `60, 61, 62`),
the tail runs and leaves `BodyPost`, when `hfit` bounds the cost `K` spent before it plus the
cost of the child step, and the heap. The bound `hACT` comes from the setup. -/
theorem nodeTail_runs {p : Program} {ω : ℕ → Bool} {bK : ℕ} (hK : MeetsChild w p bK)
    {A0 GB RB h hS ACT k0 K : ℕ} {mem M0 : ℕ → ℕ} {sp : Bool} {a : LG} {stE st : State}
    (hpre : ClPre w A0 W.T W.G W.P W.c W.R GB RB h mem) (hX2 : 2 ≤ W.c.X.card)
    (hOk0 : W.Ok w M0) (hT0 : W.Tree A M0)
    (hI : W.LInv A Q sp k0 M0 w a stE) (hL : W.LLay A Q w) (hend : a.u = W.s)
    (hdec : W.c.DecOk W.G W.P ⟨sp, a.ps⟩)
    (hlow0 : ∀ x < h, M0 x = mem x) (hz0 : ZeroFrom M0 hS)
    (hHD : h + 51 ≤ W.L.HD)
    (hTA : h + 51 ≤ A.PP ∧ h + 51 ≤ A.PF ∧ h + 51 ≤ A.PA ∧ h + 51 ≤ A.PB) (hACTh : h + 51 ≤ ACT)
    (hACT : ACT + 2 * W.nA ≤ W.L.HD)
    (hPTs : Q.PT + W.s ≤ hS) (hNXTs : W.NXT + W.s + 1 ≤ hS)
    (hact : ∀ i < W.nA, M0 (ACT + 2 * i) = W.pr i ∧
      M0 (ACT + 2 * i + 1) = if W.pr i ∈ W.c.half then 1 else 0)
    (hpath : sp = false → ∃ n, W.Path M0 (W.sv W.c.t) n ∧
      W.c.HwDec W.G W.c.t (W.stp A M0 (W.sv W.c.t) n) W.c.hw)
    (hspec : sp = true → 0 < a.ps.length ∧ ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).tj = W.c.t ∧
      ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).hw = W.c.hw)
    (hroom : hS + 16 ≤ h + ((GlobL.read mem GB).J + 2) * recCost w A0 W.T W.G W.P W.c W.R)
    (hm : st.mem = stE.mem)
    (hregs : ∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 →
      st.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0)
    (r52 : st.regs 52 = W.c.t) (r53 : st.regs 53 = if sp then 1 else 0)
    (r54 : st.regs 54 = A.PF) (r55 : st.regs 55 = A.PB) (r56 : st.regs 56 = ACT)
    (r57 : st.regs 57 = hS) (r58 : st.regs 58 = a.ps.length)
    (r60 : st.regs 60 = GB) (r61 : st.regs 61 = RB) (r62 : st.regs 62 = h)
    (hw : hS + 16 < 2 ^ w)
    (hfit : ∀ (cs : ℕ → Cl) (cost : ℕ),
      cost ≤ childCost W.T W.G W.P W.c W.R ⟨sp, a.ps⟩ cs (GlobL.read mem GB).J →
      K + cost + 500 ≤ bodyShare A0 W.T W.G W.P W.c W.R ⟨sp, a.ps⟩ cs +
        (⟨sp, a.ps⟩ : Cl.Dec).nch * kidCost w W.G.n ∧
      hS + 16 + ((GlobL.read mem GB).J + 1) *
          childCost W.T W.G W.P W.c W.R ⟨sp, a.ps⟩ cs (GlobL.read mem GB).J ≤
        h + 4 + ((GlobL.read mem GB).J + 1) *
          (bodyShare A0 W.T W.G W.P W.c W.R ⟨sp, a.ps⟩ cs +
            (⟨sp, a.ps⟩ : Cl.Dec).nch * kidCost w W.G.n)) :
    ∃ o st' c', Runs w p ω (nodeTail bK) st o st' c' ∧
      BodyPost w A0 W.T W.G W.P W.c W.R (GlobL.read mem GB) h mem st'.mem (K + c' + 20) := by
  have hWk := hI.btw.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := hWk.lay
  have hES := hWk.lES; have hNN := hWk.hNN; have hR := hWk.hR; have hCTL := hWk.hCTL
  have hSUM := hWk.hSUM; have hSL := hWk.hSL
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have hpl := hL.pl; have hpo := hL.po; have hct := hL.ct; have hcc := hL.cc
  have hpt := hL.pt
  have hout := fun {x : ℕ} (hx : W.Out Q x) => hL.out_ge hx
  set D : Cl.Dec := ⟨sp, a.ps⟩ with hD
  set E := GlobL.read mem GB with hE
  have hDps : D.ps.length = a.ps.length := rfl
  have hkle := hI.kle
  -- the memory after the loop agrees with `mem` below `h`
  have hsafe : ∀ x, x < W.L.HD → stE.mem x = M0 x := fun x hx =>
    hI.safe x (Or.inl hx) fun ho => by have := hout ho; omega
  have hlowS : ∀ x < h, st.mem x = mem x := fun x hx => by
    rw [hm, hsafe x (by omega), hlow0 x hx]
  have hbelow := hpre.below
  have hRB : RB + 9 ≤ h := by have := hbelow (RB, 9) (by simp [recRegs]); simpa using this
  have hGB : GB + 21 ≤ h := by have := hbelow (GB, 21) (by simp [recRegs]); simpa using this
  have hIN : E.IN + 3 * E.m ≤ h := by
    have := hbelow (E.IN, 3 * E.m) (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    simpa using this
  have hEm : E.m = W.G.m := hpre.glob.m
  have hx0 : st.mem (RB + 5) = W.c.x0 := by
    rw [hlowS _ (by omega)]; exact hpre.recAt.x0
  have hhw : h < 2 ^ w := by omega
  -- the registers
  have r35 : st.regs 35 = Q.CT := by
    simpa [LReg] using hregs 35 (by omega) (by omega) (by omega) (by omega)
  have r36 : st.regs 36 = Q.CC := by
    simpa [LReg] using hregs 36 (by omega) (by omega) (by omega) (by omega)
  have r37 : st.regs 37 = Q.PT := by
    simpa [LReg] using hregs 37 (by omega) (by omega) (by omega) (by omega)
  -- the target of child `0`
  set e := (W.c.raw W.G D 0).t with he
  have hspE : sp = true → ∃ pr, pr < W.G.m ∧ st.mem Q.PT = pr ∧
      st.mem (E.IN + 3 * pr) = W.G.pu pr ∧ st.mem (E.IN + 3 * pr + 1) = W.G.pv pr ∧
      st.mem (Q.CC + 1) = D.xc W.G 0 ∧ e = W.G.other pr (D.xc W.G 0) := by
    intro hs
    obtain ⟨hlen, -, -⟩ := hspec hs
    obtain ⟨-, -, -, hcc1, hpt0, -⟩ := hI.out 0 hlen
    have hok := (hdec.2.1 hs).2.2.2
    have hi : (D.pd 0).i < (D.pd 0).hw.length := hok.2.2.1
    have hpr : D.portal 0 < W.G.m := by
      refine hok.2.1.1.pair_lt ?_
      unfold Cl.Dec.portal
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    obtain ⟨u1, u2⟩ := hpre.glob.ends _ hpr
    refine ⟨D.portal 0, hpr, ?_, ?_, ?_, ?_, Cl.raw_zero_t_sp hs hi⟩
    · rw [hm]; simpa using hpt0
    · rw [hlowS _ (by omega)]; exact u1
    · rw [hlowS _ (by omega)]; exact u2
    · rw [hm]; exact hcc1
  set M1 := tailMem W A Q st.mem hS a.ps.length sp ACT e with hM1
  have hCTCC : Q.CT ≠ Q.CC := by omega
  have hM1lo : ∀ x, x < hS → M1 x = Function.update (Function.update st.mem Q.CC W.c.x0) Q.CT e x :=
    fun x hx => by rw [hM1]; unfold tailMem; rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (hS ≤ x ∧ x < hS + 16) by omega))]
  have hM : ∀ x < hS, x ≠ Q.CT → x ≠ Q.CC → M1 x = stE.mem x := fun x hx h1 h2 => by
    rw [hM1lo x hx, Function.update_of_ne h1, Function.update_of_ne h2, hm]
  have hMz : ∀ x, hS + 16 ≤ x → M1 x = stE.mem x := fun x hx => by
    rw [hM1]; unfold tailMem
    rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (hS ≤ x ∧ x < hS + 16) by omega)), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm]
  have hct0 : M1 Q.CT = (W.c.raw W.G D 0).t := by
    rw [hM1lo _ (by omega), Function.update_self]
  have hcc0 : M1 Q.CC = (W.c.raw W.G D 0).x0 := by
    rw [hM1lo _ (by omega), Function.update_of_ne hCTCC.symm, Function.update_self,
      Cl.raw_zero_x0]
  have hblk : PetL.read M1 hS = ⟨a.ps.length, if sp then 1 else 0, Q.PL, Q.PO, W.L.OK, W.L.os,
      Q.CT, Q.CC, W.NXT, A.PP, A.PF, A.PA, A.PB, W.nA, ACT, W.c.Δ W.G⟩ := by
    simp [PetL.read, hM1, tailMem, blkVals]
  have hcp : ChildPre w W.T W.G W.P W.c W.R D GB RB hS (hS + 16) M1 :=
    nodeChildPre hpre hX2 hOk0 hT0 hI hL hend hdec hlow0 hz0 hHD hTA hACTh hACT hPTs hNXTs hact
      hpath hspec hM hMz hct0 hcc0 hblk hroom
  obtain ⟨body, hb, o1, st1, cost1, hr1, hpost⟩ :=
    hK W.T W.G W.P W.c W.R D GB RB hS (hS + 16) M1 st.pos ω hcp
  have hlow1 : ∀ x < h, M1 x = mem x := fun x hx => by
    rw [hM x (by omega) (by omega) (by omega), ← hm, hlowS x hx]
  have hE1 : GlobL.read M1 GB = E := GlobL.read_congr fun i hi => hlow1 _ (by omega)
  have hport : ∀ j < D.ps.length, M1 (Q.PT + j) = D.portal j := fun j hj => by
    rw [hM _ (by omega) (by omega) (by omega)]
    exact (hI.out j hj).2.2.2.2.1
  suffices H : ∃ o st' c', Runs w p ω (nodeTail bK) st o st' c' ∧
      st'.mem = wr4 st1.mem h (a.ps.length + 1) (hS + 16) o1.value Q.PT ∧ c' ≤ cost1 + 400 by
    obtain ⟨o, st', c', hr, hmem, hc⟩ := H
    refine ⟨o, st', c', hr, ?_⟩
    rw [hmem]
    refine bodyPost_of_childPost hpre hX2 hdec (fun k _ => Cl.sat_raw hpre.ok k) hlow1
      (by omega) (by omega) (by omega) hport hE1 hpost fun cs hcs => ?_
    obtain ⟨f1, f2⟩ := hfit cs cost1 hcs
    exact ⟨by omega, f2⟩
  refine runs_start_le ?_
  unfold nodeTail
  refine runs_seq_store_le (x := Q.CC) (v := W.c.x0) (Expr.eval_reg_of_eq r36)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r61) (Expr.eval_const (by omega))
      (by omega)) hx0) ?_
  set sta : State := { st with mem := Function.update st.mem Q.CC W.c.x0 } with hsta
  have hsa : ∀ x, x ≠ Q.CC → sta.mem x = st.mem x := fun x hx => by
    simp only [hsta]; rw [Function.update_of_ne hx]
  refine runs_seq_ct0 (st := sta) (sp := sp) (CT := Q.CT) (t := W.c.t) (e := e) r53 r35 r52
    (by omega) (fun hs => ?_) (fun hs => by rw [he, Cl.raw_zero_t hs]) ?_
  · obtain ⟨pr, hpr, q1, q2, q3, q4, q5⟩ := hspE hs
    have hIN' : sta.mem (GB + 3) = E.IN := by
      rw [hsa _ (by omega), hlowS _ (by omega)]; rfl
    refine ⟨GB, Q.PT, Q.CC, E.IN, pr, r60, r37, r36, hIN', ?_, by omega, by omega, by omega, ?_⟩
    · rw [hsa _ (by omega), q1]
    · rw [hsa _ (by omega), hsa _ (by omega), hsa _ (by omega), q2, q3, q4, q5]
      rfl
  intro regs' hregs'
  refine runs_stR (c := hS) petRegs 0 _ _ _ (by simp [hregs', hsta, r57]) (by simp [petRegs]; omega) ?_
  intro mem' hin hout'
  have hmem' : mem' = M1 := by
    funext y
    by_cases hy : hS ≤ y ∧ y < hS + 16
    · obtain ⟨j, rfl⟩ : ∃ j, y = hS + j := ⟨y - hS, by omega⟩
      have hj : j < 16 := by omega
      have := hin j (by simp [petRegs]; omega)
      rw [Nat.add_zero] at this
      rw [this, hM1]
      unfold tailMem
      rw [ite_eq_left_of_eq_true _ _ (eq_true hy), Nat.add_sub_cancel_left]
      simp only [hregs' _ (show petRegs[j]'(by simp [petRegs]; omega) ≠ 59 by
        interval_cases j <;> simp [petRegs])]
      have q9 : st.regs 9 = W.L.OK := by
        simpa [LReg] using hregs 9 (by omega) (by omega) (by omega) (by omega)
      have q10 : st.regs 10 = W.L.os := by
        simpa [LReg] using hregs 10 (by omega) (by omega) (by omega) (by omega)
      have q22 : st.regs 22 = W.nA := by
        rw [hWk.nA_eq]; simpa [LReg] using hregs 22 (by omega) (by omega) (by omega) (by omega)
      have q28 : st.regs 28 = W.NXT := by
        simpa [LReg] using hregs 28 (by omega) (by omega) (by omega) (by omega)
      have q33 : st.regs 33 = Q.PL := by
        simpa [LReg] using hregs 33 (by omega) (by omega) (by omega) (by omega)
      have q34 : st.regs 34 = Q.PO := by
        simpa [LReg] using hregs 34 (by omega) (by omega) (by omega) (by omega)
      have q38 : st.regs 38 = A.PP := by
        simpa [LReg] using hregs 38 (by omega) (by omega) (by omega) (by omega)
      have q39 : st.regs 39 = A.PA := by
        simpa [LReg] using hregs 39 (by omega) (by omega) (by omega) (by omega)
      have q42 : st.regs 42 = W.c.Δ W.G := by
        simpa [LReg] using hregs 42 (by omega) (by omega) (by omega) (by omega)
      interval_cases j <;>
        simp [petRegs, blkVals, hsta, q9, q10, q22, q28, q33, q34, r35, r36, q38, q39, q42, r53,
          r54, r55, r56, r58]
    · rw [hout' y (by simp only [petRegs, List.length_cons, List.length_nil]; omega), hM1]
      unfold tailMem
      rw [ite_eq_right_of_eq_false _ _ (eq_false hy)]
  rw [hmem']
  obtain ⟨o, st', c', hr, hmm, hc⟩ := nodeEnd_runs_of (st := { sta with regs := regs', mem := M1 }) (PT := Q.PT)
    (n0 := a.ps.length) (h := h)
    hb hr1 (by simp [hregs', hsta, r37]) (by simp [hregs', hsta, r57]) (by simp [hregs', hsta, r58])
    (by simp [hregs', hsta, r60]) (by simp [hregs', hsta, r61]) (by simp [hregs', hsta, r62]) hw
    (by have := hI.kle; omega) (by omega)
  refine ⟨o, st', c', hr, hmm, ?_⟩
  simp only [Expr.size, petRegs, List.length_cons, List.length_nil] at hc ⊢
  omega

end PW

end MinCostFlow.LowStretch
