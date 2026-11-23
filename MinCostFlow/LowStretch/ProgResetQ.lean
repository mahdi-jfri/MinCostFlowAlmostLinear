module

public import MinCostFlow.LowStretch.ProgResetP

/-!
# The reset of child `k`: the call of `rsP`, and what the reset does not change

`CS.rs_call` is the call of `rsP` in `oneD`, from the state after the reset test: its arguments
are the words of `CS.rsV`, so `rsP_child` gives its run, and the call returns the heap pointer
that `RsEnd` names.

`CS.RsEnd.frame`: the reset changes a cell below `OUTK + 2` only when it is in the record block,
a label of child `k`, or the local index at the head of a node between a vertex of child `k` and
its `θ`-node. The nodes of `ncP` are the `x`-nodes in column `1` of the split walk
(`CS.RsNc.x_eq`, `CS.RsNc.hd_eq`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

/-- A call followed by `s`, given a run of the body of the procedure. -/
theorem runs_seq_callB_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ} {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ} (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- **The call of `rsP` for child `k`.** From a state whose registers below `50` are those of
`oneV` (with `45 = NAK`, `47 = |X|`, `48 = μ`), with `51 = Δ` and `52 = drawEnd`, and whose
memory agrees with `M6` below `OUTK + 2`, the call and the return end as `RsEnd` says. -/
theorem rs_call {p : Program} {ω : ℕ → Bool} {I : CIdx} (frs : p.procs[I.rs]? = some (rsP I))
    (flg : MeetsContract w p I.lg (log2C w)) (fsp : MeetsContract w p I.sp (splitC w))
    (fio : MeetsContract w p I.io (iotaC w)) (fnc : MeetsContract w p I.nc (ncC w))
    (fpc : MeetsContract w p I.pc (pcC w)) (fgc : MeetsContract w p I.gc (grpCopyC w))
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) (hroom : H + S.spaceK M1 k + 2 < 2 ^ w)
    (hroom2 : drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + S.T.N + 1) < 2 ^ w)
    {st : State} (hR : (S.oneV M1 k H).Regs st) (h45 : st.regs 45 = S.NAK M1 H k)
    (h47 : st.regs 47 = (S.raw k).X.card)
    (h48 : st.regs 48 = (S.raw k).X.sup (fun a => S.T.mw (S.T.top S.c.θ a)))
    (st' : State) (hM7 : ∀ a, a < S.OUTK M1 H k + 2 → st'.mem a = M6 a)
    (hregs : ∀ r < 50, st'.regs r = st.regs r) (h51 : st'.regs 51 = (S.raw k).Δ S.G)
    (h52 : st'.regs 52 = drawEnd (S.dwE M1 k H)) {A T : ℕ} (hc : A + S.rsCost M1 k + 20 ≤ T) :
    ∃ o st'' c, Runs w p ω (.seq (.call 54 I.rs (rgs [0, 3, 52, 51, 47, 48, 35, 36, 45, 38, 31,
      10, 2, 44])) (.ret (.reg 54))) st' o st'' c ∧
      (∃ H', o = .returned H' ∧ S.RsEnd w M1 k H M6 st'.mem (.returned H') st''.mem) ∧
      A + c ≤ T := by
  have g : ∀ r < 39, st'.regs r = (S.oneV M1 k H).vals.getD r 0 := fun r hr => by
    rw [hregs r (by omega)]; exact hR.1 r hr
  have hvs : [0, 3, 52, 51, 47, 48, 35, 36, 45, 38, 31, 10, 2, 44].map st'.regs =
      (S.rsV M1 k H).args := by
    simp only [List.map_cons, List.map_nil, RsV.args, rsV, h51, h52, hregs 47 (by norm_num),
      hregs 48 (by norm_num), hregs 45 (by norm_num), hregs 44 (by norm_num), h45, h47, h48,
      hR.2.2.2, g 0 (by norm_num), g 3 (by norm_num), g 35 (by norm_num), g 36 (by norm_num),
      g 38 (by norm_num), g 31 (by norm_num), g 10 (by norm_num), g 2 (by norm_num)]
    rfl
  obtain ⟨o₁, st₁, c₁, hr₁, hE, hc₁⟩ := rsP_child flg fsp fio fnc fpc fgc hpre hT hI hk hmid hq
    hroom hroom2 hM7 st'.pos
  obtain ⟨v, M8, M9, M10, M11, M12, -, -, -, ho⟩ := id hE
  refine runs_seq_callB_le (by rw [evalArgs_rgs, hvs]) frs hr₁ ?_
  refine runs_ret_le (v := o₁.value) (Expr.eval_reg_of_eq (by simp)) ⟨o₁.value, ?_, ?_⟩ ?_
  · rw [ho]
  · rw [ho] at hE ⊢; exact hE
  · simp only [argsSize_rgs, List.length_cons, List.length_nil, Expr.size]; omega

variable {M7 M8 M9 M10 : ℕ → ℕ} {v : ℕ}

/-- The node of entry `i` of `ncP` in the reset is entry `i` of column `1`. -/
theorem RsNc.x_eq (hR : RsNc w S M1 k H M6 M7 M8 M9 M10 v) {i : ℕ} (hi : i < S.sNK M1 k + v) :
    (rsNcE (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) S.E.HEAD S.E.LOC M9).x i =
      M8 (drawEnd (S.dwE M1 k H) + 3 * i + 1) := by
  simp only [NCE.x, rsNcE]
  rw [hR.io.1 i hi, show drawEnd (S.dwE M1 k H) + (3 * i + 1) = drawEnd (S.dwE M1 k H) + 3 * i + 1
    by omega, hR.io.2 _ (Or.inl (by omega))]

/-- Entry `i` of column `1` is the `x`-node of a vertex of child `k`. -/
theorem RsNc.col1 (hR : RsNc w S M1 k H M6 M7 M8 M9 M10 v) {i : ℕ} (hi : i < S.sNK M1 k + v) :
    ∃ a ∈ (S.raw k).X, M8 (drawEnd (S.dwE M1 k H) + 3 * i + 1) = S.T.top (S.thrK k) a := by
  have hm : M8 (drawEnd (S.dwE M1 k H) + 3 * i + 1) ∈
      rdS M8 (S.spL M1 k H).A 1 ((S.spL M1 k H).len0 + v) := by
    have : M8 (drawEnd (S.dwE M1 k H) + 3 * i + 1) =
        (rdS M8 (S.spL M1 k H).A 1 ((S.spL M1 k H).len0 + v))[i]'(by
          rw [rdS_length]; exact hi) := by simp [rdS, spL]
    rw [this]; exact List.getElem_mem _
  exact (hR.sp.2.2.2.1 _).mp hm

/-- The head of entry `i` of `ncP` in the reset is the head of entry `i` of column `1`. -/
theorem RsNc.hd_eq (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) (hR : RsNc w S M1 k H M6 M7 M8 M9 M10 v) {i : ℕ}
    (hi : i < S.sNK M1 k + v) :
    (rsNcE (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) S.E.HEAD S.E.LOC M9).hd i =
      S.T.hd S.G (M8 (drawEnd (S.dwE M1 k H) + 3 * i + 1)) := by
  obtain ⟨a, ha, hae⟩ := hR.col1 hi
  have han := hpre.ok.n_of_mem (Cl.raw_X_subset k ha)
  have hx1 := (thrK_le hpre hk hq).1
  have hxN : S.T.top (S.thrK k) a < S.T.N := top_lt_N hpre.ok.tree han hx1
  have hHD : (S.E.HEAD, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bH : S.E.HEAD + S.E.N ≤ S.h := hpre.below _ hHD
  have dH : RegDisj (S.E.HEAD, S.E.N) (S.E.LOC, S.T.N) := hpre.loc_disj _ hHD
  unfold RegDisj at dH
  dsimp only at bH dH
  have hEN : S.E.N = S.T.N := hpre.glob.N
  have hA : S.h ≤ drawEnd (S.dwE M1 k H) := by
    have := drawEnd_ge (S := S) (M1 := M1) (H := H) (k := k)
    have := S.OUTK_ge M1 H k
    have := S.h_le_HM
    have := S.HM_le_H0
    have := hI.hle
    omega
  show M9 (S.E.HEAD + _) = _
  rw [hR.x_eq hi, hae]
  have k10 := hR.keep hpre hT hI hk hmid hHD (i := S.T.top (S.thrK k) a) (by dsimp only; omega)
  rw [hR.nc.2.2 _ (fun hout => by
    rcases hout with ⟨h1, -⟩ | ⟨j, hj, he⟩
    · simp only [rsNcE] at h1; omega
    · have := (hR.ok.rd j hj).2.2.2
      simp only [rsNcE] at he this; omega)] at k10
  rw [show M9 _ = _ from k10]
  exact hpre.glob.hd _ hxN

/-- The record block of the reset changes only the seven cells it writes. -/
theorem rsBlk_of_ne {V : RsV} {n m lx : ℕ} {M : ℕ → ℕ} {a : ℕ}
    (ha : a < V.BK ∨ V.BK + 9 ≤ a) : V.rsBlk n m lx M a = M a := by
  unfold RsV.rsBlk
  repeat rw [Function.update_of_ne (by omega)]

/-- **What the reset does not change**, before the record block is written. -/
theorem RsRun.frame12 (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) {M11 M12 : ℕ → ℕ}
    (h7 : ∀ a, (a < S.OUTK M1 H k + 2 ∨ drawEnd (S.dwE M1 k H) ≤ a) → M7 a = M6 a)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v)
    (hd12 : ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).Done M12
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq) {a : ℕ}
    (ha : a < S.OUTK M1 H k + 2 ∨ drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) +
      2 * (S.cntK M1 k + ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq.length) ≤ a)
    (hlab : ∀ b ∈ (S.raw k).X, a ≠ S.E.LAB + b)
    (hloc : ∀ b ∈ (S.raw k).X, ∀ u, S.T.Under b u → S.T.Under u (S.T.top S.c.θ b) →
      a ≠ S.E.LOC + S.T.hd S.G u) : M12 a = M6 a := by
  have hend := drawEnd_ge (S := S) (M1 := M1) (H := H) (k := k)
  set A := drawEnd (S.dwE M1 k H) with hA
  set n := S.sNK M1 k + v with hn
  have e1 : ((S.rsV M1 k H).rsGcE v n M11).OUT = A + 5 * n := rfl
  have e2 : ((S.rsV M1 k H).rsGcE v n M11).c0 = S.cntK M1 k := rfl
  rw [hd12.2 _ (by rw [e1, e2]; omega)]
  show M11 a = M6 a
  rw [hR.pc.2 _ (by simp only [RsV.rsPcE, rsV]; omega)]
  show M10 a = M6 a
  have hx1 := (thrK_le hpre hk hq).1
  have hx4 := (thrK_le hpre hk hq).2
  rw [hR.nc.2.2 _ (fun hout => by
    rcases hout with ⟨h1, h2⟩ | ⟨i, hi, he⟩
    · simp only [rsNcE] at h1 h2; omega
    · have hi' : i < n := hi
      obtain ⟨b, hb, hbe⟩ := hR.col1 hi'
      rw [hR.hd_eq hpre hT hI hk hmid hq hi', hbe] at he
      have hbn := hpre.ok.n_of_mem (Cl.raw_X_subset k hb)
      have ht := isTop_top hpre.ok.tree hbn hx1
      have hθ := isTop_top hpre.ok.tree hbn hpre.ok.inv.one_le
      have hN := hpre.ok.tree.n_lt
      exact hloc b hb _ ht.1 (IsTop.under_of_le hpre.ok.tree (by omega) (by omega) ht hθ) he)]
  show M9 a = M6 a
  rw [hR.io.2 _ (by omega)]
  rcases ha with ha | ha
  · rw [hR.sp.2.2.2.2.2.2.1 a (by simp only [spL]; omega) hlab, h7 a (Or.inl ha)]
  · rw [hR.sp.2.2.2.2.2.2.2.1 a (by simp only [spL]; omega), h7 a (Or.inr (by omega))]

/-- **What the reset does not change.** A cell below `OUTK + 2` or from the returned pointer on
keeps its value in `M6`, unless it is in the record block, a label of child `k`, or the local
index at the head of a node between a vertex of child `k` and its `θ`-node. -/
theorem RsEnd.frame (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) {M7 M' : ℕ → ℕ} {H' : ℕ}
    (h7 : ∀ a, (a < S.OUTK M1 H k + 2 ∨ drawEnd (S.dwE M1 k H) ≤ a) → M7 a = M6 a)
    (hE : S.RsEnd w M1 k H M6 M7 (.returned H') M') {a : ℕ}
    (ha : a < S.OUTK M1 H k + 2 ∨ H' ≤ a) (hbk : a < S.h + 9 * k ∨ S.h + 9 * k + 9 ≤ a)
    (hlab : ∀ b ∈ (S.raw k).X, a ≠ S.E.LAB + b)
    (hloc : ∀ b ∈ (S.raw k).X, ∀ u, S.T.Under b u → S.T.Under u (S.T.top S.c.θ b) →
      a ≠ S.E.LOC + S.T.hd S.G u) : M' a = M6 a := by
  obtain ⟨v, M8, M9, M10, M11, M12, hR, hd12, rfl, ho⟩ := hE
  have hH' := Outcome.returned.inj ho
  have := S.OUTK_ge M1 H k
  have := S.h_le_HM
  have := S.HM_le_H0
  have := hI.hle
  have hend := drawEnd_ge (S := S) (M1 := M1) (H := H) (k := k)
  rw [rsBlk_of_ne (V := S.rsV M1 k H) (by simp only [rsV]; omega)]
  exact hR.frame12 hpre hT hI hk hmid hq h7 hd12 (by omega) hlab hloc

end CS

end MinCostFlow.LowStretch
