module

public import MinCostFlow.SparseCore.Program.OutStepSplitB

/-!
# One split of the output step, third part

The third part of a split round (`osSplitC`) runs after the edit of the split has been written.
It rewrites the record of the split in the batch region from the incidence list `L` of the smaller
side, so that the record has `4 + updateEnc` words, and then moves the two pointers past the new
record and the new edit, and steps to the next split record of the helper. This file proves that
the third part runs (`osSplitC_runs`): the batch gets one more record and the edits get
`outSplitEdit`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update} {E : List OrdEdit} {bp ep cur : ℕ}
  {s : OutTourAbs} {tx : T.rep.τ}

/-- **The third part of a split round.** -/
theorem osSplitC_runs (hC : SCtx T A tx₀) {flt : ℕ} (hflt : p.procs[flt]? = some outFilterBody)
    {st : State} {v v' a nb ne : ℕ} {St Sh : Finset ℕ} {L : List ℕ}
    (hB : SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.split v v' St Sh)) U E bp ep cur s tx st.mem)
    (hGU : G = S₀.applyBatch U)
    (hR : SRegs st A vCap eCap) (h14 : st.regs 14 = bp) (h16 : st.regs 16 = ep)
    (h17 : st.regs 17 = nb) (h18 : st.regs 18 = ne) (h20 : st.regs 20 = a)
    (h21 : st.regs 21 = v) (h22 : st.regs 22 = v')
    (h34 : st.regs 34 = (if (G.applyUpdate (.split v v' St Sh)).deg v <
      (G.applyUpdate (.split v v' St Sh)).deg v' then 3 else 2))
    (h36 : st.regs 36 = L.length) (hLnd : L.Nodup)
    (hLmem : ∀ k, k ∈ L ↔ k < 2 * eCap ∧ (endOfKey k).1 ∈ (G.applyUpdate (.split v v' St Sh)).E ∧
        (G.applyUpdate (.split v v' St Sh)).src (endOfKey k) =
          if (G.applyUpdate (.split v v' St Sh)).deg v <
            (G.applyUpdate (.split v v' St Sh)).deg v' then v else v')
    (hL : ListAt st.mem (ep + 4) L)
    (hdec : decodeOrdEdit st.mem ep = (outSplitEdit G v v' St Sh, 4 + L.length))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w)
    (hGv : G.IsValid) (hval : G.UpdateIsValid (.split v v' St Sh)) (ha5 : a + 5 ≤ A.h)
    (hafree : ∀ i < 5, ¬ ((outGraphRep vCap eCap).foot A.outH A.g (a + i) ∨
      T.rep.foot A.tourH tx₀ (a + i)))
    (hbk : bp + 5 + 2 * L.length ≤ A.e0) (hek : ep + 4 + L.length ≤ A.t0)
    (hnb : nb + 1 < 2 ^ w) (hne : ne + 1 < 2 ^ w) :
    ∃ stC cC, Runs w p ω (osSplitC flt) st .normal stC cC ∧
      SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.split v v' St Sh)) (U ++ [.split v v' St Sh])
        (E ++ [outSplitEdit G v v' St Sh]) (bp + (5 + L.length)) (ep + (4 + L.length)) cur s tx
        stC.mem ∧
      T.rep.phi A.tourH tx stC.mem = T.rep.phi A.tourH tx st.mem ∧
      (∀ r, r ≠ 14 → r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 20 → r ≠ 29 → r ≠ 30 →
        stC.regs r = st.regs r) ∧
      stC.regs 14 = bp + (5 + L.length) ∧ stC.regs 16 = ep + (4 + L.length) ∧
      stC.regs 17 = nb + 1 ∧ stC.regs 18 = ne + 1 ∧ stC.regs 20 = mem₀ (a + 4) ∧
      cC ≤ 200 * L.length + 300 := by
  set G' := G.applyUpdate (.split v v' St Sh) with hG'
  have hEE : G'.E = G.E := rfl
  have hR' := hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, r19, -, -, -⟩ := hR'
  have hgh := hC.2.2.1
  have hkey := rs_key_lt hw
  have hvw : vCap + eCap + 2 < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow two_ne_zero _) hw
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  have hbp1 := hB.2.2.2.2.2.2.2.1
  have hbp2 := hB.2.2.2.2.2.2.2.2.1
  have hep1 := hB.2.2.2.2.2.2.2.2.2.2.1
  have hG := hB.2.2.2.2.2.2.1
  have hpres := hG.2.2.2.2.2.2.2.2.2.2.2.1
  have hsize : dgEPresBase A.g vCap + 2 * eCap ≤ A.g + dynGraphSize vCap eCap := by
    unfold dgEPresBase dynGraphSize; omega
  have hvc : v < vCap := hG.2.1 v (mem_applySplit_V.mpr (Or.inr hval.1))
  set pb := dgEPresBase A.g vCap with hpb
  set Y := L.map endOfKey with hY
  have hYm := mem_map_endOfKey_iff hLmem
  have hYc : ∀ y ∈ Y, y.1 < eCap := fun y hy => ((hYm y).mp hy).1
  have hYE : ∀ y ∈ Y, y.1 ∈ G.E := fun y hy => ((hYm y).mp hy).2.1
  have hYnd : Y.Nodup := hLnd.map endOfKey_injective
  have hKY : Y.map endKey = L := map_endKey_endOfKey L
  have hLlt : ∀ k ∈ L, k < 2 * eCap := fun k hk => ((hLmem k).mp hk).1
  -- the first filter: the tail edges
  have hlt0 : keyFilterMem st.mem pb L 0 = endEdges Y G.E true := by
    rw [← hKY]; exact keyFilterMem_endEdges (b := true) hpres hYc
  obtain ⟨st₁, c₁, hr₁, hB₁, hp₁, hL₁, hag₁, h29₁, ho₁, hc₁⟩ := os_filter (ω := ω) (r := 29)
    (args := [.bin .add (.reg 16) (.const 4), .reg 36, .const 0,
      .bin .add (.reg 14) (.const 5), .reg 19]) hC hflt hB
    (evalArgs_five (Expr.eval_add (Expr.eval_reg_of_eq h16) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq h36) (Expr.eval_const (by omega))
      (Expr.eval_add (Expr.eval_reg_of_eq h14) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq r19))
    hL rfl (fun k hk => by have := hLlt k hk; omega)
    (by omega) (by omega) (by omega) (fun i hi j hj => by omega)
    (fun k hk j hj => by have := hLlt k hk; omega)
    (fun j hj => ⟨by omega, by omega, by omega, by omega⟩)
  rw [hlt0] at hL₁ h29₁
  set Lt := endEdges Y G.E true with hLt
  have hYlen : Y.length = L.length := by rw [hY, List.length_map]
  have hLtle : Lt.length ≤ L.length := hYlen ▸ endEdges_length_le true
  -- the second filter: the head edges
  have hlt1 : keyFilterMem st₁.mem pb L 1 = endEdges Y G.E false := by
    rw [← hKY]; exact keyFilterMem_endEdges (b := false) hB₁.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1 hYc
  have hL1 : ListAt st₁.mem (ep + 4) L := fun i hi => by rw [hag₁ _ (by omega)]; exact hL i hi
  obtain ⟨st₂, c₂, hr₂, hB₂, hp₂, hL₂, hag₂, h30₂, ho₂, hc₂⟩ := os_filter (ω := ω) (r := 30)
    (args := [.bin .add (.reg 16) (.const 4), .reg 36, .const 1,
      .bin .add (.bin .add (.reg 14) (.const 5)) (.reg 29), .reg 19]) hC hflt hB₁
    (evalArgs_five (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₁ 16 (by omega), h16]))
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by rw [ho₁ 36 (by omega), h36])) (Expr.eval_const (by omega))
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₁ 14 (by omega), h14]))
        (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq h29₁) (by omega))
      (Expr.eval_reg_of_eq (by rw [ho₁ 19 (by omega), r19])))
    hL1 rfl (fun k hk => by have := hLlt k hk; omega)
    (by omega) (by omega) (by omega) (fun i hi j hj => by omega)
    (fun k hk j hj => by have := hLlt k hk; omega)
    (fun j hj => ⟨by omega, by omega, by omega, by omega⟩)
  rw [hlt1] at hL₂ h30₂
  set Lh := endEdges Y G.E false with hLh
  have hsum : Lt.length + Lh.length = L.length := by
    rw [hLt, hLh, endEdges_length_add hYE, hY, List.length_map]
  have g₂ : ∀ r, r ≠ 29 → r ≠ 30 → st₂.regs r = st.regs r := fun r a b => by rw [ho₂ r b, ho₁ r a]
  -- the five head words
  obtain ⟨st₃, hr₃, hB₃, hp₃, hm₃, hg₃⟩ := os_store (p := p) (ω := ω) (a := .reg 14)
    (e := .reg 34) hC hB₂ (Expr.eval_reg_of_eq (by rw [g₂ 14 (by omega) (by omega), h14]))
    (Expr.eval_reg_of_eq (by rw [g₂ 34 (by omega) (by omega), h34]))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₄, hr₄, hB₄, hp₄, hm₄, hg₄⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 1)) (e := .reg 21) hC hB₃
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₃, g₂ 14 (by omega) (by omega), h14]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₃, g₂ 21 (by omega) (by omega), h21]))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₅, hr₅, hB₅, hp₅, hm₅, hg₅⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 2)) (e := .reg 22) hC hB₄
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₄, hg₃, g₂ 14 (by omega) (by omega), h14]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₄, hg₃, g₂ 22 (by omega) (by omega), h22]))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₆, hr₆, hB₆, hp₆, hm₆, hg₆⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 3)) (e := .reg 29) hC hB₅
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, hg₃, g₂ 14 (by omega) (by omega), h14]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, hg₃, ho₂ 29 (by omega), h29₁]))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₇, hr₇, hB₇, hp₇, hm₇, hg₇⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 4)) (e := .reg 30) hC hB₆
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₆, hg₅, hg₄, hg₃, g₂ 14 (by omega) (by omega),
      h14])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₆, hg₅, hg₄, hg₃, h30₂]))
    ⟨by omega, by omega, by omega, by omega⟩
  have hag : ∀ y, ¬ (bp ≤ y ∧ y < bp + 5) → st₇.mem y = st₂.mem y := by
    intro y hy
    rw [hm₇, hm₆, hm₅, hm₄, hm₃]
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | omega
  -- the record of the split
  set side := if G'.deg v < G'.deg v' then 0 else 1 with hside
  have hs1 : side ≤ 1 := by rw [hside]; split_ifs <;> omega
  have htag : (if G'.deg v < G'.deg v' then 3 else 2) = 3 - side := by
    rw [hside]; split_ifs <;> rfl
  have hrec : ListAt st₇.mem bp ([3 - side, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) := by
    have hhdr : ListAt st₇.mem bp [3 - side, v, v', Lt.length, Lh.length] := by
      rw [hm₇, hm₆, hm₅, hm₄, hm₃, ← htag]; exact listAt_five
    refine listAt_append.mpr ⟨listAt_append.mpr ⟨hhdr, fun i hi => ?_⟩, fun i hi => ?_⟩
    · simp only [List.length_cons, List.length_nil] at hi ⊢
      rw [hag _ (by omega), hag₂ _ (by omega)]
      exact hL₁ i hi
    · simp only [List.length_append, List.length_cons, List.length_nil] at hi ⊢
      rw [hag _ (by omega), show bp + (5 + Lt.length) + i = bp + 5 + Lt.length + i by omega]
      exact hL₂ i hi
  have hYs : ∀ y : End, y.1 ∈ G.E → (y ∈ Y ↔ G'.src y = if side = 0 then v else v') := by
    intro y hy
    rw [hYm y]
    have hx : (if side = 0 then v else v') = (if G'.deg v < G'.deg v' then v else v') := by
      rw [hside]; split_ifs <;> simp_all
    rw [hx]
    exact ⟨fun h => h.2.2, fun h => ⟨hG.2.2.1 _ hy, hy, h⟩⟩
  have hu := updateAt_split_of_lists (a := bp) hGv hval hYnd side hs1 hYs hrec
  rw [← hLt, ← hLh, hGU] at hu
  have hBb := hB₇.push_batch hu (by omega)
  rw [show 5 + Lt.length + Lh.length = 5 + L.length by omega] at hBb
  -- the edit is still in place
  have hdec₇ : decodeOrdEdit st₇.mem ep = (outSplitEdit G v v' St Sh, 4 + L.length) := by
    rw [decodeOrdEdit_congr (mem := st.mem) (fun i hi => ?_), hdec]
    rw [hdec] at hi
    simp only at hi
    rw [hag _ (by omega), hag₂ _ (by omega), hag₁ _ (by omega)]
  have htag₇ : st₇.mem ep ≤ 4 := by
    by_cases h4 : st₇.mem ep ≤ 4
    · exact h4
    · exfalso
      have h0 : st₇.mem ep ≠ 0 := by omega
      have h12 : ¬ (st₇.mem ep = 1 ∨ st₇.mem ep = 2) := by omega
      have h3 : st₇.mem ep ≠ 3 := by omega
      simp only [decodeOrdEdit, h0, h12, h3, ↓reduceIte] at hdec₇
      have h1 : 3 = 4 + L.length := congrArg Prod.snd hdec₇
      omega
  have hBe := hBb.push_edit hdec₇ htag₇ (by omega)
  -- the two pointers, the two counts and the next record
  have hq₇ : st₇.regs = st₂.regs := by rw [hg₇, hg₆, hg₅, hg₄, hg₃]
  obtain ⟨st₈, hr₈, hm₈, h14₈, ho₈⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 14)
    (e := .bin .add (.reg 14) (.bin .add (.const 5) (.reg 36))) (st := st₇)
    (v := bp + (5 + L.length))
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hq₇, g₂ 14 (by omega) (by omega), h14]))
      (Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by rw [hq₇, g₂ 36 (by omega) (by omega), h36])) (by omega))
      (by omega))
  obtain ⟨st₉, hr₉, hm₉, h17₉, ho₉⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 17)
    (e := .bin .add (.reg 17) (.const 1)) (st := st₈) (v := nb + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₈ 17 (by omega), hq₇,
      g₂ 17 (by omega) (by omega), h17])) (Expr.eval_const (by omega)) hnb)
  obtain ⟨st₁₀, hr₁₀, hm₁₀, h16₁₀, ho₁₀⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 16)
    (e := .bin .add (.reg 16) (.bin .add (.const 4) (.reg 36))) (st := st₉)
    (v := ep + (4 + L.length))
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₉ 16 (by omega), ho₈ 16 (by omega), hq₇,
        g₂ 16 (by omega) (by omega), h16]))
      (Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by rw [ho₉ 36 (by omega), ho₈ 36 (by omega), hq₇,
          g₂ 36 (by omega) (by omega), h36])) (by omega))
      (by omega))
  obtain ⟨st₁₁, hr₁₁, hm₁₁, h18₁₁, ho₁₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 18)
    (e := .bin .add (.reg 18) (.const 1)) (st := st₁₀) (v := ne + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₁₀ 18 (by omega), ho₉ 18 (by omega),
      ho₈ 18 (by omega), hq₇, g₂ 18 (by omega) (by omega), h18])) (Expr.eval_const (by omega)) hne)
  have hm₁₁' : st₁₁.mem = st₇.mem := by rw [hm₁₁, hm₁₀, hm₉, hm₈]
  have hnext : st₁₁.mem (a + 4) = mem₀ (a + 4) := by
    rw [hm₁₁']; exact hBe.mem_eq (by omega) (hafree 4 (by omega))
  obtain ⟨st₁₂, hr₁₂, hm₁₂, h20₁₂, ho₁₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 20)
    (e := .load (.bin .add (.reg 20) (.const 4))) (st := st₁₁) (v := mem₀ (a + 4))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₁₁ 20 (by omega),
      ho₁₀ 20 (by omega), ho₉ 20 (by omega), ho₈ 20 (by omega), hq₇, g₂ 20 (by omega) (by omega),
      h20])) (Expr.eval_const (by omega)) (by omega)) hnext)
  have hm₁₂' : st₁₂.mem = st₇.mem := by rw [hm₁₂, hm₁₁']
  refine ⟨st₁₂, _, runs_seq_normal (runs_seq_normal hr₁ hr₂) (runs_seq_normal
    (runs_seq_normal hr₃ (runs_seq_normal hr₄ (runs_seq_normal hr₅ (runs_seq_normal hr₆ hr₇))))
    (runs_seq_normal (runs_seq_normal hr₈ hr₉) (runs_seq_normal (runs_seq_normal hr₁₀ hr₁₁) hr₁₂))),
    by rw [hm₁₂']; exact hBe, by rw [hm₁₂', hp₇, hp₆, hp₅, hp₄, hp₃, hp₂, hp₁], ?_, ?_, ?_, ?_, ?_,
    h20₁₂, ?_⟩
  · intro r a b c d e f g
    rw [ho₁₂ r e, ho₁₁ r d, ho₁₀ r b, ho₉ r c, ho₈ r a, hq₇, g₂ r f g]
  · rw [ho₁₂ 14 (by omega), ho₁₁ 14 (by omega), ho₁₀ 14 (by omega), ho₉ 14 (by omega), h14₈]
  · rw [ho₁₂ 16 (by omega), ho₁₁ 16 (by omega), h16₁₀]
  · rw [ho₁₂ 17 (by omega), ho₁₁ 17 (by omega), ho₁₀ 17 (by omega), h17₉]
  · rw [ho₁₂ 18 (by omega), h18₁₁]
  · simp only [argsSize, Expr.size, List.map, List.sum_cons, List.sum_nil] at hc₁ hc₂ ⊢
    omega

end MinCostFlow.SparseCore.Program
