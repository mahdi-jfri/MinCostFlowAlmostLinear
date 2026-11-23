module

public import MinCostFlow.LowStretch.ProgSplit

/-!
# The split walk as a program: the whole run

`splitP_runs`: started on memory that meets `SplitPre`, the program `splitP` ends as
`SplitPost` says. It returns the number of split nodes. The split column then holds the nodes of
`KT.splitSet`, the finished column the `x`-nodes of the child, each once, and the labels of the
vertices of the child name the heads of their `x`-nodes. The cost is linear in the number of
`θ`-nodes plus, for each split node, the leaves of its light child.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

variable {w : ℕ} {p : Program} {T : KT} {G : PG} {r : Cl} {x : ℕ} {E : SplitL} {mem0 : ℕ → ℕ}

/-- The measure of the walk: the stack, and twice the nodes still to split. -/
noncomputable def spM (T : KT) (G : PG) (r : Cl) (x : ℕ) (a : List ℕ × List ℕ × List ℕ) : ℕ :=
  a.1.length + 2 * (T.splitSet G r x \ a.2.2.toFinset).card

/-- What the rest of the walk may cost. -/
noncomputable def spRem (T : KT) (G : PG) (r : Cl) (x : ℕ) (a : List ℕ × List ℕ × List ℕ) : ℕ :=
  400 * spM T G r x a + 30 * ∑ u ∈ T.splitSet G r x \ a.2.2.toFinset, T.sz G (T.light G u) + 4

/-- The loop of the walk. -/
def spLoop (bF : ℕ) : Stmt := .loop (.bin .lt (.const 0) (.reg 12)) (spBody bF)

/-- **The loop of the walk** ends with an empty stack. -/
theorem spLoop_triple {bF : ℕ} (hF : MeetsContract w p bF (fillAtC w))
    (P : SplitPre w T G r x E mem0) (a0 : List ℕ × List ℕ × List ℕ) :
    Triple w p (SplI T G r x E mem0 a0) (spLoop bF)
      (normalPost fun s => ∃ no sp, SplI T G r x E mem0 ([], no, sp) s)
      (fun _ => spRem T G r x a0) := by
  have hw : 3 < 2 ^ w := by have := P.room; omega
  refine Triple.loop_inv (spM T G r x) (spRem T G r x)
    (condVal := fun s => if 0 < s.regs 12 then 1 else 0)
    (fun a s _ => by eval_expr) (fun a s hI hc => ?_) (fun a s hI hc => ?_) a0
  · obtain ⟨st, no, sp⟩ := a
    have h12 := hI.2.1
    refine ⟨⟨no, sp, ?_⟩, by simp [spRem]⟩
    have hst : st = [] := by
      dsimp only at h12
      rw [ite_eq_right_iff] at hc
      exact List.eq_nil_of_length_eq_zero (by have := not_lt.mp (fun h => one_ne_zero (hc h)); omega)
    subst hst
    exact hI
  · obtain ⟨st, no, sp⟩ := a
    have h12 := hI.2.1
    dsimp only at h12
    obtain ⟨u, st, rfl⟩ : ∃ u st', st = u :: st' := by
      cases st with
      | nil => simp at h12; rw [h12] at hc; simp at hc
      | cons u st' => exact ⟨u, st', rfl⟩
    classical
    refine ⟨spStepCost T G x u, fun s ω hs => ?_⟩
    subst hs
    obtain ⟨o, s', c, hr, ⟨ho, hsp, hkp⟩, hcst⟩ := spBody_runs hF P hI ω
    subst ho
    refine ⟨.normal, s', c, hr, ?_, hcst⟩
    have I := hI.2.2.2.2
    by_cases hs : T.SplitsAt G x u
    · have I' := (hsp hs).2.2.2.2
      have hmem : u ∈ T.splitSet G r x \ sp.toFinset := by
        refine Finset.mem_sdiff.mpr ⟨I'.inv.sp_mem u (by simp), fun h => ?_⟩
        exact (List.nodup_cons.mp I'.inv.sp_nodup).1 (List.mem_toFinset.mp h)
      have e : T.splitSet G r x \ (u :: sp).toFinset = (T.splitSet G r x \ sp.toFinset).erase u := by
        rw [List.toFinset_cons, Finset.sdiff_insert]
      have hcard := Finset.card_erase_of_mem hmem
      have hsum := Finset.add_sum_erase _ (fun v => T.sz G (T.light G v)) hmem
      have hpos := Finset.card_pos.mpr ⟨u, hmem⟩
      refine ⟨_, hsp hs, ?_, ?_⟩
      · simp only [spM, List.length_cons, e, hcard]; omega
      · simp only [spRem, spM, List.length_cons, e, hcard, spStepCost, hs, ↓reduceIte,
          Expr.size_bin, Expr.size_const, Expr.size_reg]
        rw [← hsum]
        have : 400 * (st.length + 1 + 1 + 2 * ((T.splitSet G r x \ sp.toFinset).card - 1)) + 400 =
            400 * (st.length + 1 + 2 * (T.splitSet G r x \ sp.toFinset).card) := by
          have := hpos; omega
        omega
    · refine ⟨_, hkp hs, ?_, ?_⟩
      · simp only [spM, List.length_cons]; omega
      · simp only [spRem, spM, List.length_cons, spStepCost, hs, ↓reduceIte, Expr.size_bin,
          Expr.size_const, Expr.size_reg]
        omega

/-- The memory after the copy meets the invariant with the `θ`-nodes on the stack. -/
theorem SplitMem.init (P : SplitPre w T G r x E mem0) {M : ℕ → ℕ}
    (hcp : ∀ i < E.len0, M (E.A + 3 * i) = mem0 (E.NA + i))
    (hfr : ∀ a, (∀ i < E.len0, a ≠ E.A + 3 * i) → M a = mem0 a) :
    SplitMem T G r x E mem0 (E.nodes mem0).reverse [] [] M := by
  have H := P.H
  have hlab := P.lay_lab
  have hlen : (E.nodes mem0).length = E.len0 := by simp [SplitL.nodes]
  have hL : ∀ k ∈ (E.nodes mem0).reverse, ∃ v ∈ r.X, k = T.top r.θ v := fun k hk =>
    P.nd_top k (List.mem_reverse.mp hk)
  refine ⟨?_, by simp [rdS], by simp [rdS], SplitInv.init H hL
    (fun v hv => List.mem_reverse.mpr (P.top_nd v hv)) (List.nodup_reverse.mpr P.nd), ?_,
    by simp [hlen], fun a ha _ => hfr a fun i _ => by omega, fun a ha => hfr a fun i hi => by
      simp only [List.length_nil, Nat.add_zero] at ha; omega⟩
  · rw [List.length_reverse, hlen, List.reverse_inj]
    simp only [SplitL.nodes, rdS, Nat.add_zero]
    exact List.map_congr_left fun i hi => (hcp i (List.mem_range.mp hi)).symm
  · refine (LabInv.init H hL P.lab).congr fun v hv => ?_
    have := H.vx v hv
    exact hfr _ fun i _ => by omega

/-- **The postcondition of `splitP`**, with returned value `v`, final memory `mem'` and cost
`cost`. -/
def SplitPost (T : KT) (G : PG) (r : Cl) (x : ℕ) (E : SplitL) (mem0 : ℕ → ℕ) (v : ℕ)
    (mem' : ℕ → ℕ) (cost : ℕ) : Prop :=
  (rdS mem' E.A 2 v).toFinset = T.splitSet G r x ∧ (rdS mem' E.A 2 v).Nodup ∧ v ≤ T.N ∧
    (∀ k, k ∈ rdS mem' E.A 1 (E.len0 + v) ↔ ∃ a ∈ r.X, k = T.top x a) ∧
    (rdS mem' E.A 1 (E.len0 + v)).Nodup ∧
    (∀ a ∈ r.X, mem' (E.LAB + a) = T.hd G (T.top x a)) ∧
    (∀ a < E.A, (∀ b ∈ r.X, a ≠ E.LAB + b) → mem' a = mem0 a) ∧
    (∀ a, E.A + 3 * (E.len0 + v) ≤ a → mem' a = mem0 a) ∧
    cost ≤ 500 * (E.len0 + 1) + 800 * ∑ u ∈ T.splitSet G r x, (T.sz G (T.light G u) + 1)

/-- The end of the walk gives the postcondition. -/
theorem SplitPost.of_inv (P : SplitPre w T G r x E mem0) {no sp : List ℕ} {M : ℕ → ℕ} {c : ℕ}
    (S : SplitMem T G r x E mem0 [] no sp M)
    (hc : c ≤ 500 * (E.len0 + 1) + 800 * ∑ u ∈ T.splitSet G r x, (T.sz G (T.light G u) + 1)) :
    SplitPost T G r x E mem0 sp.length M c := by
  have H := P.H
  have hcount := S.count
  simp only [List.length_nil, Nat.zero_add] at hcount
  have esp : rdS M E.A 2 sp.length = sp.reverse := by
    have := congrArg List.reverse S.rsp; rw [List.reverse_reverse] at this; exact this.symm
  have eno : rdS M E.A 1 (E.len0 + sp.length) = no.reverse := by
    have := congrArg List.reverse S.rno; rw [List.reverse_reverse, hcount] at this
    exact this.symm
  refine ⟨?_, ?_, S.inv.sp_le, fun k => ?_, ?_, ?_, S.low, S.high, hc⟩
  · rw [esp, List.toFinset_reverse]; exact S.inv.sp_toFinset
  · rw [esp]; exact List.nodup_reverse.mpr S.inv.sp_nodup
  · rw [eno, List.mem_reverse]; exact S.inv.no_iff H k
  · rw [eno]; exact List.nodup_reverse.mpr (S.inv.no_nodup H)
  · exact LabInv.done H S.inv S.lab

/-- **The split walk.** Started on memory that meets `SplitPre`, `splitP` ends as `SplitPost`
says. -/
theorem splitP_runs {bF : ℕ} (hF : MeetsContract w p bF (fillAtC w))
    (P : SplitPre w T G r x E mem0) (pos : ℕ) (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω (splitP bF) (startState E.args mem0 pos) o s' c ∧
      SplitPost T G r x E mem0 o.value s'.mem c := by
  have H := P.H
  have room := P.room
  have hna := P.lay_na
  have hw : 3 < 2 ^ w := by omega
  have hR0 : SplR E (startState E.args mem0 pos) := by
    simp [SplR, startState, SplitL.args]
  -- the copy of the `θ`-nodes
  have hcopy := Triple.forRange_const (w := w) (p := p) (r := 19) (lo := .const 0) (hi := .reg 10)
    (body := .store (spCell 19) (.load (.bin .add (.reg 9) (.reg 19))))
    (P := fun s => s = startState E.args mem0 pos)
    (Inv := fun j s => SplR E s ∧ s.regs 19 = j ∧ (∀ i < j, s.mem (E.A + 3 * i) = mem0 (E.NA + i)) ∧
      ∀ a, (∀ i < j, a ≠ E.A + 3 * i) → s.mem a = mem0 a)
    12 0 E.len0 (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun s hs => by
      subst hs
      exact ⟨by eval_expr, hR0.upd (by omega) _, by simp, fun i hi => by omega, fun a _ => rfl⟩)
    (fun _ s _ _ hI => hI.2.1)
    (fun _ s _ _ hI => by have := hI.1.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun j _ hj s ω hI => by
      obtain ⟨hR, h19, hcp, hfr⟩ := hI
      have hR' := hR
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hR
      have e : s.mem (E.NA + j) = mem0 (E.NA + j) := hfr _ fun i _ => by omega
      have b1 : s.regs 9 + s.regs 19 < 2 ^ w := by rw [a9, h19]; omega
      have b2 : s.regs 8 + 3 * s.regs 19 < 2 ^ w := by rw [a8, h19]; omega
      refine runs_start_le ?_
      dsimp only [spCell]
      wram_run
      · refine ⟨⟨hR'.mem _ |>.upd (by omega) _, by simp, fun i hi => ?_, fun a ha => ?_⟩, h19⟩
        · simp only [e]
          by_cases hij : i = j
          · subst hij; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega)]; exact hcp i (by omega)
        · dsimp only
          rw [Function.update_of_ne (ha j (by omega))]
          exact hfr a fun i hi => ha i (by omega)
      · wram_cost)
  have hS := Finset.sum_add_distrib (s := T.splitSet G r x) (f := fun u => T.sz G (T.light G u))
    (g := fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hS
  have main : ∃ o s' c, Runs w p ω (splitP bF) (startState E.args mem0 pos) o s' c ∧
      (∃ no sp, o = .returned sp.length ∧ SplitMem T G r x E mem0 [] no sp s'.mem) ∧
      c ≤ 500 * (E.len0 + 1) + 800 * ∑ u ∈ T.splitSet G r x, (T.sz G (T.light G u) + 1) := by
    refine runs_start_le ?_
    dsimp only [splitP]
    refine runs_seq_triple_le hcopy rfl (fun s1 hI => ?_)
    obtain ⟨hR1, -, hcp, hfr⟩ := hI
    have S0 := SplitMem.init P hcp hfr
    have a10 := hR1.2.2.2.2.2.2.2.2.2.2.1
    refine runs_seq_assign_le (v := E.len0) (by eval_expr) ?_
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    refine runs_seq_triple_le (spLoop_triple hF P ((E.nodes mem0).reverse, [], [])) ?_
      (fun s2 hq => ?_)
    · unfold SplI
      exact ⟨((hR1.upd (by omega) _).upd (by omega) _).upd (by omega) _, by simp [SplitL.nodes],
        by simp, by simp, S0⟩
    obtain ⟨no, sp, hI2⟩ := hq
    have h14 := hI2.2.2.2.1
    refine runs_ret_le (v := sp.length) (by eval_expr) ⟨no, sp, rfl, hI2.2.2.2.2⟩ ?_
    simp only [spRem, spM, List.toFinset_nil, Finset.sdiff_empty, List.length_reverse,
      Expr.size_reg, Expr.size_const]
    have : (E.nodes mem0).length = E.len0 := by simp [SplitL.nodes]
    rw [this]
    rw [hS]
    omega
  obtain ⟨o, s', c, hr, ⟨no, sp, rfl, S⟩, hc⟩ := main
  exact ⟨_, s', c, hr, SplitPost.of_inv P S hc⟩

end MinCostFlow.LowStretch
