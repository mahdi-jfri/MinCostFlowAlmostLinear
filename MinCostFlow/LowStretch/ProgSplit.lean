module

public import MinCostFlow.LowStretch.ProgSplitDef

/-!
# The split walk as a program

`splitP bF` runs the split walk of `ProgSplitMath` with the memory layout of `ProgSplitDef`. It
copies the `θ`-nodes to the stack, then repeats: pop a node `u`; if `u` is a vertex or its weight
is below `x`, write it to the finished column; otherwise write it to the split column, push its
two children, and relabel the leaves of its light child with `fillAtP` (at `bF`). It returns the
number of split nodes.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

/-- The address `A + 3 · (register i)`. -/
def spCell (i : ℕ) : Expr := .bin .add (.reg 8) (.bin .mul (.const 3) (.reg i))

/-- The address `A + 3 · (register i) + off`. -/
def spCellOff (i off : ℕ) : Expr := .bin .add (spCell i) (.const off)

/-- Copy the `θ`-nodes to the stack column. -/
def spCopy : Stmt := forRange 19 (.const 0) (.reg 10) (.store (spCell 19) (.load (.bin .add (.reg 9) (.reg 19))))

/-- Finish the node `u` (register `15`). -/
def spKeep : Stmt :=
  .seq (.store (spCellOff 13 1) (.reg 15)) (.assign 13 (.bin .add (.reg 13) (.const 1)))

/-- Split the node `u` (register `15`). -/
def spSplit (bF : ℕ) : Stmt :=
  .seq (.assign 16 (.load (.bin .add (.reg 0) (.reg 15))))
  (.seq (.assign 17 (.load (.bin .add (.reg 1) (.reg 15))))
  (.seq (.store (spCellOff 14 2) (.reg 15))
  (.seq (.assign 14 (.bin .add (.reg 14) (.const 1)))
  (.seq (.store (spCell 12) (.reg 17))
  (.seq (.store (spCellOff 12 3) (.reg 16))
  (.seq (.assign 12 (.bin .add (.reg 12) (.const 2)))
  (.seq (.cond (.bin .lt (.load (.bin .add (.reg 3) (.reg 16))) (.load (.bin .add (.reg 3) (.reg 17))))
      (.assign 18 (.reg 16)) (.assign 18 (.reg 17)))
  (.call 20 bF [.reg 5, .reg 6, .load (.bin .add (.reg 4) (.reg 18)),
      .bin .add (.load (.bin .add (.reg 4) (.reg 18))) (.load (.bin .add (.reg 3) (.reg 18))),
      .reg 18]))))))))

/-- One step of the walk. -/
def spBody (bF : ℕ) : Stmt :=
  .seq (.assign 12 (.bin .sub (.reg 12) (.const 1)))
  (.seq (.assign 15 (.load (spCell 12)))
  (.cond (.bin .lt (.reg 15) (.reg 7)) spKeep
    (.cond (.bin .lt (.load (.bin .add (.reg 2) (.reg 15))) (.reg 11)) spKeep (spSplit bF))))

/-- `splitP bF` with `args = SplitL.args`. -/
def splitP (bF : ℕ) : Stmt :=
  .seq spCopy (.seq (.assign 12 (.reg 10)) (.seq (.assign 13 (.const 0))
    (.seq (.assign 14 (.const 0)) (.seq (.loop (.bin .lt (.const 0) (.reg 12)) (spBody bF))
      (.ret (.reg 14))))))

theorem splitP_noRand (bF : ℕ) : (splitP bF).NoRand := by
  simp [splitP, spCopy, spBody, spKeep, spSplit, forRange, forUp, Stmt.NoRand]

/-- The registers that hold the arguments. -/
def SplR (E : SplitL) (s : State) : Prop :=
  s.regs 0 = E.CH1 ∧ s.regs 1 = E.CH2 ∧ s.regs 2 = E.MW ∧ s.regs 3 = E.SZ ∧ s.regs 4 = E.LO ∧
    s.regs 5 = E.ORDL ∧ s.regs 6 = E.LAB ∧ s.regs 7 = E.n ∧ s.regs 8 = E.A ∧ s.regs 9 = E.NA ∧
    s.regs 10 = E.len0 ∧ s.regs 11 = E.x

theorem SplR.upd {E : SplitL} {s : State} (h : SplR E s) {r : ℕ} (hr : 12 ≤ r) (v : ℕ) :
    SplR E { s with regs := Function.update s.regs r v } := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.update_apply] <;> rwa [ite_eq_right (by omega)]

theorem SplR.mem {E : SplitL} {s : State} (h : SplR E s) (M : ℕ → ℕ) :
    SplR E { s with mem := M } := h

variable {w : ℕ} {p : Program} {T : KT} {G : PG} {r : Cl} {x : ℕ} {E : SplitL} {mem0 : ℕ → ℕ}

/-- The loop invariant for the walk state `(st, no, sp)`. -/
def SplI (T : KT) (G : PG) (r : Cl) (x : ℕ) (E : SplitL) (mem0 : ℕ → ℕ)
    (a : List ℕ × List ℕ × List ℕ) (s : State) : Prop :=
  SplR E s ∧ s.regs 12 = a.1.length ∧ s.regs 13 = a.2.1.length ∧ s.regs 14 = a.2.2.length ∧
    SplitMem T G r x E mem0 a.1 a.2.1 a.2.2 s.mem

open Classical in
/-- The cost of one step. -/
noncomputable def spStepCost (T : KT) (G : PG) (x u : ℕ) : ℕ :=
  if T.SplitsAt G x u then 300 + 30 * T.sz G (T.light G u) else 300

/-- Finishing a node. -/
theorem spKeep_runs (P : SplitPre w T G r x E mem0) {u : ℕ} {st no sp : List ℕ} {s : State}
    (hR : SplR E s) (h12 : s.regs 12 = st.length) (h13 : s.regs 13 = no.length)
    (h14 : s.regs 14 = sp.length) (h15 : s.regs 15 = u)
    (S : SplitMem T G r x E mem0 (u :: st) no sp s.mem) (hs : ¬ T.SplitsAt G x u)
    (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω spKeep s o s' c ∧
      (o = .normal ∧ SplI T G r x E mem0 (st, u :: no, sp) s') ∧ c ≤ 30 := by
  have hR' := hR
  rcases E with ⟨CH1, CH2, MW, SZ, LO, ORDL, LAB, n, A, NA, len0, x'⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hR
  dsimp only at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  subst a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have hc := S.count
  have hsp := S.inv.sp_le
  have room := P.room
  have hlab := P.lay_lab
  simp only [List.length_cons] at hc room hlab
  have H := P.H
  have hN := H.ok.n_lt
  refine runs_start_le ?_
  dsimp only [spKeep, spCell, spCellOff]
  wram_run
  · refine ⟨rfl, ?_⟩
    unfold SplI
    refine ⟨by simp [SplR], by simp [h12],
      by simp, by simp [h14], S.keep H hs hlab⟩
  · wram_cost

/-- Splitting a node. -/
theorem spSplit_runs {bF : ℕ} (hF : MeetsContract w p bF (fillAtC w))
    (P : SplitPre w T G r x E mem0) {u : ℕ} {st no sp : List ℕ} {s : State}
    (hR : SplR E s) (h12 : s.regs 12 = st.length) (h13 : s.regs 13 = no.length)
    (h14 : s.regs 14 = sp.length) (h15 : s.regs 15 = u)
    (S : SplitMem T G r x E mem0 (u :: st) no sp s.mem) (hs : T.SplitsAt G x u)
    (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω (spSplit bF) s o s' c ∧
      (o = .normal ∧ SplI T G r x E mem0 (T.ch1 u :: T.ch2 u :: st, no, u :: sp) s') ∧
      c ≤ 250 + 30 * T.sz G (T.light G u) := by
  have hR' := hR
  rcases E with ⟨CH1, CH2, MW, SZ, LO, ORDL, LAB, n, A, NA, len0, x'⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hR
  dsimp only at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  subst a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 h15
  have H := P.H
  have h := H.ok
  have hN := h.n_lt
  have hc := S.count
  have hsp := S.inv.sp_le
  have room := P.room
  have hlab := P.lay_lab
  have lay1 := P.lay1
  have lay2 := P.lay2
  have lay4 := P.lay4
  have lay5 := P.lay5
  have layo := P.lay_o
  simp only [SplitL.Lay] at lay1 lay2 lay4 lay5 layo room hlab
  simp only [List.length_cons] at hc
  obtain ⟨huN, -, -⟩ := S.inv.st_ok (s.regs 15) (by simp)
  obtain ⟨-, -, -, hlt1, hlt2⟩ := h.ch (s.regs 15) hs.1 huN
  have hch := P.ch (s.regs 15) hs.1 huN
  have hch1 : s.mem (s.regs 0 + (s.regs 15)) = T.ch1 (s.regs 15) := by
    rw [S.low' H (by dsimp only; omega) (by dsimp only; omega)]; exact hch.1
  have hch2 : s.mem (s.regs 1 + (s.regs 15)) = T.ch2 (s.regs 15) := by
    rw [S.low' H (by dsimp only; omega) (by dsimp only; omega)]; exact hch.2
  have hM2 : ∀ a < s.regs 8, Function.update (Function.update (Function.update s.mem
      (s.regs 8 + 3 * sp.length + 2) (s.regs 15)) (s.regs 8 + 3 * st.length) (T.ch2 (s.regs 15)))
      (s.regs 8 + 3 * st.length + 3) (T.ch1 (s.regs 15)) a = s.mem a := fun a ha => by
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hsz : ∀ c < s.regs 15, Function.update (Function.update (Function.update s.mem
      (s.regs 8 + 3 * sp.length + 2) (s.regs 15)) (s.regs 8 + 3 * st.length) (T.ch2 (s.regs 15)))
      (s.regs 8 + 3 * st.length + 3) (T.ch1 (s.regs 15)) (s.regs 3 + c) = T.sz G c := fun c hc => by
    rw [hM2 _ (by omega), S.low' H (by dsimp only; omega) (by dsimp only; omega)]
    exact P.sz c (by omega)
  have hlo : ∀ c < s.regs 15, Function.update (Function.update (Function.update s.mem
      (s.regs 8 + 3 * sp.length + 2) (s.regs 15)) (s.regs 8 + 3 * st.length) (T.ch2 (s.regs 15)))
      (s.regs 8 + 3 * st.length + 3) (T.ch1 (s.regs 15)) (s.regs 4 + c) = T.lo G c := fun c hc => by
    rw [hM2 _ (by omega), S.low' H (by dsimp only; omega) (by dsimp only; omega)]
    exact P.lo c (by omega)
  have hsz1 := hsz _ hlt1
  have hsz2 := hsz _ hlt2
  have hlo1 := hlo _ hlt1
  have hlo2 := hlo _ hlt2
  have hb1 := P.lo_sz (show T.ch1 (s.regs 15) < T.N by omega)
  have hb2 := P.lo_sz (show T.ch2 (s.regs 15) < T.N by omega)
  have hszR1 : Function.update (Function.update (Function.update s.mem
      (s.regs 8 + 3 * s.regs 14 + 2) (s.regs 15)) (s.regs 8 + 3 * s.regs 12)
      (s.mem (s.regs 1 + s.regs 15))) (s.regs 8 + 3 * s.regs 12 + 3)
      (s.mem (s.regs 0 + s.regs 15)) (s.regs 3 + s.mem (s.regs 0 + s.regs 15)) =
      T.sz G (T.ch1 (s.regs 15)) := by rw [h12, h14, hch1, hch2]; exact hsz1
  have hszR2 : Function.update (Function.update (Function.update s.mem
      (s.regs 8 + 3 * s.regs 14 + 2) (s.regs 15)) (s.regs 8 + 3 * s.regs 12)
      (s.mem (s.regs 1 + s.regs 15))) (s.regs 8 + 3 * s.regs 12 + 3)
      (s.mem (s.regs 0 + s.regs 15)) (s.regs 3 + s.mem (s.regs 1 + s.regs 15)) =
      T.sz G (T.ch2 (s.regs 15)) := by rw [h12, h14, hch1, hch2]; exact hsz2
  have hpreL : ∀ c < T.N, (fillAtC w).pre [s.regs 5, s.regs 6, T.lo G c, T.lo G c + T.sz G c, c]
      (Function.update (Function.update (Function.update s.mem
      (s.regs 8 + 3 * sp.length + 2) (s.regs 15)) (s.regs 8 + 3 * st.length) (T.ch2 (s.regs 15)))
      (s.regs 8 + 3 * st.length + 3) (T.ch1 (s.regs 15))) := by
    intro c hc
    have hfr : ∀ a < s.regs 8, (a < s.regs 6 ∨ s.regs 6 + G.n ≤ a) →
        Function.update (Function.update (Function.update s.mem
        (s.regs 8 + 3 * sp.length + 2) (s.regs 15)) (s.regs 8 + 3 * st.length) (T.ch2 (s.regs 15)))
        (s.regs 8 + 3 * st.length + 3) (T.ch1 (s.regs 15)) a = mem0 a := fun a ha hl => by
      rw [hM2 a ha]; exact S.low' H ha hl
    have hcs := P.lo_sz hc
    refine ⟨_, _, _, _, _, rfl, by omega, by omega, by omega, fun j h1 h2 => ?_,
      fun j j' h1 h2 h3 h4 => ?_⟩
    · have := (mem_lv.mp (P.ordl_mem hfr hc h1 h2)).1
      dsimp only at this ⊢
      omega
    · have := (mem_lv.mp (P.ordl_mem hfr hc h1 h2)).1
      dsimp only at this ⊢
      omega
  by_cases hcmp : T.sz G (T.ch1 (s.regs 15)) < T.sz G (T.ch2 (s.regs 15))
  · have hl : T.light G (s.regs 15) = T.ch1 (s.regs 15) := by
      unfold light; exact ite_eq_right (by omega)
    refine runs_start_le ?_
    dsimp only [spSplit, spCell, spCellOff]
    wram_run
    all_goals (try simp only [h12, h14, hch1, hch2, hsz1, hlo1])
    · omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega
    · exact hpreL _ (by omega)
    · intro v mem' pos' hp
      obtain ⟨hf1, hf2⟩ := hp _ _ _ _ _ rfl
      refine ⟨⟨trivial, ?_⟩, ?_⟩
      · unfold SplI
        refine ⟨by simp [SplR], by simp, by simp [h13], by simp, ?_⟩
        exact S.split P hs (by rw [hl]; exact hf1) (by rw [hl]; exact hf2)
      · rw [hl]
        simp only [fillAtC, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
          Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
        omega
  · have hl : T.light G (s.regs 15) = T.ch2 (s.regs 15) := by
      unfold light; exact ite_eq_left (by omega)
    refine runs_start_le ?_
    dsimp only [spSplit, spCell, spCellOff]
    wram_run
    all_goals (try simp only [h12, h14, hch1, hch2, hsz2, hlo2])
    · omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega
    · exact hpreL _ (by omega)
    · intro v mem' pos' hp
      obtain ⟨hf1, hf2⟩ := hp _ _ _ _ _ rfl
      refine ⟨⟨trivial, ?_⟩, ?_⟩
      · unfold SplI
        refine ⟨by simp [SplR], by simp, by simp [h13], by simp, ?_⟩
        exact S.split P hs (by rw [hl]; exact hf1) (by rw [hl]; exact hf2)
      · rw [hl]
        simp only [fillAtC, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
          Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
        omega

open Classical in
/-- **One step of the walk**: pop `u`, then finish or split it. -/
theorem spBody_runs {bF : ℕ} (hF : MeetsContract w p bF (fillAtC w))
    (P : SplitPre w T G r x E mem0) {u : ℕ} {st no sp : List ℕ} {s0 : State}
    (hI : SplI T G r x E mem0 (u :: st, no, sp) s0) (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω (spBody bF) s0 o s' c ∧
      (o = .normal ∧
        (T.SplitsAt G x u → SplI T G r x E mem0 (T.ch1 u :: T.ch2 u :: st, no, u :: sp) s') ∧
        (¬ T.SplitsAt G x u → SplI T G r x E mem0 (st, u :: no, sp) s')) ∧
      c ≤ spStepCost T G x u := by
  obtain ⟨hR, h12, h13, h14, S⟩ := hI
  have hR' := hR
  rcases E with ⟨CH1, CH2, MW, SZ, LO, ORDL, LAB, n, A, NA, len0, x'⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hR
  dsimp only at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 h12 h13 h14 S
  subst a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have H := P.H
  have h := H.ok
  have hN := h.n_lt
  have hc := S.count
  simp only [List.length_cons] at hc h12
  have hsp := S.inv.sp_le
  have room := P.room
  have lay3 := P.lay3
  have hxn := P.n
  have hxx := P.ex
  have hxw := P.xw
  simp only [SplitL.Lay] at lay3 room hxn hxx hc
  obtain ⟨huN, -, -⟩ := S.inv.st_ok u (by simp)
  have hu : s0.mem (s0.regs 8 + 3 * st.length) = u := by
    have := S.rst
    rw [List.length_cons, rdS_succ] at this
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons.injEq, Nat.add_zero] at this
    exact this.1.symm
  have hmw : s0.mem (s0.regs 2 + u) = T.mw u := by
    rw [S.low' H (by dsimp only; omega) (by dsimp only; omega)]
    exact P.mw u huN
  have hS2 : SplitMem T G r x _ mem0 (u :: st) no sp
      ({ s0 with regs := Function.update (Function.update s0.regs 12 st.length) 15 u } : State).mem :=
    S
  have hR2 := (hR'.upd (s := s0) (show 12 ≤ 12 by omega) st.length).upd
    (show 12 ≤ 15 by omega) u
  refine runs_start_le ?_
  dsimp only [spBody, spCell]
  refine runs_seq_assign_le (v := st.length) (by rw [show st.length = s0.regs 12 - 1 by omega]; eval_expr) ?_
  refine runs_seq_assign_le (v := u) (by eval_expr) ?_
  refine runs_cond_le (by eval_expr) (fun hc1 => ?_) (fun hc1 => ?_)
  · have hun : u < G.n := by
      try simp only [Function.update_apply] at hc1
      split_ifs at hc1 <;> omega
    have hns : ¬ T.SplitsAt G x u := fun hs => by have := hs.1; omega
    obtain ⟨o, s', c, hr, ⟨ho, hI'⟩, hcst⟩ := spKeep_runs (p := p) P hR2 (by simp) (by simp [h13])
      (by simp [h14]) (by simp) hS2 hns ω
    refine ⟨o, s', c, hr, ⟨ho, fun hs => absurd hs hns, fun _ => hI'⟩, ?_⟩
    unfold spStepCost
    rw [ite_eq_right hns]
    simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
    omega
  · refine runs_cond_le (by eval_expr) (fun hc2 => ?_) (fun hc2 => ?_)
    · have hmx : T.mw u < x := by
        try simp only [Function.update_apply] at hc2
        split_ifs at hc2 <;> omega
      have hns : ¬ T.SplitsAt G x u := fun hs => by have := hs.2; omega
      obtain ⟨o, s', c, hr, ⟨ho, hI'⟩, hcst⟩ := spKeep_runs (p := p) P hR2 (by simp)
        (by simp [h13]) (by simp [h14]) (by simp) hS2 hns ω
      refine ⟨o, s', c, hr, ⟨ho, fun hs => absurd hs hns, fun _ => hI'⟩, ?_⟩
      unfold spStepCost
      rw [ite_eq_right hns]
      simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
      omega
    · have hs : T.SplitsAt G x u := by
        try simp only [Function.update_apply] at hc1 hc2
        split_ifs at hc1 hc2
        exact ⟨by omega, by omega⟩
      obtain ⟨o, s', c, hr, ⟨ho, hI'⟩, hcst⟩ := spSplit_runs (p := p) hF P hR2 (by simp)
        (by simp [h13]) (by simp [h14]) (by simp) hS2 hs ω
      refine ⟨o, s', c, hr, ⟨ho, fun _ => hI', fun hn => absurd hs hn⟩, ?_⟩
      unfold spStepCost
      rw [ite_eq_left hs]
      simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
      omega

end MinCostFlow.LowStretch
