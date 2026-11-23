module

public import MinCostFlow.LowStretch.ProgPArcs

/-!
# The highway slots of the petal graph

Each node `u < s` of the petal graph gets one extra item, its highway slot, at item number
`M0 + u`, after the `M0` pair items. Its tail is `u` and its head is the dummy node `s`, so the
slot is off. Its cost and class are those of the parent arc of `u` in the first run of Dijkstra
(array `PC` holds the parent arcs, arrays `CS1` and `CL1` the costs and classes of the first arc
graph). Along a path of the shortest path tree these are the lengths of the highway pairs. The
center `x0` has no parent, and its slot gets cost and class `0` (`slotF_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The addresses and numbers that `slotF` uses. -/
structure SF where
  M0 : ℕ
  s : ℕ
  x0 : ℕ
  PC : ℕ
  CS1 : ℕ
  CL1 : ℕ
  TL : ℕ
  HDt : ℕ
  CSt : ℕ
  CLt : ℕ

namespace SF

variable (F : SF) (mem : ℕ → ℕ)

def args : List ℕ := [F.M0, F.s, F.x0, F.PC, F.CS1, F.CL1, F.TL, F.HDt, F.CSt, F.CLt]

theorem eq_of_args {F F' : SF} (h : F.args = F'.args) : F' = F := by
  cases F; cases F'; simp only [SF.args, List.cons.injEq] at h
  simp_all

/-- The cost of the slot of `u`. -/
def sc (u : ℕ) : ℕ := if u = F.x0 then 0 else mem (F.CS1 + mem (F.PC + u))
/-- The class of the slot of `u`. -/
def sk (u : ℕ) : ℕ := if u = F.x0 then 0 else mem (F.CL1 + mem (F.PC + u))

/-- The memory after the slots of the nodes below `i`. -/
def Done (M : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ u < i, M (F.TL + F.M0 + u) = u ∧ M (F.HDt + F.M0 + u) = F.s ∧
    M (F.CSt + F.M0 + u) = F.sc mem u ∧ M (F.CLt + F.M0 + u) = F.sk mem u

/-- The written cells. -/
def Out (a : ℕ) : Prop :=
  (F.TL + F.M0 ≤ a ∧ a < F.TL + F.M0 + F.s) ∨ (F.HDt + F.M0 ≤ a ∧ a < F.HDt + F.M0 + F.s) ∨
    (F.CSt + F.M0 ≤ a ∧ a < F.CSt + F.M0 + F.s) ∨ (F.CLt + F.M0 ≤ a ∧ a < F.CLt + F.M0 + F.s)

/-- The precondition of `slotF`: the parent arcs are below `MM`, the read arrays lie below the
written ones, and the written ranges do not overlap. -/
structure Pre (w : ℕ) (MM : ℕ) : Prop where
  pc : ∀ u < F.s, u ≠ F.x0 → mem (F.PC + u) < MM
  rPC : F.PC + F.s ≤ F.TL
  rCS : F.CS1 + MM ≤ F.TL
  rCL : F.CL1 + MM ≤ F.TL
  l1 : F.TL + F.M0 + F.s ≤ F.HDt
  l2 : F.HDt + F.M0 + F.s ≤ F.CSt
  l3 : F.CSt + F.M0 + F.s ≤ F.CLt
  l4 : F.CLt + F.M0 + F.s < 2 ^ w
  hw : 1 < 2 ^ w

end SF

/-- One node of `slotF`: the four stores, given by their addresses and values. -/
theorem SF.Done.step {F : SF} {mem M : ℕ → ℕ} {i : ℕ} (hd : F.Done mem M i)
    (l1 : F.TL + F.M0 + F.s ≤ F.HDt) (l2 : F.HDt + F.M0 + F.s ≤ F.CSt)
    (l3 : F.CSt + F.M0 + F.s ≤ F.CLt) (hi : i < F.s)
    {A1 A2 A3 A4 V1 V2 V3 V4 : ℕ}
    (e1 : A1 = F.TL + F.M0 + i) (f1 : V1 = i)
    (e2 : A2 = F.HDt + F.M0 + i) (f2 : V2 = F.s)
    (e3 : A3 = F.CSt + F.M0 + i) (f3 : V3 = F.sc mem i)
    (e4 : A4 = F.CLt + F.M0 + i) (f4 : V4 = F.sk mem i) :
    F.Done mem (Function.update (Function.update (Function.update (Function.update M A1 V1)
      A2 V2) A3 V3) A4 V4) (i + 1) ∧
    ∀ a, ¬ F.Out a → Function.update (Function.update (Function.update (Function.update M A1 V1)
      A2 V2) A3 V3) A4 V4 a = M a := by
  subst A1 A2 A3 A4 V1 V2 V3 V4
  refine ⟨fun j hj => ?_, fun a ha => ?_⟩
  · by_cases e : j = i
    · subst e
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · obtain ⟨d1, d2, d3, d4⟩ := hd j (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp (disch := omega) only [Function.update_of_ne] <;> assumption
  · unfold SF.Out at ha
    simp (disch := omega) only [Function.update_of_ne]

/-- The body of `slotF`, for node `u` in register `10`. -/
def slotFB : Stmt :=
  .seq (.cond (.bin .eq (.reg 10) (.reg 2))
      (.seq (.assign 11 (.const 0)) (.assign 12 (.const 0)))
      (.seq (.assign 13 (.load (.bin .add (.reg 3) (.reg 10))))
      (.seq (.assign 11 (.load (.bin .add (.reg 4) (.reg 13))))
        (.assign 12 (.load (.bin .add (.reg 5) (.reg 13)))))))
  (.seq (.store (.bin .add (.bin .add (.reg 6) (.reg 0)) (.reg 10)) (.reg 10))
  (.seq (.store (.bin .add (.bin .add (.reg 7) (.reg 0)) (.reg 10)) (.reg 1))
  (.seq (.store (.bin .add (.bin .add (.reg 8) (.reg 0)) (.reg 10)) (.reg 11))
    (.store (.bin .add (.bin .add (.reg 9) (.reg 0)) (.reg 10)) (.reg 12)))))

/-- `slotF` with `args = F.args`. -/
def slotF : Stmt := .seq (forRange 10 (.const 0) (.reg 1) slotFB) (.ret (.const 0))

theorem slotF_noRand : slotF.NoRand := by
  simp [slotF, slotFB, forRange, forUp, Stmt.NoRand]

/-- The contract of `slotF`. -/
def slotFC (w : ℕ) : Contract where
  pre args mem := ∃ F : SF, ∃ MM, args = F.args ∧ F.Pre mem w MM
  post args mem _ mem' := ∀ F : SF, args = F.args →
    F.Done mem mem' F.s ∧ ∀ a, ¬ F.Out a → mem' a = mem a
  cost args _ := 100 * args.getD 1 0 + 20

theorem slotF_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [slotF]) :
    MeetsContract w p b (slotFC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨F, MM, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some slotF := hp 0 (by simp)
  clear hp
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4
  have rPC := h.rPC; have rCS := h.rCS; have rCL := h.rCL
  have hw1 : 1 < 2 ^ w := h.hw
  have hwA : ∀ a ∈ F.args, a < 2 ^ w := hwords
  simp only [SF.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hwA
  obtain ⟨wM0, ws, wx0, wPC, wCS, wCL, wTL, wHD, wCSt, wCLt⟩ := hwA
  let R : State → Prop := fun st => st.regs 0 = F.M0 ∧ st.regs 1 = F.s ∧ st.regs 2 = F.x0 ∧
    st.regs 3 = F.PC ∧ st.regs 4 = F.CS1 ∧ st.regs 5 = F.CL1 ∧ st.regs 6 = F.TL ∧
    st.regs 7 = F.HDt ∧ st.regs 8 = F.CSt ∧ st.regs 9 = F.CLt
  have hRu : ∀ st r v, R st → 10 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  let I : ℕ → State → Prop := fun i st => R st ∧ st.regs 10 = i ∧ F.Done mem st.mem i ∧
    ∀ a, ¬ F.Out a → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 10) (lo := .const 0) (hi := .reg 1)
    (body := slotFB) (P := fun st => R st ∧ st.mem = mem) (Inv := I) 80 0 F.s
    (Nat.zero_le _) hw1 (fun _ => ws)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hRu st 10 0 hr (by omega), by simp,
      fun j hj => absurd hj (by omega), fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h10, hdone, hfr⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hr
      have nOut : ∀ a, a < F.TL → ¬ F.Out a := by
        intro a ha ho; unfold SF.Out at ho; omega
      have hRn : ∀ st' : State, (∀ r < 10, st'.regs r = st.regs r) → R st' := fun st' hs =>
        ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
          (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, (hs 5 (by omega)).trans a5,
          (hs 6 (by omega)).trans a6, (hs 7 (by omega)).trans a7, (hs 8 (by omega)).trans a8,
          (hs 9 (by omega)).trans a9⟩
      have key := SF.Done.step hdone l1 l2 l3 hi (M := st.mem) (A1 := _) (A2 := _) (A3 := _)
        (A4 := _) (V1 := _) (V2 := _) (V3 := _) (V4 := _) rfl rfl rfl rfl rfl rfl rfl rfl
      by_cases hx : i = F.x0
      · have e3 : F.sc mem i = 0 := by simp [SF.sc, hx]
        have e4 : F.sk mem i = 0 := by simp [SF.sk, hx]
        refine runs_start_le ?_
        dsimp only [slotFB]
        wram_run
        all_goals first
          | wram_cost
          | omega
          | (refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
              by simp, ?_, fun a ha => ?_⟩, by simp [h10]⟩
             · convert key.1 using 2 <;> simp [e3, e4, a0, a1, a6, a7, a8, a9, h10]
             · refine Eq.trans ?_ ((key.2 a ha).trans (hfr a ha))
               congr 1 <;> simp [e3, e4, a0, a1, a6, a7, a8, a9, h10])
      · have hpc := h.pc i hi hx
        have eP : st.mem (F.PC + i) = mem (F.PC + i) := hfr _ (nOut _ (by omega))
        have eC : st.mem (F.CS1 + mem (F.PC + i)) = mem (F.CS1 + mem (F.PC + i)) :=
          hfr _ (nOut _ (by omega))
        have eK : st.mem (F.CL1 + mem (F.PC + i)) = mem (F.CL1 + mem (F.PC + i)) :=
          hfr _ (nOut _ (by omega))
        have e3 : F.sc mem i = mem (F.CS1 + mem (F.PC + i)) := by simp [SF.sc, hx]
        have e4 : F.sk mem i = mem (F.CL1 + mem (F.PC + i)) := by simp [SF.sk, hx]
        have b1 : st.regs 4 + st.mem (st.regs 3 + st.regs 10) < 2 ^ w := by
          rw [a4, a3, h10, eP]; omega
        have b2 : st.regs 5 + st.mem (st.regs 3 + st.regs 10) < 2 ^ w := by
          rw [a5, a3, h10, eP]; omega
        refine runs_start_le ?_
        dsimp only [slotFB]
        wram_run
        all_goals first
          | wram_cost
          | omega
          | (refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
              by simp, ?_, fun a ha => ?_⟩, by simp [h10]⟩
             · convert key.1 using 2 <;> simp [e3, e4, a0, a1, a3, a4, a5, a6, a7, a8, a9, h10,
                 eP, eC, eK]
             · refine Eq.trans ?_ ((key.2 a ha).trans (hfr a ha))
               congr 1 <;> simp [e3, e4, a0, a1, a3, a4, a5, a6, a7, a8, a9, h10, eP, eC, eK]))
  refine ⟨slotF, hproc, ?_⟩
  dsimp only [slotF]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    (fun st hI => ?_)
  obtain ⟨-, -, hdone, hfr⟩ := hI
  refine runs_ret_le (by eval_expr) (fun F' he => ?_) ?_
  · obtain rfl := SF.eq_of_args he
    exact ⟨hdone, hfr⟩
  · simp only [slotFC, SF.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega

end MinCostFlow.LowStretch
