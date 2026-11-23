module

public import MinCostFlow.LowStretch.ProgSlot

/-!
# After a petal: carve its nodes and turn the slots off

After a petal search, the settled list `SL[0], …, SL[ns - 1]` is the petal. `pfin` marks each of
its nodes as not allowed (`OK[v] := os + 1`), so that later searches skip them, and turns the
slot of each of them off (`HD[HI[v] - 1] := S`). The slots that were on are those of the
settled highway nodes and of the highway node at the pointer `CTL + 2`, so `pfin` also turns off
the slot of the pointer node when it is a node (`pfin_spec`). The cost is linear in `ns`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The addresses and numbers that `pfin` uses. -/
structure FF where
  OK : ℕ
  os : ℕ
  HI : ℕ
  HD : ℕ
  SL : ℕ
  CTL : ℕ
  S : ℕ

namespace FF

variable (F : FF) (mem : ℕ → ℕ)

def args : List ℕ := [F.OK, F.os, F.HI, F.HD, F.SL, F.CTL, F.S]

theorem eq_of_args {F F' : FF} (h : F.args = F'.args) : F' = F := by
  cases F; cases F'; simp only [FF.args, List.cons.injEq] at h
  simp_all

/-- The number of settled nodes. -/
def ns : ℕ := mem (F.CTL + 1)
/-- Settled node `i`. -/
def v (i : ℕ) : ℕ := mem (F.SL + i)
/-- The slot cell of node `u`. -/
def sa (u : ℕ) : ℕ := F.HD + (mem (F.HI + u) - 1)
/-- The pointer node. -/
def pp : ℕ := mem (F.CTL + 2)

/-- The cells written for the settled nodes below `i`. -/
def Wr (i x : ℕ) : Prop := ∃ j < i, x = F.OK + F.v mem j ∨ x = F.sa mem (F.v mem j)

/-- The memory after the settled nodes below `i`. -/
def Done (M : ℕ → ℕ) (i : ℕ) : Prop :=
  (∀ j < i, M (F.OK + F.v mem j) = F.os + 1 ∧ M (F.sa mem (F.v mem j)) = F.S) ∧
    ∀ x, ¬ F.Wr mem i x → M x = mem x

/-- The precondition of `pfin`: the settled nodes and the pointer node are below `NN`, the slot
cells lie below `HD + MM`, and the arrays are in the order `HI`, `HD`, `OK`, then the cells of the
search. -/
structure Pre (w : ℕ) (NN MM : ℕ) : Prop where
  vN : ∀ i < F.ns mem, F.v mem i < NN
  pN : F.pp mem < F.S → F.pp mem < NN
  hiM : ∀ u < NN, mem (F.HI + u) ≤ MM
  l1 : F.HI + NN ≤ F.HD
  l2 : F.HD + MM < F.OK
  l3 : F.OK + NN ≤ F.CTL
  l4 : F.CTL + 3 ≤ F.SL
  l5 : F.SL + F.ns mem < 2 ^ w
  wos : F.os + 1 < 2 ^ w
  wS : F.S < 2 ^ w

end FF

/-- One settled node: the two stores. -/
theorem FF.Done.step {w : ℕ} {F : FF} {mem M : ℕ → ℕ} {i NN MM : ℕ} (hd : F.Done mem M i)
    (h : F.Pre mem w NN MM) (hi : i < F.ns mem) :
    F.Done mem (Function.update (Function.update M (F.OK + F.v mem i) (F.os + 1))
      (F.sa mem (F.v mem i)) F.S) (i + 1) := by
  have hv := h.vN i hi
  have hh := h.hiM _ hv
  have l1 := h.l1; have l2 := h.l2
  have hne : ∀ u v, u < NN → v < NN → F.sa mem u ≠ F.OK + v := by
    intro u v hu _; have := h.hiM u hu; unfold FF.sa; omega
  refine ⟨fun j hj => ?_, fun x hx => ?_⟩
  · have hvj : F.v mem j < NN := h.vN j (by omega)
    by_cases hji : j = i
    · subst hji
      refine ⟨?_, Function.update_self _ _ _⟩
      rw [Function.update_of_ne (hne _ _ hv hvj).symm, Function.update_self]
    have hj' : j < i := by omega
    constructor
    · rw [Function.update_of_ne (hne _ _ hv hvj).symm]
      by_cases e : F.OK + F.v mem j = F.OK + F.v mem i
      · rw [e, Function.update_self]
      · rw [Function.update_of_ne e]; exact (hd.1 j hj').1
    · by_cases e : F.sa mem (F.v mem j) = F.sa mem (F.v mem i)
      · rw [e, Function.update_self]
      · rw [Function.update_of_ne e, Function.update_of_ne (hne _ _ hvj hv)]
        exact (hd.1 j hj').2
  · have h1 : x ≠ F.sa mem (F.v mem i) := fun e => hx ⟨i, by omega, Or.inr e⟩
    have h2 : x ≠ F.OK + F.v mem i := fun e => hx ⟨i, by omega, Or.inl e⟩
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    exact hd.2 x fun ⟨j, hj, he⟩ => hx ⟨j, by omega, he⟩

/-- The body of `pfin`, for settled node `i` in register `7`. -/
def pfinB : Stmt :=
  .seq (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))))
  (.seq (.store (.bin .add (.reg 0) (.reg 8)) (.bin .add (.reg 1) (.const 1)))
  (.seq (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))))
    (.store (.bin .add (.reg 3) (.bin .sub (.reg 9) (.const 1))) (.reg 6))))

/-- `pfin` with `args = F.args`. -/
def pfin : Stmt :=
  .seq (forRange 7 (.const 0) (.load (.bin .add (.reg 5) (.const 1))) pfinB)
  (.seq (.assign 8 (.load (.bin .add (.reg 5) (.const 2))))
  (.seq (.cond (.bin .lt (.reg 8) (.reg 6))
    (.seq (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))))
      (.store (.bin .add (.reg 3) (.bin .sub (.reg 9) (.const 1))) (.reg 6))) .nop)
  (.ret (.const 0))))

theorem pfin_noRand : pfin.NoRand := by
  simp [pfin, pfinB, forRange, forUp, Stmt.NoRand]

/-- The contract of `pfin`. -/
def pfinC (w : ℕ) : Contract where
  pre args mem := ∃ F : FF, ∃ NN MM, args = F.args ∧ F.Pre mem w NN MM
  post args mem _ mem' := ∀ F : FF, args = F.args →
    (∀ j < F.ns mem, mem' (F.OK + F.v mem j) = F.os + 1 ∧ mem' (F.sa mem (F.v mem j)) = F.S) ∧
    (F.pp mem < F.S → mem' (F.sa mem (F.pp mem)) = F.S) ∧
    ∀ x, ¬ F.Wr mem (F.ns mem) x → (F.pp mem < F.S → x ≠ F.sa mem (F.pp mem)) → mem' x = mem x
  cost args mem := 100 * mem (args.getD 5 0 + 1) + 100

theorem pfin_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [pfin]) :
    MeetsContract w p b (pfinC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨F, NN, MM, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some pfin := hp 0 (by simp)
  clear hp
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have l5 := h.l5
  have wos := h.wos; have wS := h.wS
  have hw1 : 1 < 2 ^ w := by omega
  have hwA : ∀ a ∈ F.args, a < 2 ^ w := hwords
  simp only [FF.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hwA
  obtain ⟨wOK, -, wHI, wHD, wSL, wCTL, -⟩ := hwA
  have hne : ∀ u v, u < NN → v < NN → F.sa mem u ≠ F.OK + v := by
    intro u v hu _; have := h.hiM u hu; unfold FF.sa; omega
  have hsaL : ∀ u, u < NN → F.sa mem u < F.OK := by
    intro u hu; have := h.hiM u hu; unfold FF.sa; omega
  -- the cells that are read are never written
  have nW : ∀ i ≤ F.ns mem, ∀ x, (x < F.HD ∨ F.OK + NN ≤ x) → ¬ F.Wr mem i x := by
    rintro i hi x hx ⟨j, hj, he | he⟩
    · have := h.vN j (by omega); omega
    · have := h.vN j (by omega)
      have := h.hiM _ this
      unfold FF.sa at he; omega
  let R : State → Prop := fun st => st.regs 0 = F.OK ∧ st.regs 1 = F.os ∧ st.regs 2 = F.HI ∧
    st.regs 3 = F.HD ∧ st.regs 4 = F.SL ∧ st.regs 5 = F.CTL ∧ st.regs 6 = F.S
  have hRu : ∀ st r v, R st → 7 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4, a5, a6⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  let I : ℕ → State → Prop := fun i st => R st ∧ st.regs 7 = i ∧ i ≤ F.ns mem ∧ F.Done mem st.mem i
  have hns : F.ns mem = mem (F.CTL + 1) := rfl
  have hloop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0)
    (hi := .load (.bin .add (.reg 5) (.const 1)))
    (body := pfinB) (P := fun st => R st ∧ st.mem = mem) (Inv := I) 80 0 (F.ns mem)
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hRu st 7 0 hr (by omega), by simp, Nat.zero_le _,
      fun j hj => absurd hj (by omega), fun x _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun i st _ hi hI => by
      obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6⟩, -, -, hd⟩ := hI
      have e : st.mem (F.CTL + 1) = mem (F.CTL + 1) :=
        hd.2 _ (nW i hi _ (Or.inr (by omega)))
      have b : st.regs 5 + 1 < 2 ^ w := by rw [a5]; omega
      rw [hns, ← e]
      eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h7, hle, hd⟩ := hI
      obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hr
      have hRn : ∀ st' : State, (∀ r < 7, st'.regs r = st.regs r) → R st' := fun st' hs =>
        ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
          (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, (hs 5 (by omega)).trans a5,
          (hs 6 (by omega)).trans a6⟩
      have hv := h.vN i hi
      have hhM := h.hiM _ hv
      have eV : st.mem (F.SL + i) = F.v mem i := hd.2 _ (nW i hle _ (Or.inr (by omega)))
      have eH : Function.update st.mem (F.OK + F.v mem i) (F.os + 1) (F.HI + F.v mem i) =
          mem (F.HI + F.v mem i) := by
        rw [Function.update_of_ne (by omega)]
        exact hd.2 _ (nW i hle _ (Or.inl (by omega)))
      have key := FF.Done.step hd h hi
      have eH0 : st.mem (F.HI + F.v mem i) = mem (F.HI + F.v mem i) :=
        hd.2 _ (nW i hle _ (Or.inl (by omega)))
      have hc : st.regs 2 + st.mem (F.SL + i) ≠ st.regs 0 + st.mem (F.SL + i) := by
        rw [a2, a0, eV]; omega
      have e1 : st.regs 0 + st.mem (F.SL + i) = F.OK + F.v mem i := by rw [a0, eV]
      have e2 : st.regs 3 + ((if st.regs 2 + st.mem (F.SL + i) = st.regs 0 + st.mem (F.SL + i)
          then st.regs 1 + 1 else st.mem (st.regs 2 + st.mem (F.SL + i))) - 1) =
          F.sa mem (F.v mem i) := by
        rw [if_neg hc, a2, a3, eV, eH0]; rfl
      have b1 : st.regs 4 + st.regs 7 < 2 ^ w := by rw [a4, h7]; omega
      have b2 : st.regs 0 + st.mem (st.regs 4 + st.regs 7) < 2 ^ w := by
        rw [a0, a4, h7, eV]; omega
      have b3 : st.regs 1 + 1 < 2 ^ w := by rw [a1]; omega
      have b4 : st.regs 2 + st.mem (st.regs 4 + st.regs 7) < 2 ^ w := by
        rw [a2, a4, h7, eV]; omega
      have hx1 : (if st.regs 2 + st.mem (F.SL + i) = st.regs 0 + st.mem (F.SL + i)
          then st.regs 1 + 1 else st.mem (st.regs 2 + st.mem (F.SL + i))) < 2 ^ w := by
        rw [if_neg hc, a2, eV, eH0]; omega
      have hx2 : st.regs 3 + ((if st.regs 2 + st.mem (F.SL + i) = st.regs 0 + st.mem (F.SL + i)
          then st.regs 1 + 1 else st.mem (st.regs 2 + st.mem (F.SL + i))) - 1) < 2 ^ w := by
        rw [e2]; have := hsaL _ hv; omega
      refine runs_start_le ?_
      dsimp only [pfinB]
      wram_run
      all_goals first
        | wram_cost
        | omega
        | (simp only [if_neg hc]; rw [a2, eV, eH0]; omega)
        | (simp only [if_neg hc]; rw [a2, a3, eV, eH0]; omega)
        | (refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
            by simp, by omega, ?_⟩, by simp [h7]⟩
           dsimp only
           rw [e2, e1, a1, a6]
           exact key))
  refine ⟨pfin, hproc, ?_⟩
  dsimp only [pfin]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ (fun st hI => ?_)
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6⟩, -, -, hd⟩ := hI
  have eP : st.mem (F.CTL + 2) = F.pp mem := hd.2 _ (nW _ le_rfl _ (Or.inr (by omega)))
  have b5 : st.regs 5 + 2 < 2 ^ w := by rw [a5]; omega
  have hfin : ∀ M : ℕ → ℕ, (F.pp mem < F.S → M (F.sa mem (F.pp mem)) = F.S) →
      (∀ x, (F.pp mem < F.S → x ≠ F.sa mem (F.pp mem)) → M x = st.mem x) →
      (pfinC w).post F.args mem 0 M := by
    intro M h1 h2 F' he
    rw [show F' = F from FF.eq_of_args he]
    refine ⟨fun j hj => ⟨?_, ?_⟩, h1, fun x hx hx' => (h2 x hx').trans (hd.2 x hx)⟩
    · have hvj := h.vN j hj
      by_cases hp : F.pp mem < F.S
      · rw [h2 _ (fun _ => (hne _ _ (h.pN hp) hvj).symm)]; exact (hd.1 j hj).1
      · rw [h2 _ (fun e => absurd e hp)]; exact (hd.1 j hj).1
    · by_cases hp : F.pp mem < F.S
      · by_cases e : F.sa mem (F.v mem j) = F.sa mem (F.pp mem)
        · rw [e]; exact h1 hp
        · rw [h2 _ (fun _ => e)]; exact (hd.1 j hj).2
      · rw [h2 _ (fun e => absurd e hp)]; exact (hd.1 j hj).2
  by_cases hpS : F.pp mem < F.S
  · have hpN := h.pN hpS
    have eHp : st.mem (F.HI + F.pp mem) = mem (F.HI + F.pp mem) :=
      hd.2 _ (nW _ le_rfl _ (Or.inl (by omega)))
    have c1 : st.mem (st.regs 5 + 2) < st.regs 6 := by rw [a5, a6, eP]; exact hpS
    have b6 : st.regs 2 + st.mem (st.regs 5 + 2) < 2 ^ w := by rw [a2, a5, eP]; omega
    have hhp := h.hiM _ hpN
    have b7 : st.mem (st.regs 2 + st.mem (st.regs 5 + 2)) < 2 ^ w := by
      rw [a2, a5, eP, eHp]; omega
    have e3 : st.regs 3 + (st.mem (st.regs 2 + st.mem (st.regs 5 + 2)) - 1) =
        F.sa mem (F.pp mem) := by rw [a2, a3, a5, eP, eHp]; rfl
    have b8 : st.regs 3 + (st.mem (st.regs 2 + st.mem (st.regs 5 + 2)) - 1) < 2 ^ w := by
      rw [e3]; have := hsaL _ hpN; omega
    rw [a5] at b6 b7 b8 e3 c1
    wram_run
    all_goals first
      | (simp only [pfinC, FF.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]; omega)
      | omega
      | (refine hfin _ (fun _ => ?_) (fun x hx => ?_)
         · dsimp only; rw [e3, Function.update_self, a6]
         · dsimp only; rw [e3, Function.update_of_ne (hx hpS)])
  · have c1 : ¬ st.mem (st.regs 5 + 2) < st.regs 6 := by rw [a5, a6, eP]; exact hpS
    rw [a5] at c1
    wram_run
    all_goals first
      | (simp only [pfinC, FF.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]; omega)
      | omega
      | exact hfin _ (fun h' => absurd h' hpS) (fun x _ => rfl)


end MinCostFlow.LowStretch
