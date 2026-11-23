module

public import MinCostFlow.LowStretch.ProgSlot

/-!
# The tree of the first run, node by node

After the first run of Dijkstra in a cluster, every node `u ≠ x0` has a parent `par u` and a
parent arc `parc u`. The petals need, for each node, the next node toward the center, the pair of
the arc to it (with its half flag and its two ends, the end in `u` first), and the cost and class
of that arc. `treeP` copies these into arrays indexed by the node (`treeP_spec`), and writes
`PCI[u] = u`, so that `slotF` can read the slot costs through `PCI`.

The arc `parc u` holds item `ORD[parc u]`, which is a direction of the stored entry
`ORD[parc u] / 2`. The end of its pair that lies in `u` is found by its local index.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The addresses that `treeP` uses. `TS` and `NN` are those of the first run, `ORD`, `CS` and
`CL` those of its arc graph, `SA` the stored entries. The other arrays are written. -/
structure TF where
  s : ℕ
  x0 : ℕ
  TS : ℕ
  NN : ℕ
  ORD : ℕ
  CS : ℕ
  CL : ℕ
  SA : ℕ
  IN : ℕ
  LAB : ℕ
  LOC : ℕ
  PAR : ℕ
  PP : ℕ
  PF : ℕ
  PA : ℕ
  PB : ℕ
  SCc : ℕ
  SCk : ℕ
  PCI : ℕ

namespace TF

variable (F : TF) (mem : ℕ → ℕ)

def args : List ℕ := [F.s, F.x0, F.TS, F.NN, F.ORD, F.CS, F.CL, F.SA, F.IN, F.LAB, F.LOC, F.PAR,
  F.PP, F.PF, F.PA, F.PB, F.SCc, F.SCk, F.PCI]

theorem eq_of_args {F F' : TF} (h : F.args = F'.args) : F' = F := by
  cases F; cases F'; simp only [TF.args, List.cons.injEq] at h
  simp_all

/-- The parent arc of `u`. -/
def pk (u : ℕ) : ℕ := mem (F.TS + 4 * F.NN + u)
/-- The stored entry of the parent arc. -/
def pj (u : ℕ) : ℕ := mem (F.ORD + F.pk mem u) / 2
/-- Its pair. -/
def pp (u : ℕ) : ℕ := mem (F.SA + 2 * F.pj mem u)
/-- Its half flag. -/
def pf (u : ℕ) : ℕ := mem (F.SA + 2 * F.pj mem u + 1)
/-- The first end of the pair. -/
def e0 (u : ℕ) : ℕ := mem (F.IN + 3 * F.pp mem u)
/-- The second end of the pair. -/
def e1 (u : ℕ) : ℕ := mem (F.IN + 3 * F.pp mem u + 1)
/-- The local index of the first end. -/
def l0 (u : ℕ) : ℕ := mem (F.LOC + mem (F.LAB + F.e0 mem u))

/-- What `treeP` writes for node `u`: the parent, pair, flag, the end in `u`, the other end, the
cost and the class. The center gets the dummy node `s` and zeros. -/
def vPAR (u : ℕ) : ℕ := if u = F.x0 then F.s else mem (F.TS + 3 * F.NN + u)
def vPP (u : ℕ) : ℕ := if u = F.x0 then 0 else F.pp mem u
def vPF (u : ℕ) : ℕ := if u = F.x0 then 0 else F.pf mem u
def vPA (u : ℕ) : ℕ := if u = F.x0 then 0 else if F.l0 mem u = u then F.e0 mem u else F.e1 mem u
def vPB (u : ℕ) : ℕ := if u = F.x0 then 0 else if F.l0 mem u = u then F.e1 mem u else F.e0 mem u
def vSC (u : ℕ) : ℕ := if u = F.x0 then 0 else mem (F.CS + F.pk mem u)
def vSK (u : ℕ) : ℕ := if u = F.x0 then 0 else mem (F.CL + F.pk mem u)

/-- The memory after the nodes below `i`. -/
def Done (M : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ u < i, M (F.PAR + u) = F.vPAR mem u ∧ M (F.PP + u) = F.vPP mem u ∧
    M (F.PF + u) = F.vPF mem u ∧ M (F.PA + u) = F.vPA mem u ∧ M (F.PB + u) = F.vPB mem u ∧
    M (F.SCc + u) = F.vSC mem u ∧ M (F.SCk + u) = F.vSK mem u ∧ M (F.PCI + u) = u

/-- The written cells. -/
def Out (a : ℕ) : Prop := F.PAR ≤ a ∧ a ≤ F.PCI + F.s

/-- The precondition: the written arrays follow each other, and every cell that is read lies
below them. -/
structure Pre (w : ℕ) : Prop where
  l1 : F.PAR + F.s + 1 ≤ F.PP
  l2 : F.PP + F.s ≤ F.PF
  l3 : F.PF + F.s ≤ F.PA
  l4 : F.PA + F.s ≤ F.PB
  l5 : F.PB + F.s ≤ F.SCc
  l6 : F.SCc + F.s ≤ F.SCk
  l7 : F.SCk + F.s ≤ F.PCI
  l8 : F.PCI + F.s < 2 ^ w
  hw : 1 < 2 ^ w
  rd : ∀ u < F.s, u ≠ F.x0 → F.TS + 4 * F.NN + u < F.PAR ∧ F.TS + 3 * F.NN + u < F.PAR ∧
    F.ORD + F.pk mem u < F.PAR ∧ F.SA + mem (F.ORD + F.pk mem u) + 1 < F.PAR ∧
    F.IN + 3 * F.pp mem u + 1 < F.PAR ∧ F.LAB + F.e0 mem u < F.PAR ∧
    F.LOC + mem (F.LAB + F.e0 mem u) < F.PAR ∧ F.CS + F.pk mem u < F.PAR ∧
    F.CL + F.pk mem u < F.PAR

end TF

/-- One node: the eight cells of `u` get their values, and nothing else changes. -/
theorem TF.Done.step {w : ℕ} {F : TF} {mem M M' : ℕ → ℕ} {i : ℕ} (hd : F.Done mem M i) (hw : F.Pre mem w)
    (hi : i < F.s)
    (h1 : M' (F.PAR + i) = F.vPAR mem i) (h2 : M' (F.PP + i) = F.vPP mem i)
    (h3 : M' (F.PF + i) = F.vPF mem i) (h4 : M' (F.PA + i) = F.vPA mem i)
    (h5 : M' (F.PB + i) = F.vPB mem i) (h6 : M' (F.SCc + i) = F.vSC mem i)
    (h7 : M' (F.SCk + i) = F.vSK mem i) (h8 : M' (F.PCI + i) = i)
    (hfr : ∀ a, a ≠ F.PAR + i → a ≠ F.PP + i → a ≠ F.PF + i → a ≠ F.PA + i → a ≠ F.PB + i →
      a ≠ F.SCc + i → a ≠ F.SCk + i → a ≠ F.PCI + i → M' a = M a) :
    F.Done mem M' (i + 1) := by
  have l1 := hw.l1; have l2 := hw.l2; have l3 := hw.l3; have l4 := hw.l4; have l5 := hw.l5
  have l6 := hw.l6; have l7 := hw.l7
  intro u hu
  by_cases e : u = i
  · subst e; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hd u (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      first
      | (rw [hfr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)]; assumption)

/-- The body of `treeP`, for node `u` in register `19`. -/
def treePB : Stmt :=
  .seq (.cond (.bin .eq (.reg 19) (.reg 1))
    (.seq (.store (.bin .add (.reg 11) (.reg 19)) (.reg 0))
    (.seq (.store (.bin .add (.reg 12) (.reg 19)) (.const 0))
    (.seq (.store (.bin .add (.reg 13) (.reg 19)) (.const 0))
    (.seq (.store (.bin .add (.reg 14) (.reg 19)) (.const 0))
    (.seq (.store (.bin .add (.reg 15) (.reg 19)) (.const 0))
    (.seq (.store (.bin .add (.reg 16) (.reg 19)) (.const 0))
      (.store (.bin .add (.reg 17) (.reg 19)) (.const 0))))))))
    (.seq (.assign 20 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 4) (.reg 3)))
        (.reg 19))))
    (.seq (.assign 21 (.bin .div (.load (.bin .add (.reg 4) (.reg 20))) (.const 2)))
    (.seq (.assign 22 (.load (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 21)))))
    (.seq (.assign 23 (.load (.bin .add (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 21)))
        (.const 1))))
    (.seq (.assign 24 (.load (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 22)))))
    (.seq (.assign 25 (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 22)))
        (.const 1))))
    (.seq (.assign 26 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 9) (.reg 24))))))
    (.seq (.assign 27 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 3)))
        (.reg 19))))
    (.seq (.assign 28 (.load (.bin .add (.reg 5) (.reg 20))))
    (.seq (.assign 29 (.load (.bin .add (.reg 6) (.reg 20))))
    (.seq (.store (.bin .add (.reg 11) (.reg 19)) (.reg 27))
    (.seq (.store (.bin .add (.reg 12) (.reg 19)) (.reg 22))
    (.seq (.store (.bin .add (.reg 13) (.reg 19)) (.reg 23))
    (.seq (.store (.bin .add (.reg 16) (.reg 19)) (.reg 28))
    (.seq (.store (.bin .add (.reg 17) (.reg 19)) (.reg 29))
      (.cond (.bin .eq (.reg 26) (.reg 19))
        (.seq (.store (.bin .add (.reg 14) (.reg 19)) (.reg 24))
          (.store (.bin .add (.reg 15) (.reg 19)) (.reg 25)))
        (.seq (.store (.bin .add (.reg 14) (.reg 19)) (.reg 25))
          (.store (.bin .add (.reg 15) (.reg 19)) (.reg 24))))))))))))))))))))
  (.store (.bin .add (.reg 18) (.reg 19)) (.reg 19))

/-- `treeP` with `args = F.args`. -/
def treeP : Stmt :=
  .seq (forRange 19 (.const 0) (.reg 0) treePB)
  (.seq (.store (.bin .add (.reg 11) (.reg 0)) (.reg 0)) (.ret (.const 0)))

theorem treeP_noRand : treeP.NoRand := by
  simp [treeP, treePB, forRange, forUp, Stmt.NoRand]

/-- The contract of `treeP`. -/
def treePC (w : ℕ) : Contract where
  pre args mem := ∃ F : TF, args = F.args ∧ F.Pre mem w
  post args mem _ mem' := ∀ F : TF, args = F.args →
    F.Done mem mem' F.s ∧ mem' (F.PAR + F.s) = F.s ∧ ∀ a, ¬ F.Out a → mem' a = mem a
  cost args _ := 300 * args.getD 0 0 + 50

end MinCostFlow.LowStretch

namespace MinCostFlow.LowStretch

open WordRAM

set_option maxHeartbeats 4000000 in
theorem treeP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [treeP]) :
    MeetsContract w p b (treePC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨F, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some treeP := hp 0 (by simp)
  clear hp
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have l5 := h.l5
  have l6 := h.l6; have l7 := h.l7; have l8 := h.l8
  have hw1 : 1 < 2 ^ w := h.hw
  have hwA : ∀ a ∈ F.args, a < 2 ^ w := hwords
  simp only [TF.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hwA
  obtain ⟨ws, wx0, wTS, wNN, wORD, wCS, wCL, wSA, wIN, wLAB, wLOC, wPAR, wPP, wPF, wPA, wPB,
    wSCc, wSCk, wPCI⟩ := hwA
  let R : State → Prop := fun st => st.regs 0 = F.s ∧ st.regs 1 = F.x0 ∧ st.regs 2 = F.TS ∧
    st.regs 3 = F.NN ∧ st.regs 4 = F.ORD ∧ st.regs 5 = F.CS ∧ st.regs 6 = F.CL ∧
    st.regs 7 = F.SA ∧ st.regs 8 = F.IN ∧ st.regs 9 = F.LAB ∧ st.regs 10 = F.LOC ∧
    st.regs 11 = F.PAR ∧ st.regs 12 = F.PP ∧ st.regs 13 = F.PF ∧ st.regs 14 = F.PA ∧
    st.regs 15 = F.PB ∧ st.regs 16 = F.SCc ∧ st.regs 17 = F.SCk ∧ st.regs 18 = F.PCI
  have hRu : ∀ st r v, R st → 19 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
      a18⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  let I : ℕ → State → Prop := fun i st => R st ∧ st.regs 19 = i ∧ F.Done mem st.mem i ∧
    ∀ a, ¬ F.Out a → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 19) (lo := .const 0) (hi := .reg 0)
    (body := treePB) (P := fun st => R st ∧ st.mem = mem) (Inv := I) 250 0 F.s
    (Nat.zero_le _) hw1 (fun _ => ws)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hRu st 19 0 hr (by omega), by simp,
      fun j hj => absurd hj (by omega), fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h19, hdone, hfr⟩ := hI
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
        a18⟩ := hr
      have hRn : ∀ st' : State, (∀ r < 19, st'.regs r = st.regs r) → R st' := fun st' hs =>
        ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
          (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, (hs 5 (by omega)).trans a5,
          (hs 6 (by omega)).trans a6, (hs 7 (by omega)).trans a7, (hs 8 (by omega)).trans a8,
          (hs 9 (by omega)).trans a9, (hs 10 (by omega)).trans a10,
          (hs 11 (by omega)).trans a11, (hs 12 (by omega)).trans a12,
          (hs 13 (by omega)).trans a13, (hs 14 (by omega)).trans a14,
          (hs 15 (by omega)).trans a15, (hs 16 (by omega)).trans a16,
          (hs 17 (by omega)).trans a17, (hs 18 (by omega)).trans a18⟩
      have nOut : ∀ a, a < F.PAR → ¬ F.Out a := by
        intro a ha ho; unfold TF.Out at ho; omega
      by_cases hx : i = F.x0
      · refine runs_start_le ?_
        dsimp only [treePB]
        wram_run
        all_goals first
          | wram_cost
          | omega
          | (refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
              by simp, ?_, fun a ha => ?_⟩, by simp [h19]⟩
             · refine TF.Done.step hdone h hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
               all_goals simp (disch := omega) only [Function.update_of_ne, Function.update_self,
                 a0, a11, a12, a13, a14, a15, a16, a17, a18, h19, TF.vPAR, TF.vPP, TF.vPF,
                 TF.vPA, TF.vPB, TF.vSC, TF.vSK, hx, if_true]
               intro a n1 n2 n3 n4 n5 n6 n7 n8
               simp (disch := omega) only [Function.update_of_ne]
             · have : ¬ (F.PAR ≤ a ∧ a ≤ F.PCI + F.s) := ha
               simp (disch := omega) only [Function.update_of_ne, a11, a12, a13, a14, a15, a16,
                 a17, a18, h19]
               exact hfr a ha)
      · obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := h.rd i hi hx
        have eK : st.mem (F.TS + 4 * F.NN + i) = F.pk mem i := hfr _ (nOut _ r1)
        have eJ : st.mem (F.ORD + F.pk mem i) = mem (F.ORD + F.pk mem i) := hfr _ (nOut _ r3)
        have eP : st.mem (F.SA + 2 * (mem (F.ORD + F.pk mem i) / 2)) = F.pp mem i :=
          hfr _ (nOut _ (by omega))
        have eF : st.mem (F.SA + 2 * (mem (F.ORD + F.pk mem i) / 2) + 1) = F.pf mem i :=
          hfr _ (nOut _ (by omega))
        have e0 : st.mem (F.IN + 3 * F.pp mem i) = F.e0 mem i := hfr _ (nOut _ (by omega))
        have e1 : st.mem (F.IN + 3 * F.pp mem i + 1) = F.e1 mem i := hfr _ (nOut _ r5)
        have eB : st.mem (F.LAB + F.e0 mem i) = mem (F.LAB + F.e0 mem i) := hfr _ (nOut _ r6)
        have eL : st.mem (F.LOC + mem (F.LAB + F.e0 mem i)) = F.l0 mem i := hfr _ (nOut _ r7)
        have eT : st.mem (F.TS + 3 * F.NN + i) = mem (F.TS + 3 * F.NN + i) := hfr _ (nOut _ r2)
        have eC : st.mem (F.CS + F.pk mem i) = mem (F.CS + F.pk mem i) := hfr _ (nOut _ r8)
        have eD : st.mem (F.CL + F.pk mem i) = mem (F.CL + F.pk mem i) := hfr _ (nOut _ r9)
        have b1 : F.TS + 4 * F.NN + i < 2 ^ w := by omega
        have b7 : F.TS + 3 * F.NN + i < 2 ^ w := by omega
        have c1 : st.mem (st.regs 4 + st.mem (F.TS + 4 * F.NN + i)) < 2 ^ w ∧
            st.regs 7 + st.mem (st.regs 4 + st.mem (F.TS + 4 * F.NN + i)) + 1 < 2 ^ w := by
          rw [a4, a7, eK, eJ]; omega
        have c2 : st.regs 8 + 3 * st.mem (st.regs 7 + 2 * (st.mem (st.regs 4 +
            st.mem (F.TS + 4 * F.NN + i)) / 2)) + 1 < 2 ^ w := by
          rw [a4, a7, a8, eK, eJ, eP]; omega
        have c3 : st.regs 9 + st.mem (st.regs 8 + 3 * st.mem (st.regs 7 + 2 * (st.mem (st.regs 4 +
            st.mem (F.TS + 4 * F.NN + i)) / 2))) < 2 ^ w := by
          rw [a4, a7, a8, a9, eK, eJ, eP, e0]; omega
        have c4 : st.regs 10 + st.mem (st.regs 9 + st.mem (st.regs 8 + 3 * st.mem (st.regs 7 + 2 *
            (st.mem (st.regs 4 + st.mem (F.TS + 4 * F.NN + i)) / 2)))) < 2 ^ w := by
          rw [a4, a7, a8, a9, a10, eK, eJ, eP, e0, eB]; omega
        have c5 : st.regs 5 + st.mem (F.TS + 4 * F.NN + i) < 2 ^ w := by rw [a5, eK]; omega
        have c6 : st.regs 6 + st.mem (F.TS + 4 * F.NN + i) < 2 ^ w := by rw [a6, eK]; omega
        by_cases hl : F.l0 mem i = i
        · have hl' : st.mem (st.regs 10 + st.mem (st.regs 9 + st.mem (st.regs 8 + 3 *
              st.mem (st.regs 7 + 2 * (st.mem (st.regs 4 + st.mem (F.TS + 4 * F.NN + i)) / 2))))) =
              i := by
            rw [a4, a7, a8, a9, a10, eK, eJ, eP, e0, eB, eL]; exact hl
          refine runs_start_le ?_
          dsimp only [treePB]
          wram_run
          all_goals first
            | wram_cost
            | omega
            | (refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
                by simp, ?_, fun a ha => ?_⟩, by simp [h19]⟩
               · refine TF.Done.step hdone h hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                 all_goals simp (disch := omega) only [Function.update_of_ne, Function.update_self,
                   a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
                   h19, TF.vPAR, TF.vPP, TF.vPF, TF.vPA, TF.vPB, TF.vSC, TF.vSK, hx, hl, if_false,
                   if_true, eK, eJ, eP, eF, e0, e1, eB, eL, eT, eC, eD]
                 intro a n1 n2 n3 n4 n5 n6 n7 n8
                 simp (disch := omega) only [Function.update_of_ne, a11, a12, a13, a14, a15, a16,
                   a17, a18, h19]
               · have : ¬ (F.PAR ≤ a ∧ a ≤ F.PCI + F.s) := ha
                 simp (disch := omega) only [Function.update_of_ne, a11, a12, a13, a14, a15, a16,
                   a17, a18, h19]
                 exact hfr a ha)
        · have hl' : st.mem (st.regs 10 + st.mem (st.regs 9 + st.mem (st.regs 8 + 3 *
              st.mem (st.regs 7 + 2 * (st.mem (st.regs 4 + st.mem (F.TS + 4 * F.NN + i)) / 2))))) ≠
              i := by
            rw [a4, a7, a8, a9, a10, eK, eJ, eP, e0, eB, eL]; exact hl
          refine runs_start_le ?_
          dsimp only [treePB]
          wram_run
          all_goals first
            | wram_cost
            | omega
            | (refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
                by simp, ?_, fun a ha => ?_⟩, by simp [h19]⟩
               · refine TF.Done.step hdone h hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                 all_goals simp (disch := omega) only [Function.update_of_ne, Function.update_self,
                   a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
                   h19, TF.vPAR, TF.vPP, TF.vPF, TF.vPA, TF.vPB, TF.vSC, TF.vSK, hx, hl, if_false,
                   if_true, eK, eJ, eP, eF, e0, e1, eB, eL, eT, eC, eD]
                 intro a n1 n2 n3 n4 n5 n6 n7 n8
                 simp (disch := omega) only [Function.update_of_ne, a11, a12, a13, a14, a15, a16,
                   a17, a18, h19]
               · have : ¬ (F.PAR ≤ a ∧ a ≤ F.PCI + F.s) := ha
                 simp (disch := omega) only [Function.update_of_ne, a11, a12, a13, a14, a15, a16,
                   a17, a18, h19]
                 exact hfr a ha))
  refine ⟨treeP, hproc, ?_⟩
  dsimp only [treeP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ (fun st hI => ?_)
  obtain ⟨⟨a0, -, -, -, -, -, -, -, -, -, -, a11, -⟩, -, hdone, hfr⟩ := hI
  have bS : st.regs 11 + st.regs 0 < 2 ^ w := by rw [a11, a0]; omega
  wram_run
  all_goals first
    | omega
    | (simp only [treePC, TF.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]; omega)
    | skip
  intro F' he
  obtain rfl := (TF.eq_of_args he).symm
  refine ⟨fun u hu => ?_, by simp [a0, a11], fun a ha => ?_⟩
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hdone u hu
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := omega) only [Function.update_of_ne, a0, a11] <;> assumption
  · have : ¬ (F.PAR ≤ a ∧ a ≤ F.PCI + F.s) := ha
    simp (disch := omega) only [Function.update_of_ne, a0, a11]
    exact hfr a ha

end MinCostFlow.LowStretch
