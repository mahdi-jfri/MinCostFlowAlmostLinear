module

public import MinCostFlow.HierPaths.BuildProgBisect
public import MinCostFlow.HierPaths.LayoutEncode
public import MinCostFlow.HierPaths.BuildProgContracts
import Mathlib.Data.List.Sort

/-!
# Packing one side of a child request

Scan a child membership mask in vertex order. For each matching bit, append the
vertex's parent terminal number. Reading bits equal to one packs the selected set.
Reading bits equal to zero packs its complement.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The terminal numbers selected by the first `i` bits. -/
def packedCutSide (C : Finset ℕ) (off want i : ℕ) : List ℕ :=
  ((List.range i).filter (fun j => decide ((if j ∈ C then 1 else 0) = want))).map (off + ·)

/-- Read mask base, size, output base, terminal offset and wanted bit in registers 0–4. -/
def buildCutPackStep : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 0) (.reg 5))) (.reg 4))
    (.seq (.store (.bin .add (.reg 2) (.reg 6)) (.bin .add (.reg 3) (.reg 5)))
      (.assign 6 (.bin .add (.reg 6) (.const 1))))
    .nop

/-- Initialize the output count, scan the mask, and return the count. -/
def buildCutPackProc : Stmt :=
  .seq (.assign 6 (.const 0))
    (.seq (forRange 5 (.const 0) (.reg 1) buildCutPackStep) (.ret (.reg 6)))

/-- The mask is below the destination, with room for at most one word per vertex. -/
def buildCutPackContract (w s : ℕ) (C : Finset ℕ) : Contract where
  pre args mem := ∃ base dst off want, args = [base, s, dst, off, want] ∧
    base + s ≤ dst ∧ dst + s < 2 ^ w ∧ off + s < 2 ^ w ∧ 1 < 2 ^ w ∧
    ∀ i < s, mem (base + i) = if i ∈ C then 1 else 0
  post args mem v mem' := ∃ base dst off want, args = [base, s, dst, off, want] ∧
    v = (packedCutSide C off want s).length ∧ ListAt mem' dst (packedCutSide C off want s) ∧
    ∀ j, (j < dst ∨ dst + v ≤ j) → mem' j = mem j
  cost _ _ := 40 * s + 16

theorem buildCutPackProc_noRand : buildCutPackProc.NoRand := by
  simp [buildCutPackProc, buildCutPackStep, forRange, forUp, Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

private theorem packedCutSide_eq_sorted (C : Finset ℕ) (off want s : ℕ) :
    packedCutSide C off want s =
      finsetWords (shiftSet off ((Finset.range s).filter
        (fun v => (if v ∈ C then 1 else 0) = want))) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · unfold packedCutSide
    rw [List.pairwise_map]
    exact ((List.pairwise_lt_range.imp (fun h => Nat.le_of_lt h)).filter _).imp
      (fun h => Nat.add_le_add_left h _)
  · exact Finset.pairwise_sort ..
  · have hn : (packedCutSide C off want s).Nodup := by
      unfold packedCutSide
      exact (List.nodup_range.filter _).map (fun a b h => Nat.add_left_cancel h)
    apply (List.perm_ext_iff_of_nodup hn (Finset.sort_nodup ..)).mpr
    intro v
    simp [packedCutSide, shiftSet, List.mem_map, and_assoc]

/-- When the mask set lies in the child, packing ones writes the router's source set. -/
theorem packedCutSide_one {s : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.range s) (off : ℕ) :
    packedCutSide C off 1 s = finsetWords (shiftSet off C) := by
  rw [packedCutSide_eq_sorted]
  congr 2
  ext v
  by_cases h : v ∈ C
  · simp [h, hC h]
  · simp [h]

/-- Packing zeros writes the shifted complement, which is the other side of the request. -/
theorem packedCutSide_zero (s off : ℕ) (C : Finset ℕ) :
    packedCutSide C off 0 s = finsetWords (shiftSet off (Finset.range s \ C)) := by
  rw [packedCutSide_eq_sorted]
  congr 2
  ext v
  by_cases h : v ∈ C <;> simp [h]

private theorem packedCutSide_length (C : Finset ℕ) (off want i : ℕ) :
    (packedCutSide C off want i).length ≤ i := by
  simpa [packedCutSide] using List.length_filter_le
    (fun j => decide ((if j ∈ C then 1 else 0) = want)) (List.range i)

private theorem packedCutSide_succ (C : Finset ℕ) (off want i : ℕ) :
    packedCutSide C off want (i + 1) =
      packedCutSide C off want i ++ (if (if i ∈ C then 1 else 0) = want then [off + i] else []) := by
  by_cases h : (if i ∈ C then 1 else 0) = want <;>
    simp [packedCutSide, List.range_succ, List.filter_append, h]

private def packInv (mem : ℕ → ℕ) (base s dst off want : ℕ) (C : Finset ℕ)
    (i : ℕ) (st : State) : Prop :=
  st.regs 0 = base ∧ st.regs 1 = s ∧ st.regs 2 = dst ∧ st.regs 3 = off ∧
    st.regs 4 = want ∧ st.regs 5 = i ∧ st.regs 6 = (packedCutSide C off want i).length ∧
    ListAt st.mem dst (packedCutSide C off want i) ∧
    (∀ j, (j < dst ∨ dst + (packedCutSide C off want i).length ≤ j) → st.mem j = mem j)

private theorem buildPack_step {w base dst off want s i : ℕ} {C : Finset ℕ}
    {mem : ℕ → ℕ} (p : Program)
    (hSep : base + s ≤ dst) (hFit : dst + s < 2 ^ w) (hOff : off + s < 2 ^ w)
    (hw : 1 < 2 ^ w) (hi : i < s)
    (hMask : ∀ j < s, mem (base + j) = if j ∈ C then 1 else 0) :
    Triple w p (packInv mem base s dst off want C i) buildCutPackStep
      (normalPost fun st =>
        packInv mem base s dst off want C (i + 1) { st with regs := Function.update st.regs 5 (i + 1) }
          ∧ st.regs 5 = i) (fun _ => 28) := by
  intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, hAt, hFrame⟩
  let old := packedCutSide C off want i
  have hLen : old.length ≤ i := packedCutSide_length ..
  have hRead : st.mem (base + i) = if i ∈ C then 1 else 0 :=
    (hFrame _ (Or.inl (by omega))).trans (hMask i hi)
  have hAddr : base + i < 2 ^ w := by omega
  have hEval : (Expr.bin .eq (.load (.bin .add (.reg 0) (.reg 5))) (.reg 4)).eval w st =
      some (if (if i ∈ C then 1 else 0) = want then 1 else 0) := by
    by_cases h : (if i ∈ C then 1 else 0) = want <;>
      simp [Expr.eval, h0, h4, h5, hRead, hAddr, hw, h]
  unfold buildCutPackStep
  by_cases h : (if i ∈ C then 1 else 0) = want
  · have hNext : packedCutSide C off want (i + 1) = old ++ [off + i] := by
      rw [packedCutSide_succ, ite_eq_left h]
    have hDstW : dst + old.length < 2 ^ w := by omega
    have hOffW : off + i < 2 ^ w := by omega
    have hCntW : old.length + 1 < 2 ^ w := by omega
    have hSix : st.regs 6 = old.length := h6
    obtain ⟨o, out, c, hr, hPost, hc⟩ := (show ∃ o out c, Runs w p ω
        (.seq (.store (.bin .add (.reg 2) (.reg 6)) (.bin .add (.reg 3) (.reg 5)))
          (.assign 6 (.bin .add (.reg 6) (.const 1)))) st o out c ∧
        (normalPost fun st =>
          packInv mem base s dst off want C (i + 1)
            { st with regs := Function.update st.regs 5 (i + 1) } ∧ st.regs 5 = i) o out ∧
        0 + c ≤ 18 from by
      refine runs_seq_store_le (x := dst + old.length) (v := off + i) ?_ ?_ ?_
      · simp [Expr.eval, h2, hSix, hDstW]
      · simp [Expr.eval, h3, h5, hOffW]
      refine runs_assign_le (v := old.length + 1) ?_ ?_ ?_
      · simp [Expr.eval, hSix, hw, hCntW]
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
           by simpa using h4, by simp, by simp [hNext], ?_, ?_⟩, by simpa using h5⟩
        · change ListAt (Function.update st.mem (dst + old.length) (off + i)) dst _
          rw [hNext, listAt_append]
          refine ⟨?_, ?_⟩
          · intro j hj
            rw [Function.update_of_ne (by omega)]
            exact hAt j hj
          · intro j hj
            have hz : j = 0 := by simpa using hj
            subst j
            simp
        · intro j hj
          simp only [hNext, List.length_append, List.length_cons, List.length_nil] at hj
          change Function.update st.mem (dst + old.length) (off + i) j = mem j
          rw [Function.update_of_ne (by omega)]
          exact hFrame j (by omega)
      · simp [Expr.size])
    refine ⟨o, out, _, runs_cond_iff.mpr ⟨1, c, by simpa [h] using hEval, by simpa using hr, rfl⟩,
      hPost, ?_⟩
    simp [Expr.size]; omega
  · have hNext : packedCutSide C off want (i + 1) = old := by
      simp [packedCutSide_succ, h, old]
    refine ⟨.normal, st, _, runs_cond_iff.mpr ⟨0, 1, by simpa [h] using hEval, ?_, rfl⟩, ?_, ?_⟩
    · simp only [ite_true]
      exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    · exact ⟨by
        refine ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simpa using h4, by simp, by simpa [hNext] using h6, ?_, ?_⟩
        · exact hNext ▸ hAt
        · simpa [hNext] using hFrame, h5⟩
    · simp [Expr.size]

/-- The packing procedure writes exactly the selected side in increasing terminal order. -/
theorem buildCutPackProc_meetsContract {w s : ℕ} {C : Finset ℕ} {p : Program} {f : ℕ}
    (hf : p.procs[f]? = some buildCutPackProc) :
    MeetsContract w p f (buildCutPackContract w s C) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨base, dst, off, want, rfl, hSep, hFit, hOff, hw, hMask⟩ := hPre
  let st0 := startState [base, s, dst, off, want] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 6 0 }
  have hLoop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 1)
    (body := buildCutPackStep) (P := fun st => st = st1)
    (Inv := packInv mem base s dst off want C) 28 0 s (Nat.zero_le _) hw (fun _ => by omega)
    (fun st h => by
      subst st
      exact ⟨Expr.eval_const (Nat.two_pow_pos _), rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun j hj => False.elim (Nat.not_lt_zero j hj), fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun _ _ hi => buildPack_step p hSep hFit hOff hw hi hMask)
  refine runs_start_le ?_
  unfold buildCutPackProc
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _)) ?_
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_, _, _, _, _, _, hCnt, hAt, hFrame⟩
  refine runs_ret_le (Expr.eval_reg_of_eq hCnt) ⟨base, dst, off, want, rfl, rfl, hAt, hFrame⟩ ?_
  simp [buildCutPackContract, Expr.size]
  omega

end MinCostFlow.HierPaths
