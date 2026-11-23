module

public import MinCostFlow.LSF.Program.OrderPhaseFrame
public import MinCostFlow.LSF.Program.OrderPhaseIn

/-!
# The minimum table after the order phase

The order stage writes the table of minimum ranks at `minPtr`. Its post states the table as
`liftMin` of the ancestor table, the parent edges and the ranks, all read from the memory of
that stage. `orderPhase_minTable` states the same table with all three read from the memory
after the whole phase, which is the form that `AuxAt` asks for.

The three inputs survive the later calls. The ancestor table and the parents lie in the aux
arrays below `minPtr`, which only the parent edge of the root changes (`orderPhase_frame`). The
parent edge of the root is `0` both in the memory that the order stage reads and after the phase.
The ranks lie in the `T` block, which the tree stage keeps at the ranks and the `T_H` stage keeps
whole. The table itself lies above the `T` block and below the outputs of the `T_H` stage.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

set_option maxHeartbeats 800000 in
/-- After the order phase, the table at `minPtr` is `liftMin` of the ancestor table of the
parents, the parent edges and the ranks of the memory after the phase. The bound on the parent
edges is an input; the driver has it from the tree arrays of the decomposition phase. -/
theorem orderPhase_minTable {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem mem₁ mem₃ mem₄ mem₅ : ℕ → ℕ} {v₁ v₃ v₄ v₅ : ℕ}
    (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (h₁ : (rootStageContract w).post
        [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap] mem v₁ mem₁)
    (h₃ : (orderStageContract w h G₀ vList eList).post
        [X.n, 0, X.m0, dgEListBase X.gPtr X.vCap X.eCap, dgETailSlotBase X.gPtr X.vCap X.eCap,
          dgEHeadSlotBase X.gPtr X.vCap X.eCap, dgIntToExtBase X.gPtr X.vCap, X.vIdx, X.eu, X.ev,
          X.qPtr, X.Kq, X.dPtr, X.K, X.tmpPtr, X.logCap, X.auxPar + 3 * X.n,
          X.auxPar + X.n + X.n, X.auxPar, X.qOrd, X.auxPar + X.n, X.arrPtr, X.scratchPtr,
          tPiBase X.tPtr X.vCap X.tM, X.minPtr]
        (Function.update mem₁ (X.auxPar + X.n) 0) v₃ mem₃)
    (h₄ : (tStageContract w G₀ T₀ vList).post [X.tPtr, X.vCap, X.eCap, X.tM, X.vListPtr,
        X.tOrigSrc, X.tTail, X.tHead, X.n, X.nOrig, tOrigIdBase X.tPtr X.vCap X.tM,
        tDgTPtr X.tPtr] mem₃ v₄ mem₄)
    (h₅ : (thStageContract w T₀ vList).post
        [X.n, X.qOrd, X.auxPar, X.auxPar + X.n + X.n, X.thBase, 0, X.thDst] mem₄ v₅ mem₅)
    (hpe : ∀ i < X.n, mem₅ (X.auxPar + X.n + i) < X.tM) :
    ∀ i < X.n, ∀ j < X.logCap, mem₅ (X.minPtr + (i * X.logCap + j)) =
      liftMin (fun i j => liftF (fun x => mem₅ (X.auxPar + x)) i j)
        (fun x => mem₅ (X.auxPar + X.n + x)) (fun t => mem₅ (tPiBase X.tPtr X.vCap X.tM + t))
        0 i j := by
  obtain ⟨-, hF2, -, h54, hTB, hpe0⟩ := orderPhase_frame I h₁ h₃ h₄ h₅
  have hpre := orderPhase_orderPre I h₁
  have hmin := I.hmin
  have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5; have l6 := I.l6
  have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10; have l11 := I.l11
  have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15; have l16 := I.l16
  have l17 := I.l17; have l18 := I.l18
  obtain ⟨ht1, ht2⟩ := I.tPi_le
  have ht0 : X.tPtr ≤ tPiBase X.tPtr X.vCap X.tM := by
    simp only [tPiBase, tOrigIdBase, tDgTPtr]; omega
  have ht3 : tPiBase X.tPtr X.vCap X.tM + X.tM ≤ X.tPtr + tBlockSize X.vCap X.eCap X.tM := by
    simp only [tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, tl, hd, Q,
    heqp, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hR, -, -, -, hL, -⟩ := hpre
  simp only [List.cons.injEq, and_true] at heqp
  obtain ⟨rfl, rfl, rfl, rfl, -, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₃, -, -, -,
    -, hmin₃, -⟩ := h₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, -, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₄, -, -, hpi₄, -⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -⟩ := heq₄
  set memU := Function.update mem₁ (X.auxPar + X.n) 0 with hmemU
  -- the parents and the ancestor table
  have hpar : ∀ x < X.n, mem₅ (X.auxPar + x) = memU (X.auxPar + x) := fun x hx => by
    rw [hF2 _ (by omega) (by omega) (by omega), hmemU, Function.update_of_ne (by omega)]
  have hparlt : ∀ x < X.n, mem₅ (X.auxPar + x) < X.n := fun x hx => by
    rw [hpar x hx]; exact hR.par_lt x hx
  have hU : ∀ i < X.n, ∀ j < X.logCap, liftF (fun x => mem₅ (X.auxPar + x)) i j =
      memU (X.auxPar + 3 * X.n + (i * X.logCap + j)) := fun i hi j _ => by
    rw [hL.hup i hi j (by assumption)]
    exact liftF_congr hparlt hpar j i hi
  -- the parent edges
  have hpe' : ∀ x < X.n, mem₅ (X.auxPar + X.n + x) = memU (X.auxPar + X.n + x) := fun x hx => by
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · rw [Nat.add_zero, hpe0, hmemU, Function.update_self]
    · rw [hF2 _ (by omega) (by omega) (by omega), hmemU, Function.update_of_ne (by omega)]
  -- the ranks
  have hpiv : ∀ t < X.tM, mem₅ (tPiBase X.tPtr X.vCap X.tM + t) =
      mem₃ (tPiBase X.tPtr X.vCap X.tM + t) := fun t ht => by
    rw [hTB _ (by omega) (by omega), hpi₄ t ht]
  have hC := liftMin_congr_all (r := 0) (U := fun i j => liftF (fun x => mem₅ (X.auxPar + x)) i j)
    (U' := fun i j => memU (X.auxPar + 3 * X.n + (i * X.logCap + j))) hU
    (fun i hi j _ => liftF_lt hparlt j i hi) hpe' hpe hpiv
  intro i hi j hj
  have hnL : (i + 1) * X.logCap ≤ X.n * X.logCap := Nat.mul_le_mul_right _ hi
  have hij : i * X.logCap + j < X.n * X.logCap := by rw [Nat.add_mul, Nat.one_mul] at hnL; omega
  rw [h54 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)), hmin₃ i hi j hj,
    (hC j hj.le i hi).1]
