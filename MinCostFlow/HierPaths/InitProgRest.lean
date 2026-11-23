module

public import MinCostFlow.HierPaths.InitEntry
public import MinCostFlow.HierPaths.InitProgMove
public import MinCostFlow.HierPaths.InitBlockLen

/-!
# The rest of `Init` from the builder of the block

The rest of `Init` (`InitRestContract`) has two steps: a builder writes the block of
`initConcrete` at the heap pointer `h₁`, above the static output (`BuildContract`), and
`moveDown` moves it down to `h`. `restEntry fB fM` calls the two, and `restEntry_meetsContract`
proves `InitRestContract`. `restProc` and `restProc_spec` give `RestProcSpec` from a builder
meeting `BuildProcSpec`.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The contract of the builder of the block: with the precondition of `InitRestContract`, it
writes the block `initBlock` at the heap pointer `h₁` and returns its end, which is at most
`h₁ + sR …`; memory below `h₁` is unchanged and memory from the end on is zero. The cost is
`K` per step of the model and per word of the block. -/
def BuildContract (w a K : ℕ) (sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (S : StaticData) (G : Graph) :
    Contract where
  pre := (InitRestContract w a K sR S G).pre
  post args mem v mem' := ∃ (gAddr phiNum phiDen M h h₁ : ℕ),
    args = [gAddr, phiNum, phiDen, M, h, h₁] ∧
      v = h₁ + (initBlock S a G phiNum phiDen M).length ∧
      v ≤ h₁ + sR phiNum phiDen G.n G.m M ∧
      ListAt mem' h₁ (initBlock S a G phiNum phiDen M) ∧ ZeroFrom mem' v ∧
      ∀ y < h₁, mem' y = mem y
  cost args _ := K * (initRestSteps S.H S.x S.b S.owner S.label G.n G.m +
    (initBlock S a G (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)).length)

/-- The entry of the rest: `r6 := fB(args)`, `r7 := fM(h, h₁, r6)`, return `r7`. -/
def restEntry (fB fM : ℕ) : Stmt :=
  .seq (.call 6 fB [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5])
    (.seq (.call 7 fM [.reg 4, .reg 5, .reg 6]) (.ret (.reg 7)))

theorem one_le_length_initBlock (S : StaticData) (a : ℕ) (G : Graph) (phiNum phiDen M : ℕ) :
    1 ≤ (initBlock S a G phiNum phiDen M).length := by
  rw [initBlock, length_encode]; omega

/-- **The rest of `Init` from the builder and `copyDown`.** -/
theorem restEntry_meetsContract (w a K : ℕ) (sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (S : StaticData)
    (G : Graph) (p : Program) (j fB fM : ℕ)
    (hB : MeetsContract w p fB (BuildContract w a K sR S G))
    (hM : p.procs[fM]? = some copyDown) (hj : p.procs[j]? = some (restEntry fB fM)) :
    MeetsContract w p j (InitRestContract w a (K + 80) sR S G) := by
  refine meetsContract_of_runs hj fun args mem pos ω hw hpre => ?_
  have hpre' := hpre
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, hzero, hGat, hgh, h1, h2, hgood,
    hsp, -, -⟩ := hpre
  refine runs_start_le ?_
  unfold restEntry
  refine runs_seq_call_le hB (vs := [gAddr, phiNum, phiDen, M, h, h₁]) (by rfl) hw hpre' ?_
  intro v mem₁ pos₁ hpost
  obtain ⟨_, _, _, _, _, _, hargs, hv, hvs, hblock, hzero₁, hbelow₁⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hhh : h ≤ h₁ := by omega
  have hw1 : 1 < 2 ^ w := by
    have : 1 ≤ h₁ + sR phiNum phiDen G.n G.m M + 1 := by omega
    have h2w : 2 ≤ 2 ^ w := by
      rcases Nat.lt_or_ge w 1 with hw0 | hw0
      · have : w = 0 := by omega
        subst this
        have := one_le_length_initBlock S a G phiNum phiDen M
        simp at hsp; omega
      · calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw0
    omega
  have hvw : v < 2 ^ w := by omega
  refine runs_seq_call_le (copyDown_meetsContract (w := w) hM) (vs := [h, h₁, v])
    (by simp [evalArgs, Expr.eval, Function.update, startState]) ?_
    ⟨h, h₁, v, rfl, hhh, by omega, hvw, hw1⟩ ?_
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hvw
  intro v₂ mem₂ pos₂ hpost₂
  obtain ⟨_, _, _, hargs₂, hv₂, hcopy, hbelow₂, habove₂⟩ := hpost₂
  simp only [List.cons.injEq, and_true] at hargs₂
  obtain ⟨rfl, rfl, rfl⟩ := hargs₂
  have hL : v - h₁ = (initBlock S a G phiNum phiDen M).length := by omega
  refine runs_ret_le (v := v₂) (by simp [Expr.eval, Function.update]) ⟨gAddr, phiNum, phiDen, M,
    h, h₁, rfl, by simp only [Outcome.value]; omega, by simp only [Outcome.value]; omega, ?_, ?_,
    fun y hy => (hbelow₂ y hy).trans (hbelow₁ y (by omega))⟩ ?_
  · intro i hi
    show mem₂ (h + i) = _
    rw [hcopy i (by omega)]
    exact hblock i hi
  · intro x hx
    simp only [Outcome.value] at hx
    show mem₂ x = 0
    rw [habove₂ x (by omega)]
    exact hzero₁ x (by omega)
  · have h1L := one_le_length_initBlock S a G phiNum phiDen M
    simp only [BuildContract, InitRestContract, copyDownContract, List.getD_cons_succ,
      List.getD_cons_zero, argsSize, Expr.size]
    generalize initRestSteps S.H S.x S.b S.owner S.label G.n G.m = St at *
    generalize (initBlock S a G phiNum phiDen M).length = L at *
    have e : (K + 80) * (St + L) = K * (St + L) + 80 * (St + L) := by ring
    rw [e]
    generalize K * (St + L) = A
    omega

/-! ### The rest of `Init` as a `HierProc` -/

/-- The specification of the builder: deterministic, a space function of the polynomial form,
and `BuildContract` for every static output and graph. -/
def BuildProcSpec (a : ℕ) (P : HierProc) (K : ℕ) (sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (C c : ℕ) :
    Prop :=
  P.NoRand ∧ SpaceForm a sR C c ∧
    ∀ w p j k, P.At p j k → ∀ S G, MeetsContract w p j (BuildContract w a K sR S G)

/-- The rest of `Init`: the entry `restEntry`, the builder, `copyDown`, the helpers of the
builder. -/
def restProc (PB : HierProc) : HierProc where
  entry k := restEntry k (k + 1)
  helpers k := [PB.entry (k + 2), copyDown] ++ PB.helpers (k + 2)

theorem moveDown_noRand : moveDown.NoRand := by
  simp [moveDown, forRange, forUp, Stmt.NoRand]

/-- **The rest of `Init` meets `RestProcSpec`** when the builder meets `BuildProcSpec`. -/
theorem restProc_spec (a : ℕ) (PB : HierProc) (K : ℕ) (sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (C c : ℕ)
    (hB : BuildProcSpec a PB K sR C c) : RestProcSpec a (restProc PB) (K + 80) sR C c := by
  obtain ⟨hnr, hf, hspec⟩ := hB
  refine ⟨fun k => ⟨?_, ?_⟩, hf, ?_⟩
  · simp [restProc, restEntry, Stmt.NoRand]
  · intro s hs
    simp only [restProc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl) | hs
    · exact (hnr _).1
    · exact copyDown_noRand
    · exact (hnr _).2 s hs
  intro w p j k hat S G
  obtain ⟨hj, hk⟩ := hat
  have hk' := hk
  simp only [restProc] at hk'
  have h2 := hasAt_append_left hk'
  have hBh := hasAt_append_right hk'
  simp only [List.length_cons, List.length_nil] at hBh
  have hBat : PB.At p k (k + 2) :=
    ⟨by simpa using h2 0 (by simp), by simpa [Nat.add_assoc] using hBh⟩
  have hM : p.procs[k + 1]? = some copyDown := by simpa using h2 1 (by simp)
  exact restEntry_meetsContract w a K sR S G p j k (k + 1) (hspec w p k (k + 2) hBat S G) hM
    (by simpa [restProc] using hj)

end MinCostFlow.HierPaths

end
