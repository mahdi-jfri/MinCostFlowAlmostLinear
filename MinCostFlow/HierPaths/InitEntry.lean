module

public import MinCostFlow.HierPaths.InitProg

/-!
# The `Init` procedure from its two parts

`initEntry fS fR` calls the static construction (procedure `fS`, `StaticContract`) and then the
rest of `Init` (procedure `fR`, `InitRestContract`), and returns the end of the block. This file
proves that it meets the clause of the initialization of `(hierRep a).Implements`
(`initEntry_initClause`), given bounds on the length of the block.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The entry of `Init`: `r5 := fS(args)`, `r6 := fR(args, r5)`, return `r6`. -/
def initEntry (fS fR : ℕ) : Stmt :=
  .seq (.call 5 fS [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4])
    (.seq (.call 6 fR [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5]) (.ret (.reg 6)))

/-- The potential of the initial state is `0`: nothing is deleted. -/
theorem potential_initConcrete (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).potential = 0 := by
  simp [HierConcrete.potential, initConcrete, StaticArrays.potential, DelState.init]

/-- The constant of `Init`. -/
def initConst (Ks K Kb : ℕ) : ℕ := Ks + 63 * K + K * Kb + K * Ks + 17

/-- **The clause of `Init`.** Let `fS` meet `StaticContract` and `fR` meet `InitRestContract`
for every static output and graph. Let the block have length at most `Kb · m · Γ` and at most
`sB phiNum phiDen n m M` when the static output is `Good`. Then `initEntry fS fR` meets the
clause of the initialization, for constants `hc` with `K_init = initConst Ks K Kb` and
`initSpace = sS + sR + sB`. -/
theorem initEntry_initClause (a : ℕ) (hc : HierConsts a) (w : ℕ) (p : Program) (j fS fR : ℕ)
    (Ks K Kb : ℕ) (sS sR sB : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (ha : 1 ≤ a) (hK : hc.K_init = (initConst Ks K Kb : ℝ))
    (hspace : ∀ phiNum phiDen n m M, hc.initSpace phiNum phiDen n m M =
      sS phiNum phiDen n m M + sR phiNum phiDen n m M + sB phiNum phiDen n m M)
    (hS : MeetsContract w p fS (StaticContract w a Ks hc.params sS))
    (hR : ∀ S G, MeetsContract w p fR (InitRestContract w a K sR S G))
    (hBlen : ∀ (S : StaticData) (G : Graph) (phiNum phiDen M : ℕ),
      S.Good a (dOf phiNum phiDen) M G →
      (initBlock S a G phiNum phiDen M).length ≤ Kb * G.m * gammaHP a (dOf phiNum phiDen) M)
    (hBsp : ∀ (S : StaticData) (G : Graph) (phiNum phiDen M : ℕ),
      S.Good a (dOf phiNum phiDen) M G →
      (initBlock S a G phiNum phiDen M).length ≤ sB phiNum phiDen G.n G.m M)
    (hj : p.procs[j]? = some (initEntry fS fR)) :
    InitClause (hierRep a) w p j (pathDSDataStructure hc.params w) := by
  intro args mem pos ω hw hpre hzero hsp
  have hpre' := hpre
  obtain ⟨gAddr, phiNum, phiDen, M, h, G, rfl, hgh, hGat, h1, h2, hval, hm, hmM, hdeg, hcond,
    hwidth⟩ := hpre
  have hRG : readGraph mem gAddr = G := graphAt_iff_readGraph.mp hGat
  have hheap : heapArg [gAddr, phiNum, phiDen, M, h] = h := rfl
  have hsp' : h + (sS phiNum phiDen G.n G.m M + sR phiNum phiDen G.n G.m M +
      sB phiNum phiDen G.n G.m M) < 2 ^ w := by
    have := hsp
    simp only [pathDSDataStructure, hheap, List.getD_cons_succ, List.getD_cons_zero, hRG] at this
    simpa [HierConsts.params, hierParams, hspace] using this
  refine ⟨_, hj, ?_⟩
  set d := dOf phiNum phiDen
  set Γ := gammaHP a d M
  have hΓ : 1 ≤ Γ := one_le_gammaHP a d M
  have hΓword : Γ < 2 ^ w := by
    have hγ : hc.params.γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M = (Γ : ℝ) := rfl
    rw [hγ, Nat.ceil_natCast] at hwidth
    let N := G.n + G.m + phiDen + M + Γ + 2
    have hlog : Nat.log 2 N + 1 ≤ w :=
      (Nat.le_mul_of_pos_left _ hc.params.hcw_pos).trans hwidth
    have hN : Γ ≤ N := by dsimp [N]; omega
    exact hN.trans_lt ((Nat.lt_pow_succ_log_self (by decide) N).trans_le
      (Nat.pow_le_pow_right (by decide) hlog))
  have hξ := (xiOf_le_gamma a d hmM).trans_lt hΓword
  have hlamWord := (lamOf_le_xiOf a d G.m).trans_lt hξ
  -- the run, with the conditions on the final state
  have hrun : ∃ o st' c, Runs w p ω (initEntry fS fR)
      (startState [gAddr, phiNum, phiDen, M, h] mem pos) o st' c ∧
      (∃ S : StaticData, S.Good a d M G ∧ (S.model a d G.m).Spec G ∧
        (S.model a d G.m).Fits a d G.m ∧
        h + (initBlock S a G phiNum phiDen M).length ≤ o.value ∧
        o.value ≤ h + sS phiNum phiDen G.n G.m M + (initBlock S a G phiNum phiDen M).length ∧
        ListAt st'.mem h (initBlock S a G phiNum phiDen M) ∧ ZeroFrom st'.mem o.value ∧
        (∀ y < h, st'.mem y = mem y)) ∧ 0 + c ≤ initConst Ks K Kb * G.m * Γ := by
    unfold initEntry
    refine runs_seq_call_le hS (vs := [gAddr, phiNum, phiDen, M, h]) (by rfl) hw ?_ ?_
    · refine ⟨hpre', hzero, ?_⟩
      show h + sS phiNum phiDen (readGraph mem gAddr).n (readGraph mem gAddr).m M < 2 ^ w
      rw [hRG]; omega
    intro v mem₁ pos₁ hpost
    obtain ⟨⟨hv1, hv2, hbelow₁, hzero₁, -⟩, gAddr', phiNum', phiDen', M', h', G', S, hargs,
      hGat', hSO, hSlen, hgood, hrest⟩ := hpost
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
    have hGG : G' = G :=
      (graphAt_iff_readGraph.mp hGat').symm.trans (graphAt_iff_readGraph.mp hGat)
    subst hGG
    have hv2' : v ≤ h + sS phiNum phiDen G'.n G'.m M := by
      have := hv2
      simp only [heapArg, List.getLastD, List.getD_cons_succ, List.getD_cons_zero,
        startState] at this
      simpa [hRG] using this
    have hGat₁ : GraphAt mem₁ gAddr G' := by
      intro i hi
      rw [hbelow₁ _ (by simp only [heapArg]; simp; omega)]
      exact hGat i hi
    refine runs_seq_call_le (hR S G') (vs := [gAddr, phiNum, phiDen, M, h, v])
      (by simp [evalArgs, Expr.eval, Function.update, startState]) ?_ ?_ ?_
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hw _ (by simp)
      · exact hw _ (by simp)
      · exact hw _ (by simp)
      · exact hw _ (by simp)
      · exact hw _ (by simp)
      · omega
    · exact ⟨gAddr, phiNum, phiDen, M, h, v, rfl, hSO, hSlen, hzero₁, hGat₁, by omega, h1, h2,
        hgood, by omega, hξ, hlamWord⟩
    intro v₂ mem₂ pos₂ hpost₂
    obtain ⟨_, _, _, _, _, _, hargs₂, hv₂lo, hv₂hi, hblock, hzero₂, hbelow₂⟩ := hpost₂
    simp only [List.cons.injEq, and_true] at hargs₂
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs₂
    refine runs_ret_le (v := v₂) (by simp [Expr.eval, Function.update])
      ⟨S, hgood, StaticData.spec_of_good hgood hrest, StaticData.fits_of_good hgood,
        hv₂lo, by dsimp only [Outcome.value]; omega, hblock, hzero₂,
        fun y hy => (hbelow₂ y hy).trans (hbelow₁ y hy)⟩ ?_
    have hcR := initRest_cost_le w a K ha sR S G' hgood [gAddr, phiNum, phiDen, M, h, v] mem₁
    have hb := hBlen S G' phiNum phiDen M hgood
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hcR
    simp only [argsSize, Expr.size, StaticContract, heapContract, startState, hRG,
      List.getD_cons_succ, List.getD_cons_zero]
    have hX : 1 ≤ G'.m * Γ := Nat.mul_le_mul hm hΓ
    have e1 : initConst Ks K Kb * G'.m * Γ = Ks * (G'.m * Γ) + 63 * K * (G'.m * Γ) +
        K * Kb * (G'.m * Γ) + K * (Ks * (G'.m * Γ)) + 17 * (G'.m * Γ) := by unfold initConst; ring
    have e2 : K * (63 * G'.m * Γ + Kb * G'.m * Γ) =
        63 * K * (G'.m * Γ) + K * Kb * (G'.m * Γ) := by
      ring
    have e3 : Ks * G'.m * Γ = Ks * (G'.m * Γ) := by ring
    have hcR' := hcR.trans (Nat.mul_le_mul_left K (Nat.add_le_add_left hb _))
    change _ + Ks * G'.m * Γ + _ + _ + _ + _ + _ ≤ _
    rw [e1, e3]
    rw [e2] at hcR'
    generalize G'.m * Γ = X at *
    generalize (InitRestContract w a K sR S G').cost [gAddr, phiNum, phiDen, M, h, v] mem₁ = Y at *
    generalize Ks * X = A at *
    generalize K * Kb * X = B at *
    generalize 63 * K * X = D at *
    generalize K * A = E at *
    omega
  obtain ⟨o, st', c, hr, ⟨S, hgood, hspec, hfits, hvlo, hvhi, hblock, hz, hbelow⟩, hcost⟩ := hrun
  have hvalid := initModel_valid hc.params h1 h2 hval hm hmM hdeg hcond
  refine ⟨o, st', c, hr, initAbs phiNum phiDen M G, initConcrete S a (initAbs phiNum phiDen M G),
    initConcrete_rep S a hspec hfits hvalid rfl rfl hblock,
    initPost_of_initPre hc.params w hpre' hGat, ⟨?_, ?_, hz, fun y hy _ => hbelow y hy, ?_⟩, ?_⟩
  · omega
  · have hB := hBsp S G phiNum phiDen M hgood
    show o.value ≤ h + hc.initSpace phiNum phiDen (readGraph mem gAddr).n (readGraph mem gAddr).m M
    rw [hRG, hspace]
    omega
  · intro y hy
    right
    exact ⟨hy.1, lt_of_lt_of_le hy.2 hvlo⟩
  · have hphi : (hierRep a).phi h (initConcrete S a (initAbs phiNum phiDen M G)) st'.mem = 0 := by
      simp only [hierRep, potential_initConcrete, Nat.mul_zero]
    show c + (hierRep a).phi h (initConcrete S a (initAbs phiNum phiDen M G)) st'.mem ≤
      Nat.ceil (hc.K_init * ((readGraph mem gAddr).m : ℝ) *
        hc.params.γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M)
    rw [hphi, hRG, hK, Nat.add_zero]
    have hγ : hc.params.γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M = (Γ : ℝ) := rfl
    rw [hγ]
    have hc' : (c : ℝ) ≤ ((initConst Ks K Kb * G.m * Γ : ℕ) : ℝ) := by exact_mod_cast (by omega : c ≤ _)
    push_cast at hc'
    exact Nat.cast_le.mp (hc'.trans (Nat.le_ceil _)) |>.trans (le_refl _)

end MinCostFlow.HierPaths

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ### The `Init` procedure as a `HierProc` -/

/-- The specification of the static construction: deterministic, a space
function of the polynomial form, and `StaticContract` for every `hc` with `cw₀ ≤ hc.cw`. -/
def StaticProcSpec (a : ℕ) (P : HierProc) (Ks : ℕ) (sS : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (C c cw₀ : ℕ) : Prop :=
  P.NoRand ∧ SpaceForm a sS C c ∧
    ∀ hc : HierConsts a, cw₀ ≤ hc.cw → ∀ w p j k, P.At p j k →
      MeetsContract w p j (StaticContract w a Ks hc.params sS)

/-- The specification of the rest of `Init`: deterministic, a space function of the polynomial
form, and `InitRestContract` for every static output and graph. -/
def RestProcSpec (a : ℕ) (P : HierProc) (K : ℕ) (sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (C c : ℕ) :
    Prop :=
  P.NoRand ∧ SpaceForm a sR C c ∧
    ∀ w p j k, P.At p j k → ∀ S G, MeetsContract w p j (InitRestContract w a K sR S G)

/-- The `Init` procedure: the entry `initEntry`, then the static construction and the rest
with their helpers. -/
def initProc (PS PR : HierProc) : HierProc where
  entry k := initEntry k (k + 1)
  helpers k :=
    let kS := k + 2
    let kR := kS + (PS.helpers kS).length
    [PS.entry kS, PR.entry kR] ++ PS.helpers kS ++ PR.helpers kR

/-- A sum of space functions of the polynomial form has the polynomial form. -/
theorem SpaceForm.add {a : ℕ} {f g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {C c C' c' : ℕ}
    (hf : SpaceForm a f C c) (hg : SpaceForm a g C' c') :
    SpaceForm a (fun phiNum phiDen n m M => f phiNum phiDen n m M + g phiNum phiDen n m M)
      (C + C') (max c c') := by
  intro phiNum phiDen n m M h1 h2
  have h1' := (hf.mono le_rfl (le_max_left c c')) phiNum phiDen n m M h1 h2
  have h2' := (hg.mono le_rfl (le_max_right c c')) phiNum phiDen n m M h1 h2
  rw [Nat.add_mul]
  exact Nat.add_le_add h1' h2'

/-- **The `Init` procedure meets `InitProcSpec`**, from the specifications of its two parts and
the bounds on the length of the block. -/
theorem initProc_spec (a : ℕ) (ha : 1 ≤ a) (PS PR : HierProc) (Ks K Kb : ℕ)
    (sS sR sB : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (CS cS CR cR CB cB cw₀ : ℕ)
    (hS : StaticProcSpec a PS Ks sS CS cS cw₀) (hR : RestProcSpec a PR K sR CR cR)
    (hB : SpaceForm a sB CB cB)
    (hBlen : ∀ (S : StaticData) (G : Graph) (phiNum phiDen M : ℕ),
      S.Good a (dOf phiNum phiDen) M G →
      (initBlock S a G phiNum phiDen M).length ≤ Kb * G.m * gammaHP a (dOf phiNum phiDen) M)
    (hBsp : ∀ (S : StaticData) (G : Graph) (phiNum phiDen M : ℕ),
      S.Good a (dOf phiNum phiDen) M G →
      (initBlock S a G phiNum phiDen M).length ≤ sB phiNum phiDen G.n G.m M) :
    InitProcSpec a (initProc PS PR) (initConst Ks K Kb)
      (fun phiNum phiDen n m M =>
        sS phiNum phiDen n m M + sR phiNum phiDen n m M + sB phiNum phiDen n m M)
      (CS + CR + CB) (max (max cS cR) cB) cw₀ := by
  obtain ⟨hnrS, hfS, hspecS⟩ := hS
  obtain ⟨hnrR, hfR, hspecR⟩ := hR
  refine ⟨fun k => ⟨?_, ?_⟩, Nat.cast_nonneg _, (hfS.add hfR).add hB, ?_⟩
  · simp [initProc, initEntry, Stmt.NoRand]
  · intro s hs
    simp only [initProc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with ((rfl | rfl) | hs) | hs
    · exact (hnrS _).1
    · exact (hnrR _).1
    · exact (hnrS _).2 s hs
    · exact (hnrR _).2 s hs
  intro hc hK hsp hcw w p j k hat
  obtain ⟨hj, hk⟩ := hat
  have hk' := hk
  simp only [initProc] at hk'
  have h2 := hasAt_append_left (hasAt_append_left hk')
  have hSh := hasAt_append_right (hasAt_append_left hk')
  have hRh := hasAt_append_right hk'
  simp only [List.length_append, List.length_cons, List.length_nil] at hSh hRh
  have hSat : PS.At p k (k + 2) :=
    ⟨by simpa using h2 0 (by simp), by simpa [Nat.add_assoc] using hSh⟩
  have hRat : PR.At p (k + 1) (k + 2 + (PS.helpers (k + 2)).length) := by
    refine ⟨by simpa using h2 1 (by simp), ?_⟩
    convert hRh using 1; omega
  exact initEntry_initClause a hc w p j k (k + 1) Ks K Kb sS sR sB ha hK
    (fun _ _ _ _ _ => by rw [hsp])
    (hspecS hc hcw w p _ _ hSat) (fun S G => hspecR w p _ _ hRat S G) hBlen hBsp
    (by simpa [initProc] using hj)

end MinCostFlow.HierPaths

end
