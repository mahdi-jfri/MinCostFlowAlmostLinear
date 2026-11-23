module

public import MinCostFlow.Spanner.ProgBuildWitnessProps

/-!
# Word-RAM Verification of Phases 0–2 of `buildWitnessCore` (`ProgBuildWitnessLoop`)

Verifies `buildPhase01Stmt` (scalar setup, `PathDS.boundsProcs` calls, and integer
threshold computation) and `buildCeLoopStmt` (loop constructing every component expander
`W_sub` via `ConstructExpander` and writing `compExt`).
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited
open WitnessCoreInput (dWInt)

/-! ## 1. Auxiliary sequence, memory, and layout helpers -/

/-- One-step bound for `cond (rA < rB) (rA := rB) (rA := rA)` taking both branches to `max a b`,
preserving flat `State.mk` representation. -/
theorem runs_seq_max_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {rA rB : ℕ} {s : Stmt} {m₀ regs₀ : ℕ → ℕ} {pos₀ : ℕ} {a b k T : ℕ}
    {Q : Outcome → State → Prop}
    (ha : regs₀ rA = a) (hb : regs₀ rB = b) (h1w : 1 < 2 ^ w)
    (hrest : ∃ o st' c, Runs w p ω s { mem := m₀, regs := Function.update regs₀ rA (max a b), pos := pos₀ }
      o st' c ∧ Q o st' ∧ (k + 7) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      ((Stmt.cond (.bin .lt (.reg rA) (.reg rB)) (.assign rA (.reg rB)) (.assign rA (.reg rA))).seq s)
      { mem := m₀, regs := regs₀, pos := pos₀ } o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have h0w : 0 < 2 ^ w := by omega
  have he : Expr.eval w { mem := m₀, regs := regs₀, pos := pos₀ } (.bin .lt (.reg rA) (.reg rB)) =
      some (if a < b then 1 else 0) := by
    by_cases hlt : a < b <;> simp [Expr.eval, BinOp.eval, ha, hb, hlt, h1w, h0w]
  refine runs_seq_cond_le (v := if a < b then 1 else 0) he ?_ ?_
  · intro hne
    have hlt : a < b := by by_contra h; simp [h] at hne
    have hupd : Function.update regs₀ rA b = Function.update regs₀ rA (max a b) := by
      rw [max_eq_right (Nat.le_of_lt hlt)]
    rcases hrest with ⟨o, st', c, hr, hq, hc⟩
    refine runs_seq_assign_flat (v := b) (e := .reg rB) (by simp [Expr.eval, hb]) ?_
    rw [hupd]
    exact ⟨o, st', c, hr, hq, by simp [Expr.size] at *; omega⟩
  · intro heq
    have hle : b ≤ a := by
      by_contra hlt
      have hlt' : a < b := Nat.lt_of_not_ge hlt
      simp [hlt'] at heq
    have hupd : Function.update regs₀ rA a = Function.update regs₀ rA (max a b) := by
      rw [max_eq_left hle]
    rcases hrest with ⟨o, st', c, hr, hq, hc⟩
    refine runs_seq_assign_flat (v := a) (e := .reg rA) (by simp [Expr.eval, ha]) ?_
    rw [hupd]
    exact ⟨o, st', c, hr, hq, by simp [Expr.size] at *; omega⟩

/-- Prefix version of `CompExtAt`: component `W_sub` graphs live strictly below `curH`. -/
def CompExtPrefixAt (mem : ℕ → ℕ) (a phiNum_dec curH : ℕ) (cs : List CompInfo) : Prop :=
  ∀ ci (hci : ci < cs.length),
    let c := cs[ci]
    let wSubPtr := mem (a + 6 * ci + 1)
    mem (a + 6 * ci) = c.wStart ∧
    mem (a + 6 * ci + 2) = 2 ^ c.level ∧
    mem (a + 6 * ci + 3) = phiNum_dec * 2 ^ c.level ∧
    mem (a + 6 * ci + 4) = c.X.card ∧
    mem (a + 6 * ci + 5) = c.W_sub.m ∧
    GraphAt mem wSubPtr c.W_sub ∧
    a + 6 * cs.length ≤ wSubPtr ∧
    wSubPtr + (2 + 2 * c.W_sub.m) ≤ curH

/-- Prefix version of `WitnessCoreInput.ValidWSubs` for the first `nDone` components. -/
def WitnessCoreInput.ValidWSubsPrefix (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (nDone : ℕ) (WSubs : List Graph) : Prop :=
  WSubs.length = nDone ∧
  ∀ (ci : ℕ) (hci : ci < nDone) (hcir : ci < inp.prep.rawComps.length),
    let rc := inp.prep.rawComps[ci]
    let W := WSubs.getD ci ⟨0, []⟩
    let wList := inp.compWeights rc
    W.n = rc.2.length ∧
    W.IsValid ∧
    W.IsConductanceExpanderOn W.verts ce.φ_Const ∧
    ∀ (k : ℕ) (hk : k < rc.2.length),
      let hk_w : k < wList.length := by
        dsimp only [wList, WitnessCoreInput.compWeights]
        rw [List.length_map, List.length_range]
        exact hk
      (wList[k]'hk_w : ℝ) ≤ (W.deg k : ℝ) ∧
      (W.deg k : ℝ) ≤ (ce.c_deg_int : ℝ) * (wList[k]'hk_w : ℝ)

theorem buildCompsFrom_append (inp : WitnessCoreInput) :
    ∀ offset xs₁ xs₂ ws₁ ws₂,
      ws₁.length = xs₁.length →
      inp.buildCompsFrom offset (xs₁ ++ xs₂) (ws₁ ++ ws₂) =
        inp.buildCompsFrom offset xs₁ ws₁ ++
          inp.buildCompsFrom (offset + (ws₁.map Graph.m).sum) xs₂ ws₂
  | offset, [], _, [], _, _ => by simp [WitnessCoreInput.buildCompsFrom]
  | _, [], _, _ :: _, _, h => by simp at h
  | _, _ :: _, _, [], _, h => by simp at h
  | offset, (lvl, X) :: rest, xs₂, W :: ws₁, ws₂, h => by
    simp only [List.length_cons] at h
    simp only [List.cons_append, WitnessCoreInput.buildCompsFrom, List.map_cons, List.sum_cons]
    have ih := buildCompsFrom_append inp (offset + W.m) rest xs₂ ws₁ ws₂ (by omega)
    rw [ih, add_assoc]

/-! ## 2. `Phase 0 + Phase 1` invariant and Triple -/

/-- Exact cost upper bound charged for `buildPhase01Stmt`. -/
def phase01Cost (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams) : ℕ :=
  350 +
    pds.K_bounds * (Nat.log 2 (inp.dJInt + inp.prep.J0_strip.m + 2) + 1) +
    pds.K_bounds * (Nat.log 2 (dWInt ce + inp.mwInt ce + 2) + 1)

/-- Initial header slots `0..11, 17..19` written by `buildPhase01Stmt`. -/
def WitnessHdr0 (mem : ℕ → ℕ) (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) : Prop :=
  mem inp.h = inp.mwInt ce ∧
  mem (inp.h + 1) = pds.phiOutDen inp.dJInt inp.prep.J0_strip.m ∧
  mem (inp.h + 2) = pds.gExp inp.dJInt inp.prep.J0_strip.m ∧
  mem (inp.h + 3) = pds.gDel inp.dJInt inp.prep.J0_strip.m ∧
  mem (inp.h + 4) = pds.phiOutDen (dWInt ce) (inp.mwInt ce) ∧
  mem (inp.h + 5) = pds.gExp (dWInt ce) (inp.mwInt ce) ∧
  mem (inp.h + 6) = pds.gDel (dWInt ce) (inp.mwInt ce) ∧
  mem (inp.h + 7) = inp.phiDsDenInt ce pds ∧
  mem (inp.h + 8) = inp.γExpInt ce pds ∧
  mem (inp.h + 9) = inp.γDelInt ce pds ∧
  mem (inp.h + 10) = inp.tau1Int ce pds ∧
  mem (inp.h + 11) = inp.tau2Int ce pds ∧
  mem (inp.h + 17) = inp.prep.phiNum_dec ∧
  mem (inp.h + 18) = inp.prep.phiDen_dec ∧
  mem (inp.h + 19) = inp.prep.J0_strip.m

/-- Post-condition after `buildPhase01Stmt`. -/
def Phase01Post (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (st : State) : Prop :=
  let aCompExt := st.regs 18
  let curH := st.regs 17
  st.regs 0 = inp.prep.jAddr ∧
  st.regs 1 = inp.statsAddr ∧
  st.regs 2 = inp.prep.decAddr ∧
  st.regs 3 = inp.prep.h ∧
  st.regs 4 = inp.h ∧
  st.regs 5 = inp.prep.J.n ∧
  st.regs 6 = inp.prep.J.m ∧
  st.regs 7 = maxDeg inp.prep.J ∧
  st.regs 8 = length inp.prep.J inp.embJH ∧
  st.regs 9 = vcongNat inp.prep.J inp.H' inp.embJH ∧
  st.regs 10 = inp.prep.phiNum_dec ∧
  st.regs 11 = inp.prep.phiDen_dec ∧
  st.regs 12 = inp.prep.j0Edges.length ∧
  st.regs 13 = inp.prep.aJ0Out ∧
  st.regs 14 = inp.prep.rawComps.length ∧
  st.regs 15 = inp.prep.aComps ∧
  st.regs 16 = inp.prep.J0_strip.m ∧
  st.mem (inp.h + 12) = aCompExt ∧
  inp.h + 20 ≤ aCompExt ∧
  aCompExt ≤ inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
    pds.boundsSpace (dWInt ce) (inp.mwInt ce) ∧
  curH = aCompExt + 6 * inp.prep.rawComps.length ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  ZeroFrom st.mem curH ∧
  WitnessHdr0 st.mem inp ce pds

/-- Every address read from `PrepInput` and `statsAddr` in `buildWitnessCoreBody` lies strictly
below `inp.h`. -/
theorem WitnessCoreInput.input_reads_lt_h {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {w : ℕ} (hvalid : inp.Valid ce pds mem₀ w) :
    inp.prep.jAddr + 1 < inp.h ∧
    inp.statsAddr + 2 < inp.h ∧
    inp.prep.decAddr + 2 < inp.h ∧
    inp.prep.h + 5 < inp.h ∧
    inp.prep.aJ0Out + inp.prep.j0Edges.length ≤ inp.h ∧
    inp.prep.aComps + 7 * inp.prep.rawComps.length ≤ inp.h ∧
    (∀ k < inp.prep.J.m, inp.prep.jAddr + 3 + 2 * k < inp.h) ∧
    (∀ ci (hci : ci < inp.prep.rawComps.length),
      inp.prep.cVertsPtr ci + inp.prep.rawComps[ci].2.length ≤ inp.h ∧
      inp.prep.cJOrigPtr ci + (inp.prep.cJSub inp.prep.rawComps[ci]).m ≤ inp.h ∧
      inp.prep.cDegPtr ci + inp.prep.rawComps[ci].2.length ≤ inp.h) := by
  have hv := hvalid.2.2.1
  have hhend : inp.prep.hEnd ≤ inp.h := hvalid.2.2.2.1
  have hst : inp.statsAddr + 3 ≤ inp.h := hvalid.2.2.2.2.1
  have hj_enc : inp.prep.jAddr + inp.prep.J.encode.length ≤ inp.prep.h := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdec_enc : inp.prep.decAddr + (Decompose.encode inp.prep.d_ℓ inp.prep.phiNum_dec
      inp.prep.phiDen_dec inp.prep.level inp.prep.rawComps).length ≤ inp.prep.h :=
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hblocks := inp.prep.hBlocksStart_eq
  have hj_len : inp.prep.J.encode.length = 2 + 2 * inp.prep.J.m := by
    simp [Graph.encode, Graph.m]; omega
  have hdec_len : 3 ≤ (Decompose.encode inp.prep.d_ℓ inp.prep.phiNum_dec
      inp.prep.phiDen_dec inp.prep.level inp.prep.rawComps).length := by
    simp [Decompose.encode]
  have hb_le : inp.prep.hBlocksStart ≤ inp.prep.hEnd := Nat.le_add_right _ _
  have hprep_lt : inp.prep.h + 8 ≤ inp.prep.hEnd := by
    simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out,
      PrepInput.aEdgeNext, PrepInput.aLvlHead] at hblocks
    omega
  refine ⟨by rw [hj_len] at hj_enc; omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out,
      PrepInput.aEdgeNext, PrepInput.aLvlHead] at hblocks ⊢
    omega
  · simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out,
      PrepInput.aEdgeNext, PrepInput.aLvlHead] at hblocks ⊢
    omega
  · intro k hk
    rw [hj_len] at hj_enc
    have : inp.prep.h ≤ inp.h := by omega
    omega
  · intro ci hci
    have hsucc := inp.prep.cJSubPtr_succ hci
    have hle : inp.prep.cJSubPtr (ci + 1) ≤ inp.prep.hEnd := inp.prep.cJSubPtr_le_hEnd (by omega)
    have hget : inp.prep.rawComps.getD ci (0, []) = inp.prep.rawComps[ci] := List.getD_eq_getElem _ _ hci
    have hend_eq : inp.prep.cEndPtr ci = inp.prep.cDegPtr ci + inp.prep.rawComps[ci].2.length := by
      unfold PrepInput.cEndPtr; rw [hget]
    have hdeg_eq : inp.prep.cDegPtr ci = inp.prep.cJOrigPtr ci + (inp.prep.cJSub inp.prep.rawComps[ci]).m := by
      unfold PrepInput.cDegPtr; rw [hget]
    have hflat_len : (List.flatMap compRecord inp.prep.rawComps).length =
        (inp.prep.rawComps.map fun p => 2 + p.2.length).sum := by
      induction inp.prep.rawComps with
      | nil => simp
      | cons a t ih =>
        simp [compRecord, List.flatMap_cons, ih]
        omega
    have htake_le : (List.map (fun p => 2 + p.2.length) (List.take ci inp.prep.rawComps)).sum +
        (2 + inp.prep.rawComps[ci].2.length) ≤
        (List.map (fun p => 2 + p.2.length) inp.prep.rawComps).sum := by
      have hsplit : inp.prep.rawComps = inp.prep.rawComps.take ci ++ inp.prep.rawComps.drop ci :=
        (List.take_append_drop ci inp.prep.rawComps).symm
      have hdrop : inp.prep.rawComps.drop ci =
          inp.prep.rawComps[ci] :: inp.prep.rawComps.drop (ci + 1) :=
        List.drop_eq_getElem_cons hci
      conv_rhs => rw [hsplit, hdrop, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      omega
    have hlen_lvl : inp.prep.level.length = inp.prep.J0_strip.m := hv.2.2.2.2.2.2.2.1
    have hverts_le : inp.prep.cVertsPtr ci + inp.prep.rawComps[ci].2.length ≤
        inp.prep.decAddr + (Decompose.encode inp.prep.d_ℓ inp.prep.phiNum_dec
          inp.prep.phiDen_dec inp.prep.level inp.prep.rawComps).length := by
      simp only [PrepInput.cVertsPtr, Decompose.encode, List.length_append, List.length_cons,
        List.length_nil, hlen_lvl, hflat_len]
      omega
    refine ⟨by omega, by omega, by omega⟩

private lemma maxWordBound_bounds {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {w : ℕ} (hvalid : inp.Valid ce pds mem₀ w) :
    1 < 2 ^ w ∧
    inp.maxHeapEnd ce pds < 2 ^ w ∧
    inp.mwInt ce ≤ 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2 ∧
    inp.dJInt ≤ inp.prep.phiDen_dec ∧
    dWInt ce ≤ ce.phiDen ∧
    4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec +
      2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec + 2 * ce.phiDen + 2 < 2 ^ w ∧
    2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) *
      (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) + 2 < 2 ^ w ∧
    1 ≤ dWInt ce ∧
    1 ≤ inp.dJInt ∧
    4 ≤ inp.tau2Int ce pds := by
  have hv := hvalid.2.2.1
  have hpn := hv.2.2.2.2.2.2.2.2.1
  have hpnd := hv.2.2.2.2.2.2.2.2.2.1
  have hmb := hvalid.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1w := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hheap : inp.maxHeapEnd ce pds ≤ inp.maxWordBound ce pds := le_max_left _ _
  have hm_r : 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec +
      2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec + 2 * ce.phiDen + 2 ≤
      inp.maxWordBound ce pds := le_trans (le_max_left _ _) (le_max_right _ _)
  have htau_r : 2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) *
      (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) + 2 ≤
      inp.maxWordBound ce pds := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmw : inp.mwInt ce ≤ 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2 := by
    unfold WitnessCoreInput.mwInt
    have hdiv := Nat.div_le_self
      (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1)
      inp.prep.phiNum_dec
    have h1 : 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1 ≤
        2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec := by omega
    have h2 : (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1) /
        inp.prep.phiNum_dec ≤
        2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 1 := by
      have hdiv2 : (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1) /
          inp.prep.phiNum_dec ≤
          (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec) /
            inp.prep.phiNum_dec := Nat.div_le_div_right h1
      have hadd : (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec) /
          inp.prep.phiNum_dec =
          (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec) / inp.prep.phiNum_dec + 1 :=
        Nat.add_div_right _ hpn
      have hds := Nat.div_le_self (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec)
        inp.prep.phiNum_dec
      omega
    omega
  have hdJ1 : 1 ≤ inp.dJInt := by
    unfold WitnessCoreInput.dJInt
    exact Nat.div_pos (by omega) hpn
  have hdJle : inp.dJInt ≤ inp.prep.phiDen_dec := by
    unfold WitnessCoreInput.dJInt
    have h1 : inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1 ≤
        inp.prep.phiDen_dec * inp.prep.phiNum_dec + (inp.prep.phiNum_dec - 1) := by
      have : inp.prep.phiDen_dec ≤ inp.prep.phiDen_dec * inp.prep.phiNum_dec :=
        Nat.le_mul_of_pos_right _ hpn
      omega
    calc (inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1) / inp.prep.phiNum_dec
        ≤ (inp.prep.phiDen_dec * inp.prep.phiNum_dec + (inp.prep.phiNum_dec - 1)) / inp.prep.phiNum_dec :=
          Nat.div_le_div_right h1
      _ = inp.prep.phiDen_dec + (inp.prep.phiNum_dec - 1) / inp.prep.phiNum_dec := by
          rw [Nat.mul_comm, Nat.mul_add_div hpn]
      _ = inp.prep.phiDen_dec := by
          rw [Nat.div_eq_of_lt (by omega), add_zero]
  have hdW1 : 1 ≤ dWInt ce := by
    unfold dWInt
    exact Nat.div_pos (by have := ce.hphi_pos; have := ce.hphi_le; omega) ce.hphi_pos
  have hdWle : dWInt ce ≤ ce.phiDen := by
    unfold dWInt
    have := ce.hphi_pos
    have h1 : ce.phiDen + ce.phiNum - 1 ≤ ce.phiDen * ce.phiNum + (ce.phiNum - 1) := by
      have : ce.phiDen ≤ ce.phiDen * ce.phiNum := Nat.le_mul_of_pos_right _ ce.hphi_pos
      omega
    calc (ce.phiDen + ce.phiNum - 1) / ce.phiNum
        ≤ (ce.phiDen * ce.phiNum + (ce.phiNum - 1)) / ce.phiNum := Nat.div_le_div_right h1
      _ = ce.phiDen + (ce.phiNum - 1) / ce.phiNum := by rw [Nat.mul_comm, Nat.mul_add_div ce.hphi_pos]
      _ = ce.phiDen := by rw [Nat.div_eq_of_lt (by omega), add_zero]
  have hphi_ds2 : 2 ≤ inp.phiDsDenInt ce pds := by
    unfold WitnessCoreInput.phiDsDenInt
    exact le_trans (le_trans (le_max_left 2 inp.dJInt) (pds.hphiOutDen_ge inp.dJInt _ hdJ1)) (le_max_left _ _)
  have hγE2 : 2 ≤ inp.γExpInt ce pds := by
    unfold WitnessCoreInput.γExpInt WitnessCoreInput.phiDsDenInt at *
    have h1 := le_trans (pds.hphiOutDen_ge inp.dJInt inp.prep.J0_strip.m hdJ1)
      (pds.hgExp_ge inp.dJInt inp.prep.J0_strip.m hdJ1)
    exact le_trans (le_trans (le_max_left 2 _) h1) (le_max_left _ _)
  have hγD1 : 1 ≤ inp.γDelInt ce pds := by
    unfold WitnessCoreInput.γDelInt
    exact le_trans (pds.hgDel_ge inp.dJInt inp.prep.J0_strip.m hdJ1) (le_max_left _ _)
  have htau2_4 : 4 ≤ inp.tau2Int ce pds := by
    unfold WitnessCoreInput.tau2Int
    have h1 : 2 ≤ inp.γExpInt ce pds * inp.γDelInt ce pds := by nlinarith
    nlinarith
  exact ⟨h1w, lt_of_le_of_lt hheap hmb, hmw, hdJle, hdWle, lt_of_le_of_lt hm_r hmb,
    lt_of_le_of_lt htau_r hmb, hdW1, hdJ1, htau2_4⟩

/-- Precondition right after the second `boundsProcs` call in `buildPhase01Stmt`. -/
private def Phase01AfterCall2Pre (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) (mem₀ : ℕ → ℕ) (v₁ v₂ : ℕ) (st : State) : Prop :=
  st.regs 0 = inp.prep.jAddr ∧
  st.regs 1 = inp.statsAddr ∧
  st.regs 2 = inp.prep.decAddr ∧
  st.regs 3 = inp.prep.h ∧
  st.regs 4 = inp.h ∧
  st.regs 5 = inp.prep.J.n ∧
  st.regs 6 = inp.prep.J.m ∧
  st.regs 7 = maxDeg inp.prep.J ∧
  st.regs 8 = length inp.prep.J inp.embJH ∧
  st.regs 9 = vcongNat inp.prep.J inp.H' inp.embJH ∧
  st.regs 10 = inp.prep.phiNum_dec ∧
  st.regs 11 = inp.prep.phiDen_dec ∧
  st.regs 12 = inp.prep.j0Edges.length ∧
  st.regs 13 = inp.prep.aJ0Out ∧
  st.regs 14 = inp.prep.rawComps.length ∧
  st.regs 15 = inp.prep.aComps ∧
  st.regs 16 = inp.prep.J0_strip.m ∧
  st.regs 17 = v₁ ∧
  st.regs 22 = v₂ ∧
  st.regs 23 = pds.phiOutDen inp.dJInt inp.prep.J0_strip.m ∧
  st.regs 24 = pds.gExp inp.dJInt inp.prep.J0_strip.m ∧
  st.regs 25 = pds.gDel inp.dJInt inp.prep.J0_strip.m ∧
  inp.h + 20 ≤ v₁ ∧
  v₁ + 3 ≤ v₂ ∧
  v₂ ≤ inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
    pds.boundsSpace (dWInt ce) (inp.mwInt ce) ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  (st.mem inp.h = inp.mwInt ce ∧
    st.mem (inp.h + 1) = pds.phiOutDen inp.dJInt inp.prep.J0_strip.m ∧
    st.mem (inp.h + 2) = pds.gExp inp.dJInt inp.prep.J0_strip.m ∧
    st.mem (inp.h + 3) = pds.gDel inp.dJInt inp.prep.J0_strip.m ∧
    st.mem (inp.h + 17) = inp.prep.phiNum_dec ∧
    st.mem (inp.h + 18) = inp.prep.phiDen_dec ∧
    st.mem (inp.h + 19) = inp.prep.J0_strip.m) ∧
  ListAt st.mem v₁ [pds.phiOutDen (dWInt ce) (inp.mwInt ce),
    pds.gExp (dWInt ce) (inp.mwInt ce), pds.gDel (dWInt ce) (inp.mwInt ce)] ∧
  ZeroFrom st.mem v₂

/-- Tail of `buildPhase01Stmt` starting right after the second `boundsProcs` call (lines 65–85). -/
private lemma phase01_afterCall2_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} (hvalid : inp.Valid ce pds mem₀ w) (v₁ v₂ : ℕ) :
    Triple w p (Phase01AfterCall2Pre inp ce pds mem₀ v₁ v₂)
      (.assign 26 (.load (.reg 17)) ;;
       .assign 27 (.load (.bin .add (.reg 17) (.const 1))) ;;
       .assign 28 (.load (.bin .add (.reg 17) (.const 2))) ;;
       .store (.bin .add (.reg 4) (.const 4)) (.reg 26) ;;
       .store (.bin .add (.reg 4) (.const 5)) (.reg 27) ;;
       .store (.bin .add (.reg 4) (.const 6)) (.reg 28) ;;
       .assign 17 (.reg 22) ;;
       .cond (.bin .lt (.reg 23) (.reg 26)) (.assign 23 (.reg 26)) (.assign 23 (.reg 23)) ;;
       .cond (.bin .lt (.reg 24) (.reg 27)) (.assign 24 (.reg 27)) (.assign 24 (.reg 24)) ;;
       .cond (.bin .lt (.reg 25) (.reg 28)) (.assign 25 (.reg 28)) (.assign 25 (.reg 25)) ;;
       .store (.bin .add (.reg 4) (.const 7)) (.reg 23) ;;
       .store (.bin .add (.reg 4) (.const 8)) (.reg 24) ;;
       .store (.bin .add (.reg 4) (.const 9)) (.reg 25) ;;
       .assign 27 (.bin .mul (.bin .mul (.reg 24) (.reg 25)) (.reg 23)) ;;
       .store (.bin .add (.reg 4) (.const 11)) (.reg 27) ;;
       .assign 26 (.bin .mul (.bin .mul (.bin .mul (.const 2) (.reg 27)) (.reg 8))
         (.bin .add (.reg 9) (.reg 7))) ;;
       .store (.bin .add (.reg 4) (.const 10)) (.reg 26) ;;
       .assign 18 (.reg 17) ;;
       .store (.bin .add (.reg 4) (.const 12)) (.reg 18) ;;
       .assign 17 (.bin .add (.reg 17) (.bin .mul (.const 6) (.reg 14))))
      (normalPost (Phase01Post inp ce pds mem₀))
      (fun _ => 140) := by
  intro st ω hpre
  rcases hpre with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    hr14, hr15, hr16, hr17, hr22, hr23, hr24, hr25, hv1_lo, hv2_lo, hv2_hi, hless, hhdr0,
    hlistW, hzf⟩
  rcases maxWordBound_bounds hvalid with ⟨h1w, hheap_w, _, _, _, _, htau_w, hdW1, hdJ1, htau2_4⟩
  have hv_mhe : inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
      pds.boundsSpace (dWInt ce) (inp.mwInt ce) + 6 * inp.prep.rawComps.length ≤ inp.maxHeapEnd ce pds := by
    simp [WitnessCoreInput.maxHeapEnd]; omega
  have hv2_6_lt : v₂ + 6 * inp.prep.rawComps.length < 2 ^ w := by omega
  have hv2_lt : v₂ < 2 ^ w := by omega
  have hv1_2_lt : v₁ + 2 < 2 ^ w := by omega
  have hrc_lt : inp.prep.rawComps.length < 2 ^ w := by omega
  have hh12_lt : inp.h + 12 < 2 ^ w := by omega
  have hphi_ge2 : 2 ≤ inp.phiDsDenInt ce pds :=
    le_trans (le_trans (le_max_left 2 _) (pds.hphiOutDen_ge inp.dJInt _ hdJ1)) (le_max_left _ _)
  have hγE_ge2 : 2 ≤ inp.γExpInt ce pds :=
    le_trans (le_trans (le_max_left 2 _) (pds.hphiOutDen_ge inp.dJInt _ hdJ1))
      (le_trans (pds.hgExp_ge inp.dJInt _ hdJ1) (le_max_left _ _))
  have hγD_ge1 : 1 ≤ inp.γDelInt ce pds :=
    le_trans (pds.hgDel_ge inp.dJInt _ hdJ1) (le_max_left _ _)
  have hprod_ge1 : 1 ≤ (length inp.prep.J inp.embJH + 1) *
      (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have h2tau2_lt : 2 * inp.tau2Int ce pds < 2 ^ w := by
    have h1 : 2 * inp.tau2Int ce pds ≤ 2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) *
        (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) := by
      calc 2 * inp.tau2Int ce pds = 2 * inp.tau2Int ce pds * 1 := by ring
        _ ≤ 2 * inp.tau2Int ce pds * ((length inp.prep.J inp.embJH + 1) *
            (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1)) :=
          Nat.mul_le_mul_left _ hprod_ge1
        _ = _ := by ring
    omega
  have htau2_lt : inp.tau2Int ce pds < 2 ^ w := by omega
  have hphi_lt : inp.phiDsDenInt ce pds < 2 ^ w := by
    have hle : inp.phiDsDenInt ce pds ≤ inp.tau2Int ce pds := by
      unfold WitnessCoreInput.tau2Int
      exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hγD_ge1)
    omega
  have hγE_lt : inp.γExpInt ce pds < 2 ^ w := by
    have hle : inp.γExpInt ce pds ≤ inp.tau2Int ce pds := by
      have : inp.γExpInt ce pds * 1 * 1 ≤ inp.γExpInt ce pds * inp.γDelInt ce pds * inp.phiDsDenInt ce pds :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hγD_ge1) (by omega)
      simpa [WitnessCoreInput.tau2Int] using this
    omega
  have hγD_lt : inp.γDelInt ce pds < 2 ^ w := by
    have hle : inp.γDelInt ce pds ≤ inp.tau2Int ce pds := by
      have : 1 * inp.γDelInt ce pds * 1 ≤ inp.γExpInt ce pds * inp.γDelInt ce pds * inp.phiDsDenInt ce pds :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
      simpa [WitnessCoreInput.tau2Int] using this
    omega
  have hl0 : st.mem v₁ = pds.phiOutDen (dWInt ce) (inp.mwInt ce) := by
    have := hlistW 0 (by simp); simpa using this
  have hl1 : st.mem (v₁ + 1) = pds.gExp (dWInt ce) (inp.mwInt ce) := by
    have := hlistW 1 (by simp); simpa using this
  have hl2 : st.mem (v₁ + 2) = pds.gDel (dWInt ce) (inp.mwInt ce) := by
    have := hlistW 2 (by simp); simpa using this
  have hγED_lt : inp.γExpInt ce pds * inp.γDelInt ce pds < 2 ^ w := by
    have hle : inp.γExpInt ce pds * inp.γDelInt ce pds ≤ inp.tau2Int ce pds :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h2tlen_lt : 2 * inp.tau2Int ce pds * length inp.prep.J inp.embJH < 2 ^ w := by
    have : length inp.prep.J inp.embJH ≤ length inp.prep.J inp.embJH + 1 := Nat.le_succ _
    have h1 : 1 ≤ vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1 := by omega
    have h2 : 2 * inp.tau2Int ce pds * length inp.prep.J inp.embJH ≤
        2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) *
        (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) := by
      calc 2 * inp.tau2Int ce pds * length inp.prep.J inp.embJH
          ≤ 2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) := Nat.mul_le_mul_left _ this
        _ ≤ _ := Nat.le_mul_of_pos_right _ h1
    omega
  have hvc_md_lt : vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J < 2 ^ w := by
    have h1 : 1 ≤ 2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) :=
      Nat.mul_pos (by omega) (Nat.succ_pos _)
    have h2 : vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J ≤
        2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) *
        (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) := by
      have : vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J ≤
          1 * (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) := by omega
      exact le_trans this (Nat.mul_le_mul_right _ h1)
    omega
  have htau1_lt : inp.tau1Int ce pds < 2 ^ w := by
    unfold WitnessCoreInput.tau1Int
    have h1 : length inp.prep.J inp.embJH ≤ length inp.prep.J inp.embJH + 1 := Nat.le_succ _
    have h2 : vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J ≤
        vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1 := Nat.le_succ _
    have h3 : 2 * inp.tau2Int ce pds * length inp.prep.J inp.embJH *
        (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J) ≤
        2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) *
        (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    omega
  cases st
  dsimp only at *
  refine runs_start_le ?_
  refine runs_seq_assign_flat (e := .load (.reg 17)) (by
    simp [Expr.eval, hr17, hl0]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 17) (.const 1))) (by
    simp [Expr.eval, BinOp.eval, hr17, hl1, h1w, show v₁ + 1 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 17) (.const 2))) (by
    simp [Expr.eval, BinOp.eval, hr17, hl2, show 2 < 2 ^ w by omega, show v₁ + 2 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 4)) (ev := .reg 26)
    (by simp [Expr.eval, BinOp.eval, hr4, show 4 < 2 ^ w by omega, show inp.h + 4 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 5)) (ev := .reg 27)
    (by simp [Expr.eval, BinOp.eval, hr4, show 5 < 2 ^ w by omega, show inp.h + 5 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 6)) (ev := .reg 28)
    (by simp [Expr.eval, BinOp.eval, hr4, show 6 < 2 ^ w by omega, show inp.h + 6 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_assign_flat (e := .reg 22) (by
    simp [Expr.eval, hr22]; rfl) ?_
  refine runs_seq_max_le (rA := 23) (rB := 26)
    (by simp [hr23]; rfl) (by simp; rfl) h1w ?_
  refine runs_seq_max_le (rA := 24) (rB := 27)
    (by simp [hr24]; rfl) (by simp; rfl) h1w ?_
  refine runs_seq_max_le (rA := 25) (rB := 28)
    (by simp [hr25]; rfl) (by simp; rfl) h1w ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 7)) (ev := .reg 23)
    (by simp [Expr.eval, BinOp.eval, hr4, show 7 < 2 ^ w by omega, show inp.h + 7 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 8)) (ev := .reg 24)
    (by simp [Expr.eval, BinOp.eval, hr4, show 8 < 2 ^ w by omega, show inp.h + 8 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 9)) (ev := .reg 25)
    (by simp [Expr.eval, BinOp.eval, hr4, show 9 < 2 ^ w by omega, show inp.h + 9 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .mul (.bin .mul (.reg 24) (.reg 25)) (.reg 23)) (by
    simp [Expr.eval, BinOp.eval]
    have hgE' : (max (pds.gExp inp.dJInt inp.prep.J0_strip.m)
        (pds.gExp (dWInt ce) (inp.mwInt ce))) = inp.γExpInt ce pds := rfl
    have hgD' : (max (pds.gDel inp.dJInt inp.prep.J0_strip.m)
        (pds.gDel (dWInt ce) (inp.mwInt ce))) = inp.γDelInt ce pds := rfl
    have hp' : (max (pds.phiOutDen inp.dJInt inp.prep.J0_strip.m)
        (pds.phiOutDen (dWInt ce) (inp.mwInt ce))) = inp.phiDsDenInt ce pds := rfl
    rw [hgE', hgD', hp']
    have hmul : inp.γExpInt ce pds * inp.γDelInt ce pds * inp.phiDsDenInt ce pds = inp.tau2Int ce pds := rfl
    simp [hγED_lt, hmul, htau2_lt]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 11)) (ev := .reg 27)
    (by simp [Expr.eval, BinOp.eval, hr4, show 11 < 2 ^ w by omega, show inp.h + 11 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .mul (.bin .mul (.bin .mul (.const 2) (.reg 27)) (.reg 8))
      (.bin .add (.reg 9) (.reg 7))) (by
    simp [Expr.eval, BinOp.eval, hr7, hr8, hr9]
    have hmul : 2 * inp.tau2Int ce pds * length inp.prep.J inp.embJH *
        (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J) = inp.tau1Int ce pds := rfl
    simp [show 2 < 2 ^ w by omega, h2tau2_lt, h2tlen_lt, hvc_md_lt, hmul, htau1_lt]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 10)) (ev := .reg 26)
    (by simp [Expr.eval, BinOp.eval, hr4, show 10 < 2 ^ w by omega, show inp.h + 10 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_assign_flat (e := .reg 17) (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 12)) (ev := .reg 18)
    (by simp [Expr.eval, BinOp.eval, hr4, show 12 < 2 ^ w by omega, hh12_lt]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_assign_le (r := 17) (e := .bin .add (.reg 17) (.bin .mul (.const 6) (.reg 14)))
    (v := v₂ + 6 * inp.prep.rawComps.length) ?_ ?_ ?_
  · simp [Expr.eval, BinOp.eval, hr14, show 6 < 2 ^ w by omega,
      show 6 * inp.prep.rawComps.length < 2 ^ w by omega, hv2_6_lt]
  · refine ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4], ?_⟩
    refine ⟨by simp [hr5], by simp [hr6], by simp [hr7], by simp [hr8], by simp [hr9],
      by simp [hr10], by simp [hr11], by simp [hr12], by simp [hr13], by simp [hr14],
      by simp [hr15], by simp [hr16], ?_, (by simp [Function.update]; omega),
      (by simp [Function.update]; exact hv2_hi), (by simp [Function.update]), ?_, ?_, ?_⟩
    · simp [Function.update]
    · intro a ha
      dsimp only
      repeat rw [Function.update_of_ne (by omega)]
      exact hless a ha
    · intro x hx
      dsimp only at hx ⊢
      rw [Function.update_self] at hx
      repeat rw [Function.update_of_ne (by omega)]
      exact hzf x (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (dsimp only; repeat rw [Function.update_of_ne (by omega)]; try simp only [Function.update_self]) <;>
        first
          | exact hhdr0.1
          | exact hhdr0.2.1
          | exact hhdr0.2.2.1
          | exact hhdr0.2.2.2.1
          | exact hhdr0.2.2.2.2.1
          | exact hhdr0.2.2.2.2.2.1
          | exact hhdr0.2.2.2.2.2.2
          | rfl
  · simp only [Expr.size]; omega

/-- Precondition right after the first `boundsProcs` call in `buildPhase01Stmt`. -/
private def Phase01AfterCall1Pre (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) (mem₀ : ℕ → ℕ) (v₁ : ℕ) (st : State) : Prop :=
  st.regs 0 = inp.prep.jAddr ∧
  st.regs 1 = inp.statsAddr ∧
  st.regs 2 = inp.prep.decAddr ∧
  st.regs 3 = inp.prep.h ∧
  st.regs 4 = inp.h ∧
  st.regs 5 = inp.prep.J.n ∧
  st.regs 6 = inp.prep.J.m ∧
  st.regs 7 = maxDeg inp.prep.J ∧
  st.regs 8 = length inp.prep.J inp.embJH ∧
  st.regs 9 = vcongNat inp.prep.J inp.H' inp.embJH ∧
  st.regs 10 = inp.prep.phiNum_dec ∧
  st.regs 11 = inp.prep.phiDen_dec ∧
  st.regs 12 = inp.prep.j0Edges.length ∧
  st.regs 13 = inp.prep.aJ0Out ∧
  st.regs 14 = inp.prep.rawComps.length ∧
  st.regs 15 = inp.prep.aComps ∧
  st.regs 16 = inp.prep.J0_strip.m ∧
  st.regs 17 = inp.h + 20 ∧
  st.regs 19 = inp.mwInt ce ∧
  st.regs 21 = dWInt ce ∧
  st.regs 22 = v₁ ∧
  inp.h + 23 ≤ v₁ ∧
  v₁ ≤ inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  (st.mem inp.h = inp.mwInt ce ∧
    st.mem (inp.h + 17) = inp.prep.phiNum_dec ∧
    st.mem (inp.h + 18) = inp.prep.phiDen_dec ∧
    st.mem (inp.h + 19) = inp.prep.J0_strip.m) ∧
  ListAt st.mem (inp.h + 20)
    [pds.phiOutDen inp.dJInt inp.prep.J0_strip.m,
     pds.gExp inp.dJInt inp.prep.J0_strip.m,
     pds.gDel inp.dJInt inp.prep.J0_strip.m] ∧
  ZeroFrom st.mem v₁

/-- Middle segment of `buildPhase01Stmt` starting right after the first `boundsProcs` call (lines 57–85). -/
private lemma phase01_afterCall1_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pdsImpl : PathDSImpl} {boundsBase : ℕ}
    {mem₀ : ℕ → ℕ}
    (hbounds : p.HasAt boundsBase (pdsImpl.boundsProcs boundsBase))
    (hvalid : inp.Valid ce pdsImpl.params mem₀ w) (v₁ : ℕ) :
    Triple w p (Phase01AfterCall1Pre inp ce pdsImpl.params mem₀ v₁)
      (.assign 23 (.load (.reg 17)) ;;
       .assign 24 (.load (.bin .add (.reg 17) (.const 1))) ;;
       .assign 25 (.load (.bin .add (.reg 17) (.const 2))) ;;
       .store (.bin .add (.reg 4) (.const 1)) (.reg 23) ;;
       .store (.bin .add (.reg 4) (.const 2)) (.reg 24) ;;
       .store (.bin .add (.reg 4) (.const 3)) (.reg 25) ;;
       .assign 17 (.reg 22) ;;
       .call 22 boundsBase [.reg 21, .reg 19, .reg 17] ;;
       .assign 26 (.load (.reg 17)) ;;
       .assign 27 (.load (.bin .add (.reg 17) (.const 1))) ;;
       .assign 28 (.load (.bin .add (.reg 17) (.const 2))) ;;
       .store (.bin .add (.reg 4) (.const 4)) (.reg 26) ;;
       .store (.bin .add (.reg 4) (.const 5)) (.reg 27) ;;
       .store (.bin .add (.reg 4) (.const 6)) (.reg 28) ;;
       .assign 17 (.reg 22) ;;
       .cond (.bin .lt (.reg 23) (.reg 26)) (.assign 23 (.reg 26)) (.assign 23 (.reg 23)) ;;
       .cond (.bin .lt (.reg 24) (.reg 27)) (.assign 24 (.reg 27)) (.assign 24 (.reg 24)) ;;
       .cond (.bin .lt (.reg 25) (.reg 28)) (.assign 25 (.reg 28)) (.assign 25 (.reg 25)) ;;
       .store (.bin .add (.reg 4) (.const 7)) (.reg 23) ;;
       .store (.bin .add (.reg 4) (.const 8)) (.reg 24) ;;
       .store (.bin .add (.reg 4) (.const 9)) (.reg 25) ;;
       .assign 27 (.bin .mul (.bin .mul (.reg 24) (.reg 25)) (.reg 23)) ;;
       .store (.bin .add (.reg 4) (.const 11)) (.reg 27) ;;
       .assign 26 (.bin .mul (.bin .mul (.bin .mul (.const 2) (.reg 27)) (.reg 8))
         (.bin .add (.reg 9) (.reg 7))) ;;
       .store (.bin .add (.reg 4) (.const 10)) (.reg 26) ;;
       .assign 18 (.reg 17) ;;
       .store (.bin .add (.reg 4) (.const 12)) (.reg 18) ;;
       .assign 17 (.bin .add (.reg 17) (.bin .mul (.const 6) (.reg 14))))
      (normalPost (Phase01Post inp ce pdsImpl.params mem₀))
      (fun _ => 195 + pdsImpl.params.K_bounds * (Nat.log 2 (dWInt ce + inp.mwInt ce + 2) + 1)) := by
  intro st ω hpre
  rcases hpre with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    hr14, hr15, hr16, hr17, hr19, hr21, hr22, hv1_lo, hv1_hi, hless, hhdr_sub, hlistJ, hzf⟩
  set pds := pdsImpl.params
  rcases maxWordBound_bounds hvalid with ⟨h1w, hheap_w, hmw_le, _, hdW_le, hm_w, _, hdW1, _, _⟩
  have hl0 : st.mem (inp.h + 20) = pds.phiOutDen inp.dJInt inp.prep.J0_strip.m := by
    have := hlistJ 0 (by simp); simpa using this
  have hl1 : st.mem (inp.h + 20 + 1) = pds.gExp inp.dJInt inp.prep.J0_strip.m := by
    have := hlistJ 1 (by simp); simpa using this
  have hl2 : st.mem (inp.h + 20 + 2) = pds.gDel inp.dJInt inp.prep.J0_strip.m := by
    have := hlistJ 2 (by simp); simpa using this
  have hv_mhe : inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
      pds.boundsSpace (dWInt ce) (inp.mwInt ce) ≤ inp.maxHeapEnd ce pds := by
    simp [WitnessCoreInput.maxHeapEnd]; omega
  have hh22_lt : inp.h + 22 < 2 ^ w := by omega
  have hv1_lt : v₁ < 2 ^ w := by omega
  have hdw_lt : dWInt ce < 2 ^ w := by omega
  have hmw_step : 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec ≤
      2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have hmw_lt : inp.mwInt ce < 2 ^ w := by omega
  have hcw_w : pds.cw * (Nat.log 2 (dWInt ce + inp.mwInt ce +
      pds.gExp (dWInt ce) (inp.mwInt ce) + pds.gDel (dWInt ce) (inp.mwInt ce) + 2) + 1) ≤ w :=
    hvalid.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspace_w : v₁ + pds.boundsSpace (dWInt ce) (inp.mwInt ce) < 2 ^ w := by omega
  cases st
  dsimp only at *
  refine runs_start_le ?_
  refine runs_seq_assign_flat (e := .load (.reg 17)) (by simp [Expr.eval, hr17, hl0]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 17) (.const 1)))
    (by simp [Expr.eval, BinOp.eval, hr17, hl1, h1w, show inp.h + 20 + 1 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 17) (.const 2)))
    (by simp [Expr.eval, BinOp.eval, hr17, hl2, show 2 < 2 ^ w by omega,
      show inp.h + 20 + 2 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 1)) (ev := .reg 23)
    (by simp [Expr.eval, BinOp.eval, hr4, h1w, show inp.h + 1 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 2)) (ev := .reg 24)
    (by simp [Expr.eval, BinOp.eval, hr4, show 2 < 2 ^ w by omega, show inp.h + 2 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 3)) (ev := .reg 25)
    (by simp [Expr.eval, BinOp.eval, hr4, show 3 < 2 ^ w by omega, show inp.h + 3 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_assign_flat (e := .reg 22) (by simp [Expr.eval, hr22]; rfl) ?_
  have hf : MeetsContract w p boundsBase (pathDSBoundsContract pds w) :=
    pdsImpl.boundsSpec w p boundsBase hbounds
  refine WordRAM.runs_seq_call_le (vs := [dWInt ce, inp.mwInt ce, v₁]) hf
    (by simp [evalArgs, Expr.eval, hr21, hr19])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> assumption)
    (by
      refine ⟨⟨dWInt ce, inp.mwInt ce, v₁, rfl, hdW1, hcw_w⟩, ?_, ?_⟩
      · intro x hx
        dsimp only at hx ⊢
        simp [heapArg] at hx
        repeat rw [Function.update_of_ne (by omega)]
        exact hzf x hx
      · simpa [heapArg] using hspace_w) ?_
  intro v₂ mem₂ pos₂ hpost
  rcases hpost with ⟨⟨hlo₂, hhi₂, hagree₂, hzf₂, d', M', h', heq_args, hlistW⟩, hv2_3⟩
  simp only [List.cons.injEq, and_true] at heq_args
  rcases heq_args with ⟨rfl, rfl, rfl⟩
  simp [heapArg] at hlo₂ hhi₂ hagree₂ hv2_3
  have hcost_eq (m : ℕ → ℕ) : (pathDSBoundsContract pds w).cost [dWInt ce, inp.mwInt ce, v₁] m =
      pds.K_bounds * (Nat.log 2 (dWInt ce + inp.mwInt ce + 2) + 1) := by
    simp [pathDSBoundsContract, heapContract]
  refine runs_triple_le (phase01_afterCall2_triple hvalid v₁ v₂) ?_ (fun _ _ h => h)
    (by rw [hcost_eq]; simp only [Expr.size, argsSize]; omega)
  dsimp only [Phase01AfterCall2Pre]
  refine ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
    by simp [hr5], by simp [hr6], by simp [hr7], by simp [hr8], by simp [hr9],
    by simp [hr10], by simp [hr11], by simp [hr12], by simp [hr13], by simp [hr14],
    by simp [hr15], by simp [hr16],
    (by simp [Function.update]), (by simp [Function.update]), (by simp [Function.update]),
    (by simp [Function.update]), (by simp [Function.update]),
    (by omega), hv2_3, (by omega),
    (fun x hx => by
      have ha2 := hagree₂ x (by omega)
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)] at ha2
      exact ha2.trans (hless x hx)),
    ⟨by rw [hagree₂ _ (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hhdr_sub.1,
     by rw [hagree₂ _ (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self],
     by rw [hagree₂ _ (by omega), Function.update_of_ne (by omega), Function.update_self],
     by rw [hagree₂ _ (by omega), Function.update_self],
     by rw [hagree₂ _ (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hhdr_sub.2.1,
     by rw [hagree₂ _ (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hhdr_sub.2.2.1,
     by rw [hagree₂ _ (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hhdr_sub.2.2.2⟩,
    hlistW, hzf₂⟩

/-- Scalar arithmetic word-size bounds used in the first half of `buildPhase01Stmt`. -/
private lemma buildPhase01_word_bounds {w : ℕ} {inp : WitnessCoreInput}
    {ce : ConstructExpanderImpl} {pds : PathDSParams} {mem₀ : ℕ → ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) :
    inp.h + 20 < 2 ^ w ∧
    inp.prep.aJ0Out < 2 ^ w ∧
    2 * ce.c_deg_int < 2 ^ w ∧
    inp.prep.J0_strip.m * inp.prep.phiDen_dec < 2 ^ w ∧
    2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) < 2 ^ w ∧
    inp.prep.phiNum_dec - 1 < 2 ^ w ∧
    2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) + (inp.prep.phiNum_dec - 1) < 2 ^ w ∧
    (2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) + (inp.prep.phiNum_dec - 1)) / inp.prep.phiNum_dec < 2 ^ w ∧
    inp.mwInt ce < 2 ^ w ∧
    inp.prep.phiDen_dec + (inp.prep.phiNum_dec - 1) < 2 ^ w ∧
    inp.dJInt < 2 ^ w ∧
    dWInt ce < 2 ^ w ∧
    inp.prep.J0_strip.m < 2 ^ w ∧
    inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m < 2 ^ w := by
  have hv := hvalid.2.2.1
  rcases maxWordBound_bounds hvalid with ⟨_, hheap_w, hmw_le, hdJ_le, hdW_le, hm_w, _, _, _, _⟩
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hhend : inp.prep.hEnd ≤ inp.h := hvalid.2.2.2.1
  have hh20_lt : inp.h + 20 < 2 ^ w := by
    have : inp.h + 20 ≤ inp.maxHeapEnd ce pds := by simp [WitnessCoreInput.maxHeapEnd]; omega
    omega
  have haJ0_lt : inp.prep.aJ0Out < 2 ^ w := by
    have : inp.prep.aJ0Out ≤ inp.prep.hEnd := by
      have hb := inp.prep.hBlocksStart_eq
      have : inp.prep.hBlocksStart ≤ inp.prep.hEnd := Nat.le_add_right _ _
      simp [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps] at hb
      omega
    omega
  have hpd_le : inp.prep.phiDen_dec ≤ 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by
    have h1 : 1 ≤ 4 * (inp.prep.J0_strip.m + 1) := by omega
    have h2 : inp.prep.phiDen_dec * 1 ≤ inp.prep.phiDen_dec * (4 * (inp.prep.J0_strip.m + 1)) :=
      Nat.mul_le_mul_left _ h1
    linarith [show 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec =
      inp.prep.phiDen_dec * (4 * (inp.prep.J0_strip.m + 1)) by ring]
  have h2pd_le : 2 * inp.prep.phiDen_dec ≤ 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec :=
    Nat.mul_le_mul_right _ (by omega)
  have hce_pd_step : 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec ≤
      2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have h2ce_lt : 2 * ce.c_deg_int < 2 ^ w := by
    have h1 : 1 ≤ (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec :=
      Nat.mul_pos (Nat.succ_pos _) (by omega)
    have h2 : 2 * ce.c_deg_int ≤ 2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ h1
    omega
  have hm0_pd_lt : inp.prep.J0_strip.m * inp.prep.phiDen_dec < 2 ^ w := by
    have hce2 : 1 ≤ 2 * ce.c_deg_int := by have := ce.hc_deg_int; omega
    have h1 : inp.prep.J0_strip.m * inp.prep.phiDen_dec ≤
        (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    have h2 : (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec ≤
        2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ hce2
    omega
  have hterm_lt : 2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) < 2 ^ w := by
    have hmul : 2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) =
        2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by ring
    omega
  have hnum_mw_lt : 2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) +
      (inp.prep.phiNum_dec - 1) < 2 ^ w := by
    have hmul : 2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) =
        2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by ring
    omega
  have hdiv_mw_lt : (2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) +
      (inp.prep.phiNum_dec - 1)) / inp.prep.phiNum_dec < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hnum_mw_lt
  have hspace_J : inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m < 2 ^ w := by
    have : inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m ≤ inp.maxHeapEnd ce pds := by
      simp [WitnessCoreInput.maxHeapEnd]; omega
    omega
  have hm0_lt : inp.prep.J0_strip.m < 2 ^ w := by
    have : inp.prep.J0_strip.m ≤ inp.prep.aJ0Out := by simp [PrepInput.aJ0Out]
    omega
  refine ⟨hh20_lt, haJ0_lt, h2ce_lt, hm0_pd_lt, hterm_lt, by omega, hnum_mw_lt, hdiv_mw_lt,
    by omega, by omega, by omega, by omega, hm0_lt, hspace_J⟩

/-- Full verification of `buildPhase01Stmt`: computes integer scalars, invokes `boundsProcs` twice,
writes `WitnessHdr` slots `0..12, 17..19`, and sets up `aCompExt` and `curH`. -/
theorem buildPhase01_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pdsImpl : PathDSImpl} {boundsBase : ℕ}
    {mem₀ : ℕ → ℕ} {pos : ℕ}
    (hbounds : p.HasAt boundsBase (pdsImpl.boundsProcs boundsBase))
    (hvalid : inp.Valid ce pdsImpl.params mem₀ w) :
    Triple w p
      (fun st => st = startState [inp.prep.jAddr, inp.statsAddr, inp.prep.decAddr, inp.prep.h, inp.h] mem₀ pos)
      (buildPhase01Stmt ce.phiNum ce.phiDen ce.c_deg_int boundsBase)
      (normalPost (Phase01Post inp ce pdsImpl.params mem₀))
      (fun _ => phase01Cost inp ce pdsImpl.params) := by
  intro st ω hst
  subst hst
  set pds := pdsImpl.params
  have hv := hvalid.2.2.1
  rcases inp.input_reads_lt_h hvalid with ⟨_, _, _, _, _, _, _, _⟩
  rcases maxWordBound_bounds hvalid with ⟨h1w, hheap_w, hmw_le, hdJ_le, hdW_le, hm_w, _, hdW1, hdJ1, _⟩
  rcases buildPhase01_word_bounds hvalid with
    ⟨hh20_lt, haJ0_lt, h2ce_lt, hm0_pd_lt, hterm_lt, hpn_m1_lt, hnum_mw_lt, hdiv_mw_lt,
     hmw_lt, hnum_dJ_lt, hdJ_lt, hdW_lt, hm0_lt, hspace_J⟩
  have hJat := hv.2.1
  have hJn : mem₀ inp.prep.jAddr = inp.prep.J.n := graphAt_n hJat
  have hJm : mem₀ (inp.prep.jAddr + 1) = inp.prep.J.m := graphAt_m hJat
  have hst0 : mem₀ inp.statsAddr = maxDeg inp.prep.J := hvalid.2.2.2.2.2.1
  have hst1 : mem₀ (inp.statsAddr + 1) = length inp.prep.J inp.embJH := hvalid.2.2.2.2.2.2.1
  have hst2 : mem₀ (inp.statsAddr + 2) = vcongNat inp.prep.J inp.H' inp.embJH := hvalid.2.2.2.2.2.2.2.1
  have hdec := decomposeOutAt_fields hv.2.2.2.2.2.2.1
  have hpnum : mem₀ (inp.prep.decAddr + 1) = inp.prep.phiNum_dec := hdec.2.1
  have hpden : mem₀ (inp.prep.decAddr + 2) = inp.prep.phiDen_dec := hdec.2.2.1
  have hstat := hvalid.2.2.2.2.2.2.2.2.1
  have hj0l : mem₀ inp.prep.h = inp.prep.j0Edges.length := hstat.2.1
  have haj0 : mem₀ (inp.prep.h + 1) = inp.prep.aJ0Out := hstat.2.2.1
  have hrcl : mem₀ (inp.prep.h + 2) = inp.prep.rawComps.length := hstat.2.2.2.1
  have hac : mem₀ (inp.prep.h + 3) = inp.prep.aComps := hstat.2.2.2.2.1
  have haen : mem₀ (inp.prep.h + 5) = inp.prep.aEdgeNext := hstat.2.2.2.2.2.2.1
  have hm0_sub : inp.prep.aJ0Out - inp.prep.aEdgeNext = inp.prep.J0_strip.m := by
    simp [PrepInput.aJ0Out]
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hcw_J : pds.cw * (Nat.log 2 (inp.dJInt + inp.prep.J0_strip.m +
      pds.gExp inp.dJInt inp.prep.J0_strip.m + pds.gDel inp.dJInt inp.prep.J0_strip.m + 2) + 1) ≤ w :=
    hvalid.2.2.2.2.2.2.2.2.2.2.2.1
  have hzf0 : ZeroFrom mem₀ inp.h := hvalid.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [buildPhase01Stmt]
  refine runs_start_le ?_
  refine runs_seq_assign_flat (e := .load (.reg 0)) (by simp [Expr.eval, hJn]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 0) (.const 1)))
    (by simp [Expr.eval, BinOp.eval, hJm, h1w, show inp.prep.jAddr + 1 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.reg 1)) (by simp [Expr.eval, hst0]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 1) (.const 1)))
    (by simp [Expr.eval, BinOp.eval, hst1, h1w, show inp.statsAddr + 1 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 1) (.const 2)))
    (by simp [Expr.eval, BinOp.eval, hst2, show 2 < 2 ^ w by omega, show inp.statsAddr + 2 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 2) (.const 1)))
    (by simp [Expr.eval, BinOp.eval, hpnum, h1w, show inp.prep.decAddr + 1 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 2) (.const 2)))
    (by simp [Expr.eval, BinOp.eval, hpden, show 2 < 2 ^ w by omega, show inp.prep.decAddr + 2 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.reg 3)) (by simp [Expr.eval, hj0l]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 3) (.const 1)))
    (by simp [Expr.eval, BinOp.eval, haj0, h1w, show inp.prep.h + 1 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 3) (.const 2)))
    (by simp [Expr.eval, BinOp.eval, hrcl, show 2 < 2 ^ w by omega, show inp.prep.h + 2 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 3) (.const 3)))
    (by simp [Expr.eval, BinOp.eval, hac, show 3 < 2 ^ w by omega, show inp.prep.h + 3 < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .sub (.reg 13) (.load (.bin .add (.reg 3) (.const 5))))
    (by simp [Expr.eval, BinOp.eval, haen, show 5 < 2 ^ w by omega,
      show inp.prep.h + 5 < 2 ^ w by omega, hm0_sub, hm0_lt]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .add (.reg 4) (.const 20))
    (by simp [Expr.eval, BinOp.eval, show 20 < 2 ^ w by omega, hh20_lt]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .add (.bin .div (.bin .add (.bin .mul (.const (2 * ce.c_deg_int))
      (.bin .mul (.reg 16) (.reg 11))) (.bin .sub (.reg 10) (.const 1))) (.reg 10)) (.const 1)) (by
    simp only [Expr.eval, BinOp.eval, Function.update]
    simp [h1w, h2ce_lt, hm0_pd_lt, hterm_lt, hpn_m1_lt, hnum_mw_lt, hdiv_mw_lt]
    have hmw_eq : (2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) +
        (inp.prep.phiNum_dec - 1)) / inp.prep.phiNum_dec + 1 = inp.mwInt ce := by
      unfold WitnessCoreInput.mwInt
      rw [Nat.add_sub_assoc hpn, show 2 * ce.c_deg_int * (inp.prep.J0_strip.m * inp.prep.phiDen_dec) =
        2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec from by ring]
    simp [hmw_eq, hmw_lt]; rfl) ?_
  refine runs_seq_store_flat (ea := .reg 4) (ev := .reg 19)
    (by simp [Expr.eval]; rfl) (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 17)) (ev := .reg 10)
    (by simp [Expr.eval, BinOp.eval, show 17 < 2 ^ w by omega, show inp.h + 17 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 18)) (ev := .reg 11)
    (by simp [Expr.eval, BinOp.eval, show 18 < 2 ^ w by omega, show inp.h + 18 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 4) (.const 19)) (ev := .reg 16)
    (by simp [Expr.eval, BinOp.eval, show 19 < 2 ^ w by omega, show inp.h + 19 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .div (.bin .add (.reg 11) (.bin .sub (.reg 10) (.const 1)))
      (.reg 10)) (by
    simp only [Expr.eval, BinOp.eval, Function.update]
    have hdJ_eq : (inp.prep.phiDen_dec + (inp.prep.phiNum_dec - 1)) / inp.prep.phiNum_dec = inp.dJInt := by
      unfold WitnessCoreInput.dJInt; rw [Nat.add_sub_assoc hpn]
    simp [h1w, hpn_m1_lt, hnum_dJ_lt, hdJ_eq, hdJ_lt]; rfl) ?_
  refine runs_seq_assign_flat (e := .const ((ce.phiDen + ce.phiNum - 1) / ce.phiNum)) (by
    have hdW_eq : (ce.phiDen + ce.phiNum - 1) / ce.phiNum = dWInt ce := rfl
    simp [Expr.eval, hdW_eq, hdW_lt]; rfl) ?_
  have hf : MeetsContract w p boundsBase (pathDSBoundsContract pds w) :=
    pdsImpl.boundsSpec w p boundsBase hbounds
  refine WordRAM.runs_seq_call_le (vs := [inp.dJInt, inp.prep.J0_strip.m, inp.h + 20]) hf
    (by simp [evalArgs, Expr.eval])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
    (by
      refine ⟨⟨inp.dJInt, inp.prep.J0_strip.m, inp.h + 20, rfl, hdJ1, hcw_J⟩, ?_, ?_⟩
      · intro x hx
        dsimp only at hx ⊢
        simp [heapArg] at hx
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hzf0 x (by omega)
      · simpa [heapArg] using hspace_J) ?_
  intro v₁ mem₁ pos₁ hpost
  rcases hpost with ⟨⟨hlo₁, hhi₁, hagree₁, hzf₁, d', M', h', heq_args, hlistJ⟩, hv1_3⟩
  simp only [List.cons.injEq, and_true] at heq_args
  rcases heq_args with ⟨rfl, rfl, rfl⟩
  simp [heapArg] at hlo₁ hhi₁ hagree₁ hv1_3
  have hcost_eq (m : ℕ → ℕ) : (pathDSBoundsContract pds w).cost [inp.dJInt, inp.prep.J0_strip.m, inp.h + 20] m =
      pds.K_bounds * (Nat.log 2 (inp.dJInt + inp.prep.J0_strip.m + 2) + 1) := by
    simp [pathDSBoundsContract, heapContract]
  refine runs_triple_le (phase01_afterCall1_triple hbounds hvalid v₁) ?_ (fun _ _ h => h)
    (by simp only [phase01Cost, Expr.size, argsSize]; rw [hcost_eq]; dsimp only [pds]; omega)
  dsimp only [Phase01AfterCall1Pre]
  refine ⟨by simp [Function.update], by simp [Function.update], by simp [Function.update],
    by simp [Function.update], by simp [Function.update], by simp [Function.update],
    by simp [Function.update], by simp [Function.update], by simp [Function.update],
    by simp [Function.update], by simp [Function.update], by simp [Function.update],
    by simp [Function.update], by simp [Function.update], by simp [Function.update],
    by simp [Function.update], by simp [Function.update], by simp [Function.update],
    by simp [Function.update], by simp [Function.update], by simp [Function.update],
    hv1_3, hhi₁,
    (fun x hx => by
      have ha1 := hagree₁ x (by omega)
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at ha1
      exact ha1),
    ⟨by rw [hagree₁ _ (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
     by rw [hagree₁ _ (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self],
     by rw [hagree₁ _ (by omega), Function.update_of_ne (by omega), Function.update_self],
     by rw [hagree₁ _ (by omega), Function.update_self]⟩,
    hlistJ, hzf₁⟩

end MinCostFlow.Spanner
