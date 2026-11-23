module

public import MinCostFlow.Spanner.ProgWitnessPrepHelpers

/-!
# Phase A1 Verification for `witnessPrep` (`prepInit`, `prepBucket`, `prepJ0`)

Proves Hoare triples for initialization (`prepInitStmt`), downward bucket construction across
decomposition levels (`prepBucketStmt`), and level-0 edge collection (`prepJ0Stmt`).
-/

public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## 2. Phase A Proofs (`prepInit`, `prepBucket`, `prepJ0`, `prepHdrStore`, `prepParse`) -/

/-- Verification of `prepInitStmt`: loads `J.n`, `J0_strip.m`, `d_ℓ`, `rawComps.length`, and
computes table pointers into registers `5..12`. -/
theorem prepInit_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ) :
    Triple w p
      (fun st => st.mem = mem₀ ∧ inp.Valid mem₀ w ∧
        st.regs 0 = inp.jAddr ∧ st.regs 1 = inp.j0Addr ∧
        st.regs 2 = inp.nlAddr ∧ st.regs 3 = inp.decAddr ∧ st.regs 4 = inp.h)
      prepInitStmt
      (normalPost fun st => st.mem = mem₀ ∧ inp.Valid mem₀ w ∧
        PrepBaseRegs inp st ∧ st.regs 12 = 0)
      (fun _ => 60) := by
  intro st ω ⟨hmem, hv, hr0, hr1, hr2, hr3, hr4⟩
  have hsz := inp.size_bounds hv
  rcases hv with ⟨hJ, hgJ, hJ0, hgJ0, hnl, hlNl, hdec, hllen, hpn, hpnd, hpw, hprops, hdp,
    hjle, hj0le, hnlle, hdecle, hzero, hw1, hwb⟩
  have hdecF := decomposeOutAt_fields hdec
  have hJ_n : st.mem inp.jAddr = inp.J.n := hmem ▸ graphAt_n hgJ
  have hJ0_m : st.mem (inp.j0Addr + 1) = inp.J0_strip.m := hmem ▸ graphAt_m hgJ0
  have hd_l : st.mem inp.decAddr = inp.d_ℓ := hmem ▸ hdecF.1
  have hnc : st.mem (inp.decAddr + 3 + inp.J0_strip.m) = inp.rawComps.length := by
    rw [hmem, ← hllen]; exact hdecF.2.2.2.2.1
  have hlt1 : inp.jAddr < 2 ^ w := by omega
  have hlt2 : inp.j0Addr + 1 < 2 ^ w := by
    have : 2 + 2 * inp.J0_strip.m = inp.J0_strip.encode.length := (graph_encode_length _).symm
    omega
  have hlt3 : inp.decAddr < 2 ^ w := by omega
  have hlt4 : inp.decAddr + 3 + inp.J0_strip.m < 2 ^ w := by
    have hdl := decompose_encode_length inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps
    omega
  have hJ_n_lt : inp.J.n < 2 ^ w := by omega
  have hJ0_m_lt : inp.J0_strip.m < 2 ^ w := by omega
  have hd_l_lt : inp.d_ℓ < 2 ^ w := by omega
  have hnc_lt : inp.rawComps.length < 2 ^ w := by omega
  have ha9_lt : inp.aLvlHead < 2 ^ w := by simp only [PrepInput.aLvlHead]; omega
  have ha10_lt : inp.aEdgeNext < 2 ^ w := by simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have ha11_lt : inp.aJ0Out < 2 ^ w := by simp only [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  dsimp only [prepInitStmt]
  refine runs_seq_assign0 (v := inp.J.n) (ev_load (ev_reg hr0 hlt1) hJ_n hJ_n_lt) ?_
  refine runs_seq_assign_le (v := inp.J0_strip.m) ?_ ?_
  · exact ev_load (ev_add (ev_reg (by simp [hr1]) (by omega)) (ev_const hw1) hlt2) hJ0_m hJ0_m_lt
  refine runs_seq_assign_le (v := inp.d_ℓ) ?_ ?_
  · exact ev_load (ev_reg (by simp [hr3]) hlt3) hd_l hd_l_lt
  refine runs_seq_assign_le (v := inp.rawComps.length) ?_ ?_
  · exact ev_load (ev_add (ev_add (ev_reg (by simp [hr3]) hlt3) (ev_const (by omega)) (by omega)) (ev_reg (by simp) hJ0_m_lt) hlt4) hnc hnc_lt
  refine runs_seq_assign_le (v := inp.aLvlHead) ?_ ?_
  · exact ev_add (ev_reg (by simp [hr4]) (by omega)) (ev_const (by omega)) ha9_lt
  refine runs_seq_assign_le (v := inp.aEdgeNext) ?_ ?_
  · exact ev_add (ev_add (ev_reg (by simp) ha9_lt) (ev_reg (by simp) hd_l_lt) (by simp only [PrepInput.aLvlHead] at ha9_lt ⊢; omega)) (ev_const hw1) ha10_lt
  refine runs_seq_assign_le (v := inp.aJ0Out) ?_ ?_
  · exact ev_add (ev_reg (by simp) ha10_lt) (ev_reg (by simp) hJ0_m_lt) ha11_lt
  refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨0, ev_const (by omega), rfl, rfl, rfl⟩, ?_, by norm_num [Expr.size]⟩
  refine ⟨hmem, ⟨hJ, hgJ, hJ0, hgJ0, hnl, hlNl, hdec, hllen, hpn, hpnd, hpw, hprops, hdp, hjle, hj0le, hnlle, hdecle, hzero, hw1, hwb⟩, ?_, by simp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [PrepInput.aLvlHead, PrepInput.aEdgeNext, PrepInput.aJ0Out, hr0, hr1, hr2, hr3, hr4]

def prepBucketInv (inp : PrepInput) (mem₀ : ℕ → ℕ) (idx : ℕ) (st : State) : Prop :=
  idx ≤ inp.J0_strip.m ∧
  AgreeOutside st.mem mem₀ inp.aLvlHead inp.aJ0Out ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  PrepBaseRegs inp st ∧
  st.regs 12 = 0 ∧
  st.regs 19 = idx ∧
  (∀ lvl ≤ inp.d_ℓ, ChainAt st.mem inp.aEdgeNext (st.mem (inp.aLvlHead + lvl))
    (edgesAtFrom inp.level inp.J0_strip.m lvl idx)) ∧
  (∀ lvl ≤ inp.d_ℓ, st.mem (inp.aLvlHead + lvl) = 0 ∨
    ∃ b₀, idx ≤ b₀ ∧ b₀ < inp.J0_strip.m ∧ st.mem (inp.aLvlHead + lvl) = b₀ + 1) ∧
  (∀ b, b < idx → st.mem (inp.aEdgeNext + b) = 0) ∧
  (∀ b, idx ≤ b → b < inp.J0_strip.m → st.mem (inp.aEdgeNext + b) = 0 ∨
    ∃ b', b < b' ∧ b' < inp.J0_strip.m ∧ st.mem (inp.aEdgeNext + b) = b' + 1)

/-- Verification of `prepBucketStmt`: buckets `J0_strip` edges by decomposition level `0..d_ℓ`
in linear time `40 * J0_strip.m + 10` using linked arrays at `aLvlHead` and `aEdgeNext`. -/
theorem prepBucket_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv₀ : inp.Valid mem₀ w) :
    Triple w p
      (fun st => st.mem = mem₀ ∧ PrepBaseRegs inp st ∧ st.regs 12 = 0)
      prepBucketStmt
      (normalPost fun st =>
        AgreeOutside st.mem mem₀ inp.aLvlHead inp.aJ0Out ∧
        (∀ x < inp.h, st.mem x = mem₀ x) ∧
        PrepBaseRegs inp st ∧ st.regs 12 = 0 ∧
        ∀ lvl ≤ inp.d_ℓ, ChainAt st.mem inp.aEdgeNext (st.mem (inp.aLvlHead + lvl))
          (inp.decomp.edgesAt inp.J0_strip lvl))
      (fun _ => 40 * inp.J0_strip.m + 10) := by
  have _hsz := inp.size_bounds hv₀
  rcases hv₀ with ⟨hJ, hgJ, hJ0, hgJ0, hnl, hlNl, hdec, hllen, hpn, hpnd, hpw, hprops, hdp,
    hjle, hj0le, hnlle, hdecle, hzero, hw1, hwb⟩
  have hdecF := decomposeOutAt_fields hdec
  have hm0_lt : inp.J0_strip.m < 2 ^ w := by omega
  have hlvl_bound : ∀ b < inp.J0_strip.m, inp.level.getD b 0 ≤ inp.d_ℓ := fun b hb => hdp.2.1 b hb
  refine (Triple.seq_normal_const
      (R := prepBucketInv inp mem₀ inp.J0_strip.m) (c₁ := 3) (c₂ := 39 * inp.J0_strip.m + 4) ?_ ?_).conseq
    (fun st h => h) (fun o st h => h) (fun _ _ => by omega)
  · intro st ω ⟨hmem, hb, h12⟩
    refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨_, ev_reg hb.2.2.2.2.2.2.1 hm0_lt, rfl, rfl, rfl⟩,
      ?_, by norm_num [Expr.size]⟩
    refine ⟨le_rfl, hmem ▸ agreeOutside_refl mem₀ _ _, fun x _ => by rw [hmem],
      prepBaseRegs_update hb (by omega), by simp [h12], by simp,
      ?_, ?_, ?_, ?_⟩
    · intro lvl _
      rw [edgesAtFrom_m0, ChainAt, hmem]
      exact hzero _ (by simp [PrepInput.aLvlHead]; omega)
    · intro lvl _; left; rw [hmem]; exact hzero _ (by simp [PrepInput.aLvlHead]; omega)
    · intro b _; rw [hmem]; exact hzero _ (by simp [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
    · intro b h1 h2; omega
  · have hloop : ∀ idx₀ : ℕ, Triple w p (prepBucketInv inp mem₀ idx₀)
        (Stmt.loop (.bin .lt (.const 0) (.reg 19)) prepBucketBody)
        (normalPost fun st =>
          AgreeOutside st.mem mem₀ inp.aLvlHead inp.aJ0Out ∧
          (∀ x < inp.h, st.mem x = mem₀ x) ∧
          PrepBaseRegs inp st ∧ st.regs 12 = 0 ∧
          ∀ lvl ≤ inp.d_ℓ, ChainAt st.mem inp.aEdgeNext (st.mem (inp.aLvlHead + lvl))
            (inp.decomp.edgesAt inp.J0_strip lvl))
        (fun _ => 39 * idx₀ + 4) := by
      refine Triple.loop_inv (fun idx => idx) (fun idx => 39 * idx + 4)
        (condVal := fun st => if 0 < st.regs 19 then 1 else 0) ?_ ?_ ?_
      · intro idx st hinv
        have hr19 : st.regs 19 = idx := hinv.2.2.2.2.2.1
        have hlt19 : idx < 2 ^ w := by have := hinv.1; omega
        by_cases h0 : 0 < idx
        · simpa [hr19, h0] using ev_lt_t (ev_const (c := 0) (by omega)) (ev_reg hr19 hlt19) h0 hw1
        · simpa [hr19, h0] using ev_lt_f (ev_const (c := 0) (by omega)) (ev_reg hr19 hlt19) (by omega) hw1
      · intro idx st hinv hc
        have h0 : idx = 0 := by
          have hr19 := hinv.2.2.2.2.2.1
          by_contra hne; have : 0 < idx := Nat.pos_of_ne_zero hne
          simp [hr19, this] at hc
        subst h0
        refine ⟨⟨hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, fun lvl hlvl => ?_⟩, by norm_num [Expr.size]⟩
        simpa [edgesAtFrom, DecomposeOutput.edgesAt, PrepInput.decomp, mkDecomposeOutput] using
          hinv.2.2.2.2.2.2.1 lvl hlvl
      · intro idx st hinv hc
        have hr19 : st.regs 19 = idx := hinv.2.2.2.2.2.1
        have hpos : 0 < idx := by
          by_contra h0; simp [hr19, h0] at hc
        refine ⟨35, fun s ω hs => ?_⟩
        rcases hs with rfl
        rcases hinv with ⟨hidx_le, hagOut, hagLt, hb, h12, _, hch, hlhead, hzero_b, hnext_gt⟩
        set b := idx - 1
        have hbm : b < inp.J0_strip.m := by omega
        have hlvl_addr_lt : inp.decAddr + 3 + b < inp.h := by
          have := decompose_encode_length inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps
          omega
        have hlvl_eq : s.mem (inp.decAddr + 3 + b) = inp.level.getD b 0 := by
          rw [hagLt _ hlvl_addr_lt, listAt_sub_eq hdecF.2.2.2.1 (by omega)]
        set lvl := inp.level.getD b 0
        have hlvl_d : lvl ≤ inp.d_ℓ := hlvl_bound b hbm
        have hb_lt : b < 2 ^ w := by omega
        have hidx_lt : idx < 2 ^ w := by omega
        have hlvl_lt : lvl < 2 ^ w := by omega
        have hhd_addr_lt : inp.aLvlHead + lvl < 2 ^ w := by simp only [PrepInput.aLvlHead]; omega
        have hnxt_addr_lt : inp.aEdgeNext + b < 2 ^ w := by simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
        have hold_lt : s.mem (inp.aLvlHead + lvl) < 2 ^ w := by
          rcases hlhead lvl hlvl_d with h0 | ⟨b₀, _, hb₀, heq⟩
          · rw [h0]; omega
          · rw [heq]; omega
        dsimp only [prepBucketBody]
        refine runs_seq_assign0 (v := b) (ev_sub (ev_reg hr19 hidx_lt) (ev_const hw1) (by omega) hb_lt) ?_
        refine runs_seq_assign_le (v := lvl) ?_ ?_
        · exact ev_load (ev_add (ev_add (ev_reg (by simp [hb.2.2.2.1]) (by omega)) (ev_const (c := 3) (by omega)) (by omega)) (ev_reg (by simp) hb_lt) (by omega)) hlvl_eq hlvl_lt
        refine runs_seq_assign_le (v := s.mem (inp.aLvlHead + lvl)) ?_ ?_
        · exact ev_load (ev_add (ev_reg (by simp [hb.2.2.2.2.2.2.2.2.2.1]) (by simp [PrepInput.aLvlHead]; omega)) (ev_reg (by simp) hlvl_lt) hhd_addr_lt) rfl hold_lt
        refine runs_seq_store_le (x := inp.aEdgeNext + b) (v := s.mem (inp.aLvlHead + lvl)) ?_ ?_ ?_
        · exact ev_add (ev_reg (by simp [hb.2.2.2.2.2.2.2.2.2.2.1]) (by simp [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)) (ev_reg (by simp) hb_lt) hnxt_addr_lt
        · exact ev_reg (by simp) hold_lt
        refine runs_seq_store_le (x := inp.aLvlHead + lvl) (v := idx) ?_ ?_ ?_
        · exact ev_add (ev_reg (by simp [hb.2.2.2.2.2.2.2.2.2.1]) (by simp [PrepInput.aLvlHead]; omega)) (ev_reg (by simp) hlvl_lt) hhd_addr_lt
        · exact ev_reg (by simp [hr19]) hidx_lt
        refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨b, ev_reg (by simp) hb_lt, rfl, rfl, rfl⟩,
          ?_, by norm_num [Expr.size]⟩
        refine ⟨b, ?_, by simp only [Expr.size]; omega⟩
        dsimp only [prepBucketInv]
        set mem1 := Function.update s.mem (inp.aEdgeNext + b) (s.mem (inp.aLvlHead + lvl))
        set mem2 := Function.update mem1 (inp.aLvlHead + lvl) idx
        have hlo1 : inp.aLvlHead ≤ inp.aEdgeNext + b := by simp [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
        have hhi1 : inp.aEdgeNext + b < inp.aJ0Out := by simp [PrepInput.aJ0Out]; omega
        have hlo2 : inp.aLvlHead ≤ inp.aLvlHead + lvl := by omega
        have hhi2 : inp.aLvlHead + lvl < inp.aJ0Out := by simp [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
        have hag1 : AgreeOutside mem1 mem₀ inp.aLvlHead inp.aJ0Out :=
          agreeOutside_trans (agreeOutside_update (lo := inp.aLvlHead) (hi := inp.aJ0Out) hlo1 hhi1) hagOut le_rfl le_rfl
        have hag2 : AgreeOutside mem2 mem₀ inp.aLvlHead inp.aJ0Out :=
          agreeOutside_trans (agreeOutside_update (lo := inp.aLvlHead) (hi := inp.aJ0Out) hlo2 hhi2) hag1 le_rfl le_rfl
        refine ⟨by omega, hag2, fun x hx => ?_, ?_, by simp [h12], by simp, ?_, ?_, ?_, ?_⟩
        · exact hag2 x (Or.inl (by simp [PrepInput.aLvlHead]; omega))
        · exact prepBaseRegs_congr hb fun r hr => by
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        · intro lvl' hlvl'
          by_cases heq_l : lvl' = lvl
          · subst heq_l
            rw [edgesAtFrom_step_match hbm rfl]
            have hptr : mem2 (inp.aLvlHead + lvl) = b + 1 := by simp [mem2, b]; omega
            rw [hptr, ChainAt]
            refine ⟨rfl, ?_⟩
            have hnxt_eq : mem2 (inp.aEdgeNext + b) = s.mem (inp.aLvlHead + lvl) := by
              have hne : inp.aLvlHead + lvl ≠ inp.aEdgeNext + b := by
                simp only [PrepInput.aLvlHead, PrepInput.aEdgeNext]; omega
              simp [mem2, mem1, Function.update_of_ne hne.symm]
            rw [hnxt_eq, Nat.sub_add_cancel hpos]
            refine chainAt_of_agree (hch lvl hlvl') fun q hq => ?_
            have hq_ge : idx ≤ q := (edgesAtFrom_ge hq).1
            have hne1 : inp.aEdgeNext + q ≠ inp.aLvlHead + lvl := by
              simp only [PrepInput.aLvlHead, PrepInput.aEdgeNext]; omega
            have hne2 : inp.aEdgeNext + q ≠ inp.aEdgeNext + b := by omega
            simp [mem2, mem1, Function.update_of_ne hne1, Function.update_of_ne hne2]
          · rw [edgesAtFrom_step_ne hbm (fun h => heq_l h.symm)]
            have hptr : mem2 (inp.aLvlHead + lvl') = s.mem (inp.aLvlHead + lvl') := by
              have hne1 : inp.aLvlHead + lvl' ≠ inp.aLvlHead + lvl := by omega
              have hne2 : inp.aLvlHead + lvl' ≠ inp.aEdgeNext + b := by
                simp only [PrepInput.aLvlHead, PrepInput.aEdgeNext]; omega
              simp [mem2, mem1, Function.update_of_ne hne1, Function.update_of_ne hne2]
            rw [hptr, Nat.sub_add_cancel hpos]
            refine chainAt_of_agree (hch lvl' hlvl') fun q hq => ?_
            have hq_ge : idx ≤ q := (edgesAtFrom_ge hq).1
            have hne1 : inp.aEdgeNext + q ≠ inp.aLvlHead + lvl := by
              simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
            have hne2 : inp.aEdgeNext + q ≠ inp.aEdgeNext + b := by omega
            simp [mem2, mem1, Function.update_of_ne hne1, Function.update_of_ne hne2]
        · intro lvl' hlvl'
          by_cases heq_l : lvl' = lvl
          · subst heq_l; right; exact ⟨b, le_rfl, hbm, by simp [mem2, b]; omega⟩
          · have hne1 : inp.aLvlHead + lvl' ≠ inp.aLvlHead + lvl := by omega
            have hne2 : inp.aLvlHead + lvl' ≠ inp.aEdgeNext + b := by
              simp only [PrepInput.aLvlHead, PrepInput.aEdgeNext]; omega
            have hkeep : mem2 (inp.aLvlHead + lvl') = s.mem (inp.aLvlHead + lvl') :=
              by simp [mem2, mem1, Function.update_of_ne hne1, Function.update_of_ne hne2]
            rw [hkeep]
            rcases hlhead lvl' hlvl' with h0 | ⟨b₀, hb₀1, hb₀2, heq⟩
            · exact Or.inl h0
            · exact Or.inr ⟨b₀, by omega, hb₀2, heq⟩
        · intro b' hb'
          have hne1 : inp.aEdgeNext + b' ≠ inp.aLvlHead + lvl := by
            simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
          have hne2 : inp.aEdgeNext + b' ≠ inp.aEdgeNext + b := by omega
          simp [mem2, mem1, Function.update_of_ne hne1, Function.update_of_ne hne2, hzero_b b' (by omega)]
        · intro b' hb1 hb2
          by_cases hbb : b' = b
          · have hne : inp.aEdgeNext + b ≠ inp.aLvlHead + lvl := by
              simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
            have hnxt : mem2 (inp.aEdgeNext + b') = s.mem (inp.aLvlHead + lvl) := by
              simp [mem2, mem1, hbb, Function.update_of_ne hne]
            rw [hnxt]
            rcases hlhead lvl hlvl_d with h0 | ⟨b₀, _, hb₀, heq⟩
            · exact Or.inl h0
            · exact Or.inr ⟨b₀, by omega, hb₀, heq⟩
          · have hne1 : inp.aEdgeNext + b' ≠ inp.aLvlHead + lvl := by
              simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
            have hne2 : inp.aEdgeNext + b' ≠ inp.aEdgeNext + b := by omega
            simp only [mem2, mem1, Function.update_of_ne hne1, Function.update_of_ne hne2]
            exact hnext_gt b' (by omega) hb2
    exact hloop inp.J0_strip.m

def prepJ0Inv (inp : PrepInput) (mem₀ : ℕ → ℕ) (eds0 : List ℕ) (rem : List ℕ) (st : State) : Prop :=
  ∃ k,
    k + rem.length = eds0.length ∧
    eds0 = eds0.take k ++ rem ∧
    AgreeOutside st.mem mem₀ inp.aLvlHead inp.aComps ∧
    (∀ x < inp.h, st.mem x = mem₀ x) ∧
    PrepBaseRegs inp st ∧
    st.regs 12 = k ∧
    ChainAt st.mem inp.aEdgeNext (st.regs 29) rem ∧
    (∀ lvl ≤ inp.d_ℓ, ChainAt st.mem inp.aEdgeNext (st.mem (inp.aLvlHead + lvl))
      (inp.decomp.edgesAt inp.J0_strip lvl)) ∧
    ListAt st.mem inp.aJ0Out ((eds0.take k).map fun b => inp.nlIdx.getD b 0)

/-- Verification of `prepJ0Stmt`: writes original edge indices of level-0 edges (`j0Edges`) to
`aJ0Out` by traversing the bucket chain at `aLvlHead`. -/
theorem prepJ0_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv₀ : inp.Valid mem₀ w) :
    Triple w p
      (fun st =>
        AgreeOutside st.mem mem₀ inp.aLvlHead inp.aJ0Out ∧
        (∀ x < inp.h, st.mem x = mem₀ x) ∧
        PrepBaseRegs inp st ∧ st.regs 12 = 0 ∧
        ∀ lvl ≤ inp.d_ℓ, ChainAt st.mem inp.aEdgeNext (st.mem (inp.aLvlHead + lvl))
          (inp.decomp.edgesAt inp.J0_strip lvl))
      prepJ0Stmt
      (normalPost fun st =>
        AgreeOutside st.mem mem₀ inp.aLvlHead inp.aComps ∧
        (∀ x < inp.h, st.mem x = mem₀ x) ∧
        PrepBaseRegs inp st ∧ st.regs 12 = inp.j0Edges.length ∧
        ListAt st.mem inp.aJ0Out inp.j0Edges ∧
        ∀ lvl ≤ inp.d_ℓ, ChainAt st.mem inp.aEdgeNext (st.mem (inp.aLvlHead + lvl))
          (inp.decomp.edgesAt inp.J0_strip lvl))
      (fun _ => 35 * inp.J0_strip.m + 10) := by
  have hsz := inp.size_bounds hv₀
  rcases hv₀ with ⟨hJ, hgJ, hJ0, hgJ0, hnl, hlNl, hdec, hllen, hpn, hpnd, hpw, hprops, hdp,
    hjle, hj0le, hnlle, hdecle, hzero, hw1, hwb⟩
  set eds0 := inp.decomp.edgesAt inp.J0_strip 0
  have heds0_le : eds0.length ≤ inp.J0_strip.m := by simpa [PrepInput.j0Edges] using hsz.1
  have hnl_len : inp.nlIdx.length = inp.J0_strip.m := by
    rw [hJ0, hnl]; simp [stripLoops, Graph.m]
  refine (Triple.seq_normal_const
      (R := prepJ0Inv inp mem₀ eds0 eds0) (c₁ := 3) (c₂ := 34 * eds0.length + 5) ?_ ?_).conseq
    (fun st h => h) (fun o st h => h) (fun _ _ => by omega)
  · intro st ω ⟨hag, hlt, hb, h12, hch⟩
    have hptr_lt : st.mem inp.aLvlHead < 2 ^ w := by
      have h0 := hch 0 (Nat.zero_le _)
      cases he : eds0 with
      | nil => simp [ChainAt, eds0, he] at h0; rw [h0]; omega
      | cons b bs =>
        simp [ChainAt, eds0, he] at h0
        have hb_lt : b < inp.J0_strip.m := by
          have : b ∈ eds0 := he ▸ List.mem_cons_self
          exact (List.mem_range.mp (List.mem_filter.mp this).1)
        rw [h0.1]; omega
    refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨_, ev_load (ev_reg hb.2.2.2.2.2.2.2.2.2.1 (by simp [PrepInput.aLvlHead]; omega)) rfl hptr_lt, rfl, rfl, rfl⟩,
      ?_, by norm_num [Expr.size]⟩
    refine ⟨0, by simp, by simp, ?_, hlt, prepBaseRegs_update hb (by omega), by simp [h12], ?_, hch, listAt_nil _ _⟩
    · exact agreeOutside_mono hag le_rfl (by simp [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead])
    · simpa using hch 0 (Nat.zero_le _)
  · refine (Triple.loop_list (Inv := prepJ0Inv inp mem₀ eds0) (fun _ => 30) ?_ ?_ eds0).conseq
      (fun st h => h) (fun o st h => h) (fun _ _ => by norm_num [Expr.size]; omega)
    · intro st ⟨k, hklen, hsplit, hag, hlt, hb, h12, hch0, hchAll, hl⟩
      simp only [List.length_nil, add_zero] at hklen
      rw [ChainAt] at hch0
      refine ⟨by simpa [hch0] using ev_lt_f (ev_const (c := 0) (by omega)) (ev_reg hch0 (by omega)) (by omega) hw1, ?_⟩
      have hk_eq : eds0.take k = eds0 := by rw [hklen, List.take_length]
      rw [hk_eq] at hl
      refine ⟨hag, hlt, hb, ?_, hl, hchAll⟩
      simp [PrepInput.j0Edges, eds0, h12, hklen]
    · intro b rem st ⟨k, hklen, hsplit, hag, hlt, hb, h12, hch0, hchAll, hl⟩
      rcases hch0 with ⟨hr29, hchTail⟩
      have hb_m : b < inp.J0_strip.m := by
        have hmem : b ∈ eds0 := by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
        exact List.mem_range.mp (List.mem_filter.mp hmem).1
      have hnxt_lt : st.mem (inp.aEdgeNext + b) < 2 ^ w := by
        cases hrem : rem with
        | nil => rw [hrem, ChainAt] at hchTail; rw [hchTail]; omega
        | cons b' bs' =>
          rw [hrem, ChainAt] at hchTail
          have hmem : b' ∈ eds0 := by rw [hsplit, hrem]; simp
          have hb'm : b' < inp.J0_strip.m := List.mem_range.mp (List.mem_filter.mp hmem).1
          rw [hchTail.1]; omega
      have hnl_val : st.mem (inp.nlAddr + b) = inp.nlIdx.getD b 0 := by
        rw [hlt _ (by omega), listAt_sub_eq hlNl (by omega)]
      have hnl_val_lt : inp.nlIdx.getD b 0 < 2 ^ w := by
        have hmem_nl : inp.nlIdx.getD b 0 ∈ nonloopIndices inp.J := by
          rw [← hnl, List.getD_eq_getElem _ _ (by omega)]
          exact List.getElem_mem _
        have hlt_m := (mem_nonloopIndices.mp hmem_nl).1
        have hJm_len := graph_encode_length inp.J
        omega
      have hk_lt : k < 2 ^ w := by omega
      have hr29_lt : b + 1 < 2 ^ w := by omega
      have ha_out_lt : inp.aJ0Out + k < 2 ^ w := by
        simp only [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
      have ha_nxt_lt : inp.aEdgeNext + b < 2 ^ w := by simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
      refine ⟨1, ev_lt_t (ev_const (c := 0) (by omega)) (ev_reg hr29 hr29_lt) (by omega) hw1, by omega, ?_⟩
      intro s ω hs; rcases hs with rfl
      dsimp only [prepJ0Body]
      refine runs_seq_assign0 (v := b) (ev_sub (ev_reg hr29 hr29_lt) (ev_const hw1) (by omega) (by omega)) ?_
      refine runs_seq_assign_le (v := inp.nlIdx.getD b 0) ?_ ?_
      · exact ev_load (ev_add (ev_reg (by simp [hb.2.2.1]) (by omega)) (ev_reg (by simp) (by omega)) (by omega)) hnl_val hnl_val_lt
      refine runs_seq_store_le (x := inp.aJ0Out + k) (v := inp.nlIdx.getD b 0) ?_ ?_ ?_
      · exact ev_add (ev_reg (by simp [hb.2.2.2.2.2.2.2.2.2.2.2]) (by simp [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)) (ev_reg (by simp [h12]) hk_lt) ha_out_lt
      · exact ev_reg (by simp) hnl_val_lt
      refine runs_seq_assign_le (v := k + 1) ?_ ?_
      · exact ev_add (ev_reg (by simp [h12]) hk_lt) (ev_const hw1) (by omega)
      refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨s.mem (inp.aEdgeNext + b), ev_load (ev_add (ev_reg (by simp [hb.2.2.2.2.2.2.2.2.2.2.1]) (by simp [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)) (ev_reg (by simp) (by omega)) ha_nxt_lt) (by simp [Function.update_of_ne (by simp [PrepInput.aJ0Out]; omega : inp.aEdgeNext + b ≠ inp.aJ0Out + k)]) hnxt_lt, rfl, rfl, rfl⟩,
        ?_, by norm_num [Expr.size]⟩
      set mem1 := Function.update s.mem (inp.aJ0Out + k) (inp.nlIdx.getD b 0)
      have h_j0len : inp.j0Edges.length = eds0.length := by simp [PrepInput.j0Edges, eds0]
      have hlo : inp.aLvlHead ≤ inp.aJ0Out + k := by
        simp [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
        omega
      have hhi : inp.aJ0Out + k < inp.aComps := by
        simp only [PrepInput.aComps, h_j0len]; simp only [List.length_cons] at hklen; omega
      have hag1 : AgreeOutside mem1 mem₀ inp.aLvlHead inp.aComps :=
        agreeOutside_trans (agreeOutside_update (lo := inp.aLvlHead) (hi := inp.aComps) hlo hhi) hag le_rfl le_rfl
      refine ⟨k + 1, by simp only [List.length_cons] at hklen ⊢; omega, ?_, hag1,
        fun x hx => ?_, ?_, by simp, ?_, ?_, ?_⟩
      · have hlen_take : k < eds0.length := by simp only [List.length_cons] at hklen; omega
        have hgetk : eds0[k]'hlen_take = b := by
          have h1 := congrArg (·[k]?) hsplit
          rw [List.getElem?_eq_getElem hlen_take,
            List.getElem?_append_right (List.length_take_le k eds0),
            List.length_take, Nat.min_eq_left (le_of_lt hlen_take), Nat.sub_self,
            List.getElem?_cons_zero] at h1
          exact Option.some.inj h1
        rw [List.take_succ_eq_append_getElem hlen_take, hgetk, List.append_assoc, List.singleton_append]
        exact hsplit
      · exact hag1 x (Or.inl (by simp [PrepInput.aLvlHead]; omega))
      · exact prepBaseRegs_congr hb fun r hr => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · dsimp only
        simp only [Function.update_self]
        exact chainAt_of_agree hchTail fun q hq => by
          have hmem : q ∈ eds0 := by
            rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
          have hqm := List.mem_range.mp (List.mem_filter.mp hmem).1
          have hne_q : inp.aEdgeNext + q ≠ inp.aJ0Out + k := by simp [PrepInput.aJ0Out]; omega
          dsimp only [mem1]; rw [Function.update_of_ne hne_q]
      · intro lvl hlvl
        dsimp only
        have hne_hd : inp.aLvlHead + lvl ≠ inp.aJ0Out + k := by
          simp [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
        have hhd_eq : mem1 (inp.aLvlHead + lvl) = s.mem (inp.aLvlHead + lvl) := by
          dsimp only [mem1]; rw [Function.update_of_ne hne_hd]
        change ChainAt mem1 inp.aEdgeNext (mem1 (inp.aLvlHead + lvl)) _
        rw [hhd_eq]
        exact chainAt_of_agree (hchAll lvl hlvl) fun q hq => by
          simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hq
          have hqm := hq.1
          have hne_q : inp.aEdgeNext + q ≠ inp.aJ0Out + k := by simp [PrepInput.aJ0Out]; omega
          dsimp only [mem1]; rw [Function.update_of_ne hne_q]
      · have hlen_take : k < eds0.length := by simp only [List.length_cons] at hklen; omega
        have hgetk : eds0[k]'hlen_take = b := by
          have h1 := congrArg (·[k]?) hsplit
          rw [List.getElem?_eq_getElem hlen_take,
            List.getElem?_append_right (List.length_take_le k eds0),
            List.length_take, Nat.min_eq_left (le_of_lt hlen_take), Nat.sub_self,
            List.getElem?_cons_zero] at h1
          exact Option.some.inj h1
        have htake_len : (eds0.take k).length = k := List.length_take_of_le (le_of_lt hlen_take)
        rw [List.take_succ_eq_append_getElem hlen_take, hgetk, List.map_append, List.map_singleton]
        refine listAt_append_right_single ?_ (by rw [List.length_map, htake_len]; simp [mem1])
        exact listAt_of_congr hl fun i hi => by
          rw [List.length_map, htake_len] at hi
          exact Function.update_of_ne (by omega) _ _

end MinCostFlow.Spanner
