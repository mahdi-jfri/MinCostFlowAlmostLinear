module

public import MinCostFlow.Spanner.ProgWitnessPrepBlockHelpers

/-!
# Verification of `prepFindEndStmt` and `prepMarkStmt`

Proves Hoare triples for finding the end index of a contiguous same-level component block and
populating vertex scratch marks `aVComp` and `aVLoc` over the block.
-/

public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-- Verification of `prepFindEndStmt`: advances `r22` across consecutive components sharing
the same decomposition level `r23`. -/
theorem prepFindEnd_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest) :
    let i₁ := i₀ + block.length
    Triple w p
      (fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₀ ∧
        st.regs 17 = i₀ ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧
        CompsParsedFrom inp st.mem i₀ ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem (inp.cJSubPtr i₀))
      prepFindEndStmt
      (normalPost fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₀ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧
        CompsParsedFrom inp st.mem i₀ ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem (inp.cJSubPtr i₀))
      (fun _ => 25 * block.length + 30) := by
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, hpos, hle, hlvl_blk, hget_blk, hnext_blk, _⟩ :=
    compBlocksAux_split_spec hpw_rc hcb
  obtain ⟨hlvl1, hlvl2⟩ := block_lvl_bounds hv hcb
  intro i₁ st ω ⟨hf, h16, h17, hst, hdone, hparsed, hvz, hzf⟩
  have h0_val : inp.rawComps[i₀]!.1 = lvl := by
    have hg0 := hget_blk 0 hpos
    simp only [Nat.add_zero] at hg0
    rw [List.getElem!_eq_getElem?_getD, hg0]
    exact hlvl_blk block[0] (List.getElem_mem hpos)
  have hi0_len : i₀ < inp.rawComps.length := by omega
  have hmem_i0 : st.mem (inp.aComps + 7 * i₀) = lvl := by
    rw [← h0_val]; exact (hparsed i₀ (le_refl i₀) hi0_len).1
  have h7i0_lt : 7 * i₀ < 2 ^ w := by omega
  have ha7_i0_lt : inp.aComps + 7 * i₀ < 2 ^ w := by
    simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
    omega
  have hlvl_lt : lvl < 2 ^ w := by omega
  have hi01_lt : i₀ + 1 < 2 ^ w := by omega
  have hinv_init :
      Triple w p
        (fun s =>
          PrepFullRegs inp s ∧ s.regs 16 = inp.cJSubPtr i₀ ∧ s.regs 17 = i₀ ∧
          s.regs 22 = i₀ + 1 ∧ s.regs 23 = lvl ∧ s.regs 19 = 1 ∧
          s.mem = st.mem)
        (Stmt.loop (Expr.reg 19)
          (Stmt.cond (Expr.bin BinOp.lt (Expr.reg 22) (Expr.reg 8))
            (Stmt.cond
              (Expr.bin BinOp.eq
                (Expr.bin BinOp.add (Expr.reg 13) (Expr.bin BinOp.mul (Expr.const 7) (Expr.reg 22))).load
                (Expr.reg 23))
              (Stmt.assign 22 (Expr.bin BinOp.add (Expr.reg 22) (Expr.const 1)))
              (Stmt.assign 19 (Expr.const 0)))
            (Stmt.assign 19 (Expr.const 0))))
        (normalPost fun s =>
          PrepFullRegs inp s ∧ s.regs 16 = inp.cJSubPtr i₀ ∧ s.regs 17 = i₀ ∧
          s.regs 22 = i₁ ∧ s.regs 23 = lvl ∧ s.mem = st.mem)
        (fun _ => 25 * block.length + 10) := by
    let Inv : List ℕ → State → Prop := fun rem s =>
      PrepFullRegs inp s ∧ s.regs 16 = inp.cJSubPtr i₀ ∧ s.regs 17 = i₀ ∧
      s.regs 23 = lvl ∧ s.mem = st.mem ∧
      (rem = [] → s.regs 19 = 0 ∧ s.regs 22 = i₁) ∧
      (∀ k ks, rem = k :: ks →
        rem = List.range' k (i₁ + 1 - k) ∧ i₀ + 1 ≤ k ∧ k ≤ i₁ ∧
        s.regs 19 = 1 ∧ s.regs 22 = k)
    have hloop :
        Triple w p
          (Inv (List.range' (i₀ + 1) (i₁ - i₀)))
          (Stmt.loop (Expr.reg 19)
            (Stmt.cond (Expr.bin BinOp.lt (Expr.reg 22) (Expr.reg 8))
              (Stmt.cond
                (Expr.bin BinOp.eq
                  (Expr.bin BinOp.add (Expr.reg 13) (Expr.bin BinOp.mul (Expr.const 7) (Expr.reg 22))).load
                  (Expr.reg 23))
                (Stmt.assign 22 (Expr.bin BinOp.add (Expr.reg 22) (Expr.const 1)))
                (Stmt.assign 19 (Expr.const 0)))
              (Stmt.assign 19 (Expr.const 0))))
          (normalPost fun s =>
            PrepFullRegs inp s ∧ s.regs 16 = inp.cJSubPtr i₀ ∧ s.regs 17 = i₀ ∧
            s.regs 22 = i₁ ∧ s.regs 23 = lvl ∧ s.mem = st.mem)
          (fun _ => ((List.range' (i₀ + 1) (i₁ - i₀)).map (fun _ : ℕ => 20)).sum +
            (List.range' (i₀ + 1) (i₁ - i₀)).length * ((Expr.reg 19).size + 1) +
            (Expr.reg 19).size + 1) := by
      refine Triple.loop_list (Inv := Inv) (fun _ => 20) ?_ ?_ (List.range' (i₀ + 1) (i₁ - i₀))
      · intro s ⟨hsf, hs16, hs17, hs23, hsm, hnil, _⟩
        rcases hnil rfl with ⟨hs19, hs22⟩
        exact ⟨ev_reg hs19 (by omega), ⟨hsf, hs16, hs17, hs22, hs23, hsm⟩⟩
      · intro k ks s ⟨hsf, hs16, hs17, hs23, hsm, _, hcons⟩
        rcases hcons k ks rfl with ⟨hrem_eq, hk_lo, hk_hi, hs19, hs22⟩
        refine ⟨1, ev_reg hs19 hw1, by omega, ?_⟩
        intro s₀ ω₀ h_eq
        subst h_eq
        have hs₀8 : s₀.regs 8 = inp.rawComps.length := hsf.1.2.2.2.2.2.2.2.2.1
        have hs₀13 : s₀.regs 13 = inp.aComps := hsf.2.2.1
        have hk_lt_w : k < 2 ^ w := by omega
        have hnc_lt_w : inp.rawComps.length < 2 ^ w := by omega
        by_cases hlt_len : k < inp.rawComps.length
        · have hlt_val : (Expr.bin BinOp.lt (Expr.reg 22) (Expr.reg 8)).eval w s₀ = some 1 :=
            ev_lt_t (ev_reg hs22 hk_lt_w) (ev_reg hs₀8 hnc_lt_w) hlt_len hw1
          have h7k_lt : 7 * k < 2 ^ w := by omega
          have ha7k_lt : inp.aComps + 7 * k < 2 ^ w := by
            simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
            omega
          have hk_lvl_val : s₀.mem (inp.aComps + 7 * k) = inp.rawComps[k]!.1 := by
            rw [hsm]; exact (hparsed k (by omega) hlt_len).1
          have hk_lvl_lt : inp.rawComps[k]!.1 < 2 ^ w := by
            have hk_eq : inp.rawComps[k]! = inp.rawComps[k] := by
              rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt_len]; rfl
            have hp_k := hv.2.2.2.2.2.2.2.2.2.2.2.1 inp.rawComps[k]! (by rw [hk_eq]; exact List.getElem_mem hlt_len)
            omega
          have hload_k : (Expr.bin BinOp.add (Expr.reg 13)
              (Expr.bin BinOp.mul (Expr.const 7) (Expr.reg 22))).load.eval w s₀ =
              some (inp.rawComps[k]!.1) :=
            ev_load (ev_add (ev_reg hs₀13 (by omega))
              (ev_mul (ev_const (by omega)) (ev_reg hs22 hk_lt_w) h7k_lt) ha7k_lt) hk_lvl_val hk_lvl_lt
          by_cases hk_lt_i1 : k < i₁
          · have hcomp_lvl : inp.rawComps[k]!.1 = lvl := by
              have hidx : k - i₀ < block.length := by omega
              have hg := hget_blk (k - i₀) hidx
              rw [show i₀ + (k - i₀) = k by omega] at hg
              rw [List.getElem!_eq_getElem?_getD, hg]
              exact hlvl_blk block[k - i₀] (List.getElem_mem hidx)
            have heq_val : (Expr.bin BinOp.eq
                (Expr.bin BinOp.add (Expr.reg 13) (Expr.bin BinOp.mul (Expr.const 7) (Expr.reg 22))).load
                (Expr.reg 23)).eval w s₀ = some 1 :=
              ev_eq_t hload_k (ev_reg hs23 hlvl_lt) hcomp_lvl hw1
            have hk1_lt_w : k + 1 < 2 ^ w := by omega
            have hass_step :
                Runs w p ω₀
                  (Stmt.assign 22 (Expr.bin BinOp.add (Expr.reg 22) (Expr.const 1)))
                  s₀ .normal
                  { s₀ with regs := Function.update s₀.regs 22 (k + 1) } 4 :=
              runs_assign_iff.mpr ⟨k + 1, ev_add (ev_reg hs22 hk_lt_w) (ev_const hw1) hk1_lt_w, rfl, rfl, rfl⟩
            have hks_eq : ks = List.range' (k + 1) (i₁ + 1 - (k + 1)) := by
              have hsub : i₁ + 1 - k = (i₁ - k) + 1 := by omega
              rw [hsub, List.range'_succ] at hrem_eq
              have htail := (List.cons.inj hrem_eq).2
              rw [show i₁ - k = i₁ + 1 - (k + 1) by omega] at htail
              exact htail
            refine ⟨.normal, { s₀ with regs := Function.update s₀.regs 22 (k + 1) }, _,
              runs_cond_iff.mpr ⟨1, _, hlt_val,
                by simpa using runs_cond_iff.mpr ⟨1, _, heq_val, by simpa using hass_step, rfl⟩,
                rfl⟩,
              ?_, by norm_num [Expr.size]⟩
            dsimp only
            refine ⟨prepFullRegs_congr hsf (fun r hr => by
                dsimp only; rw [Function.update_of_ne (by omega)]),
              by simp [hs16], by simp [hs17], by simp [hs23], hsm,
              (fun hnil => by
                have hlen := congrArg List.length hnil
                simp only [hks_eq, List.length_nil, List.length_range'] at hlen
                omega), ?_⟩
            · intro k' ks' hcons'
              have hsub' : i₁ + 1 - (k + 1) = (i₁ - (k + 1)) + 1 := by omega
              rw [hsub', List.range'_succ] at hks_eq
              rw [hks_eq] at hcons'
              rcases List.cons.inj hcons' with ⟨rfl, rfl⟩
              refine ⟨?_, by omega, by omega, by simp [hs19], by simp⟩
              rw [hsub', List.range'_succ]
              exact hks_eq
          · have hk_eq_i1 : k = i₁ := by omega
            have hrem1 : i₁ :: ks = [i₁] := by
              rw [hk_eq_i1] at hrem_eq
              simpa [show i₁ + 1 - i₁ = 1 by omega] using hrem_eq
            have hks_nil : ks = [] := (List.cons.inj hrem1).2
            have hnext_lvl : inp.rawComps[k]!.1 ≠ lvl := by
              have ⟨q, hq, hql⟩ := hnext_blk (by omega)
              rw [hk_eq_i1, List.getElem!_eq_getElem?_getD, hq]
              dsimp only [Option.getD]; omega
            have heq_val : (Expr.bin BinOp.eq
                (Expr.bin BinOp.add (Expr.reg 13) (Expr.bin BinOp.mul (Expr.const 7) (Expr.reg 22))).load
                (Expr.reg 23)).eval w s₀ = some 0 :=
              ev_eq_f hload_k (ev_reg hs23 hlvl_lt) hnext_lvl hw1
            have hass_stop :
                Runs w p ω₀ (Stmt.assign 19 (Expr.const 0)) s₀ .normal
                  { s₀ with regs := Function.update s₀.regs 19 0 } 2 :=
              runs_assign_iff.mpr ⟨0, ev_const (by omega), rfl, rfl, rfl⟩
            refine ⟨.normal, { s₀ with regs := Function.update s₀.regs 19 0 }, _,
              runs_cond_iff.mpr ⟨1, _, hlt_val,
                by simpa using runs_cond_iff.mpr ⟨0, _, heq_val, by simpa using hass_stop, rfl⟩,
                rfl⟩,
              ?_, by norm_num [Expr.size]⟩
            dsimp only
            rw [hks_nil]
            refine ⟨prepFullRegs_congr hsf (fun r hr => by
                dsimp only; rw [Function.update_of_ne (by omega)]),
              by simp [hs16], by simp [hs17], by simp [hs23], hsm,
              fun _ => ⟨by simp, by dsimp only; rw [Function.update_of_ne (by omega)]; exact hs22.trans hk_eq_i1⟩,
              fun _ _ hc => by cases hc⟩
        · have hk_eq_i1 : k = i₁ := by omega
          have hrem1 : i₁ :: ks = [i₁] := by
            rw [hk_eq_i1] at hrem_eq
            simpa [show i₁ + 1 - i₁ = 1 by omega] using hrem_eq
          have hks_nil : ks = [] := (List.cons.inj hrem1).2
          have hlt_val : (Expr.bin BinOp.lt (Expr.reg 22) (Expr.reg 8)).eval w s₀ = some 0 :=
            ev_lt_f (ev_reg hs22 hk_lt_w) (ev_reg hs₀8 hnc_lt_w) (by omega) hw1
          have hass_stop :
              Runs w p ω₀ (Stmt.assign 19 (Expr.const 0)) s₀ .normal
                { s₀ with regs := Function.update s₀.regs 19 0 } 2 :=
            runs_assign_iff.mpr ⟨0, ev_const (by omega), rfl, rfl, rfl⟩
          refine ⟨.normal, { s₀ with regs := Function.update s₀.regs 19 0 }, _,
            runs_cond_iff.mpr ⟨0, _, hlt_val, by simpa using hass_stop, rfl⟩,
            ?_, by norm_num [Expr.size]⟩
          dsimp only
          rw [hks_nil]
          refine ⟨prepFullRegs_congr hsf (fun r hr => by
              dsimp only; rw [Function.update_of_ne (by omega)]),
            by simp [hs16], by simp [hs17], by simp [hs23], hsm,
            fun _ => ⟨by simp, by dsimp only; rw [Function.update_of_ne (by omega)]; exact hs22.trans hk_eq_i1⟩,
            fun _ _ hc => by cases hc⟩
    refine hloop.conseq (fun s h => ?_) (fun o s' h => h) (fun _ _ => ?_)
    · rcases h with ⟨hsf, hs16, hs17, hs22, hs23, hs19, hsm⟩
      refine ⟨hsf, hs16, hs17, hs23, hsm,
        fun hnil => by
          have : (List.range' (i₀ + 1) (i₁ - i₀)).length = 0 := by rw [hnil]; rfl
          simp only [List.length_range'] at this; omega,
        fun k ks hcons => ?_⟩
      have hsub : i₁ - i₀ = (i₁ - (i₀ + 1)) + 1 := by omega
      have hrem_eq : List.range' (i₀ + 1) (i₁ - i₀) =
          (i₀ + 1) :: List.range' (i₀ + 2) (i₁ - (i₀ + 1)) := by
        rw [hsub, List.range'_succ]
      rw [hcons] at hrem_eq
      rcases List.cons.inj hrem_eq with ⟨rfl, _⟩
      refine ⟨?_, le_refl _, by omega, hs19, hs22⟩
      rw [show i₁ + 1 - (i₀ + 1) = i₁ - i₀ by omega]
    · have hsum_map : ∀ s m, ((List.range' s m).map (fun _ : ℕ => 20)).sum = 20 * m := by
        intro s m
        induction m generalizing s with
        | zero => simp
        | succ n ih =>
          rw [List.range'_succ, List.map_cons, List.sum_cons, ih (s + 1)]
          omega
      have hsum_inst := hsum_map (i₀ + 1) (i₁ - i₀)
      simp only [List.length_range', Expr.size] at *
      dsimp only [i₁] at *
      omega
  have h13_st := hf.2.2.1
  dsimp only [prepFindEndStmt]
  refine runs_seq_assign0 (v := lvl)
    (ev_load (ev_add (ev_reg h13_st (by omega))
      (ev_mul (ev_const (by omega)) (ev_reg h17 (by omega)) h7i0_lt) ha7_i0_lt) hmem_i0 hlvl_lt) ?_
  refine runs_seq_assign_le (v := i₀ + 1)
    (ev_add (ev_reg (by simp [h17]) (by omega)) (ev_const hw1) hi01_lt) ?_
  refine runs_seq_assign_le (v := 1) (ev_const hw1) ?_
  set s_mid : State :=
    { mem := st.mem,
      regs := Function.update (Function.update (Function.update st.regs 23 lvl) 22 (i₀ + 1)) 19 1,
      pos := st.pos }
  have hs_mid : PrepFullRegs inp s_mid ∧ s_mid.regs 16 = inp.cJSubPtr i₀ ∧
      s_mid.regs 17 = i₀ ∧ s_mid.regs 22 = i₀ + 1 ∧ s_mid.regs 23 = lvl ∧
      s_mid.regs 19 = 1 ∧ s_mid.mem = st.mem := by
    refine ⟨prepFullRegs_congr hf (fun r hr => by
        dsimp only [s_mid]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]),
      ?_, ?_, ?_, ?_, ?_, rfl⟩
    · dsimp only [s_mid]; simp [h16]
    · dsimp only [s_mid]; simp [h17]
    · dsimp only [s_mid]; simp
    · dsimp only [s_mid]; simp
    · dsimp only [s_mid]; simp
  rcases hinv_init s_mid ω hs_mid with ⟨o, st', c, hruns, hpost, hcost⟩
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hsf', hs16', hs17', hs22', hs23', hmem'⟩
    refine ⟨.normal, st', c, hruns, ?_, ?_⟩
    · simp only [normalPost]
      refine ⟨hsf', hs16', hs17', hs22', hs23', ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hmem'] using hst
      · simpa only [hmem'] using hdone
      · simpa only [hmem'] using hparsed
      · simpa only [hmem'] using hvz
      · simpa only [hmem'] using hzf
    · norm_num [Expr.size] at hcost ⊢; omega

/-- Verification of `prepMarkStmt`: marks `aVComp` and `aVLoc` for every vertex in components
`[i₀, i₁)`. -/
theorem prepMark_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest) :
    let i₁ := i₀ + block.length
    let markCost := (block.map (fun c => 30 * c.2.length + 60)).sum + 20
    Triple w p
      (fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₀ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧
        CompsParsedFrom inp st.mem i₀ ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem (inp.cJSubPtr i₀))
      prepMarkStmt
      (normalPost fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₀ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧
        CompsParsedFrom inp st.mem i₀ ∧
        VertMarksBlock inp st.mem i₀ i₁ ∧
        ZeroFrom st.mem (inp.cJSubPtr i₀))
      (fun _ => markCost) := by
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, hle, _, hget_blk, _, _⟩ := compBlocksAux_split_spec hpw_rc hcb
  intro i₁ markCost
  let stepCost : ℕ → ℕ := fun ci => 30 * inp.rawComps[ci]!.2.length + 50
  let Inv : ℕ → State → Prop := fun ci st =>
    PrepFullRegs inp st ∧
    st.regs 16 = inp.cJSubPtr i₀ ∧
    st.regs 17 = i₀ ∧
    st.regs 22 = i₁ ∧
    st.regs 23 = lvl ∧
    st.regs 24 = ci ∧
    PrepStaticState inp mem₀ st.mem ∧
    CompsDoneUpTo inp st.mem i₀ ∧
    CompsParsedFrom inp st.mem i₀ ∧
    VertMarksPartial inp st.mem i₀ ci 0 ∧
    ZeroFrom st.mem (inp.cJSubPtr i₀)
  have hfor :
      Triple w p
        (fun st =>
          PrepFullRegs inp st ∧
          st.regs 16 = inp.cJSubPtr i₀ ∧
          st.regs 17 = i₀ ∧
          st.regs 22 = i₁ ∧
          st.regs 23 = lvl ∧
          PrepStaticState inp mem₀ st.mem ∧
          CompsDoneUpTo inp st.mem i₀ ∧
          CompsParsedFrom inp st.mem i₀ ∧
          VertMarksZero inp st.mem ∧
          ZeroFrom st.mem (inp.cJSubPtr i₀))
        prepMarkStmt
        (normalPost (Inv i₁))
        (fun _ => rangeCost stepCost i₀ i₁ + (i₁ - i₀) * ((Expr.reg 22).size + 8) +
          ((Expr.reg 17).size + (Expr.reg 22).size + 5)) := by
    refine Triple.forRange_le stepCost i₀ i₁ (Nat.le_add_right i₀ block.length) hw1
      (fun _ => by omega)
      (fun st ⟨hf, h16, h17, h22, h23, hst, hdone, hparsed, hvz, hzf⟩ =>
        ⟨ev_reg h17 (by omega),
          ⟨prepFullRegs_congr hf (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
           by simp [h16], by simp [h17], by simp [h22], by simp [h23], by simp,
           hst, hdone, hparsed, vertMarksPartial_zero hvz, hzf⟩⟩)
      (fun _ _ _ _ h => h.2.2.2.2.2.1)
      (fun _ _ _ _ h => ev_reg h.2.2.2.1 (by omega))
      ?_
    intro ci hci_lo hci_hi
    have hci_len : ci < inp.rawComps.length := by omega
    have hc_props := comp_props_at hv hci_len
    set c := inp.rawComps[ci]!
    have hmem_c : inp.rawComps[ci] = c := by
      dsimp only [c]; rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci_len]; rfl
    have hc2_lt : c.2.length < 2 ^ w := by
      have hcmem : c ∈ inp.rawComps := by rw [← hmem_c]; exact List.getElem_mem hci_len
      have hcmem2 : 2 + c.2.length ∈ inp.rawComps.map fun p => 2 + p.2.length :=
        List.mem_map.mpr ⟨c, hcmem, rfl⟩
      have := List.single_le_sum (fun x _ => Nat.zero_le x) _ hcmem2
      omega
    have hvptr_lt : inp.cVertsPtr ci < 2 ^ w := by
      have := cVertsPtr_add_le_h hv hci_len
      omega
    have hrec_raw : ∀ st_m, PrepStaticState inp mem₀ st_m →
        ListAt st_m (inp.cVertsPtr ci) c.2 := by
      intro st_m hst_m
      have hr := rawComps_recordAt hv (fun x hx => hst_m.1 x hx) hci_len
      simpa only [c, hmem_c] using hr.2.2
    have ha_end_lt : inp.aComps + 7 * inp.rawComps.length < 2 ^ w := by
      simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
      omega
    have ha31_lt : inp.aComps + 7 * ci < 2 ^ w := by omega
    have ha31_1_lt : inp.aComps + 7 * ci + 1 < 2 ^ w := by omega
    have ha31_2_lt : inp.aComps + 7 * ci + 2 < 2 ^ w := by omega
    have h7ci_lt : 7 * ci < 2 ^ w := by omega
    have hci1_lt : ci + 1 < 2 ^ w := by omega
    let InnerInv : ℕ → State → Prop := fun k st =>
      PrepFullRegs inp st ∧
      st.regs 16 = inp.cJSubPtr i₀ ∧
      st.regs 17 = i₀ ∧
      st.regs 20 = c.2.length ∧
      st.regs 21 = inp.cVertsPtr ci ∧
      st.regs 22 = i₁ ∧
      st.regs 23 = lvl ∧
      st.regs 24 = ci ∧
      st.regs 25 = k ∧
      st.regs 30 = ci + 1 ∧
      PrepStaticState inp mem₀ st.mem ∧
      CompsDoneUpTo inp st.mem i₀ ∧
      CompsParsedFrom inp st.mem i₀ ∧
      VertMarksPartial inp st.mem i₀ ci k ∧
      ZeroFrom st.mem (inp.cJSubPtr i₀)
    have hinner_loop :
        Triple w p (InnerInv 0) (forUp 25 (Expr.reg 20) prepMarkVertBody)
          (normalPost (InnerInv c.2.length))
          (fun _ => c.2.length * (20 + (Expr.reg 20).size + 8) + ((Expr.reg 20).size + 3)) := by
      refine Triple.forUp_const 20 0 c.2.length (Nat.zero_le _) hw1
        (fun _ => hc2_lt)
        (fun k _ _ _ h => h.2.2.2.2.2.2.2.2.1)
        (fun k _ _ _ h => ev_reg h.2.2.2.1 hc2_lt)
        ?_
      intro k _ hk_lt st₁ ω₁ hinv
      rcases hinv with ⟨hf1, h16_1, h17_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h30_1,
        hst1, hdone1, hparsed1, hvm1, hzf1⟩
      have hkc : k < inp.rawComps[ci].2.length := by rw [hmem_c]; exact hk_lt
      set u := inp.rawComps[ci].2[k]
      have hu_mem : u ∈ c.2 := by rw [← hmem_c]; exact List.getElem_mem hkc
      have hu_lt_n : u < inp.J.n := hc_props.2.2.2.2.2.1 u hu_mem
      have hu_lt_w : u < 2 ^ w := by omega
      have huvptr_lt : inp.cVertsPtr ci + k < 2 ^ w := by
        have := cVertsPtr_add_le_h hv hci_len
        dsimp only [c] at hk_lt
        omega
      have hvc_lt : inp.aVComp + u < 2 ^ w := by
        simp only [PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext,
          PrepInput.aLvlHead]
        omega
      have hvl_lt : inp.aVLoc + u < 2 ^ w := by
        simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out,
          PrepInput.aEdgeNext, PrepInput.aLvlHead]
        omega
      have hl_verts := hrec_raw st₁.mem hst1
      have hload_u : st₁.mem (inp.cVertsPtr ci + k) = u := by
        have hg := listAt_getElem hl_verts hk_lt
        dsimp only [u]; simpa [hmem_c] using hg
      dsimp only [prepMarkVertBody]
      have hstore1_a : (Expr.bin BinOp.add (Expr.reg 14) (Expr.reg 19)).eval w
          { mem := st₁.mem, regs := Function.update st₁.regs 19 u, pos := st₁.pos } =
          some (inp.aVComp + u) :=
        ev_add (ev_reg (by simp [hf1.2.2.2.1]) (by omega)) (ev_reg (by simp) hu_lt_w) hvc_lt
      have hstore1_v : (Expr.reg 30).eval w
          { mem := st₁.mem, regs := Function.update st₁.regs 19 u, pos := st₁.pos } =
          some (ci + 1) :=
        ev_reg (by simp [h30_1]) hci1_lt
      refine runs_seq_assign0 (v := u)
        (ev_load (ev_add (ev_reg h21_1 hvptr_lt) (ev_reg h25_1 (by omega)) huvptr_lt) hload_u hu_lt_w) ?_
      refine runs_seq_store_le (x := inp.aVComp + u) (v := ci + 1) hstore1_a hstore1_v ?_
      have hstore_eval_a : (Expr.bin BinOp.add (Expr.reg 15) (Expr.reg 19)).eval w
          { mem := Function.update st₁.mem (inp.aVComp + u) (ci + 1),
            regs := Function.update st₁.regs 19 u, pos := st₁.pos } = some (inp.aVLoc + u) :=
        ev_add (ev_reg (by simp [hf1.2.2.2.2]) (by omega)) (ev_reg (by simp) hu_lt_w) hvl_lt
      have hstore_eval_v : (Expr.reg 25).eval w
          { mem := Function.update st₁.mem (inp.aVComp + u) (ci + 1),
            regs := Function.update st₁.regs 19 u, pos := st₁.pos } = some k :=
        ev_reg (by simp [h25_1]) (by omega)
      refine ⟨.normal, _, _,
        runs_store_iff.mpr ⟨_, _, hstore_eval_a, hstore_eval_v, rfl, rfl, rfl⟩, ?_,
        by norm_num [Expr.size]⟩
      set m1 := Function.update st₁.mem (inp.aVComp + u) (ci + 1)
      set m2 := Function.update m1 (inp.aVLoc + u) k
      have hag_m2 : ∀ x, (x < inp.aVComp ∨ inp.hBlocksStart ≤ x) → m2 x = st₁.mem x := by
        intro x hx
        have hvc_in : inp.aVComp ≤ inp.aVComp + u ∧ inp.aVComp + u < inp.hBlocksStart := by
          rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc]; omega
        have hvl_in : inp.aVComp ≤ inp.aVLoc + u ∧ inp.aVLoc + u < inp.hBlocksStart := by
          rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc]; omega
        dsimp only [m2, m1]
        rw [Function.update_of_ne (by rcases hx with h | h <;> omega),
          Function.update_of_ne (by rcases hx with h | h <;> omega)]
      have hne_vc_vl : inp.aVComp + u ≠ inp.aVLoc + u := by
        simp only [PrepInput.aVLoc]; omega
      have hvm2 : VertMarksPartial inp m2 i₀ ci (k + 1) := by
        refine ⟨?_, ?_, ?_⟩
        · intro cj hcj hcj1 hcj2 p hp
          have hdisj := comp_verts_disjoint_block hv hcb hcj1 (by omega) hci_lo hci_hi (by omega)
          have hne_v : inp.rawComps[cj].2[p] ≠ u := by
            intro heq
            have hm1 : inp.rawComps[cj].2[p] ∈ inp.rawComps[cj].2.toFinset :=
              List.mem_toFinset.mpr (List.getElem_mem hp)
            have hm2 : inp.rawComps[cj].2[p] ∈ inp.rawComps[ci].2.toFinset := by
              rw [heq]; exact List.mem_toFinset.mpr (List.getElem_mem hkc)
            exact Finset.disjoint_left.mp hdisj hm1 hm2
          have hprev := hvm1.1 cj hcj hcj1 hcj2 p hp
          dsimp only [m2, m1]
          constructor
          · rw [Function.update_of_ne (by
                have hcj_eq : inp.rawComps[cj]! = inp.rawComps[cj] := by
                  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hcj]; rfl
                simp only [PrepInput.aVLoc]
                have := (comp_props_at hv hcj).2.2.2.2.2.1 _ (by rw [hcj_eq]; exact List.getElem_mem hp)
                omega),
              Function.update_of_ne (by omega)]
            exact hprev.1
          · rw [Function.update_of_ne (by simp only [PrepInput.aVLoc]; omega),
              Function.update_of_ne (by simp only [PrepInput.aVLoc]; omega)]
            exact hprev.2
        · intro hci' p hp hplen
          by_cases hpk : p = k
          · subst hpk
            dsimp only [m2, m1, u]
            constructor
            · rw [Function.update_of_ne (by dsimp only [u] at hne_vc_vl; exact hne_vc_vl),
                Function.update_self]
            · rw [Function.update_self]
          · have hlt_k : p < k := by omega
            have hne_v : inp.rawComps[ci].2[p] ≠ u := by
              intro heq
              have hnd_ci := hc_props.2.2.2.2.1
              rw [← hmem_c] at hnd_ci
              exact hpk (List.Nodup.getElem_inj_iff hnd_ci |>.mp heq)
            have hprev := hvm1.2.1 hci' p hlt_k hplen
            dsimp only [m2, m1]
            constructor
            · rw [Function.update_of_ne (by
                  simp only [PrepInput.aVLoc]
                  have := hc_props.2.2.2.2.2.1 _ (by rw [← hmem_c]; exact List.getElem_mem hplen)
                  omega),
                Function.update_of_ne (by omega)]
              exact hprev.1
            · rw [Function.update_of_ne (by simp only [PrepInput.aVLoc]; omega),
                Function.update_of_ne (by simp only [PrepInput.aVLoc]; omega)]
              exact hprev.2
        · intro u' hu' hnot_prev hnot_curr
          have hne_u : u ≠ u' := hnot_curr hci_len k (by omega) hkc
          have hprev := hvm1.2.2 u' hu' hnot_prev fun hci' p hp hplen =>
            hnot_curr hci' p (by omega) hplen
          dsimp only [m2, m1]
          constructor
          · rw [Function.update_of_ne (by simp only [PrepInput.aVLoc]; omega),
              Function.update_of_ne (by omega)]
            exact hprev.1
          · rw [Function.update_of_ne (by simp only [PrepInput.aVLoc]; omega),
              Function.update_of_ne (by simp only [PrepInput.aVLoc]; omega)]
            exact hprev.2
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hvm2, ?_⟩, ?_⟩
      · exact prepFullRegs_congr hf1 fun r hr => by
          dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · simpa using h16_1
      · simpa using h17_1
      · simpa using h20_1
      · simpa using h21_1
      · simpa using h22_1
      · simpa using h23_1
      · simpa using h24_1
      · simp
      · simpa using h30_1
      · exact prepStaticState_of_agree hst1 fun x hx =>
          hag_m2 x (Or.inl (by simp only [PrepInput.aVComp]; omega))
      · refine compsDoneUpTo_of_agree hv (by omega) hdone1
          (fun x hx1 hx2 => hag_m2 x (Or.inl (by simp only [PrepInput.aVComp]; omega)))
          (fun x hx1 hx2 => hag_m2 x (Or.inr hx1))
      · exact compsParsedFrom_of_agree hparsed1 fun x hx1 hx2 =>
          hag_m2 x (Or.inl (by simp only [PrepInput.aVComp]; omega))
      · intro x hx
        have hxbs : inp.hBlocksStart ≤ x := by
          have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le i₀); omega
        exact (hag_m2 x (Or.inr hxbs)).trans (hzf1 x hx)
      · simp [h25_1]
    intro st ω ⟨hf, h16, h17, h22, h23, h24, hst, hdone, hparsed, hvm, hzf⟩
    have hcomp_1 : st.mem (inp.aComps + 7 * ci + 1) = c.2.length := (hparsed ci (by omega) hci_len).2.1
    have hcomp_2 : st.mem (inp.aComps + 7 * ci + 2) = inp.cVertsPtr ci := (hparsed ci (by omega) hci_len).2.2.1
    dsimp only [prepMarkBody]
    refine runs_seq_assign0 (v := inp.aComps + 7 * ci)
      (ev_add (ev_reg hf.2.2.1 (by omega))
        (ev_mul (ev_const (by omega)) (ev_reg h24 (by omega)) h7ci_lt) ha31_lt) ?_
    refine runs_seq_assign_le (v := c.2.length)
      (ev_load (ev_add (ev_reg (by simp) ha31_lt) (ev_const hw1) ha31_1_lt)
        (by simpa using hcomp_1) hc2_lt) ?_
    refine runs_seq_assign_le (v := inp.cVertsPtr ci)
      (ev_load (ev_add (ev_reg (by simp) ha31_lt) (ev_const (by omega)) ha31_2_lt)
        (by simpa using hcomp_2) hvptr_lt) ?_
    refine runs_seq_assign_le (v := ci + 1)
      (ev_add (ev_reg (by simp [h24]) (by omega)) (ev_const hw1) hci1_lt) ?_
    refine runs_seq_assign_le (v := 0) (ev_const (by omega)) ?_
    set s_inner : State :=
      { mem := st.mem,
        regs := Function.update (Function.update (Function.update (Function.update
          (Function.update st.regs 31 (inp.aComps + 7 * ci)) 20 c.2.length)
          21 (inp.cVertsPtr ci)) 30 (ci + 1)) 25 0,
        pos := st.pos }
    have hs_inner : InnerInv 0 s_inner := by
      refine ⟨prepFullRegs_congr hf (fun r hr => by
          dsimp only [s_inner]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hst, hdone, hparsed, hvm, hzf⟩
      · dsimp only [s_inner]; simp [h16]
      · dsimp only [s_inner]; simp [h17]
      · dsimp only [s_inner]; simp
      · dsimp only [s_inner]; simp
      · dsimp only [s_inner]; simp [h22]
      · dsimp only [s_inner]; simp [h23]
      · dsimp only [s_inner]; simp [h24]
      · dsimp only [s_inner]; simp
      · dsimp only [s_inner]; simp
    rcases hinner_loop s_inner ω hs_inner with ⟨o, st', c_cost, hruns, hpost, hcost⟩
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      rcases hpost with ⟨hf', h16', h17', _, _, h22', h23', h24', _, _, hst', hdone', hparsed', hvm', hzf'⟩
      have hvm_next : VertMarksPartial inp st'.mem i₀ (ci + 1) 0 := by
        refine ⟨?_, fun _ _ hp _ => by omega, ?_⟩
        · intro cj hcj hcj1 hcj2 p hp
          by_cases hcj_eq : cj = ci
          · subst hcj_eq
            exact hvm'.2.1 hci_len p (by simpa only [c, hmem_c] using hp) hp
          · exact hvm'.1 cj hcj hcj1 (by omega) p hp
        · intro u hu hnot_prev _
          exact hvm'.2.2 u hu (fun cj hcj hcj1 hcj2 => hnot_prev cj hcj hcj1 (by omega))
            (fun hci' p _ hplen => by
              intro heq
              exact hnot_prev ci hci' hci_lo (by omega) (heq ▸ List.getElem_mem hplen))
      refine ⟨.normal, st', c_cost, hruns, ?_, ?_⟩
      · simp only [normalPost]
        refine ⟨⟨prepFullRegs_congr hf' (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
          by simp [h16'], by simp [h17'], by simp [h22'], by simp [h23'], by simp,
          hst', hdone', hparsed', hvm_next, hzf'⟩, h24'⟩
      · dsimp only [c] at hcost
        norm_num [stepCost, Expr.size] at hcost ⊢
        omega
  refine hfor.conseq (fun _ h => h) (fun o st' h => ?_) (fun _ _ => ?_)
  · cases o with
    | returned _ => exact h
    | normal =>
      rcases h with ⟨hf, h16, h17, h22, h23, _, hst, hdone, hparsed, hvm, hzf⟩
      exact ⟨hf, h16, h17, h22, h23, hst, hdone, hparsed, hvm, hzf⟩
  have hrc : rangeCost stepCost i₀ i₁ = (block.map (fun c => 30 * c.2.length + 50)).sum := by
    suffices ∀ m s, s + m = i₁ → i₀ ≤ s →
        ((List.range' s m).map stepCost).sum =
          ((List.range' s m).map (fun j => 30 * block[j - i₀]!.2.length + 50)).sum by
      have hsum_blk : ((List.range' i₀ block.length).map
          (fun j => 30 * block[j - i₀]!.2.length + 50)).sum =
          (block.map (fun c => 30 * c.2.length + 50)).sum := by
        clear hfor hpw_rc hsz
        have hgen : ∀ (k : ℕ) (xs : List (ℕ × List ℕ)),
            ((List.range' k xs.length).map (fun j => 30 * xs[j - k]!.2.length + 50)).sum =
              (xs.map (fun c => 30 * c.2.length + 50)).sum := by
          intro k xs
          induction xs generalizing k with
          | nil => simp
          | cons x xs ih =>
            simp only [List.length_cons, List.range'_succ, List.map_cons, List.sum_cons,
              Nat.sub_self, List.getElem!_eq_getElem?_getD, List.getElem?_cons_zero,
              Option.getD_some]
            rw [← ih (k + 1)]
            congr 2
            refine List.map_congr_left fun j hj => ?_
            simp only [List.mem_range'] at hj
            have hne : j - k = (j - (k + 1)) + 1 := by omega
            simp [hne, List.getElem!_eq_getElem?_getD]
        exact hgen i₀ block
      dsimp only [rangeCost]
      rw [show i₁ - i₀ = block.length by omega]
      rw [this block.length i₀ (by omega) le_rfl, hsum_blk]
    intro m s hsm hs
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    simp only [List.mem_range'] at hj
    have hidx : j - i₀ < block.length := by omega
    have hj_len : j < inp.rawComps.length := by omega
    have hg := hget_blk (j - i₀) hidx
    rw [show i₀ + (j - i₀) = j by omega] at hg
    simp only [stepCost, List.getElem!_eq_getElem?_getD, hg, List.getElem?_eq_getElem hidx,
      Option.getD_some]
  have hlen_sum : block.length * 9 ≤ (block.map (fun c => c.2.length)).sum + 9 * block.length := by
    omega
  have hsum_add : (block.map (fun c => 30 * c.2.length + 50)).sum + (i₁ - i₀) * 9 + 7 ≤ markCost := by
    dsimp only [markCost]
    have hmul : ∀ (xs : List (ℕ × List ℕ)) (a b : ℕ),
        (xs.map (fun c => a * c.2.length + b)).sum + xs.length * 9 + 7 ≤
          (xs.map (fun c => a * c.2.length + (b + 10))).sum + 20 := by
      intro xs a b
      induction xs with
      | nil => simp
      | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
        omega
    have := hmul block 30 50
    simpa [show i₁ - i₀ = block.length by omega] using this
  simp only [Expr.size] at *
  rw [hrc]
  exact hsum_add

end MinCostFlow.Spanner
