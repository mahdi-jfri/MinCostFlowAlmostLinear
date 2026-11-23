module

public import MinCostFlow.Spanner.ProgWitnessPrepBlockHelpers
import MinCostFlow.Spanner.ProgWitnessPrepFindMark
import MinCostFlow.Spanner.ProgWitnessPrepCountAlloc
import MinCostFlow.Spanner.ProgWitnessPrepFill

/-!
# Verification of `prepUnmarkStmt`, `prepBlockBody`, and `prepBlockLoopStmt`

Proves `prepUnmark_triple` (restoring vertex scratch marks to zero after a level block), composes
all six block-loop sub-steps into `prepBlockBody_triple`, and proves `prepBlockLoop_triple` with
total cost `≤ 820 * J0_strip.m + 10`.
-/

public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-- Partial unmarking predicate for block `[i₀, i₁)` at `(ci, k)`. -/
private def VertMarksUnmarkPartial (inp : PrepInput) (mem : ℕ → ℕ) (i₀ i₁ ci k : ℕ) : Prop :=
  (∀ u < inp.J.n,
    (∀ cj (hcj : cj < inp.rawComps.length), i₀ ≤ cj → cj < i₁ → u ∉ inp.rawComps[cj].2) →
    mem (inp.aVComp + u) = 0 ∧ mem (inp.aVLoc + u) = 0) ∧
  (∀ cj (hcj : cj < inp.rawComps.length), i₀ ≤ cj → cj < ci →
    ∀ p (hp : p < inp.rawComps[cj].2.length),
      mem (inp.aVComp + inp.rawComps[cj].2[p]) = 0 ∧
      mem (inp.aVLoc + inp.rawComps[cj].2[p]) = 0) ∧
  (∀ (hci : ci < inp.rawComps.length),
    ∀ p, p < k → ∀ (hp2 : p < inp.rawComps[ci].2.length),
      mem (inp.aVComp + inp.rawComps[ci].2[p]) = 0 ∧
      mem (inp.aVLoc + inp.rawComps[ci].2[p]) = 0)

private theorem vertMarksUnmarkPartial_init {inp : PrepInput} {mem : ℕ → ℕ} {i₀ i₁ : ℕ}
    (hvm : VertMarksBlock inp mem i₀ i₁) : VertMarksUnmarkPartial inp mem i₀ i₁ i₀ 0 :=
  ⟨fun u hu hnot => hvm.2.2 u hu hnot (fun hci p hp _ => by omega),
   fun _ _ _ _ => by omega, fun _ _ _ => by omega⟩

private theorem vertMarksZero_of_unmarkPartial {inp : PrepInput} {mem : ℕ → ℕ} {i₀ i₁ : ℕ}
    (_hhi : i₁ ≤ inp.rawComps.length) (hvm : VertMarksUnmarkPartial inp mem i₀ i₁ i₁ 0) :
    VertMarksZero inp mem := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · by_cases hin : ∃ cj, ∃ (hcj : cj < inp.rawComps.length), i₀ ≤ cj ∧ cj < i₁ ∧ u ∈ inp.rawComps[cj].2
    · rcases hin with ⟨cj, hcj, h1, h2, hmem⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hmem
      exact (hvm.2.1 cj hcj h1 h2 p hp).1
    · push Not at hin
      exact (hvm.1 u hu hin).1
  · by_cases hin : ∃ cj, ∃ (hcj : cj < inp.rawComps.length), i₀ ≤ cj ∧ cj < i₁ ∧ u ∈ inp.rawComps[cj].2
    · rcases hin with ⟨cj, hcj, h1, h2, hmem⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hmem
      exact (hvm.2.1 cj hcj h1 h2 p hp).2
    · push Not at hin
      exact (hvm.1 u hu hin).2

/-- Verification of `prepUnmarkStmt`: zeroes out vertex scratch entries `aVComp` and `aVLoc` for
every component in `[i₀, i₁)`. -/
theorem prepUnmark_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest) :
    let i₁ := i₀ + block.length
    let unmarkCost := (block.map (fun c => 30 * c.2.length + 40)).sum + 15
    Triple w p
      (fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₁ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₁ ∧
        CompsParsedFrom inp st.mem i₁ ∧
        VertMarksBlock inp st.mem i₀ i₁ ∧
        ZeroFrom st.mem (inp.cJSubPtr i₁))
      prepUnmarkStmt
      (normalPost fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₁ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₁ ∧
        CompsParsedFrom inp st.mem i₁ ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem (inp.cJSubPtr i₁))
      (fun _ => unmarkCost) := by
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, hle, _, hget_blk, _, _⟩ := compBlocksAux_split_spec hpw_rc hcb
  intro i₁ unmarkCost
  let stepCost : ℕ → ℕ := fun ci => 30 * inp.rawComps[ci]!.2.length + 30
  let Inv : ℕ → State → Prop := fun ci st =>
    PrepFullRegs inp st ∧
    st.regs 16 = inp.cJSubPtr i₁ ∧
    st.regs 17 = i₀ ∧
    st.regs 22 = i₁ ∧
    st.regs 23 = lvl ∧
    st.regs 24 = ci ∧
    PrepStaticState inp mem₀ st.mem ∧
    CompsDoneUpTo inp st.mem i₁ ∧
    CompsParsedFrom inp st.mem i₁ ∧
    VertMarksUnmarkPartial inp st.mem i₀ i₁ ci 0 ∧
    ZeroFrom st.mem (inp.cJSubPtr i₁)
  have hfor :
      Triple w p
        (fun st =>
          PrepFullRegs inp st ∧
          st.regs 16 = inp.cJSubPtr i₁ ∧
          st.regs 17 = i₀ ∧
          st.regs 22 = i₁ ∧
          st.regs 23 = lvl ∧
          PrepStaticState inp mem₀ st.mem ∧
          CompsDoneUpTo inp st.mem i₁ ∧
          CompsParsedFrom inp st.mem i₁ ∧
          VertMarksBlock inp st.mem i₀ i₁ ∧
          ZeroFrom st.mem (inp.cJSubPtr i₁))
        prepUnmarkStmt
        (normalPost (Inv i₁))
        (fun _ => rangeCost stepCost i₀ i₁ + (i₁ - i₀) * ((Expr.reg 22).size + 8) +
          ((Expr.reg 17).size + (Expr.reg 22).size + 5)) := by
    refine Triple.forRange_le stepCost i₀ i₁ (Nat.le_add_right i₀ block.length) hw1
      (fun _ => by omega)
      (fun st ⟨hf, h16, h17, h22, h23, hst, hdone, hparsed, hvm, hzf⟩ =>
        ⟨ev_reg h17 (by omega),
          ⟨prepFullRegs_congr hf (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
           by simp [h16], by simp [h17], by simp [h22], by simp [h23], by simp,
           hst, hdone, hparsed, vertMarksUnmarkPartial_init hvm, hzf⟩⟩)
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
      have := cVertsPtr_add_le_h hv hci_len; omega
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
    let InnerInv : ℕ → State → Prop := fun k st =>
      PrepFullRegs inp st ∧
      st.regs 16 = inp.cJSubPtr i₁ ∧
      st.regs 17 = i₀ ∧
      st.regs 20 = c.2.length ∧
      st.regs 21 = inp.cVertsPtr ci ∧
      st.regs 22 = i₁ ∧
      st.regs 23 = lvl ∧
      st.regs 24 = ci ∧
      st.regs 25 = k ∧
      PrepStaticState inp mem₀ st.mem ∧
      CompsDoneUpTo inp st.mem i₁ ∧
      CompsParsedFrom inp st.mem i₁ ∧
      VertMarksUnmarkPartial inp st.mem i₀ i₁ ci k ∧
      ZeroFrom st.mem (inp.cJSubPtr i₁)
    have hinner_loop :
        Triple w p (InnerInv 0) (forUp 25 (Expr.reg 20) prepUnmarkVertBody)
          (normalPost (InnerInv c.2.length))
          (fun _ => c.2.length * (20 + (Expr.reg 20).size + 8) + ((Expr.reg 20).size + 3)) := by
      refine Triple.forUp_const 20 0 c.2.length (Nat.zero_le _) hw1
        (fun _ => hc2_lt)
        (fun k _ _ _ h => h.2.2.2.2.2.2.2.2.1)
        (fun k _ _ _ h => ev_reg h.2.2.2.1 hc2_lt)
        ?_
      intro k _ hk_lt st₁ ω₁ hinv
      rcases hinv with ⟨hf1, h16_1, h17_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1,
        hst1, hdone1, hparsed1, hvm1, hzf1⟩
      have hkc : k < inp.rawComps[ci].2.length := by rw [hmem_c]; exact hk_lt
      let u := inp.rawComps[ci].2[k]
      have hu_mem : u ∈ c.2 := by rw [← hmem_c]; exact List.getElem_mem hkc
      have hu_lt_n : u < inp.J.n := hc_props.2.2.2.2.2.1 u hu_mem
      have hu_lt_w : u < 2 ^ w := by omega
      have huvptr_lt : inp.cVertsPtr ci + k < 2 ^ w := by
        have := cVertsPtr_add_le_h hv hci_len
        dsimp only [c] at hk_lt; omega
      have hvc_lt : inp.aVComp + u < 2 ^ w := by
        simp only [PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext,
          PrepInput.aLvlHead]; omega
      have hvl_lt : inp.aVLoc + u < 2 ^ w := by
        simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out,
          PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
      have hl_verts := hrec_raw st₁.mem hst1
      have hload_u : st₁.mem (inp.cVertsPtr ci + k) = u := by
        have hg := listAt_getElem hl_verts hk_lt
        dsimp only [u]; simpa [hmem_c] using hg
      dsimp only [prepUnmarkVertBody]
      have hstore1_a : (Expr.bin BinOp.add (Expr.reg 14) (Expr.reg 19)).eval w
          { mem := st₁.mem, regs := Function.update st₁.regs 19 u, pos := st₁.pos } =
          some (inp.aVComp + u) :=
        ev_add (ev_reg (by simp [hf1.2.2.2.1]) (by omega)) (ev_reg (by simp) hu_lt_w) hvc_lt
      refine runs_seq_assign0 (v := u)
        (ev_load (ev_add (ev_reg h21_1 hvptr_lt) (ev_reg h25_1 (by omega)) huvptr_lt) hload_u hu_lt_w) ?_
      refine runs_seq_store_le (x := inp.aVComp + u) (v := 0) hstore1_a (ev_const (by omega)) ?_
      have hstore_eval_a : (Expr.bin BinOp.add (Expr.reg 15) (Expr.reg 19)).eval w
          { mem := Function.update st₁.mem (inp.aVComp + u) 0,
            regs := Function.update st₁.regs 19 u, pos := st₁.pos } = some (inp.aVLoc + u) :=
        ev_add (ev_reg (by simp [hf1.2.2.2.2]) (by omega)) (ev_reg (by simp) hu_lt_w) hvl_lt
      let m1 := Function.update st₁.mem (inp.aVComp + u) 0
      let m2 := Function.update m1 (inp.aVLoc + u) 0
      have hzero_pres : ∀ z, (st₁.mem z = 0 ∨ z = inp.aVComp + u ∨ z = inp.aVLoc + u) → m2 z = 0 := by
        intro z hz
        dsimp only [m2, m1]
        by_cases hzl : z = inp.aVLoc + u
        · rw [hzl, Function.update_self]
        · rw [Function.update_of_ne hzl]
          by_cases hzc : z = inp.aVComp + u
          · rw [hzc, Function.update_self]
          · rw [Function.update_of_ne hzc]
            rcases hz with h | h | h
            · exact h
            · exact False.elim (hzc h)
            · exact False.elim (hzl h)
      have hag_m2 : ∀ x, (x < inp.aVComp ∨ inp.hBlocksStart ≤ x) → m2 x = st₁.mem x := by
        intro x hx
        have hvc_in : inp.aVComp ≤ inp.aVComp + u ∧ inp.aVComp + u < inp.hBlocksStart := by
          rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc]; omega
        have hvl_in : inp.aVComp ≤ inp.aVLoc + u ∧ inp.aVLoc + u < inp.hBlocksStart := by
          rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc]; omega
        dsimp only [m2, m1]
        rw [Function.update_of_ne (by rcases hx with h | h <;> omega),
          Function.update_of_ne (by rcases hx with h | h <;> omega)]
      have hvm2 : VertMarksUnmarkPartial inp m2 i₀ i₁ ci (k + 1) := by
        refine ⟨fun u' hu' hnot => ⟨hzero_pres _ (Or.inl (hvm1.1 u' hu' hnot).1),
            hzero_pres _ (Or.inl (hvm1.1 u' hu' hnot).2)⟩,
          fun cj hcj h1 h2 p hp => ⟨hzero_pres _ (Or.inl (hvm1.2.1 cj hcj h1 h2 p hp).1),
            hzero_pres _ (Or.inl (hvm1.2.1 cj hcj h1 h2 p hp).2)⟩,
          fun hci' p hp hp2 => ?_⟩
        by_cases hpk : p = k
        · subst hpk
          exact ⟨hzero_pres _ (Or.inr (Or.inl rfl)), hzero_pres _ (Or.inr (Or.inr rfl))⟩
        · exact ⟨hzero_pres _ (Or.inl (hvm1.2.2 hci' p (by omega) hp2).1),
            hzero_pres _ (Or.inl (hvm1.2.2 hci' p (by omega) hp2).2)⟩
      let s_next : State :=
        { mem := m2, regs := Function.update st₁.regs 19 u, pos := st₁.pos }
      have hf_next : PrepFullRegs inp s_next :=
        prepFullRegs_congr hf1 fun r hr => by
          dsimp only [s_next]; rw [Function.update_of_ne (by omega)]
      refine ⟨.normal, s_next, _,
        runs_store_iff.mpr ⟨_, _, hstore_eval_a, ev_const (by omega), rfl, rfl, rfl⟩, ?_,
        by norm_num [Expr.size]⟩
      refine ⟨⟨hf_next,
        by simp [s_next, h16_1], by simp [s_next, h17_1], by simp [s_next, h20_1], by simp [s_next, h21_1],
        by simp [s_next, h22_1], by simp [s_next, h23_1], by simp [s_next, h24_1], by simp [s_next],
        prepStaticState_of_agree hst1 (fun x hx =>
          hag_m2 x (Or.inl (by simp only [PrepInput.aVComp]; omega))),
        compsDoneUpTo_of_agree hv hle hdone1
          (fun x hx1 hx2 => hag_m2 x (Or.inl (by simp only [PrepInput.aVComp]; omega)))
          (fun x hx1 hx2 => hag_m2 x (Or.inr hx1)),
        compsParsedFrom_of_agree hparsed1 (fun x hx1 hx2 =>
          hag_m2 x (Or.inl (by simp only [PrepInput.aVComp]; omega))),
        hvm2,
        fun x hx => (hag_m2 x (Or.inr (by
          have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le i₁); omega))).trans (hzf1 x hx)⟩,
        by simp [s_next, h25_1]⟩
    intro st ω ⟨hf, h16, h17, h22, h23, h24, hst, hdone, hparsed, hvm, hzf⟩
    have hcomp_1 : st.mem (inp.aComps + 7 * ci + 1) = c.2.length := (hdone ci hci_hi).2.1
    have hcomp_2 : st.mem (inp.aComps + 7 * ci + 2) = inp.cVertsPtr ci := (hdone ci hci_hi).2.2.1
    dsimp only [prepUnmarkBody]
    refine runs_seq_assign0 (v := inp.aComps + 7 * ci)
      (ev_add (ev_reg hf.2.2.1 (by omega))
        (ev_mul (ev_const (by omega)) (ev_reg h24 (by omega)) h7ci_lt) ha31_lt) ?_
    refine runs_seq_assign_le (v := c.2.length)
      (ev_load (ev_add (ev_reg (by simp) ha31_lt) (ev_const hw1) ha31_1_lt)
        (by simpa using hcomp_1) hc2_lt) ?_
    refine runs_seq_assign_le (v := inp.cVertsPtr ci)
      (ev_load (ev_add (ev_reg (by simp) ha31_lt) (ev_const (by omega)) ha31_2_lt)
        (by simpa using hcomp_2) hvptr_lt) ?_
    refine runs_seq_assign_le (v := 0) (ev_const (by omega)) ?_
    let s_inner : State :=
      { mem := st.mem,
        regs := Function.update (Function.update (Function.update (Function.update
          st.regs 31 (inp.aComps + 7 * ci)) 20 c.2.length) 21 (inp.cVertsPtr ci)) 25 0,
        pos := st.pos }
    have hs_inner : InnerInv 0 s_inner := by
      refine ⟨prepFullRegs_congr hf (fun r hr => by
          dsimp only [s_inner]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hst, hdone, hparsed, hvm, hzf⟩
      · dsimp only [s_inner]; simp [h16]
      · dsimp only [s_inner]; simp [h17]
      · dsimp only [s_inner]; simp
      · dsimp only [s_inner]; simp
      · dsimp only [s_inner]; simp [h22]
      · dsimp only [s_inner]; simp [h23]
      · dsimp only [s_inner]; simp [h24]
      · dsimp only [s_inner]; simp
    rcases hinner_loop s_inner ω hs_inner with ⟨o, st', c_cost, hruns, hpost, hcost⟩
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      rcases hpost with ⟨hf', h16', h17', _, _, h22', h23', h24', _, hst', hdone', hparsed', hvm', hzf'⟩
      have hvm_next : VertMarksUnmarkPartial inp st'.mem i₀ i₁ (ci + 1) 0 := by
        refine ⟨hvm'.1, ?_, fun _ _ _ => by omega⟩
        intro cj hcj h1 h2 p hp
        by_cases hcj_eq : cj = ci
        · subst cj
          exact hvm'.2.2 hci_len p (by rw [← hmem_c]; exact hp) hp
        · exact hvm'.2.1 cj hcj h1 (by omega) p hp
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
      exact ⟨hf, h16, h17, h22, h23, hst, hdone, hparsed,
        vertMarksZero_of_unmarkPartial hle hvm, hzf⟩
  · have hrc : rangeCost stepCost i₀ i₁ = (block.map (fun c => 30 * c.2.length + 30)).sum := by
      suffices ∀ m s, s + m = i₁ → i₀ ≤ s →
          ((List.range' s m).map stepCost).sum =
            ((List.range' s m).map (fun j => 30 * block[j - i₀]!.2.length + 30)).sum by
        have hsum_blk : ((List.range' i₀ block.length).map
            (fun j => 30 * block[j - i₀]!.2.length + 30)).sum =
            (block.map (fun c => 30 * c.2.length + 30)).sum := by
          clear hfor hpw_rc hsz
          have hgen : ∀ (k : ℕ) (xs : List (ℕ × List ℕ)),
              ((List.range' k xs.length).map (fun j => 30 * xs[j - k]!.2.length + 30)).sum =
                (xs.map (fun c => 30 * c.2.length + 30)).sum := by
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
      have hg := hget_blk (j - i₀) hidx
      rw [show i₀ + (j - i₀) = j by omega] at hg
      simp only [stepCost, List.getElem!_eq_getElem?_getD, hg, List.getElem?_eq_getElem hidx,
        Option.getD_some]
    have hsum_add : (block.map (fun c => 30 * c.2.length + 30)).sum + (i₁ - i₀) * 9 + 7 ≤ unmarkCost := by
      dsimp only [unmarkCost]
      have hmul : ∀ (xs : List (ℕ × List ℕ)) (a b : ℕ),
          (xs.map (fun c => a * c.2.length + b)).sum + xs.length * 9 + 7 ≤
            (xs.map (fun c => a * c.2.length + (b + 10))).sum + 15 := by
        intro xs a b
        induction xs with
        | nil => simp
        | cons x xs ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
          omega
      simpa [show i₁ - i₀ = block.length by omega] using hmul block 30 30
    simp only [Expr.size] at hsum_add ⊢
    rw [hrc]
    exact hsum_add

/-- Verification of `prepBlockBody`: processes one same-level block `[i₀, i₁)` cleanly in
`O(block.length + ∑ c.2.length + edges.length)` time while preserving `VertMarksZero`. -/
theorem prepBlockBody_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest) :
    let i₁ := i₀ + block.length
    let edges := DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl
    let bCost := 365 * block.length + 60 * (block.map (·.2.length)).sum + 225 * edges.length
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
      prepBlockBody
      (normalPost fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₁ ∧
        st.regs 17 = i₁ ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₁ ∧
        CompsParsedFrom inp st.mem i₁ ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem (inp.cJSubPtr i₁))
      (fun _ => bCost) := by
  have hsz := inp.size_bounds hv
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨_, hpos, hle, _, _, _, _⟩ := compBlocksAux_split_spec hv.2.2.2.2.2.2.2.2.2.2.1 hcb
  intro i₁ edges bCost
  have h6 : Triple w p
      (fun st =>
        PrepFullRegs inp st ∧ st.regs 16 = inp.cJSubPtr i₁ ∧ st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧ st.regs 23 = lvl ∧ PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₁ ∧ CompsParsedFrom inp st.mem i₁ ∧
        VertMarksZero inp st.mem ∧ ZeroFrom st.mem (inp.cJSubPtr i₁))
      (Stmt.assign 17 (Expr.reg 22))
      (normalPost fun st =>
        PrepFullRegs inp st ∧ st.regs 16 = inp.cJSubPtr i₁ ∧ st.regs 17 = i₁ ∧
        PrepStaticState inp mem₀ st.mem ∧ CompsDoneUpTo inp st.mem i₁ ∧
        CompsParsedFrom inp st.mem i₁ ∧ VertMarksZero inp st.mem ∧ ZeroFrom st.mem (inp.cJSubPtr i₁))
      (fun _ => 2) := by
    refine Triple.conseq (Triple.assign (val := fun _ => i₁)
        (fun st h => ev_reg h.2.2.2.1 (by omega))
        (fun st ⟨hf, h16, _, h22, _, hst, hdone, hparsed, hvz, hzf⟩ =>
          ⟨prepFullRegs_congr hf (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
           by simp [h16], by simp, hst, hdone, hparsed, hvz, hzf⟩))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ => by norm_num [Expr.size])
  have h5 := Triple.seq_normal_const (prepUnmark_triple inp mem₀ hv hcb) h6
  have h4 := Triple.seq_normal_const (prepFill_triple inp mem₀ hv hcb) h5
  have h3 := Triple.seq_normal_const (prepAlloc_triple inp mem₀ hv hcb) h4
  have h2 := Triple.seq_normal_const (prepCount_triple inp mem₀ hv hcb) h3
  have h1 := Triple.seq_normal_const (prepMark_triple inp mem₀ hv hcb) h2
  have h0 := Triple.seq_normal_const (prepFindEnd_triple inp mem₀ hv hcb) h1
  refine h0.conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => ?_)
  have hsum_map : ∀ (a b : ℕ) (xs : List (ℕ × List ℕ)),
      (xs.map fun c => a * c.2.length + b).sum = a * (xs.map (·.2.length)).sum + b * xs.length := by
    intro a b xs
    induction xs with
    | nil => simp
    | cons c cs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  dsimp only [bCost, edges]
  rw [hsum_map 30 60 block, hsum_map 30 40 block]
  omega

private theorem sum_filter_nodup_le {α : Type*} (xs : List α) (f : α → ℕ) (lvls : List ℕ)
    (hnd : lvls.Nodup) :
    (lvls.map fun l => (xs.filter fun x => decide (f x = l)).length).sum ≤ xs.length := by
  induction lvls generalizing xs with
  | nil => simp
  | cons l ls ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    have hsplit : (xs.filter fun x => decide (f x = l)).length +
        (xs.filter fun x => decide (f x ≠ l)).length = xs.length := by
      clear ih hnd
      induction xs with
      | nil => simp
      | cons y ys hy =>
        rw [List.filter_cons, List.filter_cons, List.length_cons]
        by_cases hfy : f y = l
        · have h1 : decide (f y = l) = true := decide_eq_true hfy
          have h2 : decide (f y ≠ l) = false := decide_eq_false (by simp [hfy])
          simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.length_cons]
          omega
        · have h1 : decide (f y = l) = false := decide_eq_false hfy
          have h2 : decide (f y ≠ l) = true := decide_eq_true hfy
          simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.length_cons]
          omega
    have hcong : ls.map (fun l' => ((xs.filter fun x => decide (f x ≠ l)).filter fun x => decide (f x = l')).length) =
        ls.map (fun l' => (xs.filter fun x => decide (f x = l')).length) := by
      refine List.map_congr_left fun l' hl' => ?_
      have hne : l' ≠ l := fun h => hnd.1 (h ▸ hl')
      congr 1
      rw [List.filter_filter]
      refine List.filter_congr fun x _ => ?_
      by_cases hfx : f x = l' <;> simp [hfx, hne]
    have hih := ih (xs.filter fun x => decide (f x ≠ l)) hnd.2
    rw [hcong] at hih
    omega

/-- Verification of `prepBlockLoopStmt`: iterates `prepBlockBody` over all contiguous level
blocks of `rawComps` in total time `≤ 820 * J0_strip.m + 10`. -/
theorem prepBlockLoop_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w) :
    Triple w p
      (fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr 0 ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsParsedFrom inp st.mem 0 ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem inp.hBlocksStart)
      prepBlockLoopStmt
      (normalPost fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.hEnd ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem inp.rawComps.length ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem inp.hEnd)
      (fun _ => 820 * inp.J0_strip.m + 10) := by
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  have hcb_props := compBlocksAux_props 0 inp.rawComps hpw_rc
  let blocks := compBlocksAux 0 inp.rawComps
  let bodyCost : (ℕ × ℕ × List (ℕ × List ℕ)) → ℕ := fun b =>
    365 * b.2.2.length + 60 * (b.2.2.map (·.2.length)).sum +
      225 * (DecomposeOutput.edgesAt inp.J0_strip inp.decomp b.2.1).length
  let Inv : List (ℕ × ℕ × List (ℕ × List ℕ)) → State → Prop := fun rem st =>
    ∃ done,
      blocks = done ++ rem ∧
      let i := (done.flatMap (·.2.2)).length
      PrepFullRegs inp st ∧
      st.regs 16 = inp.cJSubPtr i ∧
      st.regs 17 = i ∧
      PrepStaticState inp mem₀ st.mem ∧
      CompsDoneUpTo inp st.mem i ∧
      CompsParsedFrom inp st.mem i ∧
      VertMarksZero inp st.mem ∧
      ZeroFrom st.mem (inp.cJSubPtr i)
  have hloop :
      Triple w p (Inv blocks)
        (Stmt.loop (Expr.bin BinOp.lt (Expr.reg 17) (Expr.reg 8)) prepBlockBody)
        (normalPost fun st =>
          PrepFullRegs inp st ∧
          st.regs 16 = inp.hEnd ∧
          PrepStaticState inp mem₀ st.mem ∧
          CompsDoneUpTo inp st.mem inp.rawComps.length ∧
          VertMarksZero inp st.mem ∧
          ZeroFrom st.mem inp.hEnd)
        (fun _ => (blocks.map bodyCost).sum +
          blocks.length * ((Expr.bin BinOp.lt (Expr.reg 17) (Expr.reg 8)).size + 1) +
          (Expr.bin BinOp.lt (Expr.reg 17) (Expr.reg 8)).size + 1) := by
    refine Triple.loop_list (Inv := Inv) bodyCost ?_ ?_ blocks
    · intro st ⟨done, heq, hf, h16, h17, hst, hdone, _, hvz, hzf⟩
      have hdone_eq : done = blocks := by simpa using heq.symm
      have hi_eq : (done.flatMap (·.2.2)).length = inp.rawComps.length := by
        rw [hdone_eq]; exact congrArg List.length hcb_props.2.2.1
      rw [hi_eq, inp.cJSubPtr_length] at h16 hzf
      rw [hi_eq] at hdone h17
      have hev : (Expr.bin BinOp.lt (Expr.reg 17) (Expr.reg 8)).eval w st = some 0 :=
        ev_lt_f (ev_reg h17 (by omega)) (ev_reg hf.1.2.2.2.2.2.2.2.2.1 (by omega)) le_rfl hw1
      exact ⟨hev, hf, h16, hst, hdone, hvz, hzf⟩
    · intro b rest st ⟨done, heq, hf, h16, h17, hst, hdone, hparsed, hvz, hzf⟩
      rcases b with ⟨i₀, lvl, block⟩
      obtain ⟨h1_eq, hpos, hle, _, _, _, _⟩ := compBlocksAux_split_spec hpw_rc heq
      have hev : (Expr.bin BinOp.lt (Expr.reg 17) (Expr.reg 8)).eval w st = some 1 :=
        ev_lt_t (ev_reg (h1_eq ▸ h17) (by omega)) (ev_reg hf.1.2.2.2.2.2.2.2.2.1 (by omega))
          (by omega) hw1
      refine ⟨1, hev, by omega, ?_⟩
      intro s ω h_eq
      subst h_eq
      have hstep := prepBlockBody_triple (p := p) inp mem₀ hv heq
      rcases hstep s ω ⟨hf, h1_eq ▸ h16, h1_eq ▸ h17, hst, h1_eq ▸ hdone, h1_eq ▸ hparsed,
        hvz, h1_eq ▸ hzf⟩ with ⟨o, st', c_cost, hruns, hpost, hcost⟩
      cases o with
      | returned _ => exact False.elim hpost
      | normal =>
        rcases hpost with ⟨hf', h16', h17', hst', hdone', hparsed', hvz', hzf'⟩
        refine ⟨.normal, st', c_cost, hruns, ?_, ?_⟩
        · refine ⟨done ++ [(i₀, lvl, block)], by simpa [List.append_assoc] using heq, ?_⟩
          have hi1_eq : ((done ++ [(i₀, lvl, block)]).flatMap (·.2.2)).length =
              i₀ + block.length := by
            simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.length_append]
            omega
          rw [hi1_eq]
          exact ⟨hf', h16', h17', hst', hdone', hparsed', hvz', hzf'⟩
        · exact hcost
  dsimp only [prepBlockLoopStmt]
  intro st ω ⟨hf, h16, hst, hparsed, hvz, hzf⟩
  refine runs_seq_assign0 (v := 0) (ev_const (by omega)) ?_
  have hinv0 : Inv blocks { st with regs := Function.update st.regs 17 0 } := by
    refine ⟨[], rfl,
      prepFullRegs_congr hf (fun r hr => by dsimp only; simp only [Function.update_of_ne (show r ≠ 17 by omega)]),
      by simp [h16], by simp, hst, fun _ hk => by simp at hk, hparsed, hvz, ?_⟩
    simpa [inp.cJSubPtr_zero] using hzf
  rcases hloop _ ω hinv0 with ⟨o, st', c_cost, hruns, hpost, hcost⟩
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    have hblocks_sum_len : (blocks.map (fun b => b.2.2.length)).sum = inp.rawComps.length :=
      hcb_props.2.1
    have hblocks_sum_vlen : (blocks.map (fun b => (b.2.2.map (·.2.length)).sum)).sum =
        (inp.rawComps.map (·.2.length)).sum := by
      have hfm := hcb_props.2.2.1
      clear hloop hwb hsz
      have hgen : ∀ (bs : List (ℕ × ℕ × List (ℕ × List ℕ))),
          (bs.map (fun b => (b.2.2.map (·.2.length)).sum)).sum =
            ((bs.flatMap (·.2.2)).map (·.2.length)).sum := by
        intro bs
        induction bs with
        | nil => simp
        | cons b bs ih =>
          simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
            List.sum_append, ih]
      rw [hgen blocks, hfm]
    have hblocks_sum_edges : (blocks.map (fun b =>
        (DecomposeOutput.edgesAt inp.J0_strip inp.decomp b.2.1).length)).sum ≤ inp.J0_strip.m := by
      have hnd_gen : ∀ (bs : List (ℕ × ℕ × List (ℕ × List ℕ))),
          List.Pairwise (fun a b => a.2.1 < b.2.1) bs → (bs.map (·.2.1)).Nodup := by
        intro bs hpw
        induction bs with
        | nil => simp
        | cons b bs ih =>
          rw [List.pairwise_cons] at hpw
          rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hm => ?_, ih hpw.2⟩
          rcases List.mem_map.mp hm with ⟨b', hb', hb'_eq⟩
          have := hpw.1 b' hb'
          omega
      have hnd_lvl : (blocks.map (·.2.1)).Nodup := hnd_gen blocks hcb_props.1
      have hfilt := sum_filter_nodup_le (List.range inp.J0_strip.m) (fun j => inp.decomp.level j)
        (blocks.map (·.2.1)) hnd_lvl
      simp only [List.map_map, Function.comp_def, List.length_range] at hfilt
      simpa only [DecomposeOutput.edgesAt] using hfilt
    have hblocks_len_le : blocks.length ≤ (blocks.map (fun b => b.2.2.length)).sum := by
      have hpos_b := hcb_props.2.2.2
      clear hloop hwb hsz
      have hgen : ∀ (bs : List (ℕ × ℕ × List (ℕ × List ℕ))),
          (∀ b ∈ bs, 0 < b.2.2.length) → bs.length ≤ (bs.map (fun b => b.2.2.length)).sum := by
        intro bs hbs
        induction bs with
        | nil => simp
        | cons b bs ih =>
          have hb := hbs b List.mem_cons_self
          have ih' := ih fun x hx => hbs x (List.mem_cons_of_mem _ hx)
          simp only [List.length_cons, List.map_cons, List.sum_cons]
          omega
      exact hgen blocks fun b hb => (hpos_b b hb).1
    have hsum_body : (blocks.map bodyCost).sum =
        365 * (blocks.map (fun b => b.2.2.length)).sum +
        60 * (blocks.map (fun b => (b.2.2.map (·.2.length)).sum)).sum +
        225 * (blocks.map (fun b => (DecomposeOutput.edgesAt inp.J0_strip inp.decomp b.2.1).length)).sum := by
      have hgen : ∀ (bs : List (ℕ × ℕ × List (ℕ × List ℕ))),
          (bs.map bodyCost).sum =
            365 * (bs.map (fun b => b.2.2.length)).sum +
            60 * (bs.map (fun b => (b.2.2.map (·.2.length)).sum)).sum +
            225 * (bs.map (fun b => (DecomposeOutput.edgesAt inp.J0_strip inp.decomp b.2.1).length)).sum := by
        intro bs
        induction bs with
        | nil => simp
        | cons b bs ih =>
          simp only [List.map_cons, List.sum_cons, bodyCost, ih]
          ring
      exact hgen blocks
    have hvsum_le : 2 * inp.rawComps.length + (inp.rawComps.map (·.2.length)).sum ≤ 4 * inp.J0_strip.m := by
      have := hsz.2.2.1
      have hgen : ∀ (xs : List (ℕ × List ℕ)),
          2 * xs.length + (xs.map (·.2.length)).sum = (xs.map fun c => 2 + c.2.length).sum := by
        intro xs
        induction xs with
        | nil => simp
        | cons x xs ih => simp only [List.length_cons, List.map_cons, List.sum_cons] at ih ⊢; omega
      rw [hgen inp.rawComps]
      exact this
    refine ⟨.normal, st', c_cost, hruns, hpost, ?_⟩
    norm_num [Expr.size] at hcost ⊢
    rw [hsum_body, hblocks_sum_len, hblocks_sum_vlen] at hcost
    omega


end MinCostFlow.Spanner
