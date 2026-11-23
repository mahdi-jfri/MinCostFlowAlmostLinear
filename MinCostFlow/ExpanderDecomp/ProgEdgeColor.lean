module

public import MinCostFlow.ExpanderDecomp.ProgEdgeColorBase

import Mathlib.Tactic.Linarith

/-!
# Word-RAM Greedy 17-Edge-Colouring (`ProgEdgeColor`)

Completes the verification of `edgeColor17Proc` (defined in `ProgEdgeColorBase.lean`):
- `ecColorLoop_triple`: Pass 1 greedy 17-colouring of `removeLoops G`;
- `ecClearUsed_triple`: Pass 2 resetting `usedAddr` to all zeros without scanning `range G.n`;
- `edgeColor17Proc_spec` and non-vacuity witness `edgeColor17Contract_pre_example`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Pass 1 triple: greedy 17-colouring of `removeLoops G`. -/
private lemma ecColorLoop_triple {w ga ua oa : ℕ}
    (p : Program) (mem : ℕ → ℕ) (G : Graph) (st₀ : State)
    (hGA : GraphAt mem ga G) (hval : G.IsValid)
    (hused0 : ∀ idx < 17 * G.n, mem (ua + idx) = 0)
    (hw : EdgeColorWordBound w G.n G.m ga ua oa)
    (hd : EdgeColorDisjoint G.n G.m ga ua oa)
    (hregs : EcRegs ga ua oa G.m st₀) (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) ecColorLoopStmt
      (normalPost fun st' =>
        EcRegs ga ua oa G.m st' ∧
        st'.regs ecOutM = (edgeColor17 G).length ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 mem st'.mem ua (ua + 17 * G.n) oa (oa + 3 * G.m) ∧
        (∀ x < G.n, ∀ c < 17, st'.mem (ua + 17 * x + c) =
          if colorUsedAtVert (edgeColor17 G) x c then 1 else 0) ∧
        ColoredEdgesAt st'.mem oa (edgeColor17 G))
      (fun _ => 1000 * G.m + 40) := by
  rcases hw with ⟨hga_w, hua_w, hoa_w, hw32⟩
  rcases hd with ⟨hd_ug, hd_uo, hd_og⟩
  have hw' : EdgeColorWordBound w G.n G.m ga ua oa := ⟨hga_w, hua_w, hoa_w, hw32⟩
  have hGE_at : EdgesAt mem (ga + 2) G.edges := graphAt_to_edgesAt hGA
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [ecColorLoopStmt, seqStmts]
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs ecOutM 0, pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    EcRegs ga ua oa G.m st ∧ st.regs ecI = j ∧
    st.regs ecOutM = (edgeColor17Prefix G j).length ∧
    st.pos = st₀.pos ∧
    PreservedOutside2 mem st.mem ua (ua + 17 * G.n) oa (oa + 3 * G.m) ∧
    (∀ x < G.n, ∀ c < 17, st.mem (ua + 17 * x + c) =
      if colorUsedAtVert (edgeColor17Prefix G j) x c then 1 else 0) ∧
    ColoredEdgesAt st.mem oa (edgeColor17Prefix G j)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := ecI) (lo := .const 0) (hi := .reg ecM)
    (body := seqStmts [
      .assign ecU (.load (.bin .add (.bin .add (.reg ecG) (.const 2)) (.bin .mul (.const 2) (.reg ecI)))),
      .assign ecV (.load (.bin .add (.bin .add (.reg ecG) (.const 3)) (.bin .mul (.const 2) (.reg ecI)))),
      .cond (.bin .eq (.reg ecU) (.reg ecV))
        .nop
        (seqStmts [
          ecFindColorStmt,
          .store (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecU))) (.reg ecChosen)) (.const 1),
          .store (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecV))) (.reg ecChosen)) (.const 1),
          .store (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecOutM))) (.reg ecU),
          .store (.bin .add (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecOutM))) (.const 1)) (.reg ecV),
          .store (.bin .add (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecOutM))) (.const 2)) (.reg ecChosen),
          .assign ecOutM (.bin .add (.reg ecOutM) (.const 1))
        ])])
    (P := fun st => st = st1) (Inv := Inv) 980 0 G.m (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega),
        ecRegs_update_ge (r := ecI) (by decide) (ecRegs_update_ge (r := ecOutM) (by decide) hregs),
        by simp,
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self,
             edgeColor17Prefix_zero]; rfl,
        rfl, fun a _ _ => by simp [st1, hmem],
        fun x hx c hc => by
          rw [hmem, edgeColor17Prefix_zero]
          simp only [colorUsedAtVert, List.any_nil, Bool.false_eq_true, ↓reduceIte]
          rw [Nat.add_assoc]; exact hused0 (17 * x + c) (by omega),
        fun t ht => by simp [edgeColor17Prefix_zero] at ht⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_m)
    (fun j _ hjlt => by
      intro st ω ⟨hr, hj, houtM, hpos, hpr, hused, hcol⟩
      have hj_len : j < G.edges.length := hjlt
      set ed := G.edges[j]'hj_len
      have hed_val := hval ed (List.getElem_mem hj_len)
      have hmem_u : st.mem (ga + 2 + 2 * j) = ed.1 := by
        rw [hpr (ga + 2 + 2 * j)
          (disjointRange_outside hd_ug (by omega) (by omega))
          (disjointRange_outside hd_og (by omega) (by omega))]
        exact (hGE_at j hj_len).1
      have hmem_v : st.mem (ga + 3 + 2 * j) = ed.2 := by
        rw [hpr (ga + 3 + 2 * j)
          (disjointRange_outside hd_ug (by omega) (by omega))
          (disjointRange_outside hd_og (by omega) (by omega))]
        have h2 := (hGE_at j hj_len).2
        rwa [show ga + 2 + 2 * j + 1 = ga + 3 + 2 * j by omega] at h2
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := ed.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hr.r_g) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hj) (by omega)) (by omega))
          hmem_u) ?_
      refine runs_seq_assign_le (v := ed.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := ga) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_g]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hj])) (by omega))
            (by omega))
          hmem_v) ?_
      refine runs_cond_le (v := if ed.1 = ed.2 then 1 else 0)
        (Expr.eval_eq_op
          (Expr.eval_reg_of_eq (v := ed.1) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
          (Expr.eval_reg_of_eq (v := ed.2) (by simp)) (by omega))
        (fun heq_ne => ?_) (fun heq_0 => ?_)
      · -- Loop skipped: `ed.1 = ed.2`
        have heq : ed.1 = ed.2 := by by_contra hne; simp [hne] at heq_ne
        have hsucc : edgeColor17Prefix G (j + 1) = edgeColor17Prefix G j := by
          rw [edgeColor17Prefix_succ hj_len]; simp [ed, heq]
        refine runs_nop_le ?_ (by simp [Expr.size])
        refine ⟨⟨ecRegs_update_ge (r := ecI) (by decide)
            (ecRegs_update_ge (r := ecV) (by decide) (ecRegs_update_ge (r := ecU) (by decide) hr)),
          by simp,
          by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
               Function.update_of_ne (by decide), houtM, hsucc],
          hpos, hpr, fun x hx c hc => by rw [hsucc]; exact hused x hx c hc, hsucc.symm ▸ hcol⟩,
          by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]⟩
      · -- Non-loop edge: find colour, update `usedAddr`, emit triple
        have hne : ed.1 ≠ ed.2 := fun h1 => by simp [h1] at heq_0
        set prev := edgeColor17Prefix G j
        set chosen := pickColor 17 prev ed
        have hch_lt : chosen < 17 := pickColor_lt (by omega) prev ed
        have hprev_le : prev.length ≤ j := edgeColor17Prefix_length_le G j
        have hsucc : edgeColor17Prefix G (j + 1) = prev ++ [(ed, chosen)] := by
          rw [edgeColor17Prefix_succ hj_len]; simp [ed, hne, prev, chosen]
        let st_fc : State :=
          { mem := st.mem,
            regs := Function.update (Function.update st.regs ecU ed.1) ecV ed.2,
            pos := st.pos }
        refine runs_seq_triple_le
          (ecFindColor_triple (u := ed.1) (v := ed.2) (i := j) (outM := prev.length)
            p st.mem prev st_fc hed_val.1 hed_val.2 hused hw'
            (ecRegs_update_ge (r := ecV) (by decide) (ecRegs_update_ge (r := ecU) (by decide) hr))
            (by dsimp only [st_fc]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj])
            (by dsimp only [st_fc]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), houtM])
            (by dsimp only [st_fc]; rw [Function.update_of_ne (by decide), Function.update_self])
            (by simp [st_fc]) rfl) rfl ?_
        intro st2 ⟨hr2, hri2, hroutM2, hru2, hrv2, hrch2, hmem2, hpos2⟩
        refine runs_seq_store_le (x := ua + 17 * ed.1 + chosen) (v := 1)
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hr2.r_used)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hru2) (by omega)) (by omega))
            (Expr.eval_reg_of_eq hrch2) (by omega))
          (Expr.eval_const (by omega)) ?_
        refine runs_seq_store_le (x := ua + 17 * ed.2 + chosen) (v := 1)
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hr2.r_used)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hrv2) (by omega)) (by omega))
            (Expr.eval_reg_of_eq hrch2) (by omega))
          (Expr.eval_const (by omega)) ?_
        refine runs_seq_store_le (x := oa + 3 * prev.length) (v := ed.1)
          (Expr.eval_add (Expr.eval_reg_of_eq hr2.r_out)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hroutM2) (by omega)) (by omega))
          (Expr.eval_reg_of_eq hru2) ?_
        refine runs_seq_store_le (x := oa + 3 * prev.length + 1) (v := ed.2)
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hr2.r_out)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hroutM2) (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq hrv2) ?_
        refine runs_seq_store_le (x := oa + 3 * prev.length + 2) (v := chosen)
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hr2.r_out)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hroutM2) (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq hrch2) ?_
        refine runs_assign_le (v := prev.length + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq hroutM2) (Expr.eval_const (by omega)) (by omega)) ?_
          (by simp [Expr.size])
        refine ⟨⟨ecRegs_update_ge (r := ecI) (by decide)
            (ecRegs_update_ge (r := ecOutM) (by decide)
              (ecRegs_update_mem (ecRegs_update_mem (ecRegs_update_mem
                (ecRegs_update_mem (ecRegs_update_mem hr2)))))),
          by simp,
          by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self, hsucc,
               List.length_append, List.length_singleton],
          hpos2.trans hpos, ?_, ?_, ?_⟩,
          by dsimp only; rw [Function.update_of_ne (by decide), hri2]⟩
        · intro a hau hao
          dsimp only
          rw [Function.update_of_ne (by rcases hao with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hao with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hao with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hau with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hau with h1 | h1 <;> omega), hmem2]
          exact hpr a hau hao
        · intro x hx c hc
          dsimp only
          rw [hsucc, colorUsedAtVert_append_singleton,
            Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega),
            Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega)]
          by_cases h2 : x = ed.2 ∧ c = chosen
          · rcases h2 with ⟨rfl, rfl⟩
            simp [Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            by_cases h1 : x = ed.1 ∧ c = chosen
            · rcases h1 with ⟨rfl, rfl⟩
              simp [Function.update_self]
            · rw [Function.update_of_ne (by omega), hmem2, hused x hx c hc]
              have hfalse : (decide (chosen = c) && decide (ed.1 = x ∨ ed.2 = x)) = false := by
                by_cases hcc : chosen = c
                · subst hcc; simp; omega
                · simp [hcc]
              rw [hfalse, Bool.or_false]
        · intro t ht
          dsimp only
          have ht' : t < prev.length + 1 := by
            have := ht; rw [hsucc, List.length_append, List.length_singleton] at this; exact this
          by_cases hteq : t = prev.length
          · subst hteq
            have hget : (edgeColor17Prefix G (j + 1))[prev.length]'ht = (ed, chosen) := by
              simp only [hsucc]; rw [List.getElem_append_right (le_refl _)]; simp
            rw [hget]
            exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
              by rw [Function.update_of_ne (by omega), Function.update_self],
              by rw [Function.update_self]⟩
          · have htlt : t < prev.length := by omega
            have hget : (edgeColor17Prefix G (j + 1))[t]'ht = prev[t]'htlt := by
              simp only [hsucc]; exact List.getElem_append_left htlt
            rw [hget]
            refine ⟨?_, ?_, ?_⟩
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega),
                Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega),
                Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega), hmem2]
              exact (hcol t htlt).1
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega),
                Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega),
                Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega), hmem2]
              exact (hcol t htlt).2.1
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega),
                Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega),
                Function.update_of_ne (by rcases hd_uo with h1 | h1 <;> omega), hmem2]
              exact (hcol t htlt).2.2)
  rcases hloop st1 ω rfl with ⟨o, st', c, hr, hq, hc⟩
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨hr', _, houtM', hpos', hpr', hused', hcol'⟩
    rw [edgeColor17Prefix_full] at houtM' hused' hcol'
    exact ⟨.normal, st', c, hr, ⟨hr', houtM', hpos', hpr', hused', hcol'⟩,
      by simp [Expr.size] at hc ⊢; omega⟩

/-- Pass 2 triple: resets all `usedAddr` entries marked by `colored` back to `0`. -/
private lemma ecClearUsed_triple {w n mG ga ua oa : ℕ}
    (p : Program) (mem : ℕ → ℕ) (colored : List ((ℕ × ℕ) × ℕ)) (st₀ : State)
    (hlen_le : colored.length ≤ mG)
    (hcol_val : ∀ ec ∈ colored, ec.1.1 < n ∧ ec.1.2 < n ∧ ec.2 < 17)
    (hcol_at : ColoredEdgesAt mem oa colored)
    (hused_at : ∀ x < n, ∀ c < 17, mem (ua + 17 * x + c) = if colorUsedAtVert colored x c then 1 else 0)
    (hw : EdgeColorWordBound w n mG ga ua oa)
    (hd_uo : DisjointRange ua (17 * n) oa (3 * mG))
    (hregs : EcRegs ga ua oa mG st₀) (hroutM : st₀.regs ecOutM = colored.length)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) ecClearUsedStmt
      (normalPost fun st' =>
        EcRegs ga ua oa mG st' ∧ st'.regs ecOutM = colored.length ∧ st'.pos = st₀.pos ∧
        MemFrame mem st'.mem ua (ua + 17 * n) ∧
        (∀ idx < 17 * n, st'.mem (ua + idx) = 0))
      (fun _ => 75 * colored.length + 20) := by
  rcases hw with ⟨_, hua_w, hoa_w, hw32⟩
  let Inv : ℕ → State → Prop := fun j st =>
    EcRegs ga ua oa mG st ∧ st.regs ecI = j ∧ st.regs ecOutM = colored.length ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem ua (ua + 17 * n) ∧
    (∀ x < n, ∀ c < 17, st.mem (ua + 17 * x + c) = 0 ∨ colorUsedAtVert (colored.drop j) x c = true)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := ecI) (lo := .const 0) (hi := .reg ecOutM)
    (body := seqStmts [
      .assign ecU (.load (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecI)))),
      .assign ecV (.load (.bin .add (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecI))) (.const 1))),
      .assign ecChosen (.load (.bin .add (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecI))) (.const 2))),
      .store (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecU))) (.reg ecChosen)) (.const 0),
      .store (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecV))) (.reg ecChosen)) (.const 0)])
    (P := fun st => st = st₀) (Inv := Inv) 62 0 colored.length (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), ecRegs_update_ge (r := ecI) (by decide) hregs,
        by simp, by dsimp only; rw [Function.update_of_ne (by decide), hroutM], rfl,
        hmem ▸ memFrame_refl _ _ _, fun x hx c hc => by
          rw [hmem, hused_at x hx c hc, List.drop_zero]
          cases colorUsedAtVert colored x c <;> simp⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.1)
    (fun j _ hjlt => by
      intro st ω ⟨hr, hj, hroutM', hpos, hfr, hclr⟩
      set ec := colored[j]'hjlt
      have hec_val := hcol_val ec (List.getElem_mem hjlt)
      have hmem_u : st.mem (oa + 3 * j) = ec.1.1 := by
        rw [hfr (oa + 3 * j) (disjointRange_outside hd_uo (by omega) (by omega))]
        exact (hcol_at j hjlt).1
      have hmem_v : st.mem (oa + 3 * j + 1) = ec.1.2 := by
        rw [hfr (oa + 3 * j + 1) (disjointRange_outside hd_uo (by omega) (by omega))]
        exact (hcol_at j hjlt).2.1
      have hmem_c : st.mem (oa + 3 * j + 2) = ec.2 := by
        rw [hfr (oa + 3 * j + 2) (disjointRange_outside hd_uo (by omega) (by omega))]
        exact (hcol_at j hjlt).2.2
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := ec.1.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_out)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hj) (by omega)) (by omega))
          hmem_u) ?_
      refine runs_seq_assign_le (v := ec.1.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := oa) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_out]))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hj])) (by omega))
              (by omega))
            (Expr.eval_const (by omega)) (by omega))
          hmem_v) ?_
      refine runs_seq_assign_le (v := ec.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := oa)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr.r_out]))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := j)
                  (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj])) (by omega))
              (by omega))
            (Expr.eval_const (by omega)) (by omega))
          hmem_c) ?_
      refine runs_seq_store_le (x := ua + 17 * ec.1.1 + ec.2) (v := 0)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := ua)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hr.r_used]))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := ec.1.1)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                  Function.update_self])) (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := ec.2) (by simp)) (by omega))
        (Expr.eval_const (by omega)) ?_
      refine runs_store_le (x := ua + 17 * ec.1.2 + ec.2) (v := 0)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := ua)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hr.r_used]))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := ec.1.2)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := ec.2) (by simp)) (by omega))
        (Expr.eval_const (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨ecRegs_update_ge (r := ecI) (by decide)
          (ecRegs_update_mem (ecRegs_update_mem
            (ecRegs_update_ge (r := ecChosen) (by decide)
              (ecRegs_update_ge (r := ecV) (by decide)
                (ecRegs_update_ge (r := ecU) (by decide) hr))))),
        by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), Function.update_of_ne (by decide), hroutM'],
        hpos,
        memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
          (memFrame_update (by omega) (by omega))), ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), hj]⟩
      intro x hx c hc
      dsimp only
      by_cases h2 : x = ec.1.2 ∧ c = ec.2
      · rcases h2 with ⟨rfl, rfl⟩; left; simp [Function.update_self]
      · rw [Function.update_of_ne (by omega)]
        by_cases h1 : x = ec.1.1 ∧ c = ec.2
        · rcases h1 with ⟨rfl, rfl⟩; left; simp [Function.update_self]
        · rw [Function.update_of_ne (by omega)]
          rcases hclr x hx c hc with h0 | hdrop
          · exact Or.inl h0
          · right
            rw [List.drop_eq_getElem_cons hjlt] at hdrop
            simp only [colorUsedAtVert, List.any_cons, Bool.or_eq_true] at hdrop
            rcases hdrop with hhead | htail
            · exfalso
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hhead
              rcases hhead.2 with h1' | h2'
              · exact h1 ⟨h1'.symm, hhead.1.symm⟩
              · exact h2 ⟨h2'.symm, hhead.1.symm⟩
            · exact htail)
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hroutM', hpos, hfr, hclr⟩
    refine ⟨hr, hroutM', hpos, hfr, fun idx hidx => ?_⟩
    have hx : idx / 17 < n := by omega
    have hc : idx % 17 < 17 := Nat.mod_lt _ (by omega)
    have hsplit : ua + idx = ua + 17 * (idx / 17) + idx % 17 := by omega
    rw [hsplit]
    rcases hclr (idx / 17) hx (idx % 17) hc with h0 | hdrop
    · exact h0
    · simp [colorUsedAtVert] at hdrop
  · exact False.elim hq

/-! ## 5. Main Specification Theorem and Non-Vacuity Example -/

/-- `edgeColor17Proc` meets `edgeColor17Contract w` in `O(|G.edges| + 1)` deterministic steps,
without scanning `range G.n`. -/
theorem edgeColor17Proc_spec {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [edgeColor17Proc]) :
    MeetsContract w p b (edgeColor17Contract w) := by
  have hEntry : p.procs[b]? = some edgeColor17Proc := by simpa using hp 0 (by simp)
  intro args mem pos ω _ hpre
  rcases hpre with ⟨ga, ua, oa, G, hargs, hGA, hval, hused0, hw, hd⟩
  subst hargs
  have hread_G : Cited.readGraph mem ga = G := graphAt_iff_readGraph.mp hGA
  have hm_mem : mem (ga + 1) = G.m := graphAt_m hGA
  rcases hw with ⟨hga_w, hua_w, hoa_w, hw32⟩
  rcases hd with ⟨hd_ug, hd_uo, hd_og⟩
  have hw' : EdgeColorWordBound w G.n G.m ga ua oa := ⟨hga_w, hua_w, hoa_w, hw32⟩
  have hd' : EdgeColorDisjoint G.n G.m ga ua oa := ⟨hd_ug, hd_uo, hd_og⟩
  have hlen_le : (edgeColor17 G).length ≤ G.m := by
    rw [← edgeColor17Prefix_full]; exact edgeColor17Prefix_length_le G G.m
  have hcol_val : ∀ ec ∈ edgeColor17 G, ec.1.1 < G.n ∧ ec.1.2 < G.n ∧ ec.2 < 17 := by
    intro ec hec
    have hgen : ∀ j ≤ G.m, ∀ x ∈ edgeColor17Prefix G j, x.1.1 < G.n ∧ x.1.2 < G.n ∧ x.2 < 17 := by
      intro j hj
      induction j with
      | zero => intro x hx; simp [edgeColor17Prefix_zero] at hx
      | succ j ih =>
        intro x hx
        have hjlt : j < G.edges.length := hj
        rw [edgeColor17Prefix_succ hjlt] at hx
        split_ifs at hx
        · exact ih (by omega) x hx
        · rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx1 | rfl
          · exact ih (by omega) x hx1
          · have hv := hval _ (List.getElem_mem hjlt)
            exact ⟨hv.1, hv.2, pickColor_lt (by omega) _ _⟩
    exact hgen G.m (le_refl _) ec (edgeColor17Prefix_full G ▸ hec)
  have hrun : ∃ o st' c,
      Runs w p ω edgeColor17Proc (startState [ga, ua, oa] mem pos) o st' c ∧
      (edgeColor17Contract w).post [ga, ua, oa] mem o.value st'.mem ∧
      c ≤ edgeColor17Cost G.m := by
    refine runs_start_le ?_
    dsimp only [edgeColor17Proc, seqStmts]
    refine runs_seq_assign_le (v := G.m)
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (v := ga) (by simp [startState, ecG]))
          (Expr.eval_const (by omega)) (by omega))
        (by simp [startState, hm_mem])) ?_
    let st0 : State :=
      { mem := mem,
        regs := Function.update (startState [ga, ua, oa] mem pos).regs ecM G.m,
        pos := pos }
    have hr0 : EcRegs ga ua oa G.m st0 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals simp [st0, startState, ecG, ecUsed, ecOut, ecM]
    refine runs_seq_triple_le
      (ecColorLoop_triple p mem G st0 hGA hval hused0 hw' hd' hr0 rfl) rfl ?_
    intro st1 ⟨hr1, houtM1, _, hpr1, hused1, hcol1⟩
    refine runs_seq_triple_le
      (ecClearUsed_triple p st1.mem (edgeColor17 G) st1 hlen_le hcol_val hcol1 hused1 hw' hd_uo
        hr1 houtM1 rfl) rfl ?_
    intro st2 ⟨hr2, houtM2, _, hfr2, hclr2⟩
    refine runs_ret_le (Expr.eval_reg_of_eq houtM2) ?_ ?_
    · dsimp only [edgeColor17Contract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hread_G]
      have hcol2 : ColoredEdgesAt st2.mem oa (edgeColor17 G) := fun i hi => by
        have hi_m : i < G.m := by omega
        exact ⟨by rw [hfr2 (oa + 3 * i) (disjointRange_outside hd_uo (by omega) (by omega))]; exact (hcol1 i hi).1,
          by rw [hfr2 (oa + 3 * i + 1) (disjointRange_outside hd_uo (by omega) (by omega))]; exact (hcol1 i hi).2.1,
          by rw [hfr2 (oa + 3 * i + 2) (disjointRange_outside hd_uo (by omega) (by omega))]; exact (hcol1 i hi).2.2⟩
      refine ⟨trivial, hlen_le, hcol2, readColoredEdges_eq_of_coloredEdgesAt hcol2, ?_⟩
      intro a hao
      by_cases hau : a < ua ∨ ua + 17 * G.n ≤ a
      · rw [hfr2 a hau, hpr1 a hau hao]
      · have hidx : a - ua < 17 * G.n := by omega
        have ha_eq : ua + (a - ua) = a := by omega
        rw [← ha_eq, hclr2 (a - ua) hidx, hused0 (a - ua) hidx]
    · dsimp only [edgeColor17Cost, Expr.size]; omega
  rcases hrun with ⟨o, st', c, hr, hpost, hcost⟩
  exact ⟨edgeColor17Proc, hEntry, o, st', c, hr, hpost,
    by simpa [edgeColor17Contract, hread_G] using hcost⟩

/-- Non-vacuity witness for `edgeColor17Contract 16`. -/
theorem edgeColor17Contract_pre_example :
    ∃ args mem, (∀ a ∈ args, a < 2 ^ 16) ∧ (edgeColor17Contract 16).pre args mem := by
  let G : Graph := ⟨3, [(0, 1), (1, 2), (1, 1)]⟩
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 3 else if a = 1 then 3
    else if a = 2 then 0 else if a = 3 then 1
    else if a = 4 then 1 else if a = 5 then 2
    else if a = 6 then 1 else if a = 7 then 1
    else 0
  let args : List ℕ := [0, 20, 100]
  refine ⟨args, mem, by decide, ?_⟩
  refine ⟨0, 20, 100, G, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine graphAt_of_cells (by simp [G, mem]) (by simp [G, Graph.m, mem]) fun j hj => ?_
    rcases j with _ | _ | _ | j
    · simp [G, mem]; exact ⟨rfl, rfl⟩
    · simp [G, mem]
    · simp [G, mem]
    · simp [G, Graph.m] at hj; omega
  · intro e he; simp only [G, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  · intro idx hidx; simp only [mem]; split_ifs <;> omega
  · unfold EdgeColorWordBound; decide
  · unfold EdgeColorDisjoint DisjointRange; decide

end MinCostFlow.ExpanderDecomp
