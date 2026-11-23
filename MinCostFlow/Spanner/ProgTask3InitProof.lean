module

public import MinCostFlow.Spanner.ProgTask3SetupProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Initial Embedding Proof for Word-RAM Task 3

Proves `t3InitEmb_ptriple` (exact Hoare specification + cost `110 * J.m + 80` for procedure
`selfBase + 1`).
-/

open Classical in
private def t3InitEmbLoopInv {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (mem_s : ℕ → ℕ)
    (upTo : ℕ) (st : State) (Φ : ℕ) : Prop :=
  st.regs 0 = lay.base ∧
  st.regs 1 = inp.J.m ∧
  st.regs 2 = ctx.memT1 (ctx.wInp.h + 13) ∧
  st.regs 3 = ctx.memT1 (ctx.wInp.h + 16) ∧
  st.regs 4 = lay.embJWAddr ∧
  st.regs 5 = lay.econgCountAddr ∧
  st.regs 8 = upTo ∧
  Φ = 0 ∧
  T3StaticMem ctx lay st.mem ∧
  (∀ x < lay.embJWAddr, st.mem x = mem_s x) ∧
  (∀ x, lay.dsHandlesAddr ≤ x → x < lay.econgCountAddr → st.mem x = mem_s x) ∧
  (∀ x, lay.wDelStampAddr ≤ x → x < lay.staticEnd → st.mem x = mem_s x) ∧
  lay.staticEnd ≤ st.regs 6 ∧
  st.regs 6 ≤ lay.staticEnd + 5 * upTo ∧
  ZeroFrom st.mem (st.regs 6) ∧
  (st.regs 7 = if ∃ eJ < upTo, ∃ ci jL,
      ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL then 1 else 0) ∧
  (∀ eJ < upTo, match ctx.wd.jSources.getD eJ JEdgeSource.isLoop with
    | .isLoop => lay.staticEnd ≤ st.mem (lay.embJWAddr + eJ) ∧
        st.mem (lay.embJWAddr + eJ) + 2 ≤ st.regs 6 ∧
        WalkAt st.mem (st.mem (lay.embJWAddr + eJ)) Walk.empty
    | .inJ0 eW => lay.staticEnd ≤ st.mem (lay.embJWAddr + eJ) ∧
        st.mem (lay.embJWAddr + eJ) + 5 ≤ st.regs 6 ∧
        WalkAt st.mem (st.mem (lay.embJWAddr + eJ))
          (Walk.single (ctx.wd.W.edges.getD eW (0, 0)).1 (ctx.wd.W.edges.getD eW (0, 0)).2 eW)
    | .inComp _ _ => st.mem (lay.embJWAddr + eJ) = 0) ∧
  (∀ eJ, upTo ≤ eJ → eJ < inp.J.m → st.mem (lay.embJWAddr + eJ) = 0) ∧
  (∀ eW < ctx.wd.W.m, st.mem (lay.econgCountAddr + eW) =
    {eJ ∈ Finset.range upTo | ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW}.card)

private abbrev t3InitEmbLoopBody : Stmt :=
  Stmt.seq (.assign 9 (.load (t3Add (.reg 3) (t3Mul (.const 3) (.reg 8)))))
    (.cond (t3Eq (.reg 9) (.const 0))
      (Stmt.seq (.store (.reg 6) (.const 0))
        (Stmt.seq (t3St (.reg 6) (.const 1) (.const 0))
          (Stmt.seq (.store (t3Add (.reg 4) (.reg 8)) (.reg 6))
            (.assign 6 (t3Add (.reg 6) (.const 2))))))
      (.cond (t3Eq (.reg 9) (.const 1))
        (Stmt.seq (.assign 10 (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 8)) (.const 1))))
          (Stmt.seq (.assign 11 (t3Ld (.reg 2) (t3Add (.const 2) (t3Mul (.const 2) (.reg 10)))))
            (Stmt.seq (.assign 12 (t3Ld (.reg 2) (t3Add (.const 3) (t3Mul (.const 2) (.reg 10)))))
              (Stmt.seq (.store (.reg 6) (.const 2))
                (Stmt.seq (t3St (.reg 6) (.const 1) (.reg 11))
                  (Stmt.seq (t3St (.reg 6) (.const 2) (.reg 12))
                    (Stmt.seq (t3St (.reg 6) (.const 3) (.const 1))
                      (Stmt.seq (t3St (.reg 6) (.const 4) (.reg 10))
                        (Stmt.seq (.store (t3Add (.reg 4) (.reg 8)) (.reg 6))
                          (Stmt.seq (.assign 6 (t3Add (.reg 6) (.const 5)))
                            (.store (t3Add (.reg 5) (.reg 10))
                              (t3Add (.load (t3Add (.reg 5) (.reg 10))) (.const 1)))))))))))))
        (.assign 7 (.const 1))))

private lemma t3InitEmb_step_inJ0 {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (mem_s : ℕ → ℕ) (eJ : ℕ) (heJ : eJ < inp.J.m) (eW : ℕ)
    {st : State} {Φ : ℕ} {ω : ℕ → Bool}
    (hI : t3InitEmbLoopInv ctx lay mem_s eJ st Φ)
    (hsrc : ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) :
    ∃ o st' c Φ', Runs w p ω t3InitEmbLoopBody st o st' c ∧
      pNormalPost (fun st₁ Φ₁ =>
        t3InitEmbLoopInv ctx lay mem_s (eJ + 1)
          { st₁ with regs := Function.update st₁.regs 8 (eJ + 1) } Φ₁ ∧
        st₁.regs 8 = eJ) o st' Φ' ∧ c + Φ' ≤ 100 + Φ := by
  rcases hI with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr8, hΦ0, hSt, hbm, hds, hwd, hh_lo, hh_hi, hzf,
    hr7, hemb_lt, hemb_ge, hecnt⟩
  subst hΦ0
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb
  rw [← hlay] at hlb
  simp only [t3HdrSize] at hlb
  have hof := ctx.read_out_fields hSt.1
  have hw := ctx.hwokW.1
  have hwb := ctx.hwokW.2.2
  have hjSrc_lt_v1 : ctx.memT1 (ctx.wInp.h + 16) + 3 * inp.J.m = ctx.v1 :=
    hof.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm
  have hv1_le_v2 : ctx.v1 ≤ inp.v2 := ctx.hv1_le
  have hh_lt_w : st.regs 6 + 5 < 2 ^ w := by
    have : lay.staticEnd + 5 * inp.J.m ≤ Task3Input.maxHeapEnd impl inp := by
      simp only [Task3Input.maxHeapEnd]; omega
    have : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp := le_max_left _ _
    omega
  have hjSrc_len : ctx.wd.jSources.length = inp.J.m := by
    have hs := mkW_jSources_spec ctx.hStat ctx.hw_okW ctx.hws (by rw [ctx.hWInpJ]; exact heJ)
    exact hs.1.trans (congrArg Graph.m ctx.hWInpJ)
  have hj_eq := List.getD_eq_getElem ctx.wd.jSources JEdgeSource.isLoop (by rw [hjSrc_len]; exact heJ)
  have hjAt := hof.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 eJ (by rw [hjSrc_len]; exact heJ)
  rw [← hj_eq, hsrc] at hjAt
  set tagExpr := t3Add (.reg 3) (t3Mul (.const 3) (.reg 8))
  have hev_tagAddr : tagExpr.eval w st = some (ctx.memT1 (ctx.wInp.h + 16) + 3 * eJ) := by
    refine Expr.eval_add (Expr.eval_reg_of_eq hr3)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr8) (by omega)) (by omega)
  have hms := (mkW_jSources_spec ctx.hStat ctx.hw_okW ctx.hws (by rw [ctx.hWInpJ]; exact heJ)).2
  rw [show (ctx.wInp.mkWitnessData impl.constructExpander impl.pathDS.params ctx.WSubs).jSources.getD
    eJ JEdgeSource.isLoop = .inJ0 eW from hsrc] at hms
  have heW_Wm : eW < ctx.wd.W.m := hms.2.2.1
  have hWed := hof.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hu_eq := graphAt_edge_fst hWed heW_Wm
  have hv_eq := graphAt_edge_snd hWed heW_Wm
  have hu_n : (ctx.wd.W.edges[eW]'heW_Wm).1 < ctx.wd.W.n := (ctx.hw_okW.W_valid _ (List.getElem_mem heW_Wm)).1
  have hv_n : (ctx.wd.W.edges[eW]'heW_Wm).2 < ctx.wd.W.n := (ctx.hw_okW.W_valid _ (List.getElem_mem heW_Wm)).2
  have hW_n_lt_w : ctx.wd.W.n < 2 ^ w := by
    have : ctx.wd.W.n = inp.J.n := ctx.hw_okW.W_n.trans (congrArg Graph.n ctx.hWInpJ)
    have := ctx.hStat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := congrArg Graph.n ctx.hWInpJ
    omega
  have hcnt_le : st.mem (lay.econgCountAddr + eW) ≤ eJ := by
    rw [hecnt eW heW_Wm]
    calc ({e ∈ Finset.range eJ | ctx.wd.jSources.getD e JEdgeSource.isLoop = JEdgeSource.inJ0 eW}).card
        ≤ (Finset.range eJ).card := Finset.card_filter_le _ _
      _ = eJ := Finset.card_range _
  have hcnt_lt_w : st.mem (lay.econgCountAddr + eW) + 1 < 2 ^ w := by omega
  have hev_tag : (Expr.load tagExpr).eval w st = some 1 :=
    Expr.eval_load_of_eq hev_tagAddr hjAt.1
  set st1 : State := { st with regs := Function.update st.regs 9 1 }
  have heq1 : Runs w p ω (.assign 9 (.load tagExpr)) st .normal st1 7 :=
    runs_assign_iff.mpr ⟨1, hev_tag, rfl, rfl, rfl⟩
  have hev_eWAddr : (t3Add (.reg 3) (t3Add (t3Mul (.const 3) (.reg 8)) (.const 1))).eval w st1 =
      some (ctx.memT1 (ctx.wInp.h + 16) + (3 * eJ + 1)) :=
    Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, hr3]))
      (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by simp [st1, hr8])) (by omega)) (Expr.eval_const hw) (by omega)) (by omega)
  have hev_eW : (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 8)) (.const 1))).eval w st1 = some eW :=
    Expr.eval_load_of_eq hev_eWAddr (by
      simp [st1, show ctx.memT1 (ctx.wInp.h + 16) + (3 * eJ + 1) = ctx.memT1 (ctx.wInp.h + 16) + 3 * eJ + 1 by omega, hjAt.2.1])
  set st10 : State := { st1 with regs := Function.update st1.regs 10 eW }
  have hev_u : (t3Ld (.reg 2) (t3Add (.const 2) (t3Mul (.const 2) (.reg 10)))).eval w st10 =
      some (ctx.wd.W.edges[eW]'heW_Wm).1 :=
    Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st10, st1, hr2] : st10.regs 2 = ctx.memT1 (ctx.wInp.h + 13)))
        (Expr.eval_add (Expr.eval_const (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by simp [st10] : st10.regs 10 = eW)) (by omega))
          (by omega)) (by omega))
      (by simp [st10, st1, ← hu_eq, Nat.add_assoc])
  set st11 : State := { st10 with regs := Function.update st10.regs 11 (ctx.wd.W.edges[eW]'heW_Wm).1 }
  have hev_v : (t3Ld (.reg 2) (t3Add (.const 3) (t3Mul (.const 2) (.reg 10)))).eval w st11 =
      some (ctx.wd.W.edges[eW]'heW_Wm).2 :=
    Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st11, st10, st1, hr2] : st11.regs 2 = ctx.memT1 (ctx.wInp.h + 13)))
        (Expr.eval_add (Expr.eval_const (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by simp [st11, st10] : st11.regs 10 = eW)) (by omega)) (by omega)) (by omega))
      (by simp [st11, st10, st1, ← hv_eq, Nat.add_assoc])
  set st12 : State := { st11 with regs := Function.update st11.regs 12 (ctx.wd.W.edges[eW]'heW_Wm).2 }
  set h := st.regs 6
  set u := (ctx.wd.W.edges[eW]'heW_Wm).1
  set v := (ctx.wd.W.edges[eW]'heW_Wm).2
  set m1 := Function.update st.mem h 2
  set m2 := Function.update m1 (h + 1) u
  set m3 := Function.update m2 (h + 2) v
  set m4 := Function.update m3 (h + 3) 1
  set m5 := Function.update m4 (h + 4) eW
  set m6 := Function.update m5 (lay.embJWAddr + eJ) h
  set m7 := Function.update m6 (lay.econgCountAddr + eW) (st.mem (lay.econgCountAddr + eW) + 1)
  set stF : State := { mem := m7, regs := Function.update st12.regs 6 (h + 5), pos := st.pos }
  have hm6_ec : m6 (lay.econgCountAddr + eW) = st.mem (lay.econgCountAddr + eW) := by
    simp only [m6, m5, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hrun_br : Runs w p ω
      (Stmt.seq (.assign 10 (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 8)) (.const 1))))
        (Stmt.seq (.assign 11 (t3Ld (.reg 2) (t3Add (.const 2) (t3Mul (.const 2) (.reg 10)))))
          (Stmt.seq (.assign 12 (t3Ld (.reg 2) (t3Add (.const 3) (t3Mul (.const 2) (.reg 10)))))
            (Stmt.seq (.store (.reg 6) (.const 2))
              (Stmt.seq (t3St (.reg 6) (.const 1) (.reg 11))
                (Stmt.seq (t3St (.reg 6) (.const 2) (.reg 12))
                  (Stmt.seq (t3St (.reg 6) (.const 3) (.const 1))
                    (Stmt.seq (t3St (.reg 6) (.const 4) (.reg 10))
                      (Stmt.seq (.store (t3Add (.reg 4) (.reg 8)) (.reg 6))
                        (Stmt.seq (.assign 6 (t3Add (.reg 6) (.const 5)))
                          (.store (t3Add (.reg 5) (.reg 10))
                            (t3Add (.load (t3Add (.reg 5) (.reg 10))) (.const 1)))))))))))))
      st1 .normal stF 79 := by
    refine runs_seq_iff.mpr (Or.inr ⟨st10, 9, 69, runs_assign_iff.mpr ⟨eW, hev_eW, rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨st11, 9, 59, runs_assign_iff.mpr ⟨u, hev_u, rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨st12, 9, 49, runs_assign_iff.mpr ⟨v, hev_v, rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨{ st12 with mem := m1 }, 3, 45,
      runs_store_iff.mpr ⟨h, 2, Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1]; rfl),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨{ st12 with mem := m2 }, 5, 39,
      runs_store_iff.mpr ⟨h + 1, u, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1]; rfl))
          (Expr.eval_const hw) (by omega),
        Expr.eval_reg_of_eq (by simp [st12, st11]; rfl), rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨{ st12 with mem := m3 }, 5, 33,
      runs_store_iff.mpr ⟨h + 2, v, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1]; rfl))
          (Expr.eval_const (by omega)) (by omega),
        Expr.eval_reg_of_eq (by simp [st12]; rfl), rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨{ st12 with mem := m4 }, 5, 27,
      runs_store_iff.mpr ⟨h + 3, 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1]; rfl))
          (Expr.eval_const (by omega)) (by omega),
        Expr.eval_const hw, rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨{ st12 with mem := m5 }, 5, 21,
      runs_store_iff.mpr ⟨h + 4, eW, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1]; rfl))
          (Expr.eval_const (by omega)) (by omega),
        Expr.eval_reg_of_eq (by simp [st12, st11, st10]), rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨{ st12 with mem := m6 }, 5, 15,
      runs_store_iff.mpr ⟨lay.embJWAddr + eJ, h, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1, hr4]))
        (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1, hr8])) (by omega),
        Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1]; rfl), rfl, rfl, rfl⟩, ?_, rfl⟩)
    set st13 : State := { mem := m6, regs := Function.update st12.regs 6 (h + 5), pos := st.pos }
    refine runs_seq_iff.mpr (Or.inr ⟨st13, 4, 10,
      runs_assign_iff.mpr ⟨h + 5, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st1]; rfl))
          (Expr.eval_const (by omega)) (by omega),
        rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_store_iff.mpr ⟨lay.econgCountAddr + eW, st.mem (lay.econgCountAddr + eW) + 1,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st13, st12, st11, st10, st1, hr5] : st13.regs 5 = lay.econgCountAddr))
        (Expr.eval_reg_of_eq (by simp [st13, st12, st11, st10] : st13.regs 10 = eW)) (by omega),
      Expr.eval_add
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st13, st12, st11, st10, st1, hr5] : st13.regs 5 = lay.econgCountAddr))
            (Expr.eval_reg_of_eq (by simp [st13, st12, st11, st10] : st13.regs 10 = eW)) (by omega))
          (hm6_ec : st13.mem (lay.econgCountAddr + eW) = st.mem (lay.econgCountAddr + eW)))
        (Expr.eval_const hw) hcnt_lt_w, rfl, rfl, rfl⟩
  have hev_c0 : (t3Eq (.reg 9) (.const 0)).eval w st1 = some 0 :=
    Expr.eval_eq_false (Expr.eval_reg_of_eq (by simp [st1] : st1.regs 9 = 1))
      (Expr.eval_const (by omega)) (by decide) hw
  have hev_c1 : (t3Eq (.reg 9) (.const 1)).eval w st1 = some 1 :=
    Expr.eval_eq_true (Expr.eval_reg_of_eq (by simp [st1] : st1.regs 9 = 1))
      (Expr.eval_const (by omega)) rfl hw
  have hrun_tot : Runs w p ω t3InitEmbLoopBody st .normal stF 95 := by
    refine runs_seq_iff.mpr (Or.inr ⟨st1, 7, 87, heq1, ?_, rfl⟩)
    refine runs_cond_iff.mpr ⟨0, 83, hev_c0, ?_, rfl⟩
    exact runs_cond_iff.mpr ⟨1, 79, hev_c1, by simp [hrun_br], rfl⟩
  have hno_touch : ∀ a, a < lay.embJWAddr ∨ (lay.dsHandlesAddr ≤ a ∧ a < lay.econgCountAddr) ∨
      (lay.wDelStampAddr ≤ a ∧ a < h) → m7 a = st.mem a := by
    intro a ha
    simp only [m7, m6, m5, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨.normal, stF, 95, 0, hrun_tot, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, by omega⟩
  · simp [stF, st12, st11, st10, st1, hr0]
  · simp [stF, st12, st11, st10, st1, hr1]
  · simp [stF, st12, st11, st10, st1, hr2]
  · simp [stF, st12, st11, st10, st1, hr3]
  · simp [stF, st12, st11, st10, st1, hr4]
  · simp [stF, st12, st11, st10, st1, hr5]
  · simp
  · exact hSt.mono (fun x hx => hno_touch x (Or.inl (by omega)))
      (fun i hi _ _ _ _ _ _ _ => by simp only [t3HdrSize] at hi; exact hno_touch _ (Or.inl (by omega)))
      (fun ci hci => hno_touch _ (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  · intro x hx; exact (hno_touch x (Or.inl hx)).trans (hbm x hx)
  · intro x hx1 hx2; exact (hno_touch x (Or.inr (Or.inl ⟨hx1, hx2⟩))).trans (hds x hx1 hx2)
  · intro x hx1 hx2; exact (hno_touch x (Or.inr (Or.inr ⟨hx1, by omega⟩))).trans (hwd x hx1 hx2)
  · simp [stF]; omega
  · simp [stF]; omega
  · have hstF_6 : Function.update stF.regs 8 (eJ + 1) 6 = h + 5 := by simp [stF]
    intro a ha
    rw [show ({ stF with regs := Function.update stF.regs 8 (eJ + 1) } : State).regs 6 = h + 5 from hstF_6] at ha
    simp only [stF, m7, m6, m5, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hzf a (by omega)
  · simp only [stF, st12, st11, st10, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr7]
    congr 1; ext
    refine ⟨fun ⟨e, he, h⟩ => ⟨e, by omega, h⟩, fun ⟨e, he, h⟩ => ⟨e, ?_, h⟩⟩
    by_cases hee : e = eJ
    · obtain ⟨_, _, h⟩ := h
      rw [hee, hsrc] at h; cases h
    · omega
  · intro e he
    by_cases hee : e = eJ
    · rw [hee]
      simp only [hsrc, stF]
      have hm7 : m7 (lay.embJWAddr + eJ) = h := by
        simp only [m7, m6]
        rw [Function.update_of_ne (by omega), Function.update_self]
      rw [hm7]
      refine ⟨hh_lo, le_refl _, ?_⟩
      rw [List.getD_eq_getElem _ _ heW_Wm]
      change WalkAt m7 h (Walk.single u v eW)
      simp only [WalkAt, Walk.single, Walk.encode, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append]
      rw [listAt_cons, listAt_cons, listAt_cons, listAt_cons, listAt_cons]
      have heq0 : m7 h = 2 := by
        simp only [m7, m6, m5, m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      have heq1 : m7 (h + 1) = u := by
        simp only [m7, m6, m5, m4, m3, m2]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
      have heq2 : m7 (h + 2) = v := by
        simp only [m7, m6, m5, m4, m3]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      have heq3 : m7 (h + 3) = 1 := by
        simp only [m7, m6, m5, m4]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
      have heq4 : m7 (h + 4) = eW := by
        simp only [m7, m6, m5]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      exact ⟨heq0, heq1, heq2, heq3, heq4, listAt_nil _ _⟩
    · have he_lt : e < eJ := by omega
      have hp := hemb_lt e he_lt
      have hm7_e : stF.mem (lay.embJWAddr + e) = st.mem (lay.embJWAddr + e) := by
        simp only [stF, m7, m6, m5, m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hstF_6 : Function.update stF.regs 8 (eJ + 1) 6 = h + 5 := by simp [stF]
      cases hse : ctx.wd.jSources.getD e JEdgeSource.isLoop with
      | isLoop =>
        rw [hse] at hp; simp only [stF] at hm7_e ⊢; rw [hm7_e]
        refine ⟨hp.1, by change st.mem (lay.embJWAddr + e) + 2 ≤ Function.update stF.regs 8 (eJ + 1) 6; rw [hstF_6]; omega, ?_⟩
        exact ListAt.congr hp.2.2 (fun k hk1 hk2 => by
          simp only [Walk.empty, Walk.encode, List.length_cons,
            List.length_append, List.length_nil] at hk2
          simp only [m7, m6, m5, m4, m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
      | inJ0 eW' =>
        rw [hse] at hp; simp only [stF] at hm7_e ⊢; rw [hm7_e]
        refine ⟨hp.1, by change st.mem (lay.embJWAddr + e) + 5 ≤ Function.update stF.regs 8 (eJ + 1) 6; rw [hstF_6]; omega, ?_⟩
        exact ListAt.congr hp.2.2 (fun k hk1 hk2 => by
          simp only [Walk.single, Walk.encode, List.length_cons,
            List.length_append, List.length_nil] at hk2
          simp only [m7, m6, m5, m4, m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
      | inComp ci jL =>
        rw [hse] at hp; exact hm7_e.trans hp
  · intro e he1 he2
    simp only [stF, m7, m6, m5, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hemb_ge e (by omega) he2
  · intro eW' heW'
    by_cases hew : eW' = eW
    · rw [hew] at heW' ⊢
      simp only [stF, m7, Function.update_self]
      rw [hecnt eW heW']
      have hsep : {e ∈ Finset.range (eJ + 1) | ctx.wd.jSources.getD e JEdgeSource.isLoop = JEdgeSource.inJ0 eW} =
          insert eJ {e ∈ Finset.range eJ | ctx.wd.jSources.getD e JEdgeSource.isLoop = JEdgeSource.inJ0 eW} := by
        ext e; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨he, h⟩
          by_cases hee : e = eJ
          · exact Or.inl hee
          · exact Or.inr ⟨by omega, h⟩
        · rintro (rfl | ⟨he, h⟩)
          · exact ⟨by omega, hsrc⟩
          · exact ⟨by omega, h⟩
      rw [hsep, Finset.card_insert_of_notMem (by simp)]
    · have hm7 : stF.mem (lay.econgCountAddr + eW') = st.mem (lay.econgCountAddr + eW') := by
        simp only [stF, m7, m6, m5, m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rw [hm7, hecnt eW' heW']
      congr 1; ext e
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨fun ⟨he, h⟩ => ⟨by omega, h⟩, fun ⟨he, h⟩ => ?_⟩
      by_cases hee : e = eJ
      · rw [hee, hsrc] at h
        exact (hew (by injection h; omega)).elim
      · exact ⟨by omega, h⟩
  · simp only [stF, st12, st11, st10, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact hr8

private lemma t3InitEmb_step_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (mem_s : ℕ → ℕ) (eJ : ℕ) (heJ : eJ < inp.J.m) :
    PTriple w p (t3InitEmbLoopInv ctx lay mem_s eJ) t3InitEmbLoopBody
      (pNormalPost fun st₁ Φ₁ =>
        t3InitEmbLoopInv ctx lay mem_s (eJ + 1)
          { st₁ with regs := Function.update st₁.regs 8 (eJ + 1) } Φ₁ ∧
        st₁.regs 8 = eJ)
      (fun _ => 100) := by
  intro st Φ ω hI
  by_cases hJ0_c : ∃ eW, ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW
  · rcases hJ0_c with ⟨eW, hsrc⟩
    exact t3InitEmb_step_inJ0 ctx lay hlay mem_s eJ heJ eW hI hsrc
  rcases hI with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr8, hΦ0, hSt, hbm, hds, hwd, hh_lo, hh_hi, hzf,
    hr7, hemb_lt, hemb_ge, hecnt⟩
  subst hΦ0
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb
  rw [← hlay] at hlb
  simp only [t3HdrSize] at hlb
  have hof := ctx.read_out_fields hSt.1
  have hw := ctx.hwokW.1
  have hwb := ctx.hwokW.2.2
  have hjSrc_lt_v1 : ctx.memT1 (ctx.wInp.h + 16) + 3 * inp.J.m = ctx.v1 :=
    hof.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm
  have hv1_le_v2 : ctx.v1 ≤ inp.v2 := ctx.hv1_le
  have hh_lt_w : st.regs 6 + 5 < 2 ^ w := by
    have : lay.staticEnd + 5 * inp.J.m ≤ Task3Input.maxHeapEnd impl inp := by
      simp only [Task3Input.maxHeapEnd]; omega
    have : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp := le_max_left _ _
    omega
  have hjSrc_len : ctx.wd.jSources.length = inp.J.m := by
    have hs := mkW_jSources_spec ctx.hStat ctx.hw_okW ctx.hws (by rw [ctx.hWInpJ]; exact heJ)
    exact hs.1.trans (congrArg Graph.m ctx.hWInpJ)
  have hj_eq := List.getD_eq_getElem ctx.wd.jSources JEdgeSource.isLoop (by rw [hjSrc_len]; exact heJ)
  have hjAt := hof.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 eJ (by rw [hjSrc_len]; exact heJ)
  rw [← hj_eq] at hjAt
  set tagExpr := t3Add (.reg 3) (t3Mul (.const 3) (.reg 8))
  have hev_tagAddr : tagExpr.eval w st = some (ctx.memT1 (ctx.wInp.h + 16) + 3 * eJ) := by
    refine Expr.eval_add (Expr.eval_reg_of_eq hr3)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr8) (by omega)) (by omega)
  cases hsrc : ctx.wd.jSources.getD eJ JEdgeSource.isLoop with
  | inJ0 eW => exact absurd ⟨eW, hsrc⟩ hJ0_c
  | isLoop =>
    rw [hsrc] at hjAt
    have hev_tag : (Expr.load tagExpr).eval w st = some 0 :=
      Expr.eval_load_of_eq hev_tagAddr hjAt.1
    set st1 : State := { st with regs := Function.update st.regs 9 0 }
    have heq1 : Runs w p ω (.assign 9 (.load tagExpr)) st .normal st1 7 :=
      runs_assign_iff.mpr ⟨0, hev_tag, rfl, rfl, rfl⟩
    set mem1 := Function.update st.mem (st.regs 6) 0
    set mem2 := Function.update mem1 (st.regs 6 + 1) 0
    set mem3 := Function.update mem2 (lay.embJWAddr + eJ) (st.regs 6)
    set st2 : State := { mem := mem3, regs := Function.update st1.regs 6 (st.regs 6 + 2), pos := st.pos }
    have hrun_br : Runs w p ω
        (Stmt.seq (.store (.reg 6) (.const 0))
          (Stmt.seq (t3St (.reg 6) (.const 1) (.const 0))
            (Stmt.seq (.store (t3Add (.reg 4) (.reg 8)) (.reg 6))
              (.assign 6 (t3Add (.reg 6) (.const 2))))))
        st1 .normal st2 20 := by
      refine runs_seq_iff.mpr (Or.inr ⟨{ st1 with mem := mem1 }, 3, 16, ?_, ?_, rfl⟩)
      · exact runs_store_iff.mpr ⟨st.regs 6, 0, Expr.eval_reg_of_eq (by simp [st1]),
          Expr.eval_const (by omega), rfl, rfl, rfl⟩
      · refine runs_seq_iff.mpr (Or.inr ⟨{ st1 with mem := mem2 }, 5, 10, ?_, ?_, rfl⟩)
        · exact runs_store_iff.mpr ⟨st.regs 6 + 1, 0,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1])) (Expr.eval_const hw) (by omega),
            Expr.eval_const (by omega), rfl, rfl, rfl⟩
        · refine runs_seq_iff.mpr (Or.inr ⟨{ st1 with mem := mem3 }, 5, 4, ?_, ?_, rfl⟩)
          · exact runs_store_iff.mpr ⟨lay.embJWAddr + eJ, st.regs 6,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, hr4]))
                (Expr.eval_reg_of_eq (by simp [st1, hr8])) (by omega),
              Expr.eval_reg_of_eq (by simp [st1]), rfl, rfl, rfl⟩
          · exact runs_assign_iff.mpr ⟨st.regs 6 + 2,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1])) (Expr.eval_const (by omega)) (by omega),
              rfl, rfl, rfl⟩
    have hev_c0 : (t3Eq (.reg 9) (.const 0)).eval w st1 = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (by simp [st1] : st1.regs 9 = 0))
        (Expr.eval_const (by omega)) rfl hw
    have hrun_tot : Runs w p ω t3InitEmbLoopBody st .normal st2 32 := by
      refine runs_seq_iff.mpr (Or.inr ⟨st1, 7, 24, heq1, ?_, rfl⟩)
      exact runs_cond_iff.mpr ⟨1, 20, hev_c0, by simp [hrun_br], rfl⟩
    refine ⟨.normal, st2, 32, 0, hrun_tot, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, by dsimp only; omega⟩
    · simp [st2, st1, hr0]
    · simp [st2, st1, hr1]
    · simp [st2, st1, hr2]
    · simp [st2, st1, hr3]
    · simp [st2, st1, hr4]
    · simp [st2, st1, hr5]
    · simp
    · exact hSt.mono (fun x hx => by
        simp only [st2, mem3, mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
        (fun i hi _ _ _ _ _ _ _ => by
          simp only [t3HdrSize] at hi
          simp only [st2, mem3, mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
        (fun ci hci => by
          simp only [st2, mem3, mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
    · intro x hx
      simp only [st2, mem3, mem2, mem1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hbm x hx
    · intro x hx1 hx2
      simp only [st2, mem3, mem2, mem1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hds x hx1 hx2
    · intro x hx1 hx2
      simp only [st2, mem3, mem2, mem1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hwd x hx1 hx2
    · simp [st2]; omega
    · simp [st2]; omega
    · have hst2_6 : Function.update st2.regs 8 (eJ + 1) 6 = st.regs 6 + 2 := by simp [st2]
      intro a ha
      rw [show ({ st2 with regs := Function.update st2.regs 8 (eJ + 1) } : State).regs 6 =
        st.regs 6 + 2 from hst2_6] at ha
      simp only [st2, mem3, mem2, mem1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hzf a (by omega)
    · simp only [st2, st1]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hr7]
      congr 1; ext
      refine ⟨fun ⟨e, he, h⟩ => ⟨e, by omega, h⟩, fun ⟨e, he, h⟩ => ⟨e, ?_, h⟩⟩
      by_cases hee : e = eJ
      · obtain ⟨_, _, h⟩ := h
        rw [hee, hsrc] at h; cases h
      · omega
    · intro e he
      by_cases hee : e = eJ
      · rw [hee]
        simp only [st2, hsrc]
        have hm3 : mem3 (lay.embJWAddr + eJ) = st.regs 6 := Function.update_self _ _ _
        rw [hm3]
        refine ⟨hh_lo, le_refl _, ?_⟩
        change ListAt mem3 (st.regs 6) [0, 0]
        rw [listAt_cons, listAt_cons]
        have hm1' : mem3 (st.regs 6) = 0 := by
          simp only [mem3, mem2, mem1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        have hm2' : mem3 (st.regs 6 + 1) = 0 := by
          simp only [mem3, mem2, mem1]
          rw [Function.update_of_ne (by omega), Function.update_self]
        exact ⟨hm1', hm2', listAt_nil _ _⟩
      · have he_lt : e < eJ := by omega
        have hp := hemb_lt e he_lt
        have hm3_e : st2.mem (lay.embJWAddr + e) = st.mem (lay.embJWAddr + e) := by
          simp only [st2, mem3, mem2, mem1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        have hst2_6 : Function.update st2.regs 8 (eJ + 1) 6 = st.regs 6 + 2 := by simp [st2]
        cases hse : ctx.wd.jSources.getD e JEdgeSource.isLoop with
        | isLoop =>
          rw [hse] at hp; simp only [st2] at hm3_e ⊢; rw [hm3_e]
          refine ⟨hp.1, by change st.mem (lay.embJWAddr + e) + 2 ≤ Function.update st2.regs 8 (eJ + 1) 6; rw [hst2_6]; omega, ?_⟩
          exact ListAt.congr hp.2.2 (fun k hk1 hk2 => by
            simp only [Walk.empty, Walk.encode, List.length_cons,
              List.length_append, List.length_nil] at hk2
            simp only [mem3, mem2, mem1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
        | inJ0 eW =>
          rw [hse] at hp; simp only [st2] at hm3_e ⊢; rw [hm3_e]
          refine ⟨hp.1, by change st.mem (lay.embJWAddr + e) + 5 ≤ Function.update st2.regs 8 (eJ + 1) 6; rw [hst2_6]; omega, ?_⟩
          exact ListAt.congr hp.2.2 (fun k hk1 hk2 => by
            simp only [Walk.single, Walk.encode, List.length_cons,
              List.length_append, List.length_nil] at hk2
            simp only [mem3, mem2, mem1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
        | inComp ci jL =>
          rw [hse] at hp; exact hm3_e.trans hp
    · intro e he1 he2
      simp only [st2, mem3, mem2, mem1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hemb_ge e (by omega) he2
    · intro eW heW
      have hm3 : st2.mem (lay.econgCountAddr + eW) = st.mem (lay.econgCountAddr + eW) := by
        simp only [st2, mem3, mem2, mem1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rw [hm3, hecnt eW heW]
      congr 1; ext e
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨fun ⟨he, h⟩ => ⟨by omega, h⟩, fun ⟨he, h⟩ => ?_⟩
      by_cases hee : e = eJ
      · rw [hee] at h; rw [hsrc] at h; cases h
      · exact ⟨by omega, h⟩
    · simp only [st2, st1]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      exact hr8
  | inComp ci jL =>
    rw [hsrc] at hjAt
    have hev_tag : (Expr.load tagExpr).eval w st = some 2 :=
      Expr.eval_load_of_eq hev_tagAddr hjAt.1
    set st1 : State := { st with regs := Function.update st.regs 9 2 }
    have heq1 : Runs w p ω (.assign 9 (.load tagExpr)) st .normal st1 7 :=
      runs_assign_iff.mpr ⟨2, hev_tag, rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 7 1 }
    have hrun_br : Runs w p ω (.assign 7 (.const 1)) st1 .normal st2 2 :=
      runs_assign_iff.mpr ⟨1, Expr.eval_const hw, rfl, rfl, rfl⟩
    have hev_c0 : (t3Eq (.reg 9) (.const 0)).eval w st1 = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq (by simp [st1] : st1.regs 9 = 2))
        (Expr.eval_const (by omega)) (by decide) hw
    have hev_c1 : (t3Eq (.reg 9) (.const 1)).eval w st1 = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq (by simp [st1] : st1.regs 9 = 2))
        (Expr.eval_const (by omega)) (by decide) hw
    have hrun_tot : Runs w p ω t3InitEmbLoopBody st .normal st2 18 := by
      refine runs_seq_iff.mpr (Or.inr ⟨st1, 7, 10, heq1, ?_, rfl⟩)
      refine runs_cond_iff.mpr ⟨0, 6, hev_c0, ?_, rfl⟩
      exact runs_cond_iff.mpr ⟨0, 2, hev_c1, by simp [hrun_br], rfl⟩
    refine ⟨.normal, st2, 18, 0, hrun_tot, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, by dsimp only; omega⟩
    · simp [st2, st1, hr0]
    · simp [st2, st1, hr1]
    · simp [st2, st1, hr2]
    · simp [st2, st1, hr3]
    · simp [st2, st1, hr4]
    · simp [st2, st1, hr5]
    · simp
    · exact hSt
    · exact hbm
    · exact hds
    · exact hwd
    · simp [st2, st1]; omega
    · simp [st2, st1]; omega
    · exact hzf
    · dsimp only
      rw [Function.update_of_ne (by decide)]
      simp only [st2, Function.update_self]
      split_ifs with h
      · rfl
      · exact absurd ⟨eJ, by omega, ci, jL, hsrc⟩ h
    · intro e he
      by_cases hee : e = eJ
      · rw [hee]; simp only [st2, hsrc]; exact hemb_ge eJ (le_refl _) heJ
      · exact hemb_lt e (by omega)
    · intro e he1 he2; exact hemb_ge e (by omega) he2
    · intro eW heW
      rw [hecnt eW heW]
      congr 1; ext e
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨fun ⟨he, h⟩ => ⟨by omega, h⟩, fun ⟨he, h⟩ => ?_⟩
      by_cases hee : e = eJ
      · rw [hee] at h; rw [hsrc] at h; cases h
      · exact ⟨by omega, h⟩
    · simp only [st2, st1]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      exact hr8

open Classical in
/-- Postcondition of `t3InitEmbBody` returning initial heap pointer and populating `embJW` and `econgCount`. -/
def T3InitEmbPost {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (mem_s mem' : ℕ → ℕ) (ret : ℕ) : Prop :=
  ret = mem' (lay.base + t3OffHCur) ∧
  T3StaticMem ctx lay mem' ∧
  (∀ x < lay.embJWAddr, x ≠ lay.base + t3OffHCur → x ≠ lay.base + t3OffCont → mem' x = mem_s x) ∧
  (∀ x, lay.dsHandlesAddr ≤ x → x < lay.econgCountAddr → mem' x = mem_s x) ∧
  (∀ x, lay.wDelStampAddr ≤ x → x < lay.staticEnd → mem' x = mem_s x) ∧
  mem' (lay.base + t3OffCont) = (if ∃ eJ < inp.J.m, ∃ ci jL,
    ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL then 1 else 0) ∧
  lay.staticEnd ≤ ret ∧
  ret ≤ lay.staticEnd + 5 * inp.J.m ∧
  ZeroFrom mem' ret ∧
  (∀ eJ < inp.J.m, match initEmb2 inp.J ctx.wd eJ with
    | none => mem' (lay.embJWAddr + eJ) = 0
    | some P => lay.staticEnd ≤ mem' (lay.embJWAddr + eJ) ∧
        mem' (lay.embJWAddr + eJ) + P.encode.length ≤ ret ∧
        WalkAt mem' (mem' (lay.embJWAddr + eJ)) P) ∧
  (∀ eW < ctx.wd.W.m, mem' (lay.econgCountAddr + eW) =
    {eJ ∈ Finset.range inp.J.m | eW ∈ (partialToWalk (initEmb2 inp.J ctx.wd) eJ).edges}.card)

lemma t3InitEmb_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (mem_s : ℕ → ℕ)
    (hSt : T3StaticMem ctx lay mem_s) (hHC : mem_s (lay.base + t3OffHCur) = lay.staticEnd)
    (hzf : ZeroFrom mem_s lay.staticEnd)
    (hembZ : ∀ x, lay.embJWAddr ≤ x → x < lay.dsHandlesAddr → mem_s x = 0)
    (hecntZ : ∀ x, lay.econgCountAddr ≤ x → x < lay.wDelStampAddr → mem_s x = 0) :
    PTriple w p
      (fun st Φ => st = startState [lay.base] mem_s st.pos ∧ Φ = 0)
      t3InitEmbBody
      (fun o st' Φ' => ∃ ret, o = .returned ret ∧ Φ' = 0 ∧ T3InitEmbPost ctx lay mem_s st'.mem ret)
      (fun _ => 110 * inp.J.m + 80) := by
  intro st Φ ω ⟨hst, hΦ⟩
  rw [hst, hΦ]
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb
  rw [← hlay] at hlb
  simp only [t3HdrSize] at hlb
  have hw := ctx.hwokW.1
  have hwb := ctx.hwokW.2.2
  have hJm_w : inp.J.m < 2 ^ w := by omega
  set st0 := startState [lay.base] mem_s st.pos
  have hLoop := PTriple.forRange_const (w := w) (p := p)
    (P := fun s Φ' => s.mem = mem_s ∧ s.regs 0 = lay.base ∧ s.regs 1 = inp.J.m ∧
      s.regs 2 = ctx.memT1 (ctx.wInp.h + 13) ∧ s.regs 3 = ctx.memT1 (ctx.wInp.h + 16) ∧
      s.regs 4 = lay.embJWAddr ∧ s.regs 5 = lay.econgCountAddr ∧ s.regs 6 = lay.staticEnd ∧
      s.regs 7 = 0 ∧ Φ' = 0)
    (r := 8) (lo := .const 0) (hi := .reg 1)
    (body := _) (Inv := t3InitEmbLoopInv ctx lay mem_s) 100 0 inp.J.m
    (Nat.zero_le _) hw (fun _ => hJm_w)
    (fun s Φ' ⟨hm, h0, h1, h2, h3, h4, h5, h6, h7, hPhi⟩ => by
      refine ⟨Expr.eval_const (by omega), ?_⟩
      rw [hm]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp, hPhi, hSt, fun _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, by simp [h6], by simp [h6], by simp [h6, hzf], ?_,
        fun _ h => (Nat.not_lt_zero _ h).elim, fun e _ he => hembZ (lay.embJWAddr + e) (by omega) (by omega),
        fun eW heW => by dsimp only; rw [hecntZ (lay.econgCountAddr + eW) (by omega) (by omega)]; simp⟩
      · simpa [Function.update_of_ne] using h0
      · simpa [Function.update_of_ne] using h1
      · simpa [Function.update_of_ne] using h2
      · simpa [Function.update_of_ne] using h3
      · simpa [Function.update_of_ne] using h4
      · simpa [Function.update_of_ne] using h5
      · simp [h7])
    (fun i s _ _ _ hI => hI.2.2.2.2.2.2.1)
    (fun i s _ _ _ hI => Expr.eval_reg_of_eq hI.2.1)
    (fun i _ hi => t3InitEmb_step_ptriple ctx lay hlay mem_s i hi)
  dsimp only [t3InitEmbBody]
  refine t3_ptriple_of_cps ?_
  dsimp only [st0, startState]
  have hreg0 : (startState [lay.base] mem_s st.pos).regs 0 = lay.base := rfl
  apply t3_ld_cps hreg0
    (by simp [t3OffJm]; try omega) (by simp [t3OffJm]; try omega) hSt.2.2.2.2.1
  apply t3_ld_cps (by simp [startState]) (by simp [t3OffWAddr]; try omega)
    (by simp [t3OffWAddr]; try omega) hSt.2.2.2.2.2.2.2.2.2.2.2.1
  apply t3_ld_cps (by simp [startState]) (by simp [t3OffJSrc]; try omega)
    (by simp [t3OffJSrc]; try omega) hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply t3_ld_cps (by simp [startState]) (by simp [t3OffEmbJW]; try omega)
    (by simp [t3OffEmbJW]; try omega) hSt.2.1
  apply t3_ld_cps (by simp [startState]) (by simp [t3OffECnt]; try omega)
    (by simp [t3OffECnt]; try omega) hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply t3_ld_cps (by simp [startState]) (by simp [t3OffHCur]; try omega)
    (by simp [t3OffHCur]; try omega) hHC
  apply t3_const_cps (by omega)
  apply t3_normal_ptriple_cps hLoop
    ⟨rfl, by simp [startState, Function.update_of_ne], by simp [startState, Function.update_of_ne],
      by simp [startState, Function.update_of_ne], by simp [startState, Function.update_of_ne],
      by simp [startState, Function.update_of_ne], by simp [startState, Function.update_of_ne],
      by simp [startState, Function.update_of_ne], by simp, rfl⟩
    (by simp [Expr.size]; exact le_refl _)
  intro stL ΦL hqL
  rcases hqL with ⟨hr0, _, _, _, _, _, _, hΦL0, hStL, hbm, hds, hwd, hh_lo, hh_hi, hzfL,
    hr7, hemb_lt, _, hecnt⟩
  subst hΦL0
  apply t3_st_cps hr0 (by simp [t3OffHCur]; omega)
    (by simp [t3OffHCur]; omega) rfl
  apply t3_st_cps hr0 (by simp [t3OffCont]; omega)
    (by simp [t3OffCont]; omega) rfl
  set mFinal := Function.update (Function.update stL.mem (lay.base + t3OffHCur) (stL.regs 6))
    (lay.base + t3OffCont) (stL.regs 7)
  have hev_ret : (Expr.reg 6).eval w ⟨mFinal, stL.regs, stL.pos⟩ = some (stL.regs 6) := Expr.eval_reg_of_eq rfl
  have hneHC : lay.base + t3OffHCur ≠ lay.base + t3OffCont := by
    simp [t3OffHCur, t3OffCont]
  have hmF_h : mFinal (lay.base + t3OffHCur) = stL.regs 6 := by
    simp only [mFinal, Function.update_of_ne hneHC, Function.update_self]
  have hmF_c : mFinal (lay.base + t3OffCont) = stL.regs 7 := Function.update_self _ _ _
  have hagree_big : ∀ a, a ≠ lay.base + t3OffHCur → a ≠ lay.base + t3OffCont → mFinal a = stL.mem a :=
    fun a ha1 ha2 => by simp only [mFinal, Function.update_of_ne ha2, Function.update_of_ne ha1]
  have hoff_hc : t3OffHCur < 32 := by decide
  have hoff_ct : t3OffCont < 32 := by decide
  have hStaticF : T3StaticMem ctx lay mFinal := hStL.mono
    (fun x hx => hagree_big x (by omega) (by omega))
    (fun i hi _ _ _ _ hnh _ hnc => hagree_big _ (by intro h; apply hnh; omega) (by intro h; apply hnc; omega))
    (fun ci hci => hagree_big _ (by omega) (by omega))
  apply t3_end_ret_cps (Q := fun o st' Φ' => ∃ ret, o = .returned ret ∧ Φ' = 0 ∧
      T3InitEmbPost ctx lay mem_s st'.mem ret) hev_ret
  · refine ⟨stL.regs 6, rfl, rfl, hmF_h.symm, hStaticF, ?_, ?_, ?_, ?_, hh_lo, hh_hi, ?_, ?_, ?_⟩
    · intro x hx1 hx2 hx3; exact (hagree_big x hx2 hx3).trans (hbm x hx1)
    · intro x hx1 hx2; exact (hagree_big x (by omega) (by omega)).trans (hds x hx1 hx2)
    · intro x hx1 hx2; exact (hagree_big x (by omega) (by omega)).trans (hwd x hx1 hx2)
    · dsimp only; rw [hmF_c]; exact hr7
    · intro a ha; dsimp only; rw [hagree_big a (by omega) (by omega)]; exact hzfL a ha
    · intro eJ heJ
      dsimp only
      have hp := hemb_lt eJ heJ
      have hptr : mFinal (lay.embJWAddr + eJ) = stL.mem (lay.embJWAddr + eJ) :=
        hagree_big _ (by omega) (by omega)
      dsimp only [initEmb2]
      simp only [heJ, ↓reduceIte]
      cases hsrc : ctx.wd.jSources.getD eJ JEdgeSource.isLoop with
      | isLoop =>
        rw [hsrc] at hp
        rw [hptr]
        refine ⟨hp.1, by simpa [Walk.empty, Walk.encode] using hp.2.1, ListAt.congr hp.2.2
          (fun k hk1 hk2 => hagree_big k (by omega) (by omega))⟩
      | inJ0 eW =>
        rw [hsrc] at hp
        rw [hptr]
        refine ⟨hp.1, by simpa [Walk.single, Walk.encode] using hp.2.1, ListAt.congr hp.2.2
          (fun k hk1 hk2 => hagree_big k (by omega) (by omega))⟩
      | inComp ci jL =>
        rw [hsrc] at hp; exact hptr.trans hp
    · intro eW heW
      dsimp only
      rw [hagree_big _ (by omega) (by omega), hecnt eW heW]
      congr 1; ext eJ
      simp only [Finset.mem_filter, Finset.mem_range]
      refine and_congr_right fun heJ => ?_
      dsimp only [partialToWalk, initEmb2]
      simp only [heJ, ↓reduceIte]
      cases ctx.wd.jSources.getD eJ JEdgeSource.isLoop with
      | isLoop => simp [Walk.empty]
      | inJ0 eW' => simp [Walk.single, eq_comm]
      | inComp _ _ => simp [Walk.empty]
  · simp only [Expr.size, t3Add, t3Ld]
    have : inp.J.m * 109 ≤ 110 * inp.J.m := by omega
    omega

end MinCostFlow.Spanner
