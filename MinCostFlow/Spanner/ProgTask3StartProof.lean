module

public import MinCostFlow.Spanner.ProgTask3InitProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Setup and Vhat-Offset Loop Proofs for Word-RAM Task 3

Proves `t3VhatLoop_ptriple` (`vhatLoop` in `task3Body`), `t3Setup_cps` (the setup prefix of
`task3Body` up to the outer `.loop`, establishing `T3OuterInv ctx lay 0 st 0` in at most
`140 * inp.J.m + 380` Word-RAM cycles).
-/

private abbrev t3VhatLoopBody : Stmt :=
  Stmt.seq (.store (t3Add (.reg 12) (.reg 14)) (.reg 13))
    (Stmt.seq (.assign 15 (t3Ld (.reg 8) (t3Add (t3Mul (.const 6) (.reg 14)) (.const 4))))
      (.assign 13 (t3Add (.reg 13) (.reg 15))))

private def t3VhatLoopInv {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (mem_b : ℕ → ℕ)
    (pos upTo : ℕ) (st : State) (Φ : ℕ) : Prop :=
  st.pos = pos ∧
  st.regs 0 = inp.jAddr ∧ st.regs 1 = inp.t1OutAddr ∧ st.regs 2 = inp.v2 ∧
  st.regs 7 = ctx.wd.comps.length ∧ st.regs 8 = ctx.memT1 (ctx.wInp.h + 12) ∧
  st.regs 12 = lay.vhatOffsetAddr ∧ st.regs 13 = vhatBaseW ctx.wd upTo ∧
  st.regs 14 = upTo ∧ Φ = 0 ∧ (∀ x < lay.vhatOffsetAddr, st.mem x = mem_b x) ∧
  ZeroFrom st.mem (lay.vhatOffsetAddr + upTo) ∧
  (∀ ci < upTo, st.mem (lay.vhatOffsetAddr + ci) = vhatBaseW ctx.wd ci)

private lemma t3VhatLoop_step_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout)
    (hlay : lay = T3Layout.ofCtx ctx) (mem_b : ℕ → ℕ) (pos : ℕ)
    (hb_below : ∀ x < inp.v2, mem_b x = mem₀ x) (ci : ℕ) (hci : ci < ctx.wd.comps.length) :
    PTriple w p (t3VhatLoopInv ctx lay mem_b pos ci) t3VhatLoopBody
      (pNormalPost fun st₁ Φ₁ =>
        t3VhatLoopInv ctx lay mem_b pos (ci + 1)
          { st₁ with regs := Function.update st₁.regs 14 (ci + 1) } Φ₁ ∧ st₁.regs 14 = ci)
      (fun _ => 20) := by
  intro st Φ ω hI
  rcases hI with ⟨hpos, hr0, hr1, hr2, hr7, hr8, hr12, hr13, hr14, hΦ0, hbm, hzf, hvo⟩
  subst hΦ0
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb; rw [← hlay] at hlb; simp only [t3HdrSize] at hlb
  have hw := ctx.hwokW.1
  have hst_below : ∀ x < inp.v2, st.mem x = mem₀ x := fun x hx => (hbm x (by omega)).trans (hb_below x hx)
  have hof := ctx.read_out_fields hst_below
  have hv1_le := ctx.hv1_le
  have hjSrc_lt_v1 : ctx.memT1 (ctx.wInp.h + 16) + 3 * inp.J.m = ctx.v1 :=
    hof.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm
  have hcWn : ctx.wd.comps[ci].W_sub.n = ctx.wd.comps[ci].X.card :=
    (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.1
  have hvn_mem : st.mem (ctx.memT1 (ctx.wInp.h + 12) + 6 * ci + 4) = ctx.wd.comps[ci].W_sub.n :=
    (hof.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ci hci).2.2.2.1.trans hcWn.symm
  have hvn_add : vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n = vhatBaseW ctx.wd (ci + 1) :=
    vhatBaseW_add_le hci
  have hv_sum : vhatBaseW ctx.wd (ci + 1) ≤ (ctx.wd.comps.map fun c => c.W_sub.n).sum :=
    vhatBaseW_le_sum
  have hv_base_lt : vhatBaseW ctx.wd ci < 2 ^ w := by
    have := vhatBaseW_le_sum (wd := ctx.wd) (ci := ci); omega
  have haddr_w : lay.vhatOffsetAddr + ci < 2 ^ w := by omega
  have hce_w : ctx.memT1 (ctx.wInp.h + 12) + (6 * ci + 4) < 2 ^ w := by omega
  have h6_w : 6 < 2 ^ w := lt_of_lt_of_le (by decide : 6 < 32) (by omega)
  have h4_w : 4 < 2 ^ w := lt_of_lt_of_le (by decide : 4 < 32) (by omega)
  set mem1 := Function.update st.mem (lay.vhatOffsetAddr + ci) (vhatBaseW ctx.wd ci)
  set st1 : State := { st with mem := mem1 }
  have hm1_ce : mem1 (ctx.memT1 (ctx.wInp.h + 12) + (6 * ci + 4)) = ctx.wd.comps[ci].W_sub.n := by
    simp only [mem1]; rw [Function.update_of_ne (by omega), show ctx.memT1 (ctx.wInp.h + 12) + (6 * ci + 4) =
      ctx.memT1 (ctx.wInp.h + 12) + 6 * ci + 4 by omega, hvn_mem]
  have hev_ce : (t3Ld (.reg 8) (t3Add (t3Mul (.const 6) (.reg 14)) (.const 4))).eval w st1 =
      some ctx.wd.comps[ci].W_sub.n :=
    Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st1, hr8] : st1.regs 8 = ctx.memT1 (ctx.wInp.h + 12)))
      (Expr.eval_add (Expr.eval_mul (Expr.eval_const h6_w)
        (Expr.eval_reg_of_eq (by simp [st1, hr14] : st1.regs 14 = ci)) (by omega))
        (Expr.eval_const h4_w) (by omega)) hce_w) hm1_ce
  set st2 : State := { st1 with regs := Function.update st1.regs 15 ctx.wd.comps[ci].W_sub.n }
  set st3 : State := { st2 with regs := Function.update st2.regs 13 (vhatBaseW ctx.wd (ci + 1)) }
  have hrun : Runs w p ω t3VhatLoopBody st .normal st3 20 := by
    refine runs_seq_iff.mpr (Or.inr ⟨st1, 5, 14, runs_store_iff.mpr ⟨lay.vhatOffsetAddr + ci,
      vhatBaseW ctx.wd ci, Expr.eval_add (Expr.eval_reg_of_eq hr12) (Expr.eval_reg_of_eq hr14) haddr_w,
      Expr.eval_reg_of_eq hr13, rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨st2, 9, 4,
      runs_assign_iff.mpr ⟨ctx.wd.comps[ci].W_sub.n, hev_ce, rfl, rfl, rfl⟩, ?_, rfl⟩)
    refine runs_assign_iff.mpr ⟨vhatBaseW ctx.wd (ci + 1), ?_, rfl, rfl, rfl⟩
    have h13 : st2.regs 13 = vhatBaseW ctx.wd ci := by
      simp only [st2, st1, Function.update_of_ne (by decide : (13 : ℕ) ≠ 15), hr13]
    have h15 : st2.regs 15 = ctx.wd.comps[ci].W_sub.n := by simp [st2]
    rw [← hvn_add]; exact Expr.eval_add (Expr.eval_reg_of_eq h13) (Expr.eval_reg_of_eq h15) (by omega)
  refine ⟨.normal, st3, 20, 0, hrun, ⟨⟨by simp [st3, st2, st1, hpos], by simp [st3, st2, st1, hr0],
    by simp [st3, st2, st1, hr1], by simp [st3, st2, st1, hr2], by simp [st3, st2, st1, hr7],
    by simp [st3, st2, st1, hr8], by simp [st3, st2, st1, hr12], by simp [st3], by simp, rfl,
    ?_, ?_, ?_⟩, by simp [st3, st2, st1, hr14]⟩, by dsimp only; omega⟩
  · intro x hx; simp only [st3, st2, st1, mem1]; rw [Function.update_of_ne (by omega)]; exact hbm x hx
  · intro x hx; simp only [st3, st2, st1, mem1]; rw [Function.update_of_ne (by omega)]; exact hzf x (by omega)
  · intro j hj
    by_cases hjc : j = ci
    · rw [hjc]; simp [st3, st2, st1, mem1]
    · simp only [st3, st2, st1, mem1]; rw [Function.update_of_ne (by omega)]; exact hvo j (by omega)

private lemma t3VhatLoop_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout)
    (hlay : lay = T3Layout.ofCtx ctx) (mem_b : ℕ → ℕ) (pos : ℕ)
    (hb_below : ∀ x < inp.v2, mem_b x = mem₀ x) (hz_off : ZeroFrom mem_b lay.vhatOffsetAddr) :
    PTriple w p
      (fun st Φ => st.pos = pos ∧ st.mem = mem_b ∧ st.regs 0 = inp.jAddr ∧
        st.regs 1 = inp.t1OutAddr ∧ st.regs 2 = inp.v2 ∧ st.regs 7 = ctx.wd.comps.length ∧
        st.regs 8 = ctx.memT1 (ctx.wInp.h + 12) ∧ st.regs 12 = lay.vhatOffsetAddr ∧
        st.regs 13 = 0 ∧ Φ = 0)
      (t3ForRange 14 (.const 0) (.reg 7) t3VhatLoopBody)
      (pNormalPost (t3VhatLoopInv ctx lay mem_b pos ctx.wd.comps.length)) (fun _ => 30 * inp.J.m + 7) := by
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb; rw [← hlay] at hlb
  have hK_w : ctx.wd.comps.length < 2 ^ w := by
    have : 1 ≤ t3HdrSize := by decide
    omega
  have hK_le := ctx.hK_le
  have hraw := PTriple.forRange_const (w := w) (p := p)
    (P := fun s Φ' => s.pos = pos ∧ s.mem = mem_b ∧ s.regs 0 = inp.jAddr ∧
      s.regs 1 = inp.t1OutAddr ∧ s.regs 2 = inp.v2 ∧ s.regs 7 = ctx.wd.comps.length ∧
      s.regs 8 = ctx.memT1 (ctx.wInp.h + 12) ∧ s.regs 12 = lay.vhatOffsetAddr ∧
      s.regs 13 = 0 ∧ Φ' = 0)
    (r := 14) (lo := .const 0) (hi := .reg 7) (body := t3VhatLoopBody)
    (Inv := t3VhatLoopInv ctx lay mem_b pos) 20 0 ctx.wd.comps.length
    (Nat.zero_le _) ctx.hwokW.1 (fun _ => hK_w)
    (fun s Φ' ⟨hp, hm, h0, h1, h2, h7, h8, h12, h13, hPhi⟩ => by
      refine ⟨Expr.eval_const (by omega), ?_⟩
      rw [hm]
      refine ⟨hp, by simpa [Function.update_of_ne] using h0, by simpa [Function.update_of_ne] using h1,
        by simpa [Function.update_of_ne] using h2, by simpa [Function.update_of_ne] using h7,
        by simpa [Function.update_of_ne] using h8, by simpa [Function.update_of_ne] using h12,
        by simpa [vhatBaseW, Function.update_of_ne] using h13, by simp, hPhi,
        fun _ _ => rfl, by simpa [Nat.add_zero] using hz_off, fun _ h => (Nat.not_lt_zero _ h).elim⟩)
    (fun i s _ _ _ hI => hI.2.2.2.2.2.2.2.2.1)
    (fun i s _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.1)
    (fun i _ hi => t3VhatLoop_step_ptriple ctx lay hlay mem_b pos hb_below i hi)
  intro st Φ ω hP
  obtain ⟨o, st', c, Φ', hr, hq, hc⟩ := hraw st Φ ω hP
  refine ⟨o, st', c, Φ', hr, hq, ?_⟩
  dsimp only at hc ⊢
  simp only [Expr.size, Nat.sub_zero] at hc
  have hmul : ctx.wd.comps.length * 29 ≤ inp.J.m * 30 := Nat.mul_le_mul hK_le (show 29 ≤ 30 by decide)
  omega

private lemma t3_st_ld_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rs off rsrc off2 base srcBase v k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hrs : regs rs = base) (hoff : off < 2 ^ w) (hadd : base + off < 2 ^ w)
    (hrsrc : regs rsrc = srcBase) (hoff2 : off2 < 2 ^ w) (hadd2 : srcBase + off2 < 2 ^ w)
    (hm : mem (srcBase + off2) = v)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨Function.update mem (base + off) v, regs, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k + 9) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq (t3St (.reg rs) (.const off) (t3Ld (.reg rsrc) (.const off2))) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k + c_tot + Φ' ≤ T :=
  t3_store_cps
    (Expr.eval_add (Expr.eval_reg_of_eq hrs) (Expr.eval_const hoff) hadd)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hrsrc) (Expr.eval_const hoff2) hadd2) hm)
    (by simpa [Expr.size, t3Add, t3Ld] using hrest)

private structure T3Hdr1Out {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (mem mem1 regs1 : ℕ → ℕ) : Prop where
  r0 : regs1 0 = inp.jAddr
  r1 : regs1 1 = inp.t1OutAddr
  r2 : regs1 2 = inp.v2
  r3 : regs1 3 = inp.J.m
  r5 : regs1 5 = ctx.wInp.h
  r7 : regs1 7 = ctx.wd.comps.length
  r8 : regs1 8 = ctx.memT1 (ctx.wInp.h + 12)
  r10 : regs1 10 = ctx.wd.W.m
  mb : ∀ x < inp.v2, mem1 x = mem x
  mlo : ∀ x, lay.base ≤ x → x < lay.base + 6 → mem1 x = mem x
  mhi : ∀ x, lay.base + 16 ≤ x → mem1 x = mem x
  jAddr : mem1 (lay.base + t3OffJAddr) = inp.jAddr
  t1Addr : mem1 (lay.base + t3OffT1Addr) = inp.t1OutAddr
  jm : mem1 (lay.base + t3OffJm) = inp.J.m
  wm : mem1 (lay.base + t3OffWm) = ctx.wd.W.m
  k : mem1 (lay.base + t3OffK) = ctx.wd.comps.length
  prepH : mem1 (lay.base + t3OffPrepH) = ctx.wInp.prep.h
  wInpH : mem1 (lay.base + t3OffWInpH) = ctx.wInp.h
  aComps : mem1 (lay.base + t3OffAComps) = ctx.wInp.prep.aComps
  aCompExt : mem1 (lay.base + t3OffACompExt) = ctx.memT1 (ctx.wInp.h + 12)
  wAddr : mem1 (lay.base + t3OffWAddr) = ctx.memT1 (ctx.wInp.h + 13)

private structure T3StaticHdr {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (memH : ℕ → ℕ) : Prop where
  below : ∀ x < inp.v2, memH x = mem₀ x
  zeros : ∀ i ∈ ([1, 2, 3, 4, 5, 29, 30, 31] : List ℕ), memH (lay.base + i) = 0
  zfE : WordRAM.ZeroFrom memH lay.embJWAddr
  jAddr : memH (lay.base + t3OffJAddr) = inp.jAddr
  t1Addr : memH (lay.base + t3OffT1Addr) = inp.t1OutAddr
  jm : memH (lay.base + t3OffJm) = inp.J.m
  wm : memH (lay.base + t3OffWm) = ctx.wd.W.m
  k : memH (lay.base + t3OffK) = ctx.wd.comps.length
  prepH : memH (lay.base + t3OffPrepH) = ctx.wInp.prep.h
  wInpH : memH (lay.base + t3OffWInpH) = ctx.wInp.h
  aComps : memH (lay.base + t3OffAComps) = ctx.wInp.prep.aComps
  aCompExt : memH (lay.base + t3OffACompExt) = ctx.memT1 (ctx.wInp.h + 12)
  wAddr : memH (lay.base + t3OffWAddr) = ctx.memT1 (ctx.wInp.h + 13)
  wWNum : memH (lay.base + t3OffWWNum) = ctx.memT1 (ctx.wInp.h + 14)
  wSrc : memH (lay.base + t3OffWSrc) = ctx.memT1 (ctx.wInp.h + 15)
  jSrc : memH (lay.base + t3OffJSrc) = ctx.memT1 (ctx.wInp.h + 16)
  tau2 : memH (lay.base + t3OffTau2) = ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params
  phiDen : memH (lay.base + t3OffPhiDen) = ctx.wInp.prep.phiDen_dec
  mw : memH (lay.base + t3OffMw) = ctx.wd.M_W
  phiNumC : memH (lay.base + t3OffPhiNumC) = impl.constructExpander.phiNum
  phiDenC : memH (lay.base + t3OffPhiDenC) = impl.constructExpander.phiDen

private lemma t3Setup_hdr1_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (mem : ℕ → ℕ) (regs : ℕ → ℕ) (pos k T : ℕ)
    (hbelow : ∀ x < inp.v2, mem x = mem₀ x)
    (hr0 : regs 0 = inp.jAddr) (hr1 : regs 1 = inp.t1OutAddr) (hr2 : regs 2 = inp.v2)
    (sRest : Stmt) {Q : Outcome → State → ℕ → Prop}
    (hrest : ∀ mem1 regs1, T3Hdr1Out ctx lay mem mem1 regs1 →
      ∃ o stF c_s Φ', Runs w p ω sRest ⟨mem1, regs1, pos⟩ o stF c_s ∧
        Q o stF Φ' ∧ (k + 108) + c_s + Φ' ≤ T) :
    let rJAddr := Expr.reg 0; let rT1 := Expr.reg 1; let base := Expr.reg 2
    let rJm := Expr.reg 3; let rPrepH := Expr.reg 4; let rWInpH := Expr.reg 5
    let rAComps := Expr.reg 6; let rK := Expr.reg 7; let rAExt := Expr.reg 8
    let rWAddr := Expr.reg 9; let rWm := Expr.reg 10
    let hdr1 :=
      Stmt.seq (.assign 3 (t3Ld rJAddr (.const 1))) (Stmt.seq (.assign 4 (t3Ld rT1 (.const 4)))
        (Stmt.seq (.assign 5 (t3Ld rT1 (.const 5))) (Stmt.seq (.assign 6 (t3Ld rPrepH (.const 3)))
          (Stmt.seq (.assign 7 (t3Ld rPrepH (.const 2))) (Stmt.seq (.assign 8 (t3Ld rWInpH (.const 12)))
            (Stmt.seq (.assign 9 (t3Ld rWInpH (.const 13))) (Stmt.seq (.assign 10 (t3Ld rWAddr (.const 1)))
              (Stmt.seq (t3St base (.const t3OffJAddr) rJAddr) (Stmt.seq (t3St base (.const t3OffT1Addr) rT1)
                (Stmt.seq (t3St base (.const t3OffJm) rJm) (Stmt.seq (t3St base (.const t3OffWm) rWm)
                  (Stmt.seq (t3St base (.const t3OffK) rK) (Stmt.seq (t3St base (.const t3OffPrepH) rPrepH)
                    (Stmt.seq (t3St base (.const t3OffWInpH) rWInpH) (Stmt.seq (t3St base (.const t3OffAComps) rAComps)
                      (Stmt.seq (t3St base (.const t3OffACompExt) rAExt)
                        (Stmt.seq (t3St base (.const t3OffWAddr) rWAddr) sRest)))))))))))))))))
    ∃ o stF c_tot Φ', Runs w p ω hdr1 ⟨mem, regs, pos⟩ o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb; rw [← hlay] at hlb; simp only [t3HdrSize] at hlb
  have hof := ctx.read_out_fields hbelow
  have hv1_lo := ctx.hv1_lo
  have hlt_v1 := ctx.lt_v1_of_t1; have hv1_le := ctx.hv1_le; have hj_lt_t1 := ctx.hJ_lt_t1
  have hj_enc : inp.J.encode.length = 2 + 2 * inp.J.m := graph_encode_length inp.J
  have hw_enc : ctx.wd.W.encode.length = 2 + 2 * ctx.wd.W.m := graph_encode_length ctx.wd.W
  have hjSrc_lt_v1 : ctx.memT1 (ctx.wInp.h + 16) + 3 * inp.J.m = ctx.v1 :=
    hof.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm
  have hJ_m := graphAt_m (ctx.read_j_graphAt hbelow)
  have hW_m := graphAt_m hof.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only
  apply t3_ld_cps hr0 (by omega) (by omega) hJ_m
  apply t3_ld_cps (by simp [hr1]) (by omega) (by omega) hof.1
  apply t3_ld_cps (by simp [hr1]) (by omega) (by omega) hof.2.1
  apply t3_ld_cps (by simp) (by omega) (by omega) hof.2.2.2.2.1
  apply t3_ld_cps (by simp) (by omega) (by omega) hof.2.2.2.1
  apply t3_ld_cps (by simp) (by omega) (by omega) hof.2.2.2.2.2.2.2.1
  apply t3_ld_cps (by simp) (by omega) (by omega) hof.2.2.2.2.2.2.2.2.1
  apply t3_ld_cps (by simp) (by omega) (by omega) hW_m
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffJAddr]; omega) (by simp [t3OffJAddr]; omega) (by simp [hr0]; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffT1Addr]; omega) (by simp [t3OffT1Addr]; omega) (by simp [hr1]; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffJm]; omega) (by simp [t3OffJm]; omega) (by simp; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffWm]; omega) (by simp [t3OffWm]; omega) (by simp; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffK]; omega) (by simp [t3OffK]; omega) (by simp; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffPrepH]; omega) (by simp [t3OffPrepH]; omega) (by simp; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffWInpH]; omega) (by simp [t3OffWInpH]; omega) (by simp; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffAComps]; omega) (by simp [t3OffAComps]; omega) (by simp; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffACompExt]; omega) (by simp [t3OffACompExt]; omega) (by simp; rfl)
  apply t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffWAddr]; omega) (by simp [t3OffWAddr]; omega) (by simp; rfl)
  have h108 : ∀ (r v : ℕ), r + (t3Ld (.reg 0) (.const 1)).size + 2 + (t3Ld (.reg 1) (.const 4)).size + 2 +
      (t3Ld (.reg 1) (.const 5)).size + 2 + (t3Ld (.reg 4) (.const 3)).size + 2 +
      (t3Ld (.reg 4) (.const 2)).size + 2 + (t3Ld (.reg 5) (.const 12)).size + 2 +
      (t3Ld (.reg 5) (.const 13)).size + 2 + (t3Ld (.reg 9) (.const 1)).size + 2 +
      (t3Add (.reg 2) (.const t3OffJAddr)).size + (Expr.reg 0).size + 2 +
      (t3Add (.reg 2) (.const t3OffT1Addr)).size + (Expr.reg 1).size + 2 +
      (t3Add (.reg 2) (.const t3OffJm)).size + (Expr.reg 3).size + 2 +
      (t3Add (.reg 2) (.const t3OffWm)).size + (Expr.reg 10).size + 2 +
      (t3Add (.reg 2) (.const t3OffK)).size + (Expr.reg 7).size + 2 +
      (t3Add (.reg 2) (.const t3OffPrepH)).size + (Expr.reg 4).size + 2 +
      (t3Add (.reg 2) (.const t3OffWInpH)).size + (Expr.reg 5).size + 2 +
      (t3Add (.reg 2) (.const t3OffAComps)).size + (Expr.reg 6).size + 2 +
      (t3Add (.reg 2) (.const t3OffACompExt)).size + (Expr.reg 8).size + 2 +
      (t3Add (.reg 2) (.const t3OffWAddr)).size + (Expr.reg 9).size + 2 + v = r + 108 + v := by
    intro r v; dsimp only [Expr.size, t3Add, t3Ld]
  simp_rw [h108]
  refine hrest _ _ ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp, by simp, by simp, by simp, by simp,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [t3OffJAddr, t3OffT1Addr, t3OffJm, t3OffWm, t3OffK, t3OffPrepH, t3OffWInpH,
      t3OffAComps, t3OffACompExt, t3OffWAddr, hlb.1] at *
  · intro x hx; repeat' rw [Function.update_of_ne (by omega)]
  · intro x hx1 hx2; repeat' rw [Function.update_of_ne (by omega)]
  · intro x hx; repeat' rw [Function.update_of_ne (by omega)]
  all_goals simp [Nat.add_left_cancel_iff]

private lemma t3Setup_hdr2_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (mem1 regs1 : ℕ → ℕ) (pos k T : ℕ)
    (hm1_below : ∀ x < inp.v2, mem1 x = mem₀ x)
    (hr2 : regs1 2 = inp.v2) (hr5 : regs1 5 = ctx.wInp.h)
    (phiNumConst phiDenConst : ℕ)
    (hphiN : phiNumConst = impl.constructExpander.phiNum)
    (hphiD : phiDenConst = impl.constructExpander.phiDen)
    (sRest : Stmt) {Q : Outcome → State → ℕ → Prop}
    (hrest : ∀ mem2, (∀ x < lay.base + 16, mem2 x = mem1 x) →
      (∀ x, lay.base + 24 ≤ x → mem2 x = mem1 x) →
      mem2 (lay.base + t3OffWWNum) = ctx.memT1 (ctx.wInp.h + 14) →
      mem2 (lay.base + t3OffWSrc) = ctx.memT1 (ctx.wInp.h + 15) →
      mem2 (lay.base + t3OffJSrc) = ctx.memT1 (ctx.wInp.h + 16) →
      mem2 (lay.base + t3OffTau2) = ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params →
      mem2 (lay.base + t3OffPhiDen) = ctx.wInp.prep.phiDen_dec →
      mem2 (lay.base + t3OffMw) = ctx.wd.M_W →
      mem2 (lay.base + t3OffPhiNumC) = impl.constructExpander.phiNum →
      mem2 (lay.base + t3OffPhiDenC) = impl.constructExpander.phiDen →
      ∃ o stF c_s Φ', Runs w p ω sRest ⟨mem2, regs1, pos⟩ o stF c_s ∧
        Q o stF Φ' ∧ (k + 64) + c_s + Φ' ≤ T) :
    let base := Expr.reg 2; let rWInpH := Expr.reg 5
    let hdr2 :=
      Stmt.seq (t3St base (.const t3OffWWNum) (t3Ld rWInpH (.const 14)))
        (Stmt.seq (t3St base (.const t3OffWSrc) (t3Ld rWInpH (.const 15)))
          (Stmt.seq (t3St base (.const t3OffJSrc) (t3Ld rWInpH (.const 16)))
            (Stmt.seq (t3St base (.const t3OffTau2) (t3Ld rWInpH (.const 11)))
              (Stmt.seq (t3St base (.const t3OffPhiDen) (t3Ld rWInpH (.const 18)))
                (Stmt.seq (t3St base (.const t3OffMw) (.load rWInpH))
                  (Stmt.seq (t3St base (.const t3OffPhiNumC) (.const phiNumConst))
                    (Stmt.seq (t3St base (.const t3OffPhiDenC) (.const phiDenConst)) sRest)))))))
    ∃ o stF c_tot Φ', Runs w p ω hdr2 ⟨mem1, regs1, pos⟩ o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb; rw [← hlay] at hlb; simp only [t3HdrSize] at hlb
  have hof := ctx.read_out_fields hm1_below
  have hv1_lo := ctx.hv1_lo
  have hlt_v1 := ctx.lt_v1_of_t1; have hv1_le := ctx.hv1_le
  have hphi_lt_w : impl.constructExpander.phiDen < 2 ^ w := by
    have hcw_pos := impl.pathDS.params.hcw_pos; have hlog := ctx.hwokW.2.1
    set dW := WitnessCoreInput.dWInt impl.constructExpander
    set mw := Task1Input.mwCap impl inp.J
    set X := impl.constructExpander.phiDen + 4 * mw + impl.pathDS.params.gExp dW mw + 2
    have hX_lt : X < 2 ^ (Nat.log 2 X + 1) := Nat.lt_pow_succ_log_self (by decide) X
    have hpow : 2 ^ (Nat.log 2 X + 1) ≤ 2 ^ w :=
      Nat.pow_le_pow_right (by decide) (le_trans (Nat.le_mul_of_pos_left _ hcw_pos) hlog)
    omega
  have hphiN_lt_w : impl.constructExpander.phiNum < 2 ^ w :=
    lt_of_le_of_lt impl.constructExpander.hphi_le hphi_lt_w
  dsimp only
  apply t3_st_ld_cps hr2 (by simp [t3OffWWNum]; omega) (by simp [t3OffWWNum]; omega)
    hr5 (by omega) (by omega) hof.2.2.2.2.2.2.2.2.2.1
  apply t3_st_ld_cps hr2 (by simp [t3OffWSrc]; omega) (by simp [t3OffWSrc]; omega)
    hr5 (by omega) (by omega) (show _ = ctx.memT1 (ctx.wInp.h + 15) from by
      rw [Function.update_of_ne (by omega)]; exact hof.2.2.2.2.2.2.2.2.2.2.1)
  apply t3_st_ld_cps hr2 (by simp [t3OffJSrc]; omega) (by simp [t3OffJSrc]; omega)
    hr5 (by omega) (by omega) (show _ = ctx.memT1 (ctx.wInp.h + 16) from by
      (repeat' rw [Function.update_of_ne (by omega)]); exact hof.2.2.2.2.2.2.2.2.2.2.2.1)
  apply t3_st_ld_cps hr2 (by simp [t3OffTau2]; omega) (by simp [t3OffTau2]; omega)
    hr5 (by omega) (by omega) (show _ = ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params from by
      (repeat' rw [Function.update_of_ne (by omega)]); exact hof.2.2.2.2.2.2.1)
  apply t3_st_ld_cps hr2 (by simp [t3OffPhiDen]; omega) (by simp [t3OffPhiDen]; omega)
    hr5 (by omega) (by omega) (show _ = ctx.wInp.prep.phiDen_dec from by
      (repeat' rw [Function.update_of_ne (by omega)]); exact hof.2.2.2.2.2.2.2.2.2.2.2.2.1)
  apply t3_store_cps
    (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_const (by simp [t3OffMw]; omega)) (by simp [t3OffMw]; omega))
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr5) (show _ = ctx.wd.M_W from by
      dsimp only; (repeat' rw [Function.update_of_ne (by omega)]); exact hof.2.2.2.2.2.1))
  apply t3_st_const_cps hr2 (by simp [t3OffPhiNumC]; omega) (by simp [t3OffPhiNumC]; omega) (hphiN ▸ hphiN_lt_w)
  apply t3_st_const_cps hr2 (by simp [t3OffPhiDenC]; omega) (by simp [t3OffPhiDenC]; omega) (hphiD ▸ hphi_lt_w)
  have h64 : ∀ (r v : ℕ), r + 9 + 9 + 9 + 9 + 9 + (Expr.bin .add (.reg 2) (.const t3OffMw)).size +
      (Expr.load (.reg 5)).size + 2 + (t3Add (.reg 2) (.const t3OffPhiNumC)).size + 3 +
      (t3Add (.reg 2) (.const t3OffPhiDenC)).size + 3 + v = r + 64 + v := by
    intro r v; dsimp only [Expr.size, t3Add]
  simp_rw [h64]
  refine hrest _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [t3OffWWNum, t3OffWSrc, t3OffJSrc, t3OffTau2, t3OffPhiDen, t3OffMw,
    t3OffPhiNumC, t3OffPhiDenC, hlb.1] at *
  · intro x hx; repeat' rw [Function.update_of_ne (by omega)]
  · intro x hx; repeat' rw [Function.update_of_ne (by omega)]
  all_goals (simp [Nat.add_left_cancel_iff]; try first | exact hphiN | exact hphiD)

private lemma t3_ptr_upd_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rInc off base ptr inc k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hr2 : regs 2 = base) (hrP : regs 11 = ptr) (hrI : regs rInc = inc)
    (h_w : ptr + inc < 2 ^ w) (hoff : off < 2 ^ w) (hadd : base + off < 2 ^ w)
    (hrest : ∃ o stF c_s Φ',
      Runs w p ω s ⟨Function.update mem (base + off) (ptr + inc), Function.update regs 11 (ptr + inc), pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k + 11) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ',
      Runs w p ω (.seq (.assign 11 (t3Add (.reg 11) (.reg rInc)))
        (.seq (t3St (.reg 2) (.const off) (.reg 11)) s)) ⟨mem, regs, pos⟩ o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  refine t3_assign_cps (Expr.eval_add (Expr.eval_reg_of_eq hrP) (Expr.eval_reg_of_eq hrI) h_w) ?_
  refine t3_st_cps (by rw [Function.update_of_ne (by decide)]; exact hr2) hoff hadd
    (show _ = ptr + inc from rfl) ?_
  have h11 : ∀ r v, r + (t3Add (.reg 11) (.reg rInc)).size + 2 +
      (t3Add (.reg 2) (.const off)).size + (Expr.reg 11).size + 2 + v = r + 11 + v := by
    intro r v; dsimp only [Expr.size, t3Add]
  simpa only [h11] using hrest

private lemma t3Setup_ptrs1_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (memH regsH : ℕ → ℕ) (pos k T : ℕ) (hStaticH : T3StaticHdr ctx lay memH)
    (hr0 : regsH 0 = inp.jAddr) (hr1 : regsH 1 = inp.t1OutAddr) (hr2 : regsH 2 = inp.v2)
    (hr3 : regsH 3 = inp.J.m) (hr7 : regsH 7 = ctx.wd.comps.length)
    (hr8 : regsH 8 = ctx.memT1 (ctx.wInp.h + 12)) (hr10 : regsH 10 = ctx.wd.W.m)
    (sRest : Stmt) {Q : Outcome → State → ℕ → Prop}
    (hrest : ∀ memB regsB,
      regsB 0 = inp.jAddr → regsB 1 = inp.t1OutAddr → regsB 2 = inp.v2 →
      regsB 7 = ctx.wd.comps.length → regsB 8 = ctx.memT1 (ctx.wInp.h + 12) →
      regsB 12 = lay.vhatOffsetAddr → regsB 13 = 0 →
      (∀ x < inp.v2, memB x = mem₀ x) → ZeroFrom memB lay.vhatOffsetAddr →
      (∀ x, lay.embJWAddr ≤ x → memB x = memH x) →
      (∀ i, 6 ≤ i → i ≤ 23 → memB (lay.base + i) = memH (lay.base + i)) →
      (∀ i ∈ ([1, 2, 3, 4, 30, 31] : List ℕ), memB (lay.base + i) = 0) →
      (memB (lay.base + t3OffEmbJW) = lay.embJWAddr ∧ memB (lay.base + t3OffDsHdl) = lay.dsHandlesAddr ∧
        memB (lay.base + t3OffECnt) = lay.econgCountAddr ∧ memB (lay.base + t3OffWDel) = lay.wDelStampAddr ∧
        memB (lay.base + t3OffQueue) = lay.queueAddr ∧ memB (lay.base + t3OffVOff) = lay.vhatOffsetAddr) →
      ∃ o stF c_s Φ', Runs w p ω sRest ⟨memB, regsB, pos⟩ o stF c_s ∧
        Q o stF Φ' ∧ (k + 69) + c_s + Φ' ≤ T) :
    let base := Expr.reg 2; let rJm := Expr.reg 3; let rK := Expr.reg 7
    let rWm := Expr.reg 10; let rPtr := Expr.reg 11; let rVOff := Expr.reg 12
    let s :=
      Stmt.seq (.assign 11 (t3Add base (.const t3HdrSize))) (Stmt.seq (t3St base (.const t3OffEmbJW) rPtr)
        (Stmt.seq (.assign 11 (t3Add rPtr rJm)) (Stmt.seq (t3St base (.const t3OffDsHdl) rPtr)
          (Stmt.seq (.assign 11 (t3Add rPtr rK)) (Stmt.seq (t3St base (.const t3OffECnt) rPtr)
            (Stmt.seq (.assign 11 (t3Add rPtr rWm)) (Stmt.seq (t3St base (.const t3OffWDel) rPtr)
              (Stmt.seq (.assign 11 (t3Add rPtr rWm)) (Stmt.seq (t3St base (.const t3OffQueue) rPtr)
                (Stmt.seq (.assign 12 (t3Add rPtr rWm)) (Stmt.seq (t3St base (.const t3OffVOff) rVOff)
                  (Stmt.seq (.assign 13 (.const 0)) sRest))))))))))))
    ∃ o stF c_tot Φ', Runs w p ω s ⟨memH, regsH, pos⟩ o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb; rw [← hlay] at hlb; simp only [t3HdrSize] at hlb
  dsimp only
  refine t3_assign_cps (Expr.eval_add (Expr.eval_reg_of_eq hr2)
    (Expr.eval_const (by simp [t3HdrSize]; omega)) (by simp [t3HdrSize]; omega)) ?_
  refine t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffEmbJW])
    (by simp [t3OffEmbJW]; omega) (show _ = inp.v2 + t3HdrSize from rfl) ?_
  refine t3_ptr_upd_cps (show _ = inp.v2 from by simp [hr2]) (show _ = inp.v2 + t3HdrSize from by simp)
    (show _ = inp.J.m from by simp [hr3])
    (by simp [t3HdrSize]; omega) (by simp [t3OffDsHdl]; omega) (by simp [t3OffDsHdl]; omega) ?_
  refine t3_ptr_upd_cps (show _ = inp.v2 from by simp [hr2]) (show _ = inp.v2 + t3HdrSize + inp.J.m from by simp)
    (show _ = ctx.wd.comps.length from by simp [hr7])
    (by simp [t3HdrSize]; omega) (by simp [t3OffECnt]; omega) (by simp [t3OffECnt]; omega) ?_
  refine t3_ptr_upd_cps (show _ = inp.v2 from by simp [hr2])
    (show _ = inp.v2 + t3HdrSize + inp.J.m + ctx.wd.comps.length from by simp)
    (show _ = ctx.wd.W.m from by simp [hr10])
    (by simp [t3HdrSize]; omega) (by simp [t3OffWDel]; omega) (by simp [t3OffWDel]; omega) ?_
  refine t3_ptr_upd_cps (show _ = inp.v2 from by simp [hr2])
    (show _ = inp.v2 + t3HdrSize + inp.J.m + ctx.wd.comps.length + ctx.wd.W.m from by simp)
    (show _ = ctx.wd.W.m from by simp [hr10])
    (by simp [t3HdrSize]; omega) (by simp [t3OffQueue]; omega) (by simp [t3OffQueue]; omega) ?_
  refine t3_assign_cps (Expr.eval_add
    (Expr.eval_reg_of_eq (show _ = inp.v2 + t3HdrSize + inp.J.m + ctx.wd.comps.length + ctx.wd.W.m + ctx.wd.W.m from by simp))
    (Expr.eval_reg_of_eq (show _ = ctx.wd.W.m from by simp [hr10])) (by simp [t3HdrSize]; omega)) ?_
  refine t3_st_cps (by simp [hr2]; rfl) (by simp [t3OffVOff]; omega)
    (by simp [t3OffVOff]; omega)
    (show _ = inp.v2 + t3HdrSize + inp.J.m + ctx.wd.comps.length + ctx.wd.W.m + ctx.wd.W.m + ctx.wd.W.m from rfl) ?_
  apply t3_const_cps (by omega)
  have h69 : ∀ (r v : ℕ), r + (t3Add (.reg 2) (.const t3HdrSize)).size + 2 +
      (t3Add (.reg 2) (.const t3OffEmbJW)).size + (Expr.reg 11).size + 2 + 11 + 11 + 11 + 11 +
      (t3Add (.reg 11) (.reg 10)).size + 2 +
      (t3Add (.reg 2) (.const t3OffVOff)).size + (Expr.reg 12).size + 2 + 3 + v = r + 69 + v := by
    intro r v; dsimp only [Expr.size, t3Add, t3HdrSize]
  simp_rw [h69]
  obtain ⟨memB, hmemB⟩ : ∃ m : ℕ → ℕ, m =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update memH (inp.v2 + t3OffEmbJW) (inp.v2 + t3HdrSize))
        (inp.v2 + t3OffDsHdl) (inp.v2 + t3HdrSize + inp.J.m))
        (inp.v2 + t3OffECnt) (inp.v2 + t3HdrSize + inp.J.m + ctx.wd.comps.length))
        (inp.v2 + t3OffWDel) (inp.v2 + t3HdrSize + inp.J.m + ctx.wd.comps.length + ctx.wd.W.m))
        (inp.v2 + t3OffQueue) (inp.v2 + t3HdrSize + inp.J.m + ctx.wd.comps.length + ctx.wd.W.m + ctx.wd.W.m))
        (inp.v2 + t3OffVOff)
        (inp.v2 + t3HdrSize + inp.J.m + ctx.wd.comps.length + ctx.wd.W.m + ctx.wd.W.m + ctx.wd.W.m) := ⟨_, rfl⟩
  rw [← hmemB]
  refine hrest memB _ (by simp [hr0]) (by simp [hr1]) (by simp [hr2]) (by simp [hr7]) (by simp [hr8])
    (by simp only [Function.update_of_ne (by decide : (12 : ℕ) ≠ 13), Function.update_self, t3HdrSize]; omega)
    (by simp) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx; rw [hmemB]
    simp only [t3OffEmbJW, t3OffDsHdl, t3OffECnt, t3OffWDel, t3OffQueue, t3OffVOff]
    repeat' rw [Function.update_of_ne (by omega)]
    exact hStaticH.below x hx
  · intro x hx; rw [hmemB]
    simp only [t3OffEmbJW, t3OffDsHdl, t3OffECnt, t3OffWDel, t3OffQueue, t3OffVOff]
    repeat' rw [Function.update_of_ne (by omega)]
    exact hStaticH.zfE x (by omega)
  · intro x hx; rw [hmemB]
    simp only [t3OffEmbJW, t3OffDsHdl, t3OffECnt, t3OffWDel, t3OffQueue, t3OffVOff, ← hlb.1]
    repeat' rw [Function.update_of_ne (by omega)]
  · intro i hi1 hi2; rw [hmemB]
    simp only [t3OffEmbJW, t3OffDsHdl, t3OffECnt, t3OffWDel, t3OffQueue, t3OffVOff, ← hlb.1]
    repeat' rw [Function.update_of_ne (by omega)]
  · intro i hi; rw [hmemB]
    simp only [t3OffEmbJW, t3OffDsHdl, t3OffECnt, t3OffWDel, t3OffQueue, t3OffVOff, ← hlb.1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · repeat' rw [Function.update_of_ne (by omega)]
      exact hStaticH.zeros _ (by decide)
  · rw [hmemB]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [t3OffEmbJW, t3OffDsHdl, t3OffECnt, t3OffWDel, t3OffQueue, t3OffVOff, ← hlb.1, t3HdrSize]
      simp [Nat.add_left_cancel_iff]; omega

private lemma t3Setup_ptrs2_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (memH memB : ℕ → ℕ) (stV : State) (pos k T : ℕ)
    (hStaticH : T3StaticHdr ctx lay memH)
    (hmB_below : ∀ x < inp.v2, memB x = mem₀ x)
    (hmB_eq_hi : ∀ x, lay.embJWAddr ≤ x → memB x = memH x)
    (hmB_6_23 : ∀ i, 6 ≤ i → i ≤ 23 → memB (lay.base + i) = memH (lay.base + i))
    (hmB_zeros : ∀ i ∈ ([1, 2, 3, 4, 30, 31] : List ℕ), memB (lay.base + i) = 0)
    (hmB_ptrs : memB (lay.base + t3OffEmbJW) = lay.embJWAddr ∧ memB (lay.base + t3OffDsHdl) = lay.dsHandlesAddr ∧
      memB (lay.base + t3OffECnt) = lay.econgCountAddr ∧ memB (lay.base + t3OffWDel) = lay.wDelStampAddr ∧
      memB (lay.base + t3OffQueue) = lay.queueAddr ∧ memB (lay.base + t3OffVOff) = lay.vhatOffsetAddr)
    (hvpos : stV.pos = pos) (hv0 : stV.regs 0 = inp.jAddr) (hv1 : stV.regs 1 = inp.t1OutAddr)
    (hv2 : stV.regs 2 = inp.v2) (hv7 : stV.regs 7 = ctx.wd.comps.length)
    (hv12 : stV.regs 12 = lay.vhatOffsetAddr) (hv13 : stV.regs 13 = vhatBaseW ctx.wd ctx.wd.comps.length)
    (hmv : ∀ x < lay.vhatOffsetAddr, stV.mem x = memB x)
    (hzfV : WordRAM.ZeroFrom stV.mem (lay.vhatOffsetAddr + ctx.wd.comps.length))
    (hvo : ∀ ci < ctx.wd.comps.length, stV.mem (lay.vhatOffsetAddr + ci) = vhatBaseW ctx.wd ci)
    (sRest : Stmt) {Q : Outcome → State → ℕ → Prop}
    (hrest : ∀ mem_s regs_s,
      regs_s 0 = inp.jAddr → regs_s 1 = inp.t1OutAddr → regs_s 2 = inp.v2 →
      T3StaticMem ctx lay mem_s → mem_s (lay.base + t3OffHCur) = lay.staticEnd →
      WordRAM.ZeroFrom mem_s lay.staticEnd →
      (∀ i ∈ ([1, 2, 3, 4, 30, 31] : List ℕ), mem_s (lay.base + i) = 0) →
      (∀ x, lay.embJWAddr ≤ x → x < lay.dsHandlesAddr → mem_s x = 0) →
      (∀ x, lay.econgCountAddr ≤ x → x < lay.wDelStampAddr → mem_s x = 0) →
      (∀ x, lay.wDelStampAddr ≤ x → x < lay.vhatOffsetAddr → mem_s x = 0) →
      (∀ x, lay.vhatStampAddr ≤ x → x < lay.staticEnd → mem_s x = 0) →
      ∃ o stF c_s Φ', Runs w p ω sRest ⟨mem_s, regs_s, pos⟩ o stF c_s ∧ Q o stF Φ' ∧ (k + 19) + c_s + Φ' ≤ T) :
    let tail :=
      Stmt.seq (.assign 11 (t3Add (.reg 12) (.reg 7)))
        (Stmt.seq (t3St (.reg 2) (.const t3OffVStmp) (.reg 11))
          (Stmt.seq (t3St (.reg 2) (.const t3OffHCur) (t3Add (.reg 11) (.reg 13))) sRest))
    ∃ o stF c_tot Φ', Runs w p ω tail stV o stF c_tot ∧ Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb; rw [← hlay] at hlb; simp only [t3HdrSize] at hlb
  have hstV : stV = ⟨stV.mem, stV.regs, pos⟩ := by cases stV; cases hvpos; rfl
  rw [hstV]
  have hv_sum : vhatBaseW ctx.wd ctx.wd.comps.length = (ctx.wd.comps.map fun c => c.W_sub.n).sum := by simp [vhatBaseW]
  rw [hv_sum] at hv13
  dsimp only
  refine t3_assign_cps (Expr.eval_add (Expr.eval_reg_of_eq hv12) (Expr.eval_reg_of_eq hv7) (by omega)) ?_
  refine t3_st_cps (by simp [hv2]; rfl) (by simp [t3OffVStmp]; omega)
    (by simp [t3OffVStmp]; omega) (show _ = lay.vhatOffsetAddr + ctx.wd.comps.length from rfl) ?_
  refine t3_store_cps
    (Expr.eval_add (Expr.eval_reg_of_eq (show _ = inp.v2 from hv2))
      (Expr.eval_const (by simp [t3OffHCur]; omega)) (by simp [t3OffHCur]; omega))
    (Expr.eval_add (Expr.eval_reg_of_eq (show _ = lay.vhatOffsetAddr + ctx.wd.comps.length from rfl))
      (Expr.eval_reg_of_eq (show _ = (ctx.wd.comps.map fun c => c.W_sub.n).sum from hv13)) (by omega)) ?_
  have h19 : ∀ (r v : ℕ), r + (t3Add (.reg 12) (.reg 7)).size + 2 +
      (t3Add (.reg 2) (.const t3OffVStmp)).size + (Expr.reg 11).size + 2 +
      (t3Add (.reg 2) (.const t3OffHCur)).size + (t3Add (.reg 11) (.reg 13)).size + 2 + v = r + 19 + v := by
    intro r v; dsimp only [Expr.size, t3Add]
  simp_rw [h19]
  obtain ⟨memS, hmemS⟩ : ∃ m : ℕ → ℕ, m =
      Function.update (Function.update stV.mem (inp.v2 + t3OffVStmp) (lay.vhatOffsetAddr + ctx.wd.comps.length))
        (inp.v2 + t3OffHCur) (lay.vhatOffsetAddr + ctx.wd.comps.length + (ctx.wd.comps.map fun c => c.W_sub.n).sum) :=
    ⟨_, rfl⟩
  rw [← hmemS]
  have h32 : t3OffHCur < 32 ∧ t3OffVStmp < 32 := by decide
  have hvst_eq : lay.vhatOffsetAddr + ctx.wd.comps.length = lay.vhatStampAddr := hlb.2.2.2.2.2.2.2.1.symm
  have hend_eq : lay.vhatOffsetAddr + ctx.wd.comps.length + (ctx.wd.comps.map fun c => c.W_sub.n).sum = lay.staticEnd := by omega
  have hmemS_hi : ∀ x, lay.base + 32 ≤ x → memS x = stV.mem x := fun x hx => by
    rw [hmemS, Function.update_of_ne (Nat.ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left h32.1 inp.v2) (hlb.1 ▸ hx))),
      Function.update_of_ne (Nat.ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left h32.2 inp.v2) (hlb.1 ▸ hx)))]
  have hmS_lt : ∀ x, x < lay.vhatOffsetAddr → x ≠ lay.base + t3OffVStmp → x ≠ lay.base + t3OffHCur → memS x = memB x :=
    fun x hx1 hx2 hx3 => by rw [hmemS, ← hlb.1, Function.update_of_ne hx3, Function.update_of_ne hx2, hmv x hx1]
  have hmS_6_23 : ∀ i, 6 ≤ i → i ≤ 23 → memS (lay.base + i) = memH (lay.base + i) := fun i hi1 hi2 => by
    rw [hmS_lt _ (by omega) (by simp [t3OffVStmp]; omega) (by simp [t3OffHCur]; omega)]; exact hmB_6_23 i hi1 hi2
  have hmS_ptr_eq : ∀ off, off ∈ [t3OffEmbJW, t3OffDsHdl, t3OffECnt, t3OffWDel, t3OffQueue, t3OffVOff] →
      memS (lay.base + off) = memB (lay.base + off) := fun off hoff => by
    have : off = 0 ∨ 24 ≤ off ∧ off ≤ 28 := by
      simp only [t3OffEmbJW, t3OffDsHdl, t3OffECnt, t3OffWDel, t3OffQueue, t3OffVOff, List.mem_cons, List.not_mem_nil, or_false] at hoff; omega
    exact hmS_lt _ (by omega) (by simp only [t3OffVStmp]; omega) (by simp only [t3OffHCur]; omega)
  have hStS : T3StaticMem ctx lay memS :=
    ⟨fun x hx => (hmS_lt x (by omega) (by omega) (by omega)).trans (hmB_below x hx), (hmS_ptr_eq _ (by simp)).trans hmB_ptrs.1,
      (hmS_6_23 t3OffJAddr (by decide) (by decide)).trans hStaticH.jAddr, (hmS_6_23 t3OffT1Addr (by decide) (by decide)).trans hStaticH.t1Addr,
      (hmS_6_23 t3OffJm (by decide) (by decide)).trans hStaticH.jm, (hmS_6_23 t3OffWm (by decide) (by decide)).trans hStaticH.wm,
      (hmS_6_23 t3OffK (by decide) (by decide)).trans hStaticH.k, (hmS_6_23 t3OffPrepH (by decide) (by decide)).trans hStaticH.prepH,
      (hmS_6_23 t3OffWInpH (by decide) (by decide)).trans hStaticH.wInpH, (hmS_6_23 t3OffAComps (by decide) (by decide)).trans hStaticH.aComps,
      (hmS_6_23 t3OffACompExt (by decide) (by decide)).trans hStaticH.aCompExt, (hmS_6_23 t3OffWAddr (by decide) (by decide)).trans hStaticH.wAddr,
      (hmS_6_23 t3OffWWNum (by decide) (by decide)).trans hStaticH.wWNum, (hmS_6_23 t3OffWSrc (by decide) (by decide)).trans hStaticH.wSrc,
      (hmS_6_23 t3OffJSrc (by decide) (by decide)).trans hStaticH.jSrc, (hmS_6_23 t3OffTau2 (by decide) (by decide)).trans hStaticH.tau2,
      (hmS_6_23 t3OffPhiDen (by decide) (by decide)).trans hStaticH.phiDen, (hmS_6_23 t3OffMw (by decide) (by decide)).trans hStaticH.mw,
      (hmS_6_23 t3OffPhiNumC (by decide) (by decide)).trans hStaticH.phiNumC, (hmS_6_23 t3OffPhiDenC (by decide) (by decide)).trans hStaticH.phiDenC,
      (hmS_ptr_eq _ (by simp)).trans hmB_ptrs.2.1, (hmS_ptr_eq _ (by simp)).trans hmB_ptrs.2.2.1,
      (hmS_ptr_eq _ (by simp)).trans hmB_ptrs.2.2.2.1, (hmS_ptr_eq _ (by simp)).trans hmB_ptrs.2.2.2.2.1,
      (hmS_ptr_eq _ (by simp)).trans hmB_ptrs.2.2.2.2.2,
      by rw [hmemS]; simp [← hlb.1, t3OffVStmp, t3OffHCur, Nat.add_left_cancel_iff, hvst_eq],
      fun ci hci => by rw [hmemS_hi _ (by omega)]; exact hvo ci hci⟩
  have hmS_zero_mid : ∀ x, lay.embJWAddr ≤ x → x < lay.vhatOffsetAddr → memS x = 0 := fun x hx1 hx2 => by
    rw [hmS_lt x hx2 (by simp only [t3OffVStmp]; omega) (by simp only [t3OffHCur]; omega), hmB_eq_hi x hx1]; exact hStaticH.zfE x hx1
  refine hrest memS _ (by simp [hv0]) (by simp [hv1]) (by simp [hv2]) hStS
    (by rw [hmemS]; simp only [← hlb.1, Function.update_self, hend_eq])
    (fun x hx => by rw [hmemS_hi x (by omega)]; exact hzfV x (by omega))
    (fun i hi => by
      have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 30 ∨ i = 31 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; exact hi
      rw [hmS_lt _ (by omega) (by simp only [t3OffVStmp]; omega) (by simp only [t3OffHCur]; omega)]; exact hmB_zeros i hi)
    (fun x hx1 hx2 => hmS_zero_mid x hx1 (by omega)) (fun x hx1 hx2 => hmS_zero_mid x (by omega) (by omega))
    (fun x hx1 hx2 => hmS_zero_mid x (by omega) hx2)
    (fun x hx1 hx2 => by rw [hmemS_hi x (by omega)]; exact hzfV x (by omega))

private lemma t3Setup_ptrs_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} {ω : ℕ → Bool} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (memH regsH : ℕ → ℕ) (pos k T : ℕ) (hStaticH : T3StaticHdr ctx lay memH)
    (hr0 : regsH 0 = inp.jAddr) (hr1 : regsH 1 = inp.t1OutAddr) (hr2 : regsH 2 = inp.v2)
    (hr3 : regsH 3 = inp.J.m) (hr7 : regsH 7 = ctx.wd.comps.length)
    (hr8 : regsH 8 = ctx.memT1 (ctx.wInp.h + 12)) (hr10 : regsH 10 = ctx.wd.W.m)
    (sRest : Stmt) {Q : Outcome → State → ℕ → Prop}
    (hrest : ∀ mem_s regs_s,
      regs_s 0 = inp.jAddr → regs_s 1 = inp.t1OutAddr → regs_s 2 = inp.v2 →
      T3StaticMem ctx lay mem_s → mem_s (lay.base + t3OffHCur) = lay.staticEnd →
      WordRAM.ZeroFrom mem_s lay.staticEnd →
      (∀ i ∈ ([1, 2, 3, 4, 30, 31] : List ℕ), mem_s (lay.base + i) = 0) →
      (∀ x, lay.embJWAddr ≤ x → x < lay.dsHandlesAddr → mem_s x = 0) →
      (∀ x, lay.econgCountAddr ≤ x → x < lay.wDelStampAddr → mem_s x = 0) →
      (∀ x, lay.wDelStampAddr ≤ x → x < lay.vhatOffsetAddr → mem_s x = 0) →
      (∀ x, lay.vhatStampAddr ≤ x → x < lay.staticEnd → mem_s x = 0) →
      ∃ o stF c_s Φ', Runs w p ω sRest ⟨mem_s, regs_s, pos⟩ o stF c_s ∧ Q o stF Φ' ∧ (k + (30 * inp.J.m + 96)) + c_s + Φ' ≤ T) :
    let base := Expr.reg 2; let rJm := Expr.reg 3; let rK := Expr.reg 7
    let rWm := Expr.reg 10; let rPtr := Expr.reg 11; let rVOff := Expr.reg 12; let rVSum := Expr.reg 13
    let ptrsStmt :=
      Stmt.seq (.assign 11 (t3Add base (.const t3HdrSize))) (Stmt.seq (t3St base (.const t3OffEmbJW) rPtr)
        (Stmt.seq (.assign 11 (t3Add rPtr rJm)) (Stmt.seq (t3St base (.const t3OffDsHdl) rPtr)
          (Stmt.seq (.assign 11 (t3Add rPtr rK)) (Stmt.seq (t3St base (.const t3OffECnt) rPtr)
            (Stmt.seq (.assign 11 (t3Add rPtr rWm)) (Stmt.seq (t3St base (.const t3OffWDel) rPtr)
              (Stmt.seq (.assign 11 (t3Add rPtr rWm)) (Stmt.seq (t3St base (.const t3OffQueue) rPtr)
                (Stmt.seq (.assign 12 (t3Add rPtr rWm)) (Stmt.seq (t3St base (.const t3OffVOff) rVOff)
                  (Stmt.seq (.assign 13 (.const 0)) (Stmt.seq (t3ForRange 14 (.const 0) rK t3VhatLoopBody)
                    (Stmt.seq (.assign 11 (t3Add rVOff rK)) (Stmt.seq (t3St base (.const t3OffVStmp) rPtr)
                      (Stmt.seq (t3St base (.const t3OffHCur) (t3Add rPtr rVSum)) sRest))))))))))))))))
    ∃ o stF c_tot Φ', Runs w p ω ptrsStmt ⟨memH, regsH, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  dsimp only
  apply t3Setup_ptrs1_cps ctx lay hlay memH regsH pos k T hStaticH hr0 hr1 hr2 hr3 hr7 hr8 hr10
  intro memB regsB hb0 hb1 hb2 hb7 hb8 hb12 hb13 hmB_below hzfB hmB_eq_hi hmB_6_23 hmB_zeros hmB_ptrs
  apply t3_normal_ptriple_cps (t3VhatLoop_ptriple ctx lay hlay memB pos hmB_below hzfB)
    ⟨rfl, rfl, hb0, hb1, hb2, hb7, hb8, hb12, hb13, rfl⟩ (show _ ≤ 30 * inp.J.m + 7 from le_refl _)
  intro stV ΦV ⟨hvpos, hv0, hv1, hv2, hv7, _, hv12, hv13, _, hΦV, hmv, hzfV, hvo⟩
  subst hΦV
  exact t3Setup_ptrs2_cps ctx lay hlay memH memB stV pos (k + 69 + (30 * inp.J.m + 7) + 1) T hStaticH
    hmB_below hmB_eq_hi hmB_6_23 hmB_zeros hmB_ptrs hvpos hv0 hv1 hv2 hv7 hv12 hv13 hmv hzfV hvo sRest
    (fun ms rs h0 h1 h2 hs hh hz hz2 hm1 hm2 hm3 hm4 => by
      obtain ⟨o, stF, c_s, Φ', hr_s, hq_s, hc_s⟩ := hrest ms rs h0 h1 h2 hs hh hz hz2 hm1 hm2 hm3 hm4
      exact ⟨o, stF, c_s, Φ', hr_s, hq_s, by omega⟩)

/-- Setup prefix of `task3Body` through `.call 15 (selfBase + 1) [base]`, establishing
`T3OuterInv ctx lay 0 st_loop 0` in at most `140 * inp.J.m + 380` Word-RAM cycles. -/
lemma t3Setup_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    (selfBase dsBase phiNumConst phiDenConst : ℕ)
    (hprog : p.HasAt selfBase (task3Module phiNumConst phiDenConst selfBase dsBase))
    (hphiN : phiNumConst = impl.constructExpander.phiNum)
    (hphiD : phiDenConst = impl.constructExpander.phiDen)
    (mem : ℕ → ℕ) (regs : ℕ → ℕ) (pos k T : ℕ)
    (hbelow : ∀ x < inp.v2, mem x = mem₀ x) (hz2 : WordRAM.ZeroFrom mem inp.v2)
    (hr0 : regs 0 = inp.jAddr) (hr1 : regs 1 = inp.t1OutAddr) (hr2 : regs 2 = inp.v2)
    {Q : Outcome → State → ℕ → Prop}
    (hrest : ∀ st₁, T3OuterInv ctx lay 0 st₁ 0 →
      ∃ o stF c_s Φ', Runs w p ω
          (.seq (.loop (t3Eq (t3Ld (.reg 2) (.const t3OffCont)) (.const 1))
            (.call 15 (selfBase + 4) [.reg 2]))
            (.ret (t3Ld (.reg 2) (.const t3OffHCur))))
          st₁ o stF c_s ∧ Q o stF Φ' ∧ (k + (140 * inp.J.m + 380)) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ',
      Runs w p ω (task3Body phiNumConst phiDenConst selfBase) ⟨mem, regs, pos⟩ o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  have hlb := T3Layout.bounds ctx
  dsimp only at hlb; rw [← hlay] at hlb; simp only [t3HdrSize] at hlb
  dsimp only [task3Body]
  apply t3Setup_hdr1_cps ctx lay hlay mem regs pos k T hbelow hr0 hr1 hr2
  intro mem1 regs1 hh1
  have hm1_below : ∀ x < inp.v2, mem1 x = mem₀ x := fun x hx => (hh1.mb x hx).trans (hbelow x hx)
  apply t3Setup_hdr2_cps ctx lay hlay mem1 regs1 pos (k + 108) T hm1_below hh1.r2 hh1.r5
    phiNumConst phiDenConst hphiN hphiD
  intro mem2 hm2_lt hm2_hi h16 h17 h18 h19 h20 h21 h22 h23
  have hm2_16 : ∀ off, off < 16 → mem2 (lay.base + off) = mem1 (lay.base + off) :=
    fun off hoff => hm2_lt _ (by omega)
  have hStaticH : T3StaticHdr ctx lay mem2 :=
    ⟨fun x hx => (hm2_lt x (by omega)).trans (hm1_below x hx),
      fun i hi => by
        by_cases h16' : i < 16
        · have hi' : 1 ≤ i ∧ i < 6 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
          rw [hm2_lt _ (by omega), hh1.mlo _ (by omega) (by omega)]; exact hz2 _ (by omega)
        · have hi' : 29 ≤ i := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
          rw [hm2_hi _ (by omega), hh1.mhi _ (by omega)]; exact hz2 _ (by omega),
      fun x hx => by rw [hm2_hi x (by omega), hh1.mhi x (by omega)]; exact hz2 x (by omega),
      (hm2_16 _ (by decide)).trans hh1.jAddr, (hm2_16 _ (by decide)).trans hh1.t1Addr, (hm2_16 _ (by decide)).trans hh1.jm,
      (hm2_16 _ (by decide)).trans hh1.wm, (hm2_16 _ (by decide)).trans hh1.k, (hm2_16 _ (by decide)).trans hh1.prepH,
      (hm2_16 _ (by decide)).trans hh1.wInpH, (hm2_16 _ (by decide)).trans hh1.aComps, (hm2_16 _ (by decide)).trans hh1.aCompExt,
      (hm2_16 _ (by decide)).trans hh1.wAddr, h16, h17, h18, h19, h20, h21, h22, h23⟩
  apply t3Setup_ptrs_cps ctx lay hlay mem2 regs1 pos (k + 172) T hStaticH hh1.r0 hh1.r1 hh1.r2
    hh1.r3 hh1.r7 hh1.r8 hh1.r10
  intro mem_s regs_s hrs0 hrs1 hrs2 hStS hHCS hzfS hzerosS hembZS hecntZS hwdelZS hvstZS
  have hproc1 : p.procs[selfBase + 1]? = some t3InitEmbBody := by
    simpa [task3Module] using hprog.get (i := 1) (by dsimp [task3Module]; decide)
  obtain ⟨o₁, st₁, c₁, Φ₁, hr₁, hq₁, hc₁⟩ :=
    t3InitEmb_ptriple ctx lay hlay mem_s hStS hHCS hzfS hembZS hecntZS
      (startState [lay.base] mem_s pos) 0 ω ⟨rfl, rfl⟩
  rcases hq₁ with ⟨ret, rfl, hΦ₁0, hPost⟩
  subst hΦ₁0
  have hargs : evalArgs w ⟨mem_s, regs_s, pos⟩ [.reg 2] = some [lay.base] := by
    simp [evalArgs, hrs2, hlb.1, Expr.eval]
  have hcall : Runs w p ω (.call 15 (selfBase + 1) [.reg 2]) ⟨mem_s, regs_s, pos⟩ .normal
      { st₁ with regs := Function.update regs_s 15 ret } (1 + c₁ + 1) :=
    runs_call_iff.mpr ⟨[lay.base], t3InitEmbBody, .returned ret, st₁, c₁, hargs, hproc1, hr₁, rfl,
      rfl, by simp [argsSize]⟩
  set stL := { st₁ with regs := Function.update regs_s 15 ret }
  rcases hPost with ⟨hret_eq, hStL, hbmL, _, hwdL, hcontL, hh_lo, hh_hi, hzfL, hembL, hecntL⟩
  have hw_okWInp : ∀ {N_max : ℕ} {W_max : ℝ} (t : LocalSpannerTools N_max W_max),
      WitnessOK t ctx.wInp.H' ctx.wInp.prep.J ctx.wInp.embJH
        (ctx.wInp.mkWitnessData impl.constructExpander impl.pathDS.params ctx.WSubs) := by
    intro N_max W_max t; have h := ctx.hw_ok t; rw [← ctx.hWInpJ] at h
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13,
      h.14, h.15, h.16, h.17, h.18, h.19, h.20, h.21, h.22⟩
  have htp := ctx.hWInpJ ▸ t3Init_pure_inv ctx.hStat hw_okWInp ctx.hws
  have hemb_len_W : ∀ eJ < inp.J.m, (partialToWalk (initEmb2 inp.J ctx.wd) eJ).edges.length ≤
      impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) := by
    intro eJ heJ; have h1 := htp.2.2.1 eJ heJ
    dsimp only [T3Ctx.wd] at h1 ⊢
    have hdW : 1 ≤ WitnessCoreInput.dWInt impl.constructExpander := by
      have hpos := impl.constructExpander.hphi_pos; have hle := impl.constructExpander.hphi_le
      unfold WitnessCoreInput.dWInt; exact Nat.div_pos (by omega) hpos
    have hg := impl.pathDS.params.hgExp_ge (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J) hdW
    have hp := impl.pathDS.params.hphiOutDen_ge (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J) hdW
    omega
  have hcont_iff : (unembeddedSet2Pure inp.J (initEmb2 inp.J ctx.wd)).Nonempty ↔
      ∃ eJ < inp.J.m, ∃ ci jL, ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL := by
    simp only [Finset.Nonempty, unembeddedSet2Pure, Finset.mem_filter, Finset.mem_range, initEmb2]
    constructor
    · rintro ⟨eJ, heJ, hnone⟩; simp only [heJ, ↓reduceIte] at hnone
      cases hsrc : ctx.wd.jSources.getD eJ JEdgeSource.isLoop with
      | inComp ci jL => exact ⟨eJ, heJ, ci, jL, hsrc⟩
      | isLoop => dsimp only [List.getD] at hnone hsrc; rw [hsrc] at hnone; simp at hnone
      | inJ0 _ => dsimp only [List.getD] at hnone hsrc; rw [hsrc] at hnone; simp at hnone
    · rintro ⟨eJ, heJ, ci, jL, hsrc⟩; dsimp only [List.getD] at hsrc; exact ⟨eJ, heJ, by simp [heJ, hsrc]⟩
  have hecnt_zero : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      stL.mem (lay.econgCountAddr + eW) = 0 := fun eW heW =>
    (hecntL eW (Finset.mem_Ico.mp heW).2).trans
      (by dsimp only [T3Ctx.wd] at heW ⊢; exact htp.2.2.2.2.2.2.1 eW heW)
  have hwdel_zero : ∀ eW < ctx.wd.W.m, stL.mem (lay.wDelStampAddr + eW) = 0 := fun eW heW =>
    (hwdL (lay.wDelStampAddr + eW) (by omega) (by omega)).trans
      (hwdelZS (lay.wDelStampAddr + eW) (by omega) (by omega))
  have hephi0 : t3EcongPhi ctx lay stL.mem = 0 := by
    unfold t3EcongPhi; exact Finset.sum_eq_zero fun eW heW => by
      simp [hecnt_zero eW heW, hwdel_zero eW (Finset.mem_Ico.mp heW).2]
  have hbmL0 : ∀ i ∈ ([1, 2, 3, 4] : List ℕ), stL.mem (lay.base + i) = 0 := fun i hi => by
    have : 1 ≤ i ∧ i ≤ 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    exact (hbmL _ (by omega) (by simp [t3OffHCur]; omega) (by simp [t3OffCont]; omega)).trans
      (hzerosS i (by simp only [List.mem_cons] at hi ⊢; tauto))
  have hj0_m_le : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
    rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
  let d0 : T3OuterData :=
    { emb := initEmb2 inp.J ctx.wd, getPathCnt := 0, delCnt := 0, econgUpd := 0, hCur := ret }
  have hOuter : T3OuterInv ctx lay 0 stL 0 := by
    refine ⟨d0, ⟨by simp [stL, hrs0], by simp [stL, hrs1], by simp [stL, hrs2], hStL, hh_lo,
      by dsimp only [d0]; omega, hzfL, hbmL0 t3OffEta2 (by decide), hbmL0 t3OffGetPath (by decide),
      hbmL0 t3OffDel (by decide), hbmL0 t3OffEcongUpd (by decide), hret_eq.symm, ?_, htp.1, htp.2.1,
      htp.2.2.2.2.1, hemb_len_W, htp.2.2.2.1, hembL, hecntL,
      by dsimp only [T3Ctx.wd, d0]; simpa using htp.2.2.2.2.2.2.2.2.2,
      htp.2.2.2.2.2.2.2.1, fun eW heW => hwdel_zero eW (lt_of_lt_of_le heW hj0_m_le),
      fun eW heW => (hwdel_zero eW (Finset.mem_Ico.mp heW).2).symm ▸ ⟨Nat.le_refl 0, Nat.zero_le _⟩,
      ?_, Nat.zero_le _, ?_, by simp [d0], by simp [d0], Nat.le_refl _, ?_, ?_⟩⟩
    · dsimp only [d0]; rw [hcontL]; split_ifs with h1 h2 h2
      · rfl
      · exact absurd (hcont_iff.mpr h1) h2
      · exact absurd (hcont_iff.mp h2) h1
      · rfl
    · intro ci hci v hv
      have hvb : vhatBaseW ctx.wd ci + v < (ctx.wd.comps.map fun c => c.W_sub.n).sum := by
        have h1 := vhatBaseW_add_le hci; have h2 := vhatBaseW_le_sum (wd := ctx.wd) (ci := ci + 1); omega
      have hv0 : stL.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) = 0 :=
        (hwdL (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) (by omega) (by omega)).trans
          (hvstZS (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) (by omega) (by omega))
      exact hv0.symm ▸ Nat.le_refl 0
    · dsimp only [d0]; exact (Finset.sum_eq_zero fun eW heW => hecnt_zero eW heW).symm
    · simp only [pow_zero, one_mul, d0]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [Finset.card_range])
    · rw [hephi0, mul_zero]
  dsimp only at hc₁
  obtain ⟨o, stF, c_s, Φ', hr_s, hq_s, hc_s⟩ := hrest stL hOuter
  exact ⟨o, stF, (1 + c₁ + 1) + c_s + 1, Φ',
    runs_seq_iff.mpr (Or.inr ⟨stL, 1 + c₁ + 1, c_s, hcall, hr_s, rfl⟩), hq_s, by omega⟩

end MinCostFlow.Spanner
