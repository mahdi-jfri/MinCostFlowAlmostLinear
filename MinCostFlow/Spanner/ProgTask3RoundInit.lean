module

public import MinCostFlow.Spanner.ProgTask3MiddleHelpers

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# The PathDS Init Loop of a Task 3 Round

Each round of Task 3 (`t3RoundBody`) starts by building one fresh `PathDS` on every component
expander `W_sub`. The loop runs over the component index in register 8. Step `k` reads the heap
cursor from the header, stores it as the handle of component `k`, calls `Init` of the `PathDS`
on `W_sub` at that cursor, and writes the new cursor back.

The invariant `T3InitAt` says that after `k` steps the first `k` handles hold valid, fresh
`PathDS` states, that they live above the start cursor `hc0`, and that the rest of the memory
below `hc0` is unchanged. The main result is `t3InitLoop_ptriple`.
-/

/-- One step of the init loop of `t3RoundBody` (component index in register 8). -/
def t3InitStep (dsBase : ℕ) : Stmt :=
  Stmt.seq (.assign 9 (t3Ld (.reg 0) (.const t3OffHCur)))
    (Stmt.seq (.assign 10 (t3Ld (.reg 3) (t3Add (t3Mul (.const 6) (.reg 8)) (.const 1))))
      (Stmt.seq (.store (t3Add (.reg 4) (.reg 8)) (.reg 9))
        (Stmt.seq (.call 11 dsBase [.reg 10, .reg 5, .reg 6, .reg 7, .reg 9])
          (t3St (.reg 0) (.const t3OffHCur) (.reg 11)))))

/-- Invariant of the init loop after `k` steps. The start memory is `memS`, the start cursor is
`hc0`, and `Φ0` is the potential carried through the loop unchanged. -/
structure T3InitAt {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (rCur hc0 Φ0 : ℕ) (memS : ℕ → ℕ) (k : ℕ)
    (hCur : ℕ) (states : ℕ → PathDSAbsState) (reps : ℕ → impl.pathDS.R.τ)
    (st : State) (Φ : ℕ) : Prop where
  r0 : st.regs 0 = lay.base
  r1 : st.regs 1 = rCur
  r2 : st.regs 2 = ctx.wd.comps.length
  r3 : st.regs 3 = ctx.memT1 (ctx.wInp.h + 12)
  r4 : st.regs 4 = lay.dsHandlesAddr
  r5 : st.regs 5 = impl.constructExpander.phiNum
  r6 : st.regs 6 = impl.constructExpander.phiDen
  r7 : st.regs 7 = ctx.wd.M_W
  r8 : st.regs 8 = k
  agree : ∀ a < hc0, a ≠ lay.base + t3OffHCur → (∀ ci < k, a ≠ lay.dsHandlesAddr + ci) →
    st.mem a = memS a
  hCur_eq : st.mem (lay.base + t3OffHCur) = hCur
  hCur_lo : hc0 ≤ hCur
  hCur_le : hCur ≤ hc0 + k * Task3Input.dsOneW impl inp.J
  dsArr : DSArrayWAt impl.pathDS ctx.wd.comps impl.constructExpander.phiNum
    impl.constructExpander.phiDen ctx.wd.M_W w lay.staticEnd lay.dsHandlesAddr hCur st.mem k
    states reps
  fresh : ∀ ci < k, (states ci).Vhat = ∅ ∧ (states ci).deleted = ∅
  foot_hi : ∀ ci < k, ∀ a, impl.pathDS.R.foot (st.mem (lay.dsHandlesAddr + ci)) (reps ci) a →
    hc0 ≤ a
  phi : Φ = Φ0 + dsTotalPhi impl.pathDS lay.dsHandlesAddr k reps st.mem

/-- `T3InitAt` with the cursor and the `PathDS` ghost states hidden. -/
def T3InitInv {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (rCur hc0 Φ0 : ℕ) (memS : ℕ → ℕ) (k : ℕ)
    (st : State) (Φ : ℕ) : Prop :=
  ∃ hCur states reps, T3InitAt ctx lay rCur hc0 Φ0 memS k hCur states reps st Φ

/-- The tool constants `phiNum`, `phiDen` and the bound `M_W` fit in a word. They follow from
the word-size condition `cw · (log₂ X + 1) ≤ w` of `Task3Input.WordWidthOK`, with `cw ≥ 1`. -/
lemma t3_phi_word_bounds {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    impl.constructExpander.phiNum < 2 ^ w ∧ impl.constructExpander.phiDen < 2 ^ w ∧
      ctx.wd.M_W < 2 ^ w := by
  have hww : Task3Input.WordWidthOK impl inp w := ctx.hwokW
  simp only [Task3Input.WordWidthOK] at hww
  obtain ⟨_, hw, _⟩ := hww
  have hcw := impl.pathDS.params.hcw_pos
  set X := impl.constructExpander.phiDen + 4 * Task1Input.mwCap impl inp.J +
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J) + 2 with hX
  have hlog : Nat.log 2 X + 1 ≤ w := le_trans (Nat.le_mul_of_pos_left _ hcw) hw
  have hX_lt : X < 2 ^ w := lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) X)
    (Nat.pow_le_pow_right (by norm_num) hlog)
  have hMW : ctx.wd.M_W ≤ Task1Input.mwCap impl inp.J := ctx.hds_bounds.2.2.2.2.2.1
  have h1 := impl.constructExpander.hphi_le
  refine ⟨by omega, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
/-- One step of the init loop: it builds the `PathDS` of component `k`. -/
lemma t3InitStep_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    {rCur hc0 Φ0 : ℕ} {memS : ℕ → ℕ} (hS : T3StaticMem ctx lay memS)
    (hc0_lo : lay.staticEnd ≤ hc0)
    (hc0_w : hc0 + inp.J.m * Task3Input.dsOneW impl inp.J < 2 ^ w)
    {k : ℕ} (hk : k < ctx.wd.comps.length) :
    PTriple w p (T3InitInv ctx lay rCur hc0 Φ0 memS k) (t3InitStep dsBase)
      (pNormalPost fun st₁ Φ₁ =>
        T3InitInv ctx lay rCur hc0 Φ0 memS (k + 1)
          { st₁ with regs := Function.update st₁.regs 8 (k + 1) } Φ₁ ∧ st₁.regs 8 = k)
      (fun _ => ctx.wd.comps[k].W_sub.m * ⌈impl.pathDS.params.K_init *
        (impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
          (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 40) := by
  intro st Φ ω hI
  obtain ⟨hCur, states, reps, hs⟩ := hI
  have hLoc : impl.pathDS.R.Local := hSpec.1
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have hK_le := ctx.hK_le
  have hv1_le_v2 : ctx.v1 ≤ lay.base := by rw [hb1]; exact ctx.hv1_le
  obtain ⟨hpN_w, hpD_w, hM_w⟩ := t3_phi_word_bounds ctx
  -- Memory below `v2` is the input memory.
  have hbelow : ∀ x < inp.v2, st.mem x = mem₀ x := fun x hx =>
    (hs.agree x (by omega) (by unfold t3OffHCur; omega) (fun ci _ => by omega)).trans (hS.1 x hx)
  have hro := ctx.read_out_fields hbelow
  rcases hro with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hce_at, _, _, _, _, _, haExt_w, hwW_eq,
    hwS_eq, hjS_eq, hv1_eq⟩
  set aExt := ctx.memT1 (ctx.wInp.h + 12)
  obtain ⟨_, _, _, _, _, hG_at, hptr_lo, hptr_hi⟩ := hce_at k hk
  set c := ctx.wd.comps[k]
  set ptr := st.mem (aExt + 6 * k + 1)
  have hcp := ctx.hw_okW.comp_props k hk
  have hds_k := ctx.hds_bounds.1 k hk
  have hlo := hs.hCur_lo
  have hle := hs.hCur_le
  have hWlen : c.W_sub.encode.length = 2 + 2 * c.W_sub.m := graph_encode_length _
  -- Word bounds.
  have hkdsle : k * Task3Input.dsOneW impl inp.J + Task3Input.dsOneW impl inp.J ≤
      inp.J.m * Task3Input.dsOneW impl inp.J := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hsp : impl.pathDS.params.initSpace impl.constructExpander.phiNum
      impl.constructExpander.phiDen c.W_sub.n c.W_sub.m ctx.wd.M_W ≤ Task3Input.dsOneW impl inp.J :=
    hds_k.1
  have hCur_sp_w : hCur + impl.pathDS.params.initSpace impl.constructExpander.phiNum
      impl.constructExpander.phiDen c.W_sub.n c.W_sub.m ctx.wd.M_W < 2 ^ w := by
    have := hs.hCur_le; omega
  have hCur_w : hCur < 2 ^ w := by omega
  have hHC_w : lay.base + t3OffHCur < 2 ^ w := by unfold t3OffHCur; omega
  have hk_w : k < 2 ^ w := by omega
  have h6k_w : 6 * k < 2 ^ w := by omega
  have h6k1_w : 6 * k + 1 < 2 ^ w := by omega
  have haddr_w : aExt + (6 * k + 1) < 2 ^ w := by omega
  have hdl_w : lay.dsHandlesAddr + k < 2 ^ w := by omega
  have hptr_w : ptr < 2 ^ w := by omega
  -- Statement 1: `r9 := mem[base + HCur]`.
  let s9 : State := { mem := st.mem, regs := Function.update st.regs 9 hCur, pos := st.pos }
  have hr9 : Runs w p ω (.assign 9 (t3Ld (.reg 0) (.const t3OffHCur))) st .normal s9 5 := by
    have he := Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hs.r0)
      (Expr.eval_const (by unfold t3OffHCur; omega)) hHC_w) hs.hCur_eq
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, by simp [Expr.size, t3Ld, t3Add]⟩
  -- Statement 2: `r10 := mem[aExt + (6 k + 1)]`, the address of `W_sub`.
  let s10 : State := { mem := st.mem, regs := Function.update s9.regs 10 ptr, pos := st.pos }
  have hr10 : Runs w p ω (.assign 10 (t3Ld (.reg 3) (t3Add (t3Mul (.const 6) (.reg 8)) (.const 1))))
      s9 .normal s10 9 := by
    have h3 : s9.regs 3 = aExt := by
      simp (disch := decide) only [s9, Function.update_of_ne, hs.r3]; rfl
    have h8 : s9.regs 8 = k := by simp (disch := decide) only [s9, Function.update_of_ne, hs.r8]
    have he := Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h3)
      (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega : 6 < 2 ^ w))
        (Expr.eval_reg_of_eq h8) h6k_w) (Expr.eval_const (by omega : 1 < 2 ^ w)) h6k1_w) haddr_w)
      (show s9.mem (aExt + (6 * k + 1)) = ptr by simp only [s9, ptr, Nat.add_assoc])
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, by simp [Expr.size, t3Ld, t3Add, t3Mul]⟩
  -- Statement 3: store the handle `mem[hdl + k] := hCur`.
  let memB := Function.update st.mem (lay.dsHandlesAddr + k) hCur
  let sB : State := { mem := memB, regs := s10.regs, pos := st.pos }
  have hrB : Runs w p ω (.store (t3Add (.reg 4) (.reg 8)) (.reg 9)) s10 .normal sB 5 := by
    have h4 : s10.regs 4 = lay.dsHandlesAddr := by
      simp (disch := decide) only [s10, s9, Function.update_of_ne, hs.r4]
    have h8 : s10.regs 8 = k := by
      simp (disch := decide) only [s10, s9, Function.update_of_ne, hs.r8]
    have h9 : s10.regs 9 = hCur := by
      simp (disch := decide) only [s10, s9, Function.update_of_ne, Function.update_self]
    exact runs_store_iff.mpr ⟨_, _, Expr.eval_add (Expr.eval_reg_of_eq h4)
      (Expr.eval_reg_of_eq h8) hdl_w, Expr.eval_reg_of_eq h9, rfl, rfl, by simp [Expr.size, t3Add]⟩
  -- The array of the first `k` structures is unchanged by the handle store.
  have hDS_B := hs.dsArr.frame_range hLoc (mem' := memB)
    (fun ci hci => by
      have hne : lay.dsHandlesAddr + ci ≠ lay.dsHandlesAddr + k := by omega
      simp only [memB, Function.update_of_ne hne])
    (fun a ha1 _ => by
      have hne : a ≠ lay.dsHandlesAddr + k := by omega
      simp only [memB, Function.update_of_ne hne])
    (fun a ha => by
      have hne : a ≠ lay.dsHandlesAddr + k := by have := hs.dsArr.h_ge; omega
      simp only [memB, Function.update_of_ne hne]; exact hs.dsArr.zero_from a ha)
  have hG_B : GraphAt memB ptr c.W_sub := fun i hi => by
    have hne : ptr + i ≠ lay.dsHandlesAddr + k := by omega
    simp only [memB, Function.update_of_ne hne]; exact hG_at i hi
  have hcw : impl.pathDS.params.cw * (Nat.log 2 (c.W_sub.n + c.W_sub.m +
      impl.constructExpander.phiDen + ctx.wd.M_W + ⌈impl.pathDS.params.γ_ExpPath
        (↑impl.constructExpander.phiNum / ↑impl.constructExpander.phiDen) ctx.wd.M_W⌉₊ + 2) + 1)
      ≤ w := hds_k.2.2.2.1
  have hexp : c.W_sub.IsConductanceExpanderOn c.W_sub.verts
      (↑impl.constructExpander.phiNum / ↑impl.constructExpander.phiDen) := hcp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstep := hDS_B.1.step_init (pos := st.pos) (ω := ω) hSpec hk (by omega) hptr_w hpN_w hpD_w
    hM_w hCur_w (by rw [graph_encode_length]; omega) hG_B impl.constructExpander.hphi_pos
    impl.constructExpander.hphi_le hcp.2.2.2.2.2.2.2.2.2.2.2.2.1 hcp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hcp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun v hv => hcp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v (hcp.2.2.2.2.2.2.2.2.2.2.2.1 ▸ hv))
    hexp hcw hCur_sp_w
  obtain ⟨body, o_ds, st_ds, c_ds, s', x', hbody, hruns_ds, ho_le, ho_ge, hst_ds_lt, hft_new,
    hs'_vh, hs'_del, hDS', hPhi_ds⟩ := hstep
  have ho_le' : o_ds.value ≤ hCur + impl.pathDS.params.initSpace impl.constructExpander.phiNum
      impl.constructExpander.phiDen c.W_sub.n c.W_sub.m ctx.wd.M_W := ho_le
  set hCur' := o_ds.value
  have hge := hs.dsArr.h_ge
  have h_upd_eq : Function.update st_ds.mem (lay.dsHandlesAddr + k) hCur = st_ds.mem := by
    ext a
    by_cases ha : a = lay.dsHandlesAddr + k
    · subst ha
      rw [Function.update_self, hst_ds_lt _ (by omega)]
      simp only [memB, Function.update_self]
    · rw [Function.update_of_ne ha]
  rw [h_upd_eq] at hDS' hPhi_ds
  -- Statement 4: the call `r11 := Init(W_sub, phiNum, phiDen, M_W, hCur)`.
  let s11 : State := { mem := st_ds.mem, regs := Function.update sB.regs 11 hCur', pos := st_ds.pos }
  have hr11 : Runs w p ω (.call 11 dsBase [.reg 10, .reg 5, .reg 6, .reg 7, .reg 9])
      sB .normal s11 (5 + c_ds + 1) := by
    have h10 : sB.regs 10 = ptr := by
      simp (disch := decide) only [sB, s10, Function.update_self]
    have h5 : sB.regs 5 = impl.constructExpander.phiNum := by
      simp (disch := decide) only [sB, s10, s9, Function.update_of_ne, hs.r5]
    have h6 : sB.regs 6 = impl.constructExpander.phiDen := by
      simp (disch := decide) only [sB, s10, s9, Function.update_of_ne, hs.r6]
    have h7 : sB.regs 7 = ctx.wd.M_W := by
      simp (disch := decide) only [sB, s10, s9, Function.update_of_ne, hs.r7]
    have h9 : sB.regs 9 = hCur := by
      simp (disch := decide) only [sB, s10, s9, Function.update_of_ne, Function.update_self]
    refine runs_call_iff.mpr
      ⟨[ptr, impl.constructExpander.phiNum, impl.constructExpander.phiDen, ctx.wd.M_W, hCur],
        body, o_ds, st_ds, c_ds, ?_, hbody, hruns_ds, rfl, rfl, by simp [argsSize, Expr.size]⟩
    simp [evalArgs, Expr.eval_reg_of_eq h10, Expr.eval_reg_of_eq h5, Expr.eval_reg_of_eq h6,
      Expr.eval_reg_of_eq h7, Expr.eval_reg_of_eq h9]
  -- Statement 5: write the new cursor back, `mem[base + HCur] := r11`.
  have hCur'_w : hCur' < 2 ^ w := by omega
  let memF := Function.update st_ds.mem (lay.base + t3OffHCur) hCur'
  let sF : State := { mem := memF, regs := s11.regs, pos := st_ds.pos }
  have hrF : Runs w p ω (t3St (.reg 0) (.const t3OffHCur) (.reg 11)) s11 .normal sF 5 := by
    have h0 : s11.regs 0 = lay.base := by
      simp (disch := decide) only [s11, sB, s10, s9, Function.update_of_ne, hs.r0]
    have h11 : s11.regs 11 = hCur' := by
      simp (disch := decide) only [s11, Function.update_self]
    exact runs_store_iff.mpr ⟨_, _, Expr.eval_add (Expr.eval_reg_of_eq h0)
      (Expr.eval_const (by unfold t3OffHCur; omega)) hHC_w, Expr.eval_reg_of_eq h11, rfl, rfl,
      by simp [Expr.size, t3Add]⟩
  have hrun_tot := runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, hr9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 9, _, hr10,
      runs_seq_iff.mpr (Or.inr ⟨sB, 5, _, hrB,
        runs_seq_iff.mpr (Or.inr ⟨s11, 5 + c_ds + 1, _, hr11, hrF, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hHC_lt : lay.base + t3OffHCur < lay.staticEnd := by unfold t3OffHCur; omega
  have hDS_F := hDS'.frame_range hLoc (mem' := memF)
    (fun ci _ => by
      have hne : lay.dsHandlesAddr + ci ≠ lay.base + t3OffHCur := by unfold t3OffHCur; omega
      simp only [memF, Function.update_of_ne hne])
    (fun a ha1 _ => by
      have hne : a ≠ lay.base + t3OffHCur := by omega
      simp only [memF, Function.update_of_ne hne])
    (fun a ha => by
      have hne : a ≠ lay.base + t3OffHCur := by have := hDS'.h_ge; omega
      simp only [memF, Function.update_of_ne hne]; exact hDS'.zero_from a ha)
  let stOut : State := { sF with regs := Function.update sF.regs 8 (k + 1) }
  have hF_hdl : ∀ ci < k, memF (lay.dsHandlesAddr + ci) = st.mem (lay.dsHandlesAddr + ci) := by
    intro ci hci
    have hne : lay.dsHandlesAddr + ci ≠ lay.base + t3OffHCur := by unfold t3OffHCur; omega
    have hne2 : lay.dsHandlesAddr + ci ≠ lay.dsHandlesAddr + k := by omega
    simp only [memF, Function.update_of_ne hne]
    rw [hst_ds_lt _ (by omega)]
    simp only [memB, Function.update_of_ne hne2]
  have hinv : T3InitAt ctx lay rCur hc0 Φ0 memS (k + 1) hCur' (Function.update states k s')
      (Function.update reps k x') stOut
      (Φ0 + dsTotalPhi impl.pathDS lay.dsHandlesAddr (k + 1) (Function.update reps k x') memF) :=
    { r0 := by simp (disch := decide) only [stOut, sF, s11, sB, s10, s9, Function.update_of_ne, hs.r0]
      r1 := by simp (disch := decide) only [stOut, sF, s11, sB, s10, s9, Function.update_of_ne, hs.r1]
      r2 := by simp (disch := decide) only [stOut, sF, s11, sB, s10, s9, Function.update_of_ne, hs.r2]
      r3 := by simp (disch := decide) only [stOut, sF, s11, sB, s10, s9, Function.update_of_ne, hs.r3]
      r4 := by simp (disch := decide) only [stOut, sF, s11, sB, s10, s9, Function.update_of_ne, hs.r4]
      r5 := by simp (disch := decide) only [stOut, sF, s11, sB, s10, s9, Function.update_of_ne, hs.r5]
      r6 := by simp (disch := decide) only [stOut, sF, s11, sB, s10, s9, Function.update_of_ne, hs.r6]
      r7 := by simp (disch := decide) only [stOut, sF, s11, sB, s10, s9, Function.update_of_ne, hs.r7]
      r8 := by simp only [stOut, Function.update_self]
      agree := fun a ha hne5 hdl => by
        change memF a = memS a
        have hne_k : a ≠ lay.dsHandlesAddr + k := hdl k (Nat.lt_succ_self k)
        simp only [memF, Function.update_of_ne hne5]
        rw [hst_ds_lt a (by omega)]
        simp only [memB, Function.update_of_ne hne_k]
        exact hs.agree a ha hne5 fun ci hci => hdl ci (Nat.lt_succ_of_lt hci)
      hCur_eq := by simp only [stOut, sF, memF, Function.update_self]
      hCur_lo := le_trans hs.hCur_lo ho_ge
      hCur_le := by
        have := hs.hCur_le
        rw [Nat.succ_mul]; omega
      dsArr := hDS_F.1
      fresh := fun ci hci => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hci with hci' | rfl
        · simp [Function.update_of_ne (Nat.ne_of_lt hci'), hs.fresh ci hci']
        · simp [Function.update_self, hs'_vh, hs'_del]
      foot_hi := fun ci hci a ha => by
        change impl.pathDS.R.foot (memF (lay.dsHandlesAddr + ci)) _ a at ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp hci with hci' | rfl
        · rw [hF_hdl ci hci', Function.update_of_ne (Nat.ne_of_lt hci')] at ha
          exact hs.foot_hi ci hci' a ha
        · have hne : lay.dsHandlesAddr + ci ≠ lay.base + t3OffHCur := by unfold t3OffHCur; omega
          have hh : memF (lay.dsHandlesAddr + ci) = hCur := by
            simp only [memF, Function.update_of_ne hne]
            rw [hst_ds_lt _ (by omega)]
            simp only [memB, Function.update_self]
          rw [hh, Function.update_self] at ha
          exact le_trans hs.hCur_lo (hft_new a ha).1
      phi := rfl }
  have hs8 : sF.regs 8 = k := by
    simp (disch := decide) only [sF, s11, sB, s10, s9, Function.update_of_ne, hs.r8]
  refine ⟨.normal, sF, _, _, hrun_tot, ⟨⟨hCur', _, _, hinv⟩, hs8⟩, ?_⟩
  have hceil : ⌈impl.pathDS.params.K_init * (c.W_sub.m : ℝ) * impl.pathDS.params.γ_ExpPath
      (↑impl.constructExpander.phiNum / ↑impl.constructExpander.phiDen) ctx.wd.M_W⌉₊ ≤
      c.W_sub.m * ⌈impl.pathDS.params.K_init *
        (impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
          (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ := hds_k.2.2.2.2
  have hPhi_ds' : c_ds + dsTotalPhi impl.pathDS lay.dsHandlesAddr (k + 1)
      (Function.update reps k x') st_ds.mem ≤
      ⌈impl.pathDS.params.K_init * (c.W_sub.m : ℝ) * impl.pathDS.params.γ_ExpPath
        (↑impl.constructExpander.phiNum / ↑impl.constructExpander.phiDen) ctx.wd.M_W⌉₊ +
      dsTotalPhi impl.pathDS lay.dsHandlesAddr k reps memB := hPhi_ds
  rw [hs.phi, ← hDS_B.2, hDS_F.2]
  beta_reduce
  omega

/-- Every `PathDS` representation type is inhabited: run `Init` on a one-edge graph. -/
lemma t3_pathDS_nonempty_tau (pds : PathDSImpl) : Nonempty pds.R.τ := by
  let G : Cited.Graph := ⟨1, [(0, 0)]⟩
  let φ_r : ℝ := (1 : ℝ) / (1 : ℝ)
  let M_val : ℕ := 1
  let wBig := pds.params.cw * (Nat.log 2 (G.n + G.m + 1 + M_val +
    Nat.ceil (pds.params.γ_ExpPath φ_r M_val) + 2) + 1) +
    4 + pds.params.initSpace 1 1 G.n G.m M_val + 4
  have hBig_lt : 4 + pds.params.initSpace 1 1 G.n G.m M_val < 2 ^ wBig :=
    lt_of_lt_of_le (by omega) (le_of_lt (Nat.lt_two_pow_self (n := wBig)))
  let pBig : Program := { procs := pds.procs 0 }
  have hHas : pBig.HasAt 0 (pds.procs 0) := fun i hi => by simp [pBig, hi]
  have hSpec := pds.spec wBig pBig 0 hHas
  let memBig : ℕ → ℕ := fun i => G.encode.getD i 0
  have hArgs : ∀ a ∈ ([0, 1, 1, 1, 4] : List ℕ), a < 2 ^ wBig := fun a ha => by
    have ha4 : a ≤ 4 := by simp at ha; omega
    exact lt_of_le_of_lt (le_trans ha4 (Nat.le_add_right _ _)) hBig_lt
  have hGat : GraphAt memBig 0 G := by
    intro i hi
    simp only [G, Cited.Graph.encode, Cited.Graph.m, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_cons, List.length_nil] at hi ⊢
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  have hPre : (pathDSDataStructure pds.params wBig).initPre [0, 1, 1, 1, 4] memBig := by
    refine ⟨0, 1, 1, 1, 4, G, rfl, by simp [G, Cited.Graph.encode, Cited.Graph.m], hGat,
      le_rfl, le_rfl, ?_, by simp [G, Cited.Graph.m], by simp [G, Cited.Graph.m], ?_, ?_, ?_⟩
    · intro e he; simp [G] at he; subst he; simp [G]
    · intro v hv; have : v = 0 := by simpa [G] using hv
      subst this; simp [Cited.Graph.deg, Cited.Graph.degIn, Cited.Graph.inside, Cited.Graph.verts, G]
    · intro S hS hSne hSneX
      have hV : G.verts = {0} := by simp [Cited.Graph.verts, G]
      rw [hV] at hS hSneX
      rcases Finset.subset_singleton_iff.mp hS with rfl | rfl
      · exact False.elim (Finset.not_nonempty_empty hSne)
      · exact False.elim (hSneX rfl)
    · have hcast : ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = φ_r := by simp [φ_r]
      rw [hcast]; dsimp only [wBig, M_val]; omega
  have hZero : WordRAM.ZeroFrom memBig (heapArg [0, 1, 1, 1, 4]) := fun a ha => by
    have ha4 : 4 ≤ a := by simpa [heapArg] using ha
    simp only [memBig, G, Cited.Graph.encode, Cited.Graph.m]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
  have hSpace : heapArg [0, 1, 1, 1, 4] +
      (pathDSDataStructure pds.params wBig).initSpace [0, 1, 1, 1, 4] memBig < 2 ^ wBig := by
    have hread : Cited.readGraph memBig 0 = G := graphAt_iff_readGraph.mp hGat
    simp only [pathDSDataStructure, heapArg, List.getLastD_cons, List.getLastD_nil,
      List.getD_cons_zero, List.getD_cons_succ, hread]
    exact hBig_lt
  obtain ⟨_, _, _, _, _, _, _, x', _⟩ :=
    hSpec.2.1 [0, 1, 1, 1, 4] memBig 0 (fun _ => false) hArgs hPre hZero hSpace
  exact ⟨x'⟩

/-- The init loop of `t3RoundBody`. It starts from memory `memS` with cursor `hc0` and ends with
one fresh `PathDS` for every component. The cost is the sum of the `Init` costs plus a constant
per component. -/
lemma t3InitLoop_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    {rCur hc0 Φ0 : ℕ} {memS : ℕ → ℕ} (hS : T3StaticMem ctx lay memS)
    (hc0_lo : lay.staticEnd ≤ hc0)
    (hc0_w : hc0 + inp.J.m * Task3Input.dsOneW impl inp.J < 2 ^ w)
    (hHC : memS (lay.base + t3OffHCur) = hc0) (hZ : WordRAM.ZeroFrom memS hc0) :
    PTriple w p
      (fun st Φ => st.mem = memS ∧ Φ = Φ0 ∧ st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧
        st.regs 2 = ctx.wd.comps.length ∧ st.regs 3 = ctx.memT1 (ctx.wInp.h + 12) ∧
        st.regs 4 = lay.dsHandlesAddr ∧ st.regs 5 = impl.constructExpander.phiNum ∧
        st.regs 6 = impl.constructExpander.phiDen ∧ st.regs 7 = ctx.wd.M_W)
      (t3ForRange 8 (.const 0) (.reg 2) (t3InitStep dsBase))
      (pNormalPost (T3InitInv ctx lay rCur hc0 Φ0 memS ctx.wd.comps.length))
      (fun _ => Task1Input.mwCap impl inp.J * ⌈impl.pathDS.params.K_init *
        (impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
          (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 49 * inp.J.m + 7) := by
  set X := ⌈impl.pathDS.params.K_init *
    (impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ with hX
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hK_le := ctx.hK_le
  have hK_w : ctx.wd.comps.length < 2 ^ w := by omega
  obtain ⟨x_tau⟩ := t3_pathDS_nonempty_tau impl.pathDS
  have hfor := PTriple.forRange_le (w := w) (p := p)
    (P := fun st Φ => st.mem = memS ∧ Φ = Φ0 ∧ st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧
        st.regs 2 = ctx.wd.comps.length ∧ st.regs 3 = ctx.memT1 (ctx.wInp.h + 12) ∧
        st.regs 4 = lay.dsHandlesAddr ∧ st.regs 5 = impl.constructExpander.phiNum ∧
        st.regs 6 = impl.constructExpander.phiDen ∧ st.regs 7 = ctx.wd.M_W)
    (r := 8) (lo := .const 0) (hi := .reg 2) (body := t3InitStep dsBase)
    (Inv := T3InitInv ctx lay rCur hc0 Φ0 memS)
    (fun i => (ctx.wd.comps.getD i defaultCompInfo).W_sub.m * X + 40)
    0 ctx.wd.comps.length (Nat.zero_le _) ctx.hwokW.1 (fun _ => hK_w)
    (fun st Φ ⟨hm, hΦ, h0, h1, h2, h3, h4, h5, h6, h7⟩ => by
      refine ⟨Expr.eval_const (by omega), hc0,
        fun _ => { phiNum := 0, phiDen := 1, M := 0, G := ⟨0, []⟩, Vhat := ∅, deleted := ∅ },
        fun _ => x_tau, ?_⟩
      exact
        { r0 := by simpa [Function.update_of_ne] using h0
          r1 := by simpa [Function.update_of_ne] using h1
          r2 := by simpa [Function.update_of_ne] using h2
          r3 := by simpa [Function.update_of_ne] using h3
          r4 := by simpa [Function.update_of_ne] using h4
          r5 := by simpa [Function.update_of_ne] using h5
          r6 := by simpa [Function.update_of_ne] using h6
          r7 := by simpa [Function.update_of_ne] using h7
          r8 := by simp
          agree := fun a _ _ _ => by simp [hm]
          hCur_eq := by simp [hm, hHC]
          hCur_lo := le_rfl
          hCur_le := by simp
          dsArr :=
            { h_ge := hc0_lo
              zero_from := fun a ha => by simpa [hm] using hZ a ha
              at_ci := fun _ h => absurd h (Nat.not_lt_zero _)
              disjoint := fun _ h => absurd h (Nat.not_lt_zero _) }
          fresh := fun _ h => absurd h (Nat.not_lt_zero _)
          foot_hi := fun _ h => absurd h (Nat.not_lt_zero _)
          phi := by simp [dsTotalPhi, hΦ] })
    (fun _ _ _ _ _ hi => by obtain ⟨_, _, _, hi⟩ := hi; exact hi.r8)
    (fun _ _ _ _ _ hi => by obtain ⟨_, _, _, hi⟩ := hi; exact Expr.eval_reg_of_eq hi.r2)
    (fun i _ hi => by
      simpa only [List.getD_eq_getElem _ _ hi] using
        t3InitStep_ptriple ctx lay hlay hSpec (rCur := rCur) (Φ0 := Φ0) hS hc0_lo hc0_w hi)
  refine PTriple.conseq hfor (fun _ _ h => h) (fun _ _ _ h => h) fun _ _ _ => ?_
  have hsum : rangeCost (fun i => (ctx.wd.comps.getD i defaultCompInfo).W_sub.m * X + 40) 0
      ctx.wd.comps.length ≤ Task1Input.mwCap impl inp.J * X + 40 * ctx.wd.comps.length := by
    rw [rangeCost_zero_eq_sum, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_range, smul_eq_mul,
      sum_range_getD_nat ctx.wd.comps defaultCompInfo (fun c => c.W_sub.m), mul_comm _ 40]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ ctx.hsum_Wm_le) _
  have hsz1 : (Expr.reg 2).size = 1 := rfl
  have hsz2 : (Expr.const 0).size = 1 := rfl
  rw [hsz1, hsz2, Nat.sub_zero]
  omega

/-- With all `Vhat` sets empty, the count `t3VhatRem` of vertices not yet in `Vhat` is the total
number of vertices of the component expanders. -/
lemma t3VhatRem_of_fresh {wd : WitnessData} {states : ℕ → PathDSAbsState}
    (h : ∀ ci < wd.comps.length, (states ci).Vhat = ∅) :
    t3VhatRem wd states = (wd.comps.map fun c => c.W_sub.n).sum := by
  unfold t3VhatRem
  rw [← sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.W_sub.n)]
  refine Finset.sum_congr rfl fun ci hci => ?_
  rw [h ci (Finset.mem_range.mp hci)]
  simp

/-- After the init loop, the round invariant `T3RoundAt` holds for round `η + 1`. The loop starts
from the outer memory with `nextHasUnemb` reset to `0`. The potential of the loop start is the
outer potential plus `25` per vertex of the component expanders, which pays for the `Vhat`
term of `t3RoundPhi`. -/
lemma t3_roundAt_of_init {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {η : ℕ} {d0 : T3OuterData} {stO : State} {ΦO : ℕ} (hO : T3OuterAt ctx lay η d0 stO ΦO)
    (hEta : η + 1 ≤ eta2Bound inp.J)
    {Φ0 hCur : ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → impl.pathDS.R.τ} {st : State} {Φ : ℕ}
    (hI : T3InitAt ctx lay (η + 1) d0.hCur Φ0
      (Function.update stO.mem (lay.base + t3OffNextU) 0) ctx.wd.comps.length hCur states reps st Φ)
    (hΦ0 : Φ0 = t3KdelCost impl inp.J * t3EcongPhi ctx lay stO.mem +
      25 * (ctx.wd.comps.map fun c => c.W_sub.n).sum) :
    T3RoundAt ctx lay (η + 1)
      ⟨d0.emb, d0.getPathCnt, d0.delCnt, d0.econgUpd, hCur, states, reps, 0⟩ st Φ := by
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hK_le := ctx.hK_le
  have hlo := hO.hCur_lo
  -- Every cell below the start cursor, other than `HCur`, `NextU` and the handles, is unchanged.
  have hag : ∀ a < d0.hCur, a ≠ lay.base + t3OffHCur → a ≠ lay.base + t3OffNextU →
      (a < lay.dsHandlesAddr ∨ lay.dsHandlesAddr + ctx.wd.comps.length ≤ a) →
      st.mem a = stO.mem a := fun a ha h5 hN hh => by
    rw [hI.agree a ha h5 (fun ci hci => by omega), Function.update_of_ne hN]
  have hhdr : ∀ i < 32, i ≠ t3OffHCur → i ≠ t3OffNextU →
      st.mem (lay.base + i) = stO.mem (lay.base + i) := fun i hi h5 hN =>
    hag _ (by omega) (by omega) (by omega) (Or.inl (by omega))
  have hstat : ∀ a, lay.dsHandlesAddr + ctx.wd.comps.length ≤ a → a < lay.staticEnd →
      st.mem a = stO.mem a := fun a h1 h2 =>
    hag a (by omega) (by unfold t3OffHCur; omega) (by unfold t3OffNextU; omega) (Or.inr h1)
  have hτ := ctx.hw_okW.τ₂_pos
  have hj0 : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
    simp [T3Ctx.wd, WitnessCoreInput.mkWitnessData, Graph.m]
  have hvs : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (v : ℕ), v < ctx.wd.comps[ci].W_sub.n →
      st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) =
        stO.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) := fun ci hci v hv => by
    have h1 := vhatBaseW_add_le hci
    have h2 := vhatBaseW_le_sum (wd := ctx.wd) (ci := ci + 1)
    exact hstat _ (by omega) (by omega)
  have hecPhi : t3EcongPhi ctx lay st.mem = t3EcongPhi ctx lay stO.mem := by
    unfold t3EcongPhi
    refine Finset.sum_congr rfl fun eW heW => ?_
    have h := (Finset.mem_Ico.mp heW).2
    rw [hstat _ (by omega) (by omega), hstat (lay.wDelStampAddr + eW) (by omega) (by omega)]
  exact
    { rCur_pos := by omega
      rCur_le := hEta
      staticMem := hO.staticMem.mono
        (fun x hx => hag x (by omega) (by unfold t3OffHCur; omega) (by unfold t3OffNextU; omega)
          (Or.inl (by omega)))
        (fun i hi hE hG hD hU hH hN hC => hhdr i hi hH hN)
        (fun ci hci => hstat _ (by omega) (by omega))
      dsArr := hI.dsArr
      hCur_lo := le_trans hlo hI.hCur_lo
      hCur_bd := by
        have h1 := hI.hCur_le
        have h2 := hO.hCur_bd
        have h3 : ctx.wd.comps.length * Task3Input.dsOneW impl inp.J ≤
            inp.J.m * Task3Input.dsOneW impl inp.J := Nat.mul_le_mul_right _ hK_le
        have h4 : ((η + 1) * inp.J.m + d0.getPathCnt + d0.delCnt) * Task3Input.dsOneW impl inp.J =
            (η * inp.J.m + d0.getPathCnt + d0.delCnt) * Task3Input.dsOneW impl inp.J +
              inp.J.m * Task3Input.dsOneW impl inp.J := by ring
        dsimp only
        omega
      zero_from := hI.dsArr.zero_from
      eta2_eq := by
        rw [hhdr t3OffEta2 (by decide) (by decide) (by decide), hO.eta2_eq]
      getPath_eq := by
        rw [hhdr t3OffGetPath (by decide) (by decide) (by decide), hO.getPath_eq]
      del_eq := by rw [hhdr t3OffDel (by decide) (by decide) (by decide), hO.del_eq]
      econgUpd_eq := by
        rw [hhdr t3OffEcongUpd (by decide) (by decide) (by decide), hO.econgUpd_eq]
      hCur_eq := hI.hCur_eq
      nextU_eq := by
        change st.mem (lay.base + t3OffNextU) = 0
        rw [hI.agree _ (by unfold t3OffNextU; omega) (by unfold t3OffNextU t3OffHCur; omega)
          (fun ci hci => by unfold t3OffNextU; omega), Function.update_self]
      nextU_bin := Or.inl rfl
      emb_part := hO.emb_part
      emb_j0_cov := hO.emb_j0_cov
      emb_nodup := hO.emb_nodup
      emb_len_W := hO.emb_len_W
      emb_len_real := hO.emb_len_real
      emb_mem := fun eJ heJ => by
        have hm := hO.emb_mem eJ heJ
        have hslot : st.mem (lay.embJWAddr + eJ) = stO.mem (lay.embJWAddr + eJ) :=
          hag _ (by omega) (by unfold t3OffHCur; omega) (by unfold t3OffNextU; omega)
            (Or.inl (by omega))
        dsimp only
        rcases hE : d0.emb eJ with _ | P
        · rw [hE] at hm
          rw [hslot]; exact hm
        · rw [hE] at hm
          obtain ⟨h1, h2, h3⟩ := hm
          rw [hslot]
          refine ⟨h1, le_trans h2 hI.hCur_lo, t3_walkAt_of_agree h3 fun x hx1 hx2 =>
            hag x (by omega) (by unfold t3OffHCur; omega) (by unfold t3OffNextU; omega)
              (Or.inr (by omega)), ?_⟩
          intro a ha1 ha2 cj hcj hft
          have := hI.foot_hi cj hcj a hft
          omega
      econg_cnt_eq := fun eW heW => by
        rw [hstat _ (by omega) (by omega)]; exact hO.econg_cnt_eq eW heW
      econg_le_round := fun eW heW => by
        have h := hO.econg_le_round eW heW
        dsimp only
        push_cast
        nlinarith
      econg_j0_le := hO.econg_j0_le
      wdel_j0 := fun eW heW => by
        rw [hstat _ (by omega) (by omega)]; exact hO.wdel_j0 eW heW
      wdel_comp := fun eW heW => by
        have h := (Finset.mem_Ico.mp heW).2
        have h1 := hO.wdel_comp eW heW
        rw [hstat _ (by omega) (by omega), hstat (lay.econgCountAddr + eW) (by omega) (by omega)]
        omega
      wdel_thresh := fun eW heW heq => by
        have h := (Finset.mem_Ico.mp heW).2
        have h1 := hO.wdel_comp eW heW
        rw [hstat _ (by omega) (by omega)] at heq
        omega
      wdel_lt_econg := fun eW heW _ => by
        have h := hO.econg_le_round eW (Finset.mem_Ico.mp heW).2
        dsimp only
        push_cast
        nlinarith
      getPath_cnt_le := hO.getPath_cnt_le
      econgUpd_sum := hO.econgUpd_sum.trans (Finset.sum_congr rfl fun eW heW => by
        have h := (Finset.mem_Ico.mp heW).2
        exact (hstat _ (by omega) (by omega)).symm)
      econgUpd_bound := hO.econgUpd_bound
      econgUpd_W := hO.econgUpd_W
      del_le_econgUpd := hO.del_le_econgUpd
      del_iff := fun ci hci eL heL => by
        have hcp := ctx.hw_okW.comp_props ci hci
        have hws1 : ctx.wd.j0Edges.length ≤ ctx.wd.comps[ci].wStart :=
          hcp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hws2 : ctx.wd.comps[ci].wStart + ctx.wd.comps[ci].W_sub.m ≤ ctx.wd.W.m :=
          hcp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have h1 := hO.wdel_comp (ctx.wd.comps[ci].wStart + eL) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        rw [(hI.fresh ci hci).2, hstat _ (by omega) (by omega)]
        simp only [Finset.notMem_empty, false_iff]
        omega
      vhat_stmp_eq := fun ci hci v hv => by
        have h1 := hO.vhat_stmp_le ci hci v hv
        rw [(hI.fresh ci hci).1, hvs ci hci v hv]
        simp only [Finset.notMem_empty, iff_false]
        omega
      vhat_stmp_le := fun ci hci v hv => by
        have h1 := hO.vhat_stmp_le ci hci v hv
        rw [hvs ci hci v hv]; omega
      phi_eq := by
        unfold t3RoundPhi
        dsimp only
        rw [hI.phi, hΦ0, hecPhi, t3VhatRem_of_fresh fun ci hci => (hI.fresh ci hci).1]
        ring }

end MinCostFlow.Spanner
