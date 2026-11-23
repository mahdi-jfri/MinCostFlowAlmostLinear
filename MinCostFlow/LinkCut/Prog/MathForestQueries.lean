module

public import MinCostFlow.LinkCut.Prog.MathForestPathSetup

/-!
# Word-RAM Query Procedures (`connected`, `pathSum`) for `MathForest`

Implements deterministic (`Stmt.NoRand`) Word-RAM bodies `lctConnectedBody` and
`lctPathSumBody` and proves their full `LctMemRep` + `Respects` + `O((L + 1) log n)`
amortized bounds (van den Brand et al., `arXiv:2309.16629v1`, Lemma 4.1 p. 13, from
[KangP15] Section 4). The `pathMin` procedure lives in `MathForestPathMin.lean`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section SharedQueryHelpers

lemma arenaHi_bounds {w h L P b hp_caller : ℕ} {F : MathForest} {x₀ : LctConc}
    {mem₀ : ℕ → ℕ} (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller) (hhp_w : hp_caller < 2 ^ w) :
    lctArenaHi b (lctCap F.n) ≤ hp_caller ∧
    lctNodesBase b < 2 ^ w ∧
    b < 2 ^ w ∧
    36 < 2 ^ w ∧
    NODE_STRIDE < 2 ^ w ∧
    b + LCT_HDR_L < 2 ^ w ∧
    b + LCT_HDR_HP = lctNodesBase b - 1 ∧
    F.n + 1 < 2 ^ w ∧
    ∀ x off, 1 ≤ x → x ≤ lctCap F.n → off < NODE_STRIDE →
      lctNodesBase b + NODE_STRIDE * x + off < hp_caller ∧
      lctNodesBase b + NODE_STRIDE * x + off < 2 ^ w := by
  have hhp := hrep₀.hp_le_of_foot hfoot
  have harena : lctArenaHi b (lctCap F.n) ≤ hp_caller := le_trans hhp.1 hhp.2.1
  have hdef : lctArenaHi b (lctCap F.n) =
      b + LCT_HDR_SIZE + NODE_STRIDE * (2 * F.n + 1) := by
    unfold lctArenaHi lctNodesBase lctCap; rfl
  have harena' : b + LCT_HDR_SIZE + NODE_STRIDE * (2 * F.n + 1) ≤ hp_caller := hdef ▸ harena
  have h36 : 36 ≤ hp_caller := by
    unfold LCT_HDR_SIZE NODE_STRIDE at harena'
    have hmul : 30 ≤ 30 * (2 * F.n + 1) := Nat.le_mul_of_pos_right 30 (by omega)
    omega
  have hnb_le : lctNodesBase b ≤ hp_caller := by
    unfold lctArenaHi at harena; omega
  have hfn_le : F.n + 1 ≤ hp_caller := by
    unfold LCT_HDR_SIZE NODE_STRIDE at harena'
    have : F.n + 1 ≤ 30 * (2 * F.n + 1) := by
      have h2 : 1 ≤ 2 * F.n + 1 := by omega
      have h1 : F.n + 1 ≤ 2 * (2 * F.n + 1) := by omega
      exact le_trans h1 (Nat.mul_le_mul_right _ (by decide))
    omega
  refine ⟨harena, by unfold lctNodesBase LCT_HDR_SIZE at hnb_le ⊢; omega,
    by unfold lctNodesBase LCT_HDR_SIZE at hnb_le; omega, by omega,
    by unfold NODE_STRIDE; omega,
    by unfold lctNodesBase LCT_HDR_SIZE at hnb_le; unfold LCT_HDR_L; omega,
    by unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega, by omega, ?_⟩
  intro x off _ hx2 hoff
  have hlt : lctNodesBase b + NODE_STRIDE * x + off < lctArenaHi b (lctCap F.n) := by
    unfold lctArenaHi NODE_STRIDE at ⊢
    have hx1 : 30 * (x + 1) ≤ 30 * (lctCap F.n + 1) := Nat.mul_le_mul_left 30 (by omega)
    have hmul : 30 * x + 30 = 30 * (x + 1) := by ring
    unfold NODE_STRIDE at hoff
    omega
  exact ⟨lt_of_lt_of_le hlt harena, lt_trans (lt_of_lt_of_le hlt harena) hhp_w⟩

lemma room_lt_pow5 {a b c d e k p2w : ℕ} (hk : k ≤ e)
    (hbd : a + b + c + d + e < p2w) : a + k < p2w := by
  omega

lemma room_lt_pow6 {a b c d e f k p2w : ℕ} (hk : k ≤ e)
    (hbd : a + b + c + d + e + f < p2w) : a + k < p2w := by
  omega

lemma room_lt_pow6_tail {a b c d e f k p2w : ℕ} (hk : k ≤ e + f)
    (hbd : a + b + c + d + e + f < p2w) : a + k < p2w := by
  omega

end SharedQueryHelpers

section ConnectedProcedure

/-- Deterministic Word-RAM `connected` body taking `args = [b, u, v, hp_caller]`:
runs `findRoot` on `u` (at `hp_caller + 1`), reads `r_u`, runs `findRoot` on `v` (at `hp₁`),
reads `r_v`, stores `if r_u = r_v then 1 else 0` at `mem[hp_caller]`, and returns `hp₂`. -/
def lctConnectedBody (lp : LctProcs) : Stmt :=
  .assign 7 (.bin .add (.reg 3) (.const 1)) ;;
  .call 8 lp.findRoot [.reg 0, .reg 1, .reg 7] ;;
  .assign 10 (.load (.reg 7)) ;;
  .call 9 lp.findRoot [.reg 0, .reg 2, .reg 8] ;;
  .assign 11 (.load (.reg 8)) ;;
  .assign 12 (.bin .eq (.reg 10) (.reg 11)) ;;
  .store (.reg 3) (.reg 12) ;;
  .ret (.reg 9)

theorem lctConnectedBody_noRand (lp : LctProcs) : (lctConnectedBody lp).NoRand := by
  simp [lctConnectedBody, Stmt.NoRand]

private lemma conn_room1_arith {hp phi0 cf c_fr m p2w : ℕ}
    (hbd : hp + phi0 + cf + m + 4 < p2w) (hle : c_fr ≤ cf) :
    (hp + 1) + phi0 + c_fr + m + 2 < p2w := by
  omega

private lemma conn_room2_arith {c1 hp1 hp phi0 phi1 c_fr1 c_fr2 c_conn m p2w : ℕ}
    (hphi : c1 + (hp1 - (hp + 1)) + phi1 ≤ phi0 + c_fr1) (hle : hp + 1 ≤ hp1)
    (hsum : c_fr1 + c_fr2 ≤ c_conn) (hbd : hp + phi0 + c_conn + m + 4 < p2w) :
    hp1 + phi1 + c_fr2 + m + 2 < p2w := by
  omega

private lemma conn_cost_arith {c_tot c1 c2 hp hp1 hp2 phi0 phi1 phi2 c_fr c_conn space logN : ℕ}
    (h1 : c1 + (hp1 - (hp + 1)) + phi1 ≤ phi0 + c_fr * logN)
    (h2 : c2 + (hp2 - hp1) + phi2 ≤ phi1 + c_fr * logN)
    (hle1 : hp + 1 ≤ hp1) (hle2 : hp1 ≤ hp2)
    (hct : c_tot ≤ c1 + c2 + 45)
    (hk : 2 * c_fr + 50 ≤ c_conn) (hlog : 1 ≤ logN)
    (hsp : phi0 + c_conn * logN + 4 ≤ space) :
    hp2 ≤ hp + space ∧
      c_tot + (hp2 - hp) + phi2 ≤ phi0 + c_conn * logN := by
  have hmul : 2 * c_fr * logN + 50 * logN = (2 * c_fr + 50) * logN := by ring
  have h50 : 50 ≤ 50 * logN := Nat.le_mul_of_pos_right 50 hlog
  have hkc : (2 * c_fr + 50) * logN ≤ c_conn * logN := Nat.mul_le_mul_right logN hk
  have h2mul : 2 * (c_fr * logN) = 2 * c_fr * logN := by ring
  omega

private lemma conn_hp2_lt_arith {hp1 phi1 c_fr m hp2 sp2 p2w : ℕ}
    (hsp2 : sp2 = phi1 + c_fr + 2) (h2' : hp2 ≤ hp1 + sp2)
    (hroom : hp1 + phi1 + c_fr + m + 2 < p2w) : hp2 < p2w := by
  subst hsp2; omega

theorem lctConnectedBody_runs {w h L P b u v hp_caller space pos : ℕ}
    {F : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : u < F.n) (hv : v < F.n)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hhp_bd : hp_caller + lctPhi L mem₀ b F.n + C_CONNECTED_OP L * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 4 < 2 ^ w)
    (hsp_ge : lctPhi L mem₀ b F.n + C_CONNECTED_OP L * (Nat.log 2 (F.n + 2) + 1) + 4 ≤ space)
    (ω : ℕ → Bool) :
    ∃ hp_final st' c x',
      Runs w p ω (lctConnectedBody lp) (startState [b, u, v, hp_caller] mem₀ pos)
        (.returned hp_final) st' c ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_final b x' st'.mem ∧
      (st'.mem hp_caller = 1 ↔ F.SameComp u v) ∧
      st'.mem hp_caller ≤ 1 ∧
      c + (hp_final - hp_caller) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_CONNECTED_OP L * (Nat.log 2 (F.n + 2) + 1) := by
  have hlog_pos : 1 ≤ Nat.log 2 (F.n + 2) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hfr_le_conn : C_FINDROOT_OP L ≤ C_CONNECTED_OP L := by
    unfold C_FINDROOT_OP C_CONNECTED_OP; omega
  have hfr2_le_conn : 2 * C_FINDROOT_OP L + 50 ≤ C_CONNECTED_OP L := by
    unfold C_FINDROOT_OP C_CONNECTED_OP; omega
  have hroom1 : (hp_caller + 1) + lctPhi L mem₀ b F.n +
      C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) + 2 < 2 ^ w :=
    conn_room1_arith hhp_bd (Nat.mul_le_mul_right _ hfr_le_conn)
  have hfoot1 : ∀ a, lctFoot b x₀ a → a < hp_caller + 1 := fun a ha => Nat.lt_succ_of_lt (hfoot a ha)
  have hz1 : ZeroFrom mem₀ (hp_caller + 1) := fun a ha => hz₀ a (by omega)
  let sp1 := lctPhi L mem₀ b F.n + C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + 2
  have hhp1_w : hp_caller + 1 < 2 ^ w := room_lt_pow5 (by omega : 1 ≤ 4) hhp_bd
  have hhp_w : hp_caller < 2 ^ w := lt_trans (Nat.lt_succ_self _) hhp1_w
  rcases arenaHi_bounds hrep₀ hfoot hhp_w with ⟨_, _, hb_w, h36_w, _, _, _, hfn1_w, _⟩
  have hu_w : u < 2 ^ w := by omega
  have hv_w : v < 2 ^ w := by omega
  rcases lctFindRootBody_runs (pos := pos) p lp mem₀ hp_base hp_sp hexpose_eq hrep₀ hu hfoot1 hz1 hroom1
      (le_refl sp1) ω with
    ⟨hp₁, st₁, c₁, x₁, hrun₁, hrep₁, hresp₁, hmem₁_u, _hru_lt, hcanon1, hiff1, hphi1⟩
  have hhp1_ge : hp_caller + 1 ≤ hp₁ := hresp₁.1
  have hroom2 : hp₁ + lctPhi L st₁.mem b F.n +
      C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) + 2 < 2 ^ w := by
    have hsum : C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) +
        C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) ≤
        C_CONNECTED_OP L * (Nat.log 2 (F.n + 2) + 1) := by
      have hm : (2 * C_FINDROOT_OP L) * (Nat.log 2 (F.n + 2) + 1) ≤
          C_CONNECTED_OP L * (Nat.log 2 (F.n + 2) + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2m : 2 * C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) =
          C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) +
            C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) := by ring
      omega
    exact conn_room2_arith hphi1 hhp1_ge hsum hhp_bd
  have hfoot2 : ∀ a, lctFoot b x₁ a → a < hp₁ := LctMemRep.foot_lt_of_respects hfoot1 hresp₁
  have hz2 : ZeroFrom st₁.mem hp₁ := LctMemRep.zeroFrom_of_respects hresp₁
  let sp2 := lctPhi L st₁.mem b F.n + C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + 2
  rcases lctFindRootBody_runs (pos := st₁.pos) p lp st₁.mem hp_base hp_sp hexpose_eq hrep₁ hv
      hfoot2 hz2 hroom2 (le_refl sp2) ω with
    ⟨hp₂, st₂, c₂, x₂, hrun₂, hrep₂, hresp₂, hmem₂_v, _hrv_lt, _, _, hphi2⟩
  have hhp2_ge : hp₁ ≤ hp₂ := hresp₂.1
  have hhp2_w : hp₂ < 2 ^ w := conn_hp2_lt_arith rfl hresp₂.2.1 hroom2
  have hhp1_lt_w : hp₁ < 2 ^ w := lt_of_le_of_lt hhp2_ge hhp2_w
  have hw_ge2 : 1 < 2 ^ w := lt_trans (by decide) h36_w
  let r_u := lctCanonRoot mem₀ b F.n u
  let r_v := lctCanonRoot mem₀ b F.n v
  have hrv_eq : st₂.mem hp₁ = r_v := by rw [hmem₂_v, hcanon1 v]
  have harith := conn_cost_arith (c_tot := 4 + ((3 + c₁ + 1) + (3 + ((3 + c₂ + 1) +
    (3 + (4 + (3 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    hphi1 hphi2 hhp1_ge hhp2_ge (by omega) hfr2_le_conn hlog_pos hsp_ge
  let st_init := startState [b, u, v, hp_caller] mem₀ pos
  let s1 := { st_init with regs := Function.update st_init.regs 7 (hp_caller + 1) }
  have hs1 : Runs w p ω (.assign 7 (.bin .add (.reg 3) (.const 1))) st_init .normal s1 4 :=
    runs_assign_iff.mpr ⟨hp_caller + 1, Expr.eval_add (Expr.eval_reg_of_eq rfl)
      (Expr.eval_const hw_ge2) hhp1_w, rfl, rfl, by decide⟩
  let rB := Function.update s1.regs 8 hp₁
  have hs1_args : s1.regs 0 = b ∧ s1.regs 1 = u ∧ s1.regs 3 = hp_caller ∧ s1.regs 7 = hp_caller + 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [s1, st_init, startState, Function.update_of_ne]
  have hcall1 : Runs w p ω (.call 8 lp.findRoot [.reg 0, .reg 1, .reg 7]) s1 .normal
      { mem := st₁.mem, regs := rB, pos := st₁.pos } (3 + c₁ + 1) :=
    runs_call_iff.mpr ⟨[b, u, hp_caller + 1], lctFindRootBody lp, .returned hp₁, st₁, c₁,
      by simp [evalArgs, Expr.eval, hs1_args], hfr_eq, hrun₁, rfl, by cases st₁; rfl, rfl⟩
  let s3 : State := { mem := st₁.mem, regs := Function.update rB 10 r_u, pos := st₁.pos }
  have hs3 : Runs w p ω (.assign 10 (.load (.reg 7)))
      { mem := st₁.mem, regs := rB, pos := st₁.pos } .normal s3 3 := by
    refine runs_assign_iff.mpr ⟨r_u, ?_, rfl, rfl, by decide⟩
    have hreg7 : ({ mem := st₁.mem, regs := rB, pos := st₁.pos } : State).regs 7 = hp_caller + 1 := by
      simp [rB, Function.update_of_ne, hs1_args]
    rw [Expr.eval_load (Expr.eval_reg_of_eq hreg7)]
    simp [r_u, hmem₁_u]
  let rC := Function.update s3.regs 9 hp₂
  have hs3_args : s3.regs 0 = b ∧ s3.regs 2 = v ∧ s3.regs 8 = hp₁ ∧ s3.regs 10 = r_u ∧ s3.regs 3 = hp_caller := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [s3, rB, s1, st_init, startState, Function.update_of_ne]
  have hcall2 : Runs w p ω (.call 9 lp.findRoot [.reg 0, .reg 2, .reg 8]) s3 .normal
      { mem := st₂.mem, regs := rC, pos := st₂.pos } (3 + c₂ + 1) :=
    runs_call_iff.mpr ⟨[b, v, hp₁], lctFindRootBody lp, .returned hp₂, st₂, c₂,
      by simp [evalArgs, Expr.eval, hs3_args], hfr_eq, hrun₂, rfl, by cases st₂; rfl, rfl⟩
  let s5 : State := { mem := st₂.mem, regs := Function.update rC 11 r_v, pos := st₂.pos }
  have hs5 : Runs w p ω (.assign 11 (.load (.reg 8)))
      { mem := st₂.mem, regs := rC, pos := st₂.pos } .normal s5 3 := by
    refine runs_assign_iff.mpr ⟨r_v, ?_, rfl, rfl, by decide⟩
    have hreg8 : ({ mem := st₂.mem, regs := rC, pos := st₂.pos } : State).regs 8 = hp₁ := by
      simp [rC, Function.update_of_ne, hs3_args]
    rw [Expr.eval_load (Expr.eval_reg_of_eq hreg8)]
    simp [r_v, hrv_eq]
  let ans := if r_u = r_v then 1 else 0
  have hans_w : ans < 2 ^ w := by dsimp only [ans]; split_ifs <;> omega
  let s6 : State := { mem := st₂.mem, regs := Function.update s5.regs 12 ans, pos := st₂.pos }
  have hs6 : Runs w p ω (.assign 12 (.bin .eq (.reg 10) (.reg 11))) s5 .normal s6 4 := by
    refine runs_assign_iff.mpr ⟨ans, ?_, rfl, rfl, by decide⟩
    have hr10 : s5.regs 10 = r_u := by simp [s5, rC, Function.update_of_ne, hs3_args]
    have hr11 : s5.regs 11 = r_v := by simp [s5]
    have hev := Expr.eval_bin (op := .eq) (Expr.eval_reg_of_eq (st := s5) hr10)
      (Expr.eval_reg_of_eq (st := s5) hr11) (by simpa [BinOp.eval, ans] using hans_w)
    simpa [BinOp.eval, ans] using hev
  let mem_fin := Function.update st₂.mem hp_caller ans
  let s7 : State := { mem := mem_fin, regs := s6.regs, pos := st₂.pos }
  have hs7 : Runs w p ω (.store (.reg 3) (.reg 12)) s6 .normal s7 3 :=
    runs_store_iff.mpr ⟨hp_caller, ans,
      Expr.eval_reg_of_eq (by simp [s6, s5, rC, Function.update_of_ne, hs3_args]),
      Expr.eval_reg_of_eq (by simp [s6]), rfl, rfl, by decide⟩
  have hs8 : Runs w p ω (.ret (.reg 9)) s7 (.returned hp₂) s7 2 :=
    runs_ret_iff.mpr ⟨hp₂, Expr.eval_reg_of_eq (by simp [s7, s6, s5, rC, Function.update_of_ne]),
      rfl, rfl, by decide⟩
  have hrun_full :=
    runs_seq_normal hs1 (runs_seq_normal hcall1 (runs_seq_normal hs3 (runs_seq_normal hcall2
      (runs_seq_normal hs5 (runs_seq_normal hs6 (runs_seq_normal hs7 hs8))))))
  have hnot_ft2 : ¬ lctFoot b x₂ hp_caller := by
    intro hf
    rcases hresp₂.2.2.2.2 hp_caller hf with hf1 | ⟨hlo, _⟩
    · rcases hresp₁.2.2.2.2 hp_caller hf1 with hf0 | ⟨hlo0, _⟩
      · exact absurd (hfoot hp_caller hf0) (by omega)
      · omega
    · omega
  have hag_loc : ∀ a, lctFoot b x₂ a → st₂.mem a = mem_fin a := fun a ha => by
    have hne : a ≠ hp_caller := fun heq => hnot_ft2 (heq ▸ ha)
    exact (Function.update_of_ne hne ans st₂.mem).symm
  have hloc := lctDSRep_local w h L P b F x₂ st₂.mem mem_fin hag_loc
  have hrep_fin : LctMemRep w h L P b F x₂ mem_fin := hloc.1 hrep₂
  have hphi_fin : lctPhi L mem_fin b F.n = lctPhi L st₂.mem b F.n := by
    simpa [lctDSRep, hrep₂.2.2.2.2.1] using hloc.2.symm
  have hresp_fin : (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp₂ b x₂ mem_fin := by
    refine ⟨by omega, harith.1, ?_, ?_, ?_⟩
    · intro a ha
      dsimp only [mem_fin]
      rw [Function.update_of_ne (by omega : a ≠ hp_caller)]
      exact hresp₂.2.2.1 a ha
    · intro a ha_lt hnot
      dsimp only [mem_fin]
      rw [Function.update_of_ne (by omega : a ≠ hp_caller)]
      have hnf1 : ¬ lctFoot b x₁ a := fun hf1 => by
        rcases hresp₁.2.2.2.2 a hf1 with hf0 | ⟨hlo, _⟩
        · exact hnot hf0
        · omega
      exact (hresp₂.2.2.2.1 a (by omega) hnf1).trans (hresp₁.2.2.2.1 a (by omega) hnot)
    · intro a ha2
      rcases hresp₂.2.2.2.2 a ha2 with ha1 | ⟨_, ha_hi⟩
      · rcases hresp₁.2.2.2.2 a ha1 with ha0 | ⟨_, _⟩
        · exact Or.inl ha0
        · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, ha_hi⟩
  have hiff_ans : mem_fin hp_caller = 1 ↔ F.SameComp u v := by
    have hif : r_v = r_u ↔ F.SameComp v u := by
      simpa [r_u, r_v, hmem₁_u] using hiff1 v hv
    have hm_eq : mem_fin hp_caller = ans := Function.update_self _ _ _
    rw [hm_eq]
    dsimp only [ans]
    constructor
    · intro h1
      by_cases he : r_u = r_v
      · exact (hif.1 he.symm).symm
      · simp [he] at h1
    · intro hsc
      have he : r_u = r_v := (hif.2 hsc.symm).symm
      simp [he]
  have hle_ans : mem_fin hp_caller ≤ 1 := by
    have hm_eq : mem_fin hp_caller = ans := Function.update_self _ _ _
    rw [hm_eq]; dsimp only [ans]; split_ifs <;> omega
  refine ⟨hp₂, s7, _, x₂, hrun_full, hrep_fin, hresp_fin, hiff_ans, hle_ans, ?_⟩
  change _ + (hp₂ - hp_caller) + lctPhi L mem_fin b F.n ≤ _
  rw [hphi_fin]
  exact harith.2

end ConnectedProcedure

section PathSumProcedure

/-- Deterministic Word-RAM `pathSum` body taking `args = [b, u, v, hp_caller]`:
allocates `L` answer words at `hp_caller`, rerroots `u`, exposes `v`, copies `OFF_CSUM_FWD`
of `(v + 1)` to `hp_caller` when non-null (otherwise `[hp_caller, hp_caller + L)` remains zero
by `ZeroFrom`), and returns `hp_final`. -/
def lctPathSumBody (lp : LctProcs) : Stmt :=
  .assign 4 (.reg 3) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))) ;;
  .assign 6 (.reg 0) ;;
  .assign 7 (.bin .add (.reg 0) (.const LCT_HDR_SIZE)) ;;
  .assign 8 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 9 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 10 (.bin .add (.reg 4) (.reg 5)) ;;
  .store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 10) ;;
  .call 12 lp.reroot [.reg 7, .reg 8] ;;
  .call 12 lp.expose [.reg 7, .reg 9] ;;
  .assign 11 (.load (.bin .add (.bin .add (.reg 7) (.bin .mul (.const NODE_STRIDE) (.reg 9)))
    (.const OFF_CSUM_FWD))) ;;
  .cond (.reg 11) (.call 12 lp.copyWords [.reg 11, .reg 4, .reg 5]) .nop ;;
  .assign 13 (.load (.bin .add (.reg 6) (.const LCT_HDR_HP))) ;;
  .ret (.bin .add (.reg 13) (.const 1))

theorem lctPathSumBody_noRand (lp : LctProcs) : (lctPathSumBody lp).NoRand := by
  simp [lctPathSumBody, Stmt.NoRand]

private lemma pathSum_room_arith {hp L phi0 ce1 ce2 cp m p2w : ℕ}
    (hce : ce1 ≤ cp) (_hle : L + 1 ≤ ce2)
    (hbd : hp + phi0 + cp + m + L + 1 < p2w) :
    (hp + L) + phi0 + ce1 + m + 1 < p2w := by
  omega

private lemma pathSum_cost_arith {c_tot c_re c_exp s hp L phi0 phi2 cr ce cp space logN : ℕ}
    (h1 : c_re + c_exp + (s - (hp + L)) + phi2 ≤ phi0 + (cr + ce) * logN)
    (_hle : hp + L ≤ s) (hct : c_tot ≤ c_re + c_exp + 17 * L + 120)
    (hk : cr + ce + 10000 * (L + 1) ≤ cp) (hlog : 1 ≤ logN)
    (hsp : phi0 + cp * logN + L + 1 ≤ space) :
    s + 1 ≤ hp + space ∧ c_tot + (s + 1 - hp) + phi2 ≤ phi0 + cp * logN := by
  have h100 : 18 * L + 121 ≤ 10000 * (L + 1) * logN := by
    have h1' : 18 * L + 121 ≤ 10000 * (L + 1) := by omega
    exact le_trans h1' (Nat.le_mul_of_pos_right _ hlog)
  have hexp : (cr + ce) * logN + 10000 * (L + 1) * logN = (cr + ce + 10000 * (L + 1)) * logN := by ring
  have hkc : (cr + ce + 10000 * (L + 1)) * logN ≤ cp * logN := Nat.mul_le_mul_right logN hk
  omega

private lemma TreeMemMatch.root_csumFwd_optOk {w h L cap p pp x nb : ℕ} {l r : AuxTree}
    {mem : ℕ → ℕ} (hm : TreeMemMatch w h L mem nb cap (.node x l r) p pp) :
    OptNumPtrOk mem (nb + NODE_STRIDE * (cap + 1)) (mem (nb - 1)) h L
      (nodeField mem nb x OFF_CSUM_FWD) := by
  rw [TreeMemMatch.eq_2] at hm
  exact hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lctPathSumBody_runs {w h L P b u v hp_caller space pos : ℕ}
    {F : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : u < F.n) (hv : v < F.n) (hsc : F.SameComp u v)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hhp_bd : hp_caller + lctPhi L mem₀ b F.n + C_PATHSUM_OP L * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + L + 1 < 2 ^ w)
    (hsp_ge : lctPhi L mem₀ b F.n + C_PATHSUM_OP L * (Nat.log 2 (F.n + 2) + 1) + L + 1 ≤ space)
    (ω : ℕ → Bool) :
    ∃ hp_final st' c x',
      Runs w p ω (lctPathSumBody lp) (startState [b, u, v, hp_caller] mem₀ pos)
        (.returned hp_final) st' c ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_final b x' st'.mem ∧
      Valid st'.mem hp_caller h L ∧
      intVal st'.mem hp_caller h L = wrap h L (F.pathSum u v) ∧
      c + (hp_final - hp_caller) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_PATHSUM_OP L * (Nat.log 2 (F.n + 2) + 1) ∧
      RerootRoots mem₀ st'.mem b F u := by
  have hlog_pos : 1 ≤ Nat.log 2 (F.n + 2) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hre_le : C_REROOT_OP L + C_EXPOSE_OP L + 10000 * (L + 1) ≤ C_PATHSUM_OP L := by
    unfold C_REROOT_OP C_EXPOSE_OP C_PATHSUM_OP; omega
  have hroom_re : (hp_caller + L) + lctPhi L mem₀ b F.n +
      (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w := by
    have hm : (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) ≤
        C_PATHSUM_OP L * (Nat.log 2 (F.n + 2) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    exact pathSum_room_arith (ce2 := L + 1) hm (le_refl _) hhp_bd
  let nb := lctNodesBase b
  let cap := lctCap F.n
  let hp_eff := hp_caller + L
  let mem₁ := Function.update mem₀ (nb - 1) hp_eff
  have hhp_ge : hp_caller ≤ hp_eff := Nat.le_add_right _ _
  have hhpeff_w : hp_eff < 2 ^ w := room_lt_pow6 (by omega : L ≤ L) hhp_bd
  have hhp_w : hp_caller < 2 ^ w := lt_of_le_of_lt hhp_ge hhpeff_w
  rcases arenaHi_bounds hrep₀ hfoot hhp_w with
    ⟨harena_hp, hnb_w, hb_w, h36_w, hstr_w, hbh_lt, hbh_hp, hfn1_w, hnode_lt⟩
  have hu1_w : u + 1 < 2 ^ w := by omega
  have hv1_w : v + 1 < 2 ^ w := by omega
  have hL_w : L < 2 ^ w := by omega
  let st_init := startState [b, u, v, hp_caller] mem₀ pos
  let s1 := { st_init with regs := Function.update st_init.regs 4 hp_caller }
  let s2 := { s1 with regs := Function.update s1.regs 5 L }
  let s3 := { s2 with regs := Function.update s2.regs 6 b }
  let s4 := { s3 with regs := Function.update s3.regs 7 nb }
  let s5 := { s4 with regs := Function.update s4.regs 8 (u + 1) }
  let s6 := { s5 with regs := Function.update s5.regs 9 (v + 1) }
  let s7 := { s6 with regs := Function.update s6.regs 10 hp_eff }
  let st_pre_re : State := { mem := mem₁, regs := s7.regs, pos := pos }
  have hs1 : Runs w p ω (.assign 4 (.reg 3)) st_init .normal s1 2 :=
    runs_assign_iff.mpr ⟨hp_caller, Expr.eval_reg_of_eq rfl, rfl, rfl, by decide⟩
  have hs2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const LCT_HDR_L)))) s1 .normal s2 5 := by
    refine runs_assign_iff.mpr ⟨L, ?_, rfl, rfl, by decide⟩
    have hadd := Expr.eval_add (Expr.eval_reg_of_eq (st := s1) (r := 0) (by simp [s1, st_init, startState]))
      (Expr.eval_const (lt_trans (by decide : LCT_HDR_L < 36) h36_w)) hbh_lt
    rw [Expr.eval_load hadd]; simp [s1, st_init, startState, hrep₀.2.2.2.2.2.2.2.2.2.2.2.1]
  have hs3 : Runs w p ω (.assign 6 (.reg 0)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨b, Expr.eval_reg_of_eq (by simp [s2, s1, st_init, startState, Function.update_of_ne]),
      rfl, rfl, by decide⟩
  have hs4 : Runs w p ω (.assign 7 (.bin .add (.reg 0) (.const LCT_HDR_SIZE))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_add (Expr.eval_reg_of_eq
      (by simp [s3, s2, s1, st_init, startState, Function.update_of_ne]))
      (Expr.eval_const (lt_trans (by decide : LCT_HDR_SIZE < 36) h36_w)) hnb_w,
      rfl, rfl, by decide⟩
  have hs5 : Runs w p ω (.assign 8 (.bin .add (.reg 1) (.const 1))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨u + 1, Expr.eval_add (Expr.eval_reg_of_eq
      (by simp [s4, s3, s2, s1, st_init, startState, Function.update_of_ne]))
      (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w)) hu1_w, rfl, rfl, by decide⟩
  have hs6 : Runs w p ω (.assign 9 (.bin .add (.reg 2) (.const 1))) s5 .normal s6 4 :=
    runs_assign_iff.mpr ⟨v + 1, Expr.eval_add (Expr.eval_reg_of_eq
      (by simp [s5, s4, s3, s2, s1, st_init, startState, Function.update_of_ne]))
      (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w)) hv1_w, rfl, rfl, by decide⟩
  have hs7 : Runs w p ω (.assign 10 (.bin .add (.reg 4) (.reg 5))) s6 .normal s7 4 :=
    runs_assign_iff.mpr ⟨hp_eff, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne]))
      (Expr.eval_reg_of_eq (by simp [s6, s5, s4, s3, s2, Function.update_of_ne])) hhpeff_w, rfl, rfl, by decide⟩
  have hs8 : Runs w p ω (.store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 10)) s7 .normal st_pre_re 5 := by
    refine runs_store_iff.mpr ⟨nb - 1, hp_eff, ?_, Expr.eval_reg_of_eq (by simp [s7]), rfl, ?_, by decide⟩
    · rw [← hbh_hp]
      exact Expr.eval_add (Expr.eval_reg_of_eq
        (by simp [s7, s6, s5, s4, s3, s2, s1, st_init, startState, Function.update_of_ne]))
        (Expr.eval_const (lt_trans (by decide : LCT_HDR_HP < 36) h36_w)) (by rw [hbh_hp]; omega)
    · simp only [st_pre_re, mem₁, s7, s6, s5, s4, s3, s2, s1, st_init, startState, nb]
  rcases rerootExpose_runs (pos := pos) p lp mem₀ hp_base hp_sp hexpose_eq hrep₀ hu hv hfoot
      hz₀ hhp_ge hroom_re ω with
    ⟨st₁, st₂, c_re, c_exp, l₂, rest₂, x₂, hrun_re, hrun_exp, hi₂, hsafe₂, _hz₂, hle₂, hpp₂,
      _hrev₂, _hht₂, _hev₂, hhead_same, hlast_v, hcost_re_exp, hrep₂, hx2_trees, hz0_safe, hpf0,
      hag0, _harena_eff, hfin_lt, _, hmove_re⟩
  have hr_pre_ok : st_pre_re.regs 4 = hp_caller ∧ st_pre_re.regs 5 = L ∧
      st_pre_re.regs 6 = b ∧ st_pre_re.regs 7 = nb ∧
      st_pre_re.regs 8 = u + 1 ∧ st_pre_re.regs 9 = v + 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [st_pre_re, s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne]
  let rB := Function.update st_pre_re.regs 12 0
  have hcall_re : Runs w p ω (.call 12 lp.reroot [.reg 7, .reg 8]) st_pre_re .normal
      { mem := st₁.mem, regs := rB, pos := st₁.pos } (2 + c_re + 1) :=
    runs_call_iff.mpr ⟨[nb, u + 1], lctRerootBody lp, .returned 0, st₁, c_re,
      by simp [evalArgs, Expr.eval, hr_pre_ok], hreroot_eq, hrun_re, rfl, by cases st₁; rfl, rfl⟩
  let rC := Function.update rB 12 (v + 1)
  have hcall_exp : Runs w p ω (.call 12 lp.expose [.reg 7, .reg 9])
      { mem := st₁.mem, regs := rB, pos := st₁.pos } .normal
      { mem := st₂.mem, regs := rC, pos := st₂.pos } (2 + c_exp + 1) := by
    have hargs : rB 7 = nb ∧ rB 9 = v + 1 := by
      simp [rB, Function.update_of_ne, hr_pre_ok]
    exact runs_call_iff.mpr ⟨[nb, v + 1], exposeBody lp.splay, .returned (v + 1), st₂, c_exp,
      by simp [evalArgs, Expr.eval, hargs], hexpose_eq, hrun_exp, rfl, by cases st₂; rfl, rfl⟩
  let ptr := nodeField st₂.mem nb (v + 1) OFF_CSUM_FWD
  let st_st2 : State := { mem := st₂.mem, regs := rC, pos := st₂.pos }
  have hrC_ok : rC 4 = hp_caller ∧ rC 5 = L ∧ rC 6 = b ∧ rC 7 = nb ∧ rC 9 = v + 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [rC, rB, Function.update_of_ne, hr_pre_ok]
  have ht2m := (SplayForestOk.trees_ok hi₂.sf (.node (v + 1) l₂ .leaf) (by simp)).2.2
  have hopt_ptr := ht2m.root_csumFwd_optOk
  have hptr_w : ptr < 2 ^ w := by
    rcases hopt_ptr with h0 | ⟨_, hle_st2, _⟩
    · rw [show ptr = nodeField st₂.mem nb (v + 1) OFF_CSUM_FWD from rfl, h0]
      exact lt_trans (by decide) h36_w
    · have hst2_lt : st₂.mem (nb - 1) < 2 ^ w := lt_trans (Nat.lt_succ_self _) hfin_lt
      exact lt_of_le_of_lt (by dsimp only [ptr, nb] at *; omega) hst2_lt
  have hload_ptr : Runs w p ω (.assign 11 (.load (.bin .add (.bin .add (.reg 7)
      (.bin .mul (.const NODE_STRIDE) (.reg 9))) (.const OFF_CSUM_FWD)))) st_st2 .normal
      { st_st2 with regs := Function.update st_st2.regs 11 ptr } 9 := by
    refine runs_assign_iff.mpr ⟨ptr, ?_, rfl, rfl, by decide⟩
    have hv_bd := hnode_lt (v + 1) OFF_CSUM_FWD (by omega)
      (by unfold lctCap; omega) (by decide)
    have e1 := Expr.eval_bin (op := .mul) (Expr.eval_const hstr_w)
      (Expr.eval_reg_of_eq (st := st_st2) (r := 9) hrC_ok.2.2.2.2) (by simpa [BinOp.eval] using lt_of_le_of_lt (Nat.le_add_left _ _) (lt_of_le_of_lt (Nat.le_add_right _ _) hv_bd.2))
    have e2 := Expr.eval_add (Expr.eval_reg_of_eq (st := st_st2) (r := 7) hrC_ok.2.2.2.1) e1
      (lt_of_le_of_lt (Nat.le_add_right _ _) hv_bd.2)
    have e3 := Expr.eval_add e2 (Expr.eval_const (lt_trans (by decide : OFF_CSUM_FWD < 36) h36_w)) hv_bd.2
    rw [Expr.eval_load e3]
    rfl
  let st_ptr := { st_st2 with regs := Function.update st_st2.regs 11 ptr }
  have hst_ptr_regs : st_ptr.regs 4 = hp_caller ∧ st_ptr.regs 5 = L ∧ st_ptr.regs 6 = b ∧
      st_ptr.regs 11 = ptr := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [st_ptr, st_st2, Function.update_of_ne, hrC_ok]
  have ht2_mem : AuxTree.node (v + 1) l₂ .leaf ∈ x₂.trees := by rw [hx2_trees]; simp
  have hsum_wrap := hrep₂.pathSum_eq_wrap ht2_mem hu hv hpp₂ (hhead_same hsc) hlast_v
  dsimp only [AuxTree.rootId] at hsum_wrap
  have hcopy_branch : ∃ mem_fin r_post pos_post c_cond,
      Runs w p ω (.cond (.reg 11) (.call 12 lp.copyWords [.reg 11, .reg 4, .reg 5]) .nop)
        st_ptr .normal { mem := mem_fin, regs := r_post, pos := pos_post } c_cond ∧
      c_cond ≤ 17 * L + 16 ∧
      r_post 6 = b ∧
      Valid mem_fin hp_caller h L ∧
      intVal mem_fin hp_caller h L = wrap h L (F.pathSum u v) ∧
      (∀ a, a < hp_caller ∨ hp_eff ≤ a → mem_fin a = st₂.mem a) := by
    by_cases hpz : ptr = 0
    · have hzero_ans : ∀ i < L, st₂.mem (hp_caller + i) = 0 := fun i hi => by
        have ha_lo : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller + i :=
          le_trans (by simpa [nb, cap, lctArenaHi] using harena_hp) (Nat.le_add_right _ _)
        have ha_hi : hp_caller + i < hp_eff := by omega
        have hne_hp : hp_caller + i ≠ nb - 1 := by
          have hpos : 1 ≤ nb := by dsimp only [nb, lctNodesBase, LCT_HDR_SIZE]; omega
          have hle : nb ≤ hp_caller :=
            le_trans (Nat.le_add_right _ _) (by simpa [nb, lctArenaHi] using harena_hp)
          omega
        rw [hsafe₂.2.1 _ (Or.inr (Or.inr ⟨ha_lo, ha_hi⟩))]
        rw [Function.update_of_ne hne_hp, hz₀ _ (by omega)]
      refine ⟨st₂.mem, st_ptr.regs, st_ptr.pos, 3, ?_, by omega, hst_ptr_regs.2.2.1, ?_, ?_, fun _ _ => rfl⟩
      · rw [runs_cond_iff]
        refine ⟨0, 1, by simpa [hpz] using Expr.eval_reg_of_eq hst_ptr_regs.2.2.2, ?_, by decide⟩
        simp [runs_nop_iff, st_ptr, st_st2]
      · refine fun i hi => ?_
        rw [hzero_ans i hi]; exact MinCostFlow.Num.base_pos h
      · have hiv0 : intVal st₂.mem hp_caller h L = intVal (fun _ => 0) hp_caller h L :=
          intVal_congr fun i hi => hzero_ans i hi
        have hz_fn : ZeroFrom (fun _ => 0) 0 := fun _ _ => rfl
        have h0 : intVal (fun _ => 0) hp_caller h L = 0 := intVal_zeroFrom hz_fn (Nat.zero_le _)
        have hopt0 : optIntVal st₂.mem h L ptr = 0 := by simp [optIntVal, hpz]
        rw [hiv0, h0, ← hopt0]
        exact hsum_wrap
    · rcases hopt_ptr with h0 | ⟨_, hptr_hi, hptr_val⟩
      · exact absurd h0 hpz
      · have hdisj := SafeMem.ptr_disjoint_ans hfoot hpf0
          (by rw [hrep₀.2.2.2.2.1]; exact hsafe₂) (x := v + 1) (off := OFF_CSUM_FWD)
          (by omega) (by rw [hrep₀.2.2.2.2.1]; unfold lctCap; omega) (by decide)
        dsimp only at hdisj
        have hno_ov : hp_caller + L ≤ ptr ∨ ptr + L ≤ hp_caller := by
          rcases hdisj with h0 | hhi | hlo
          · exact absurd h0 hpz
          · exact Or.inl hhi
          · exact Or.inr hlo
        have hpre : (copyWordsContract w).pre [ptr, hp_caller, L] st₂.mem :=
          ⟨ptr, hp_caller, L, rfl, lt_trans (by decide) h36_w,
            Nat.le_of_lt (lt_of_le_of_lt (le_trans hptr_hi (Nat.le_succ _)) hfin_lt), le_of_lt hhpeff_w, hno_ov⟩
        rcases hp_base.copyWords_ok [ptr, hp_caller, L] st₂.mem st_ptr.pos ω
            (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> omega) hpre with
          ⟨body_cp, hcp_eq, o_cp, st_cp, c_cp, hrun_cp, hpost_cp, hc_cp⟩
        rcases hpost_cp with ⟨_, _, _, hcp_arg, _, hcp_eq_vals, hcp_out⟩
        cases hcp_arg
        have hc_cp' : c_cp ≤ 17 * L + 10 := hc_cp
        refine ⟨st_cp.mem, Function.update st_ptr.regs 12 o_cp.value, st_cp.pos, 1 + (3 + c_cp + 1) + 1,
          ?_, by omega, ?_, ?_, ?_, hcp_out⟩
        · rw [runs_cond_iff]
          refine ⟨ptr, 3 + c_cp + 1, by simpa [hpz] using Expr.eval_reg_of_eq hst_ptr_regs.2.2.2, ?_, rfl⟩
          simp only [hpz, ↓reduceIte]
          exact runs_call_iff.mpr ⟨[ptr, hp_caller, L], body_cp, o_cp, st_cp, c_cp,
            by simp [evalArgs, Expr.eval, hst_ptr_regs], hcp_eq, hrun_cp, rfl, rfl, rfl⟩
        · simp [Function.update_of_ne, hst_ptr_regs]
        · intro i hi
          rw [hcp_eq_vals i hi]
          exact hptr_val i hi
        · have hiv : intVal st_cp.mem hp_caller h L = intVal st₂.mem ptr h L :=
            intVal_congr hcp_eq_vals
          have hopt_nz : optIntVal st₂.mem h L ptr = intVal st₂.mem ptr h L := by simp [optIntVal, hpz]
          rw [hiv, ← hopt_nz]
          exact hsum_wrap
  rcases hcopy_branch with ⟨mem_fin, r_post, pos_post, c_cond, hcond_run, hc_cond, hr6_post,
    hval_fin, hiv_fin, hag_fin⟩
  have hcost_arith := pathSum_cost_arith hcost_re_exp hle₂
    (c_tot := 2 + (5 + (2 + (4 + (4 + (4 + (4 + (5 + ((2 + c_re + 1) + ((2 + c_exp + 1) +
      (9 + (c_cond + (5 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
    (by omega) hre_le hlog_pos hsp_ge
  have hfin_sp : st₂.mem (nb - 1) + 1 ≤ hp_caller + space := hcost_arith.1
  have hmem_fin_hp : mem_fin (b + LCT_HDR_HP) = st₂.mem (nb - 1) := by
    rw [hbh_hp]
    have h1 : nb - 1 < hp_caller := by
      have hpos : 1 ≤ nb := by dsimp only [nb, lctNodesBase, LCT_HDR_SIZE]; omega
      have hle : nb ≤ hp_caller :=
        le_trans (Nat.le_add_right _ _) (by simpa [nb, lctArenaHi] using harena_hp)
      omega
    exact hag_fin (nb - 1) (Or.inl h1)
  let st_cond : State := { mem := mem_fin, regs := r_post, pos := pos_post }
  let r_end := Function.update r_post 13 (st₂.mem (nb - 1))
  let st_load : State := { mem := mem_fin, regs := r_end, pos := pos_post }
  have hload_hp : Runs w p ω (.assign 13 (.load (.bin .add (.reg 6) (.const LCT_HDR_HP))))
      st_cond .normal st_load 5 := by
    refine runs_assign_iff.mpr ⟨st₂.mem (nb - 1), ?_, rfl, rfl, by decide⟩
    have hnb_hp : nb - 1 < hp_caller := by
      have hpos : 1 ≤ nb := by dsimp only [nb, lctNodesBase, LCT_HDR_SIZE]; omega
      have hle : nb ≤ hp_caller :=
        le_trans (Nat.le_add_right _ _) (by simpa [nb, lctArenaHi] using harena_hp)
      omega
    have hadd := Expr.eval_add (Expr.eval_reg_of_eq (st := st_cond) hr6_post)
      (Expr.eval_const (lt_trans (by decide : LCT_HDR_HP < 36) h36_w))
      (by rw [hbh_hp]; exact lt_trans hnb_hp hhp_w)
    rw [Expr.eval_load hadd]; simp [st_cond, hmem_fin_hp]
  let hp_final := st₂.mem (nb - 1) + 1
  have hret_hp : Runs w p ω (.ret (.bin .add (.reg 13) (.const 1))) st_load (.returned hp_final) st_load 4 :=
    runs_ret_iff.mpr ⟨hp_final, Expr.eval_add (Expr.eval_reg_of_eq (st := st_load) (by simp [st_load, r_end]))
      (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w)) hfin_lt, rfl, rfl, by decide⟩
  have hrun_full :=
    runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3 (runs_seq_normal hs4
      (runs_seq_normal hs5 (runs_seq_normal hs6 (runs_seq_normal hs7 (runs_seq_normal hs8
      (runs_seq_normal hcall_re (runs_seq_normal hcall_exp (runs_seq_normal hload_ptr
      (runs_seq_normal hcond_run (runs_seq_normal hload_hp hret_hp))))))))))))
  rcases exitOp_rep hrep₀ hfoot hhp_ge rfl hrep₀.valid hrep₀.edgeFits hz0_safe hpf0 hag0 hsafe₂
      hi₂.sf hi₂.hdrN hi₂.hdrCap hi₂.hdrL hi₂.hdrP hrep₀.edgeMap_snd_perm hrep₀.slots_perm
      hi₂.freeChain hi₂.freeNodeOk hi₂.vertexOk hi₂.edgeOk hi₂.auxPathOk hi₂.subdivOk
      hfin_lt hfin_sp hag_fin with
    ⟨hrep_fin, hresp_fin, hphi_fin⟩
  refine ⟨hp_final, st_load, _, _, hrun_full, hrep_fin, hresp_fin, hval_fin, hiv_fin, ?_, ?_⟩
  · change _ + (hp_final - hp_caller) + lctPhi L mem_fin b F.n ≤ _
    rw [hphi_fin]
    exact hcost_arith.2
  · have harena_le : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller := by
      simpa [nb, cap, lctArenaHi] using harena_hp
    exact hrep₀.rerootRoots_of_rootMove hu (rootMove_of_agree hmove_re fun z =>
      lctAuxParent_agree (fun i _ hi => (hag_fin i (Or.inl (lt_of_lt_of_le hi harena_le))).symm) z)

end PathSumProcedure

end MinCostFlow.LinkCut.Prog
