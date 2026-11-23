module

public import MinCostFlow.LinkCut.Prog.MathForestQueryAux

/-!
# Word-RAM `findRoot` Procedure for `MathForest`

Implements deterministic (`Stmt.NoRand`) Word-RAM body `lctFindRootBody` and proves its full
`LctMemRep` + `Respects` + `O((L + 1) log n)` amortized potential bound (van den Brand et al.,
`arXiv:2309.16629v1`, Lemma 4.1 p. 13, from [KangP15] Section 4).

`lctFindRootBody` runs `expose(v)`, descends to the leftmost node `r + 1` in the exposed
auxiliary tree without modifying memory via `descendExtremeLoop true`, splays `r + 1`
(whose `200 * (depth / 2)` descend-credit from `splayLoop_credit_runs` pays for the
un-pushed descent), and writes `r = lctCanonRoot mem₀ b F.n v` to `mem[hp_caller]`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section FindRootProcedure

/-- In an exposed `LctExposeInvs` tree with `OFF_PPAR = 0`, the inorder head equals
`rootAbove (lctAuxParent mem nb cap) cap (v + 1)` for any terminal vertex `v + 1`. -/
theorem head_evalInorder_eq_rootAbove {w h L P b n v r : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {t : AuxTree} {rest : List AuxTree} {mem : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (t :: rest) mem)
    (hpp0 : nodeField mem (lctNodesBase b) t.rootId OFF_PPAR = 0)
    (hlast : (t.evalInorder (revFlag mem (lctNodesBase b)) false).getLast? = some (v + 1))
    (hhead : (t.evalInorder (revFlag mem (lctNodesBase b)) false).head? = some r) :
    r = rootAbove (lctAuxParent mem (lctNodesBase b) (lctCap n)) (lctCap n) (v + 1) := by
  let nb := lctNodesBase b
  let cap := lctCap n
  let par := lctAuxParent mem nb cap
  let seq := t.evalInorder (revFlag mem nb) false
  have hseq_eq : seq = lctTreeSeq mem nb cap t.rootId :=
    (SplayForestOk.lctTreeSeq_eq hi.sf (by simp)).symm
  have hpp_le : ∀ s ∈ t :: rest, nodeField mem nb s.rootId OFF_PPAR ≤ cap :=
    fun s hs => hi.ppar_le_cap s hs
  have hp0 : par 0 = 0 := lctAuxParent_zero_of_trees hi.sf hpp_le
  have hle : ∀ u, 1 ≤ u → u ≤ cap → par u ≤ cap :=
    fun u _ _ => lctAuxParent_le_cap_of_trees hi.sf hpp_le u
  have hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0 := hi.subdivOk.1
  have hpar_seq : ∀ i (hi_lt : i < seq.length),
      par seq[i] = if i = 0 then 0 else seq[i - 1]! := by
    intro i hi_lt
    have hi_seq : i < (lctTreeSeq mem nb cap t.rootId).length := by rw [← hseq_eq]; exact hi_lt
    have h1 := lctAuxParent_of_tree hi.sf hpp_le (by simp : t ∈ t :: rest) i hi_seq
    have h1' : par (lctTreeSeq mem nb cap t.rootId)[i] =
        if i = 0 then 0 else (lctTreeSeq mem nb cap t.rootId)[i - 1]! := by
      simpa [hpp0] using h1
    simpa [← hseq_eq] using h1'
  have hseq_ne : seq ≠ [] := by
    intro he
    have hh' : seq.head? = some r := hhead
    rw [he] at hh'; contradiction
  have hpos : 0 < seq.length := List.length_pos_of_ne_nil hseq_ne
  have h0_eq : seq[0]'hpos = r := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at hhead
    exact Option.some.inj hhead
  have hlast_eq : seq[seq.length - 1]'(by omega) = v + 1 := by
    have hg := List.getLast?_eq_getElem? (l := seq)
    rw [List.getElem?_eq_getElem (by omega : seq.length - 1 < seq.length), hlast] at hg
    exact Option.some.inj hg.symm
  have hmem_bounds : ∀ z ∈ seq, 1 ≤ z ∧ z ≤ cap := by
    intro z hz
    have hz' : z ∈ t.toList := (t.evalInorder_perm _ _).mem_iff.1 hz
    exact (SplayForestOk.trees_ok hi.sf t (by simp)).2.2.nodup_perm_mem hz'
  have hroot_all : ∀ k (hk : k < seq.length), rootAbove par cap seq[k] = r := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hpr0 : par seq[0] = 0 := by simpa using hpar_seq 0 hk
        have heq_r : rootAbove par cap (seq[0]'hk) = seq[0]'hk := by
          cases hcap : cap with
          | zero => simp [rootAbove]
          | succ m => simp [rootAbove, hpr0]
        rw [heq_r, h0_eq]
    | succ k ih =>
        intro hk
        have hpk : par (seq[k + 1]'hk) = seq[k]'(by omega) := by
          have h1 := hpar_seq (k + 1) hk
          simp at h1
          simpa [getElem!_pos, (by omega : k < seq.length)] using h1
        have hbd := hmem_bounds (seq[k + 1]'hk) (List.getElem_mem hk)
        have hbd_k := hmem_bounds (seq[k]'(by omega)) (List.getElem_mem (by omega : k < seq.length))
        have hnz : par (seq[k + 1]'hk) ≠ 0 := by rw [hpk]; exact Nat.ne_of_gt hbd_k.1
        rw [← rootAbove_step hp0 hle hacyc hbd.1 hbd.2 hnz, hpk]
        exact ih (by omega)
  exact (hlast_eq ▸ hroot_all (seq.length - 1) (by omega)).symm

/-- Deterministic Word-RAM `findRoot` body taking `args = [b, v, hp_caller]`:
exposes `v`, descends to the leftmost node `r + 1` in the exposed path tree without
modifying memory, splays `r + 1` (paying the descend cost via `200 * (depth / 2)`
credit), writes `r` to `mem[hp_caller]`, and returns `hp_final`. -/
def lctFindRootBody (lp : LctProcs) : Stmt :=
  .assign 7 (.reg 2) ;;
  .assign 8 (.reg 0) ;;
  .assign 9 (.bin .add (.reg 0) (.const LCT_HDR_SIZE)) ;;
  .assign 10 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 11 (.bin .add (.reg 2) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 11) ;;
  .call 12 lp.expose [.reg 9, .reg 10] ;;
  .assign 0 (.reg 9) ;;
  .assign 1 (.reg 10) ;;
  .assign 2 (.const 0) ;;
  .assign 3 (.const 1) ;;
  descendExtremeLoop true ;;
  .call 12 lp.splay.splay [.reg 0, .reg 1] ;;
  .assign 1 (.bin .sub (.reg 1) (.const 1)) ;;
  .store (.reg 7) (.reg 1) ;;
  .assign 13 (.load (.bin .add (.reg 8) (.const LCT_HDR_HP))) ;;
  .ret (.bin .add (.reg 13) (.const 1))

theorem lctFindRootBody_noRand (lp : LctProcs) : (lctFindRootBody lp).NoRand := by
  simp [lctFindRootBody, descendExtremeLoop, Stmt.NoRand]

private lemma findRoot_room1_arith {s hp0 phi0 phi1 ce cf a b p2w : ℕ}
    (h1 : (s - (hp0 + 1)) + phi1 ≤ phi0 + ce) (hle : hp0 + 1 ≤ s) (hce : ce ≤ cf)
    (hab : a ≤ b) (hbd : hp0 + phi0 + cf + b + 2 < p2w) :
    s + a < p2w := by
  omega

private lemma findRoot_cost_arith
    {L n c_tot c1 c_loop c_sp d_sp m_mod hp_eff hp1_m hp_end hp_caller phi0 phi1 phi3 rk1 : ℕ}
    (h1 : c1 + (hp1_m - hp_eff) + phi1 ≤ phi0 + C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1))
    (hloop : c_loop ≤ 40 * (2 * d_sp + m_mod) + 40)
    (hmod : m_mod ≤ 1)
    (hsp : c_sp + 200 * d_sp + (hp_end - hp1_m) + phi3 ≤
      phi1 + 3 * K_SPLAY_STEP L * rk1 + C_SPLAY_CONST L)
    (hrk : rk1 ≤ Nat.log 2 (n + 2) + 1)
    (hle1 : hp_eff ≤ hp1_m)
    (hle3 : hp1_m ≤ hp_end)
    (hp_rel : hp_eff = hp_caller + 1)
    (hct : c_tot ≤ c1 + c_loop + c_sp + 80) :
    c_tot + (hp_end + 1 - hp_caller) + phi3 ≤
      phi0 + C_FINDROOT_OP L * (Nat.log 2 (n + 2) + 1) := by
  have hlog_pos : 1 ≤ Nat.log 2 (n + 2) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hk_rk : 3 * K_SPLAY_STEP L * rk1 ≤ 3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) :=
    Nat.mul_le_mul_left _ hrk
  have hc_sp_mul : C_SPLAY_CONST L + 165 ≤ (C_SPLAY_CONST L + 165) * (Nat.log 2 (n + 2) + 1) :=
    Nat.le_mul_of_pos_right _ hlog_pos
  have hk_bound : C_EXPOSE_OP L + 3 * K_SPLAY_STEP L + (C_SPLAY_CONST L + 165) ≤
      C_FINDROOT_OP L := by
    unfold C_EXPOSE_OP K_SPLAY_STEP K_DOUBLE K_ROTATE K_PULL K_PUSH_PATH K_PUSH_DOWN
      C_SPLAY_CONST C_FINDROOT_OP
    omega
  have hmul_sum : (C_EXPOSE_OP L + 3 * K_SPLAY_STEP L + (C_SPLAY_CONST L + 165)) *
      (Nat.log 2 (n + 2) + 1) ≤ C_FINDROOT_OP L * (Nat.log 2 (n + 2) + 1) :=
    Nat.mul_le_mul_right _ hk_bound
  have h40 : c_loop ≤ 80 * d_sp + 80 := by
    have h2 : 40 * (2 * d_sp + m_mod) + 40 ≤ 40 * (2 * d_sp + 1) + 40 := by omega
    omega
  have hexpand : C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1) +
      3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + (C_SPLAY_CONST L + 165) * (Nat.log 2 (n + 2) + 1) =
      (C_EXPOSE_OP L + 3 * K_SPLAY_STEP L + (C_SPLAY_CONST L + 165)) * (Nat.log 2 (n + 2) + 1) := by
    ring
  omega

/-- Complete Word-RAM specification for `lctFindRootBody` starting from `args = [b, v, hp_caller]`:
returns `hp_final`, preserves `LctMemRep`, satisfies `DSRep.Respects`, writes `lctCanonRoot`
at `mem[hp_caller]`, preserves all canonical roots, and runs in amortized cost
`≤ C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1)`. -/
theorem lctFindRootBody_runs {w h L P b v hp_caller space pos : ℕ}
    {F : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hv : v < F.n)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hhp_bd : hp_caller + lctPhi L mem₀ b F.n +
      C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) + 2 < 2 ^ w)
    (hsp_ge : lctPhi L mem₀ b F.n + C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + 2 ≤ space) :
    ∀ ω, ∃ hp_final st' c x',
      Runs w p ω (lctFindRootBody lp) (startState [b, v, hp_caller] mem₀ pos)
        (.returned hp_final) st' c ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_final b x' st'.mem ∧
      st'.mem hp_caller = lctCanonRoot mem₀ b F.n v ∧
      st'.mem hp_caller < F.n ∧
      (∀ u, lctCanonRoot st'.mem b F.n u = lctCanonRoot mem₀ b F.n u) ∧
      (∀ u < F.n, lctCanonRoot mem₀ b F.n u = st'.mem hp_caller ↔ F.SameComp u v) ∧
      c + (hp_final - hp_caller) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) := by
  intro ω
  let nb := lctNodesBase b
  let cap := lctCap F.n
  let hp_eff := hp_caller + 1
  have harena_hp : lctArenaHi b cap ≤ hp_caller := by
    by_contra hlt
    have hbl := b_lt_lctArenaHi b cap
    have hxn : x₀.n = F.n := hrep₀.2.2.2.2.1
    have hpos_ar : 0 < lctArenaHi b cap := lt_of_le_of_lt (Nat.zero_le b) hbl
    have hb_foot : lctFoot b x₀ (lctArenaHi b cap - 1) :=
      lctFoot_arena (by omega) (by rw [hxn]; exact Nat.sub_lt hpos_ar Nat.zero_lt_one)
    have hfl := hfoot _ hb_foot
    omega
  have hnb_w : nb < 2 ^ w := by unfold nb lctArenaHi lctNodesBase NODE_STRIDE at *; omega
  have hb_w : b < 2 ^ w := by unfold lctArenaHi lctNodesBase NODE_STRIDE at *; omega
  have hhp_eff_w : hp_eff < 2 ^ w := by dsimp only [hp_eff]; omega
  have hv1_w : v + 1 < 2 ^ w := by
    have hvc : v + 1 ≤ cap := by unfold cap lctCap; omega
    have hcm : cap < NODE_STRIDE * (cap + 1) := by unfold NODE_STRIDE; omega
    unfold lctArenaHi lctNodesBase at harena_hp; omega
  have hhdr_w : LCT_HDR_SIZE < 2 ^ w ∧ LCT_HDR_HP < 2 ^ w ∧ 1 < 2 ^ w := by
    unfold LCT_HDR_SIZE LCT_HDR_HP lctArenaHi lctNodesBase NODE_STRIDE at *; omega
  have hbh_eq : b + LCT_HDR_HP = nb - 1 := by unfold nb lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
  rcases enterOp_invs hrep₀ hfoot hz₀ (Nat.le_succ hp_caller) hhp_eff_w with
    ⟨hi0, hsafe0, hphi0_eq, hz0', hz0_safe, hpf0, hpar0, hag0⟩
  let mem₁ := Function.update mem₀ (nb - 1) hp_eff
  have hmem₁_hp : mem₁ (nb - 1) = hp_eff := Function.update_self _ _ _
  have hmem₁_lt : mem₁ (nb - 1) + lctPhi L mem₁ b F.n +
      C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) < 2 ^ w := by
    have hc : C_EXPOSE_OP L ≤ C_FINDROOT_OP L := by unfold C_EXPOSE_OP C_FINDROOT_OP; omega
    have hm := Nat.mul_le_mul_right (Nat.log 2 (F.n + 2) + 1) hc
    have hle_bd : mem₁ (nb - 1) + lctPhi L mem₁ b F.n +
        C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) ≤
        hp_caller + lctPhi L mem₀ b F.n + C_FINDROOT_OP L * (Nat.log 2 (F.n + 2) + 1) +
        7000 * (L + 1) * (F.n + 2) + 2 := by
      rw [hmem₁_hp, hphi0_eq]; dsimp only [hp_eff]; omega
    exact lt_of_le_of_lt hle_bd hhp_bd
  have hsafe0' : SafeMem mem₁ (lctNodesBase b) (lctCap F.n) hp_eff mem₁ := hsafe0
  have hz0'' : ZeroFrom mem₁ (mem₁ (lctNodesBase b - 1)) := by
    simpa [mem₁, nb, hmem₁_hp, hp_eff] using hz0'
  have harena_eff : lctArenaHi b cap ≤ hp_eff := by
    dsimp only [hp_eff]; omega
  rcases exposeBody_runs p lp.splay mem₁ mem₁ hp_base.splay_hasAt hp_sp hp_base.splay_ok
      hz0_safe harena_eff hsafe0' hi0 hv hz0'' hmem₁_lt ω with
    ⟨st₁, c₁, l_fin, rest_fin, hrun₁, hi₁, hsafe₁, hfr₁, hpar₁, hpp₁, _hrev₁, _hht₁, hev₁, hphi₁⟩
  let t₁ := AuxTree.node (v + 1) l_fin .leaf
  have hbase_w : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := by
    have h1 : nb + NODE_STRIDE * (cap + 1) ≤ st₁.mem (nb - 1) := hi₁.sf.2.2.2.1
    have h2 : st₁.mem (nb - 1) < 2 ^ w := hi₁.sf.2.2.2.2.2.1
    omega
  have ht1_m : TreeMemMatch w h L st₁.mem nb cap t₁ 0 0 := by
    have hm := (SplayForestOk.trees_ok hi₁.sf t₁ (by dsimp only [t₁]; simp)).2.2
    simpa [t₁, AuxTree.rootId, hpp₁] using hm
  have ht1_nd : t₁.toList.Nodup := by
    have hnd := (SplayForestOk.perm hi₁.sf).nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
    exact list_nodup_of_flatMap_nodup hnd (by dsimp only [t₁]; simp)
  let st_init := startState [b, v, hp_caller] mem₀ pos
  let s1 := { st_init with regs := Function.update st_init.regs 7 hp_caller }
  let s2 := { s1 with regs := Function.update s1.regs 8 b }
  let s3 := { s2 with regs := Function.update s2.regs 9 nb }
  let s4 := { s3 with regs := Function.update s3.regs 10 (v + 1) }
  let s5 := { s4 with regs := Function.update s4.regs 11 hp_eff }
  let rA : ℕ → ℕ := s5.regs
  let st_pre_exp : State := { mem := mem₁, regs := rA, pos := pos }
  have hr0 : st_init.regs 0 = b := rfl
  have hr1 : st_init.regs 1 = v := rfl
  have hr2 : st_init.regs 2 = hp_caller := rfl
  have hs1 : Runs w p ω (.assign 7 (.reg 2)) st_init .normal s1 2 :=
    runs_assign_iff.mpr ⟨hp_caller, Expr.eval_reg_of_eq hr2, rfl, rfl, by decide⟩
  have hs2 : Runs w p ω (.assign 8 (.reg 0)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨b, Expr.eval_reg_of_eq (by simp [s1, hr0, Function.update_of_ne]), rfl, rfl, by decide⟩
  have hs3 : Runs w p ω (.assign 9 (.bin .add (.reg 0) (.const LCT_HDR_SIZE))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_add (Expr.eval_reg_of_eq (by simp [s2, s1, hr0, Function.update_of_ne]))
      (Expr.eval_const hhdr_w.1) hnb_w, rfl, rfl, by decide⟩
  have hs4 : Runs w p ω (.assign 10 (.bin .add (.reg 1) (.const 1))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨v + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [s3, s2, s1, hr1, Function.update_of_ne]))
      (Expr.eval_const hhdr_w.2.2) hv1_w, rfl, rfl, by decide⟩
  have hs5 : Runs w p ω (.assign 11 (.bin .add (.reg 2) (.const 1))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨hp_eff, Expr.eval_add (Expr.eval_reg_of_eq (by simp [s4, s3, s2, s1, hr2, Function.update_of_ne]))
      (Expr.eval_const hhdr_w.2.2) hhp_eff_w, rfl, rfl, by decide⟩
  have hnb_lt_eff : b + LCT_HDR_HP < 2 ^ w := by
    rw [hbh_eq]
    have h1 : nb - 1 < lctArenaHi b cap := by unfold nb lctArenaHi lctNodesBase NODE_STRIDE; omega
    have h2 : lctArenaHi b cap < hp_eff := by dsimp only [hp_eff]; omega
    exact lt_trans (lt_trans h1 h2) hhp_eff_w
  have heval_hp : (Expr.bin .add (.reg 0) (.const LCT_HDR_HP)).eval w s5 = some (nb - 1) := by
    rw [← hbh_eq]
    exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [s5, s4, s3, s2, s1, hr0, Function.update_of_ne]))
      (Expr.eval_const hhdr_w.2.1) hnb_lt_eff
  have hs6 : Runs w p ω (.store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 11)) s5 .normal st_pre_exp 5 :=
    runs_store_iff.mpr ⟨nb - 1, hp_eff, heval_hp, Expr.eval_reg_of_eq (by simp [s5]),
      rfl, by simp only [st_pre_exp, rA, mem₁, s5, s4, s3, s2, s1, st_init, startState], by decide⟩
  have hrA_ok : rA 7 = hp_caller ∧ rA 8 = b ∧ rA 9 = nb ∧ rA 10 = v + 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [rA, s5, s4, s3, s2, s1, st_init, startState, Function.update_of_ne]
  let rB := Function.update rA 12 (v + 1)
  have hcall_exp : Runs w p ω (.call 12 lp.expose [.reg 9, .reg 10]) st_pre_exp .normal
      { mem := st₁.mem, regs := rB, pos := st₁.pos } (2 + c₁ + 1) := by
    refine runs_call_iff.mpr ⟨[nb, v + 1], exposeBody lp.splay, .returned (v + 1), st₁, c₁,
      by simp [evalArgs, Expr.eval, st_pre_exp, hrA_ok], hexpose_eq, hrun₁, rfl,
      by cases st₁; rfl, rfl⟩
  let rC := Function.update (Function.update (Function.update (Function.update rB 0 nb) 1 (v + 1)) 2 0) 3 1
  let st_pre_loop : State := { mem := st₁.mem, regs := rC, pos := st₁.pos }
  have hrC_ok : rC 0 = nb ∧ rC 1 = v + 1 ∧ rC 2 = 0 ∧ rC 3 = 1 ∧ rC 7 = hp_caller ∧ rC 8 = b := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [rC, rB, Function.update_of_ne, hrA_ok]
  have ha0 : Runs w p ω (.assign 0 (.reg 9)) { mem := st₁.mem, regs := rB, pos := st₁.pos } .normal
      { mem := st₁.mem, regs := Function.update rB 0 nb, pos := st₁.pos } 2 :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_reg_of_eq (by simp [rB, Function.update_of_ne, hrA_ok]), rfl, rfl, by decide⟩
  have ha1 : Runs w p ω (.assign 1 (.reg 10))
      { mem := st₁.mem, regs := Function.update rB 0 nb, pos := st₁.pos } .normal
      { mem := st₁.mem, regs := Function.update (Function.update rB 0 nb) 1 (v + 1), pos := st₁.pos } 2 :=
    runs_assign_iff.mpr ⟨v + 1, Expr.eval_reg_of_eq (by simp [rB, Function.update_of_ne, hrA_ok]), rfl, rfl, by decide⟩
  have ha2 : Runs w p ω (.assign 2 (.const 0))
      { mem := st₁.mem, regs := Function.update (Function.update rB 0 nb) 1 (v + 1), pos := st₁.pos } .normal
      { mem := st₁.mem, regs := Function.update (Function.update (Function.update rB 0 nb) 1 (v + 1)) 2 0, pos := st₁.pos } 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by decide⟩
  have ha3 : Runs w p ω (.assign 3 (.const 1))
      { mem := st₁.mem, regs := Function.update (Function.update (Function.update rB 0 nb) 1 (v + 1)) 2 0, pos := st₁.pos } .normal
      st_pre_loop 2 :=
    runs_assign_iff.mpr ⟨1, Expr.eval_const hhdr_w.2.2, rfl, rfl, by decide⟩
  rcases runs_descendExtremeLoop p true st₁.mem hbase_w t₁ 0 0 false st_pre_loop
      ht1_m (by simp [t₁]) ht1_nd rfl (by simp [st_pre_loop, hrC_ok.1])
      (by simpa [st_pre_loop, t₁, AuxTree.rootId] using hrC_ok.2.1)
      (by simpa [st_pre_loop] using hrC_ok.2.2.1) (by simpa [st_pre_loop] using hrC_ok.2.2.2.1) ω with
    ⟨st₂, c_loop, rNode, hrun_loop, hmem₂, hr2_0, hr2_1, hrNode_in, hr2_ge7, hc_loop, hhd_r, _⟩
  have hhd_eval := hhd_r rfl
  have hlast_eval : (t₁.evalInorder (revFlag st₁.mem nb) false).getLast? = some (v + 1) := by
    rw [hev₁]; simp
  have hrNode_eq : rNode = rootAbove (lctAuxParent st₁.mem nb cap) cap (v + 1) :=
    head_evalInorder_eq_rootAbove hi₁ hpp₁ hlast_eval hhd_eval
  have hpar_eq01 : ∀ u, lctAuxParent st₁.mem nb cap u = lctAuxParent mem₀ nb cap u :=
    fun u => (hpar₁ u).trans (hpar0 u)
  have hcanon_spec := hrep₀.lctCanonRoot_spec hv
  have hrNode_canon : rNode = lctCanonRoot mem₀ b F.n v + 1 := by
    rw [hrNode_eq]
    have hfun : lctAuxParent st₁.mem nb cap = lctAuxParent mem₀ nb cap := funext hpar_eq01
    rw [hfun]
    exact hcanon_spec.2.1.symm
  have hphi_m1 : lctPhi L mem₁ b F.n = lctPhi L mem₀ b F.n := hphi0_eq
  have hfr₁_le : mem₁ (nb - 1) ≤ st₁.mem (nb - 1) := hfr₁.2.2.1
  have hle1_fr : hp_eff ≤ st₁.mem (nb - 1) := by simpa [hmem₁_hp] using hfr₁_le
  have h1_fr_base : (st₁.mem (nb - 1) - (hp_caller + 1)) + lctPhi L st₁.mem b F.n ≤
      lctPhi L mem₀ b F.n + C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) := by
    have hh := hphi₁
    change c₁ + (st₁.mem (nb - 1) - mem₁ (nb - 1)) + lctPhi L st₁.mem b F.n ≤
      lctPhi L mem₁ b F.n + C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) at hh
    rw [hmem₁_hp, hphi_m1] at hh; dsimp only [hp_eff] at hh; omega
  have hroom₁ : st₁.mem (nb - 1) + 6000 * (L + 1) * (F.n + 2) < 2 ^ w := by
    have hc : C_EXPOSE_OP L ≤ C_FINDROOT_OP L := by unfold C_EXPOSE_OP C_FINDROOT_OP; omega
    have hm := Nat.mul_le_mul_right (Nat.log 2 (F.n + 2) + 1) hc
    have hab : 6000 * (L + 1) * (F.n + 2) ≤ 7000 * (L + 1) * (F.n + 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    exact findRoot_room1_arith h1_fr_base (by dsimp only [hp_eff] at hle1_fr; omega) hm hab hhp_bd
  have hhp_sp : st₁.mem (nb - 1) + K_PUSH_PATH L * (t₁.depthOf rNode + 1) +
      8 * L * t₁.depthOf rNode < 2 ^ w :=
    splay_lct_tree_headroom_lt hi₁.sf rfl (by dsimp only [t₁]; simp) hrNode_in hroom₁
  have harena_eff_nb : nb + NODE_STRIDE * (cap + 1) ≤ hp_eff := by
    unfold lctArenaHi at harena_hp; dsimp only [nb, hp_eff]; omega
  rcases splayForest_lct_credit_runs p lp.splay mem₁ st₁.mem nb cap hp_eff st₂.pos
      hp_base.splay_hasAt hp_sp hp_base.splay_ok hz0_safe harena_eff_nb hsafe₁ hi₁.sf
      (List.Perm.refl (t₁ :: rest_fin)) hrNode_in hhp_sp ω with
    ⟨st₃, c_sp, t₃, hrun_sp, hsf₃, hsafe₃, hr3_root, ht3_perm, hev₃, hsteps₃, _hrev₃, _hht₃,
      hpp₃, hout₃, hstat₃, hfr₃, hphi₃_all⟩
  have ht1_free : t₁.rootId ∉ x₀.freeEdges := fun hfm => by
    have h1 := (hi₁.freeNodeOk t₁.rootId hfm).1
    dsimp only [t₁, AuxTree.rootId] at h1; omega
  rcases LctExposeInvs.of_splay hi₁ (List.Perm.refl (t₁ :: rest_fin)) ht1_free hsf₃
      hev₃ hsteps₃ ht3_perm (hr3_root ▸ hpp₃) hout₃ hstat₃ hfr₃ with
    ⟨hi₃, hpar₃, _hrsz, hvs₃, hhc₃⟩
  have hst2_ge7 : st₂.regs 7 = hp_caller ∧ st₂.regs 8 = b :=
    ⟨(hr2_ge7 7 (by decide)).trans hrC_ok.2.2.2.2.1,
     (hr2_ge7 8 (by decide)).trans hrC_ok.2.2.2.2.2⟩
  let rD := Function.update st₂.regs 12 rNode
  have hcall_sp : Runs w p ω (.call 12 lp.splay.splay [.reg 0, .reg 1]) st₂ .normal
      { mem := st₃.mem, regs := rD, pos := st₃.pos } (2 + c_sp + 1) := by
    refine runs_call_iff.mpr ⟨[nb, rNode], splayBody lp.splay, .returned rNode, st₃, c_sp,
      by simp [evalArgs, Expr.eval, hr2_0, hr2_1], hp_base.splay_ok.splay_eq,
      by simpa [startState, hmem₂] using hrun_sp, rfl, by cases st₃; rfl, rfl⟩
  let rNode1 := rNode - 1
  have hrD_ok : rD 1 = rNode ∧ rD 7 = hp_caller ∧ rD 8 = b := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [rD, Function.update_of_ne, hr2_1, hst2_ge7]
  have hrNode_pos : 1 ≤ rNode := by omega
  have hrNode_w : rNode < 2 ^ w := by
    have hrn : rNode ≤ F.n := by omega
    unfold cap lctCap at harena_hp; unfold lctArenaHi lctNodesBase NODE_STRIDE at harena_hp; omega
  have hvs₃_fn : lctVSize st₃.mem nb cap = lctVSize st₁.mem nb cap := funext hvs₃
  have ht1_rk : t₁.rank (lctVSize st₁.mem nb cap) ≤ Nat.log 2 (F.n + 2) + 1 :=
    treeRank_le_log_of_invs hi₁.sf hi₁.subdivOk.1 hi₁.auxPathOk (by dsimp only [t₁]; simp)
  rcases hphi₃_all (lctVSize st₁.mem nb cap) with ⟨_hsz₃, hphi_sp⟩
  have hphi₃_eq : lctPhi L st₃.mem b F.n =
      splayMemPhi (K_SPLAY_STEP L) st₃.mem nb cap (lctVSize st₁.mem nb cap) +
        C_HEAVY L * lctHeavyCount st₁.mem nb cap := by
    unfold lctPhi; rw [← hvs₃_fn, hhc₃]
  have hphi₁_eq : lctPhi L st₁.mem b F.n =
      splayMemPhi (K_SPLAY_STEP L) st₁.mem nb cap (lctVSize st₁.mem nb cap) +
        C_HEAVY L * lctHeavyCount st₁.mem nb cap := rfl
  have hsp_lct : c_sp + 200 * (t₁.depthOf rNode / 2) + (st₃.mem (nb - 1) - st₁.mem (nb - 1)) +
      lctPhi L st₃.mem b F.n ≤
      lctPhi L st₁.mem b F.n + 3 * K_SPLAY_STEP L * t₁.rank (lctVSize st₁.mem nb cap) +
        C_SPLAY_CONST L := by
    rw [hphi₃_eq, hphi₁_eq]; clear hrun₁ hrun_sp hrun_loop hi0 hi₁ hi₃ hsafe0 hsafe₁ hsafe₃
    omega
  have hdiv_mod : t₁.depthOf rNode = 2 * (t₁.depthOf rNode / 2) + t₁.depthOf rNode % 2 := by omega
  have hloop' : c_loop ≤ 40 * (2 * (t₁.depthOf rNode / 2) + t₁.depthOf rNode % 2) + 40 := by
    simpa [← hdiv_mod] using hc_loop
  have h1_fr : c₁ + (st₁.mem (nb - 1) - hp_eff) + lctPhi L st₁.mem b F.n ≤
      lctPhi L mem₀ b F.n + C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) := by
    have hh := hphi₁
    change c₁ + (st₁.mem (nb - 1) - mem₁ (nb - 1)) + lctPhi L st₁.mem b F.n ≤
      lctPhi L mem₁ b F.n + C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) at hh
    rwa [hmem₁_hp, hphi_m1] at hh
  have hle3_fr : st₁.mem (nb - 1) ≤ st₃.mem (nb - 1) := hfr₃.2.2.1
  have hcost_core := findRoot_cost_arith (c_tot := c₁ + c_loop + c_sp)
    (d_sp := t₁.depthOf rNode / 2) (m_mod := t₁.depthOf rNode % 2)
    h1_fr hloop' (by omega) hsp_lct ht1_rk hle1_fr hle3_fr rfl (by omega)
  have hfin_lt : st₃.mem (nb - 1) + 1 < 2 ^ w := by
    clear hrun₁ hrun_sp hrun_loop hi0 hi₁ hi₃ hsafe0 hsafe₁ hsafe₃ hs1 hs2 hs3 hs4 hs5 hs6 hcall_exp
      ha0 ha1 ha2 ha3 hcall_sp
    omega
  have hfin_sp : st₃.mem (nb - 1) + 1 ≤ hp_caller + space := by
    clear hrun₁ hrun_sp hrun_loop hi0 hi₁ hi₃ hsafe0 hsafe₁ hsafe₃ hs1 hs2 hs3 hs4 hs5 hs6 hcall_exp
      ha0 ha1 ha2 ha3 hcall_sp
    omega
  let st_sub1 : State := { mem := st₃.mem, regs := Function.update rD 1 rNode1, pos := st₃.pos }
  have hsub1 : Runs w p ω (.assign 1 (.bin .sub (.reg 1) (.const 1)))
      { mem := st₃.mem, regs := rD, pos := st₃.pos } .normal st_sub1 4 :=
    runs_assign_iff.mpr ⟨rNode1, Expr.eval_sub (Expr.eval_reg_of_eq hrD_ok.1)
      (Expr.eval_const hhdr_w.2.2) hrNode_w, rfl, rfl, by decide⟩
  let mem_fin := Function.update st₃.mem hp_caller rNode1
  let st_st : State := { mem := mem_fin, regs := st_sub1.regs, pos := st₃.pos }
  have hstore_ans : Runs w p ω (.store (.reg 7) (.reg 1)) st_sub1 .normal st_st 3 :=
    runs_store_iff.mpr ⟨hp_caller, rNode1,
      Expr.eval_reg_of_eq (by simp [st_sub1, Function.update_of_ne, hrD_ok]),
      Expr.eval_reg_of_eq (by simp [st_sub1]), rfl, rfl, by decide⟩
  have hhp_ne : hp_caller ≠ nb - 1 := by
    have : nb - 1 < lctArenaHi b cap := by unfold nb lctArenaHi lctNodesBase NODE_STRIDE; omega
    omega
  have hload_hp : Runs w p ω (.assign 13 (.load (.bin .add (.reg 8) (.const LCT_HDR_HP)))) st_st
      .normal { st_st with regs := Function.update st_st.regs 13 (st₃.mem (nb - 1)) } 5 := by
    refine runs_assign_iff.mpr ⟨st₃.mem (nb - 1), ?_, rfl, rfl, by decide⟩
    rw [← hbh_eq]
    have hadd : (Expr.bin .add (.reg 8) (.const LCT_HDR_HP)).eval w st_st = some (b + LCT_HDR_HP) :=
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st_st, st_sub1, Function.update_of_ne, hrD_ok]))
        (Expr.eval_const hhdr_w.2.1) (by rw [hbh_eq]; exact lt_trans (by omega) hhp_eff_w)
    have hmem_hp : mem_fin (b + LCT_HDR_HP) = st₃.mem (nb - 1) := by
      rw [hbh_eq]; exact Function.update_of_ne hhp_ne.symm _ _
    rw [Expr.eval_load hadd]
    simp only [st_st]; rw [hmem_hp, hbh_eq]
  let hp_final := st₃.mem (nb - 1) + 1
  let st_end := { st_st with regs := Function.update st_st.regs 13 (st₃.mem (nb - 1)) }
  have hret_hp : Runs w p ω (.ret (.bin .add (.reg 13) (.const 1))) st_end (.returned hp_final)
      st_end 4 :=
    runs_ret_iff.mpr ⟨hp_final, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st_end]))
      (Expr.eval_const hhdr_w.2.2) hfin_lt, rfl, rfl, by decide⟩
  have hrun_full' :=
    runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3 (runs_seq_normal hs4
      (runs_seq_normal hs5 (runs_seq_normal hs6 (runs_seq_normal hcall_exp (runs_seq_normal ha0
      (runs_seq_normal ha1 (runs_seq_normal ha2 (runs_seq_normal ha3 (runs_seq_normal hrun_loop
      (runs_seq_normal hcall_sp (runs_seq_normal hsub1 (runs_seq_normal hstore_ans
      (runs_seq_normal hload_hp hret_hp)))))))))))))))
  have hag_fin : ∀ a, a < hp_caller ∨ hp_eff ≤ a → mem_fin a = st₃.mem a := fun a ha =>
    Function.update_of_ne (by
      rcases ha with h1 | h2
      · omega
      · dsimp only [hp_eff] at h2; omega) _ _
  rcases exitOp_rep hrep₀ hfoot (Nat.le_succ hp_caller) rfl hrep₀.valid hrep₀.edgeFits
      hz0_safe hpf0 hag0 hsafe₃ hi₃.sf hi₃.hdrN hi₃.hdrCap hi₃.hdrL hi₃.hdrP
      hrep₀.edgeMap_snd_perm hrep₀.slots_perm hi₃.freeChain hi₃.freeNodeOk hi₃.vertexOk
      hi₃.edgeOk hi₃.auxPathOk hi₃.subdivOk hfin_lt hfin_sp hag_fin with
    ⟨hrep_fin, hresp_fin, hphi_fin⟩
  have hst_end_mem : st_end.mem = mem_fin := rfl
  have hmem_ans : mem_fin hp_caller = lctCanonRoot mem₀ b F.n v := by
    simp [mem_fin, rNode1, hrNode_canon]
  have hpar_fin : ∀ u, lctAuxParent mem_fin nb cap u = lctAuxParent mem₀ nb cap u := fun u => by
    have hag_nb : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem_fin st₃.mem := fun a ha1 ha2 =>
      hag_fin a (Or.inl (by unfold nb lctArenaHi lctNodesBase at *; omega))
    have hpar₃' : lctAuxParent st₃.mem nb cap u = lctAuxParent st₁.mem nb cap u := hpar₃ u
    exact (lctAuxParent_agree hag_nb u).symm.trans (hpar₃'.trans (hpar_eq01 u))
  refine ⟨hp_final, st_end, _, _, by unfold lctFindRootBody; exact hrun_full',
    hrep_fin, hresp_fin, hmem_ans, ?_, fun u => lctCanonRoot_congr hpar_fin u, ?_, ?_⟩
  · show mem_fin hp_caller < F.n
    rw [hmem_ans]; exact hcanon_spec.1
  · intro u hu
    show lctCanonRoot mem₀ b F.n u = mem_fin hp_caller ↔ F.SameComp u v
    rw [hmem_ans]; exact hcanon_spec.2.2.2 u hu
  · change _ + (hp_final - hp_caller) + lctPhi L mem_fin b F.n ≤ _
    rw [hphi_fin]
    refine findRoot_cost_arith (d_sp := t₁.depthOf rNode / 2)
      (m_mod := t₁.depthOf rNode % 2) h1_fr hloop' (by omega) hsp_lct ht1_rk hle1_fr hle3_fr rfl ?_
    omega

end FindRootProcedure

end MinCostFlow.LinkCut.Prog
