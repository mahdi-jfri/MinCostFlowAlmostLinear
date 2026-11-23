module

public import MinCostFlow.LinkCut.Prog.MathForestReroot

/-!
# Shared Query & Operation Helpers (`enterOp_invs`, Splay Credit, Extreme Descent)

Shared helpers for deterministic Word-RAM `MathForest` operations: `enterOp_invs`,
canonical root helpers, `splayForest_lct_credit_runs`, and the memory-preserving
`descendExtremeLoop` procedure.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section ConstantsAndHelpers

/-- Amortized constant factor for `lctFindRootBody` (`≤ 180000 * (L + 1) * (log(n+2)+1)`). -/
def C_FINDROOT_OP (L : ℕ) : ℕ := 180000 * (L + 1)

/-- Amortized constant factor for `lctConnectedBody` (`≤ 365000 * (L + 1) * (log(n+2)+1)`). -/
def C_CONNECTED_OP (L : ℕ) : ℕ := 365000 * (L + 1)

/-- Canonical current-tree root index (`0 .. n - 1`) of vertex `v` in auxiliary memory `mem`. -/
def lctCanonRoot (mem : ℕ → ℕ) (b n v : ℕ) : ℕ :=
  rootAbove (lctAuxParent mem (lctNodesBase b) (lctCap n)) (lctCap n) (v + 1) - 1

theorem lctCanonRoot_congr {mem₁ mem₂ : ℕ → ℕ} {b n : ℕ}
    (h : ∀ u, lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u =
      lctAuxParent mem₂ (lctNodesBase b) (lctCap n) u) (v : ℕ) :
    lctCanonRoot mem₁ b n v = lctCanonRoot mem₂ b n v := by
  simp only [lctCanonRoot, funext h]

theorem LctMemRep.lctCanonRoot_spec {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) {v : ℕ} (hv : v < F.n) :
    let r := lctCanonRoot mem b F.n v
    r < F.n ∧
    r + 1 = rootAbove (lctAuxParent mem (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (v + 1) ∧
    F.SameComp v r ∧
    (∀ u < F.n, lctCanonRoot mem b F.n u = r ↔ F.SameComp u v) := by
  have hs := hrep.sameComp_of_rootAbove hv
  refine ⟨by unfold lctCanonRoot; omega, by unfold lctCanonRoot; omega, hs.2.2.2, ?_⟩
  intro u hu
  have hsu := hrep.sameComp_of_rootAbove hu
  have hiff := hrep.sameComp_iff_rootAbove hu hv
  dsimp only [lctCanonRoot]
  constructor
  · intro heq
    have h1 := hsu.1; have h2 := hs.1
    exact hiff.2 (by omega)
  · intro hsc
    rw [hiff.1 hsc]

theorem LctMemRep.zeroFrom_of_respects {w h L P b hp_caller space hp' : ℕ}
    {x₀ x' : LctConc} {mem₀ mem' : ℕ → ℕ}
    (hresp : (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp' b x' mem') :
    ZeroFrom mem' hp' :=
  hresp.2.2.1

theorem LctMemRep.foot_lt_of_respects {w h L P b hp_caller space hp' : ℕ}
    {x₀ x' : LctConc} {mem₀ mem' : ℕ → ℕ}
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hresp : (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp' b x' mem') :
    ∀ a, lctFoot b x' a → a < hp' := fun a ha => by
  rcases hresp.2.2.2.2 a ha with hold | hnew
  · exact lt_of_lt_of_le (hfoot a hold) hresp.1
  · exact hnew.2

/-- Unpack `enterOp_ready` directly into `LctExposeInvs` plus auxiliary invariants. -/
theorem enterOp_invs {w h L P b hp_caller hp_eff : ℕ} {F : MathForest}
    {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem)
    (hfoot : ∀ a, lctFoot b x a → a < hp_caller)
    (hz : ZeroFrom mem hp_caller)
    (hcaller_le : hp_caller ≤ hp_eff)
    (hhp_w : hp_eff < 2 ^ w) :
    let mem₁ := Function.update mem (lctNodesBase b - 1) hp_eff
    let nb := lctNodesBase b
    let cap := lctCap F.n
    LctExposeInvs w h L P b F.n x.freeEdges x.edgeMap x.trees mem₁ ∧
    SafeMem mem₁ nb cap hp_eff mem₁ ∧
    lctPhi L mem₁ b F.n = lctPhi L mem b F.n ∧
    ZeroFrom mem₁ hp_eff ∧
    SlotZeroOk mem₁ nb ∧
    PtrFootOk b mem₁ x L ∧
    (∀ u, lctAuxParent mem₁ nb cap u = lctAuxParent mem nb cap u) ∧
    (∀ a, a < b ∨ lctArenaHi b cap ≤ a ∧ a < hp_caller → mem₁ a = mem a) := by
  rcases enterOp_ready hrep hfoot hz hcaller_le hhp_w with
    ⟨hsf, hsafe, hphi, hz1, hn, hcap, hL, hP, hfc, hvok, heok, hax, hsub, hz0, hpf, hnf, hout⟩
  have hfree_ok : ∀ ed ∈ x.freeEdges,
      F.n + 1 ≤ ed ∧ ed ≤ lctCap F.n ∧ AuxTree.node ed .leaf .leaf ∈ x.trees ∧
      nodeField (Function.update mem (lctNodesBase b - 1) hp_eff) (lctNodesBase b) ed OFF_PPAR = 0 ∧
      nodeField (Function.update mem (lctNodesBase b - 1) hp_eff) (lctNodesBase b) ed OFF_ISV = 0 ∧
      nodeField (Function.update mem (lctNodesBase b - 1) hp_eff) (lctNodesBase b) ed OFF_HASE = 0 := by
    intro ed hed
    rcases hrep.free_ok ed hed with ⟨h1, h2, h3, h4, h5, h6⟩
    have hed_le : ed ≤ lctCap F.n := h2
    refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
    · rw [hnf ed hed_le OFF_PPAR (by decide)]; exact h4
    · rw [hnf ed hed_le OFF_ISV (by decide)]; exact h5
    · rw [hnf ed hed_le OFF_HASE (by decide)]; exact h6
  have hi : LctExposeInvs w h L P b F.n x.freeEdges x.edgeMap x.trees
      (Function.update mem (lctNodesBase b - 1) hp_eff) :=
    ⟨hn, hcap, hL, hP, hsf, hfc, hfree_ok, hvok, heok, hax, hsub⟩
  have hpar : ∀ u, lctAuxParent (Function.update mem (lctNodesBase b - 1) hp_eff)
      (lctNodesBase b) (lctCap F.n) u =
      lctAuxParent mem (lctNodesBase b) (lctCap F.n) u := by
    intro u
    refine lctAuxParent_agree ?_ u
    intro a ha1 _ha2
    have hne : a ≠ lctNodesBase b - 1 := by unfold lctNodesBase LCT_HDR_SIZE at ha1 ⊢; omega
    exact (Function.update_of_ne hne hp_eff mem).symm
  have hag_out : ∀ a, a < b ∨ lctArenaHi b (lctCap F.n) ≤ a ∧ a < hp_caller →
      Function.update mem (lctNodesBase b - 1) hp_eff a = mem a := by
    intro a ha
    apply hout
    rcases ha with h1 | h2
    · left; unfold lctNodesBase LCT_HDR_SIZE at *; omega
    · right; exact h2.1
  exact ⟨hi, hsafe, hphi, hz1, hz0, hpf, hpar, hag_out⟩

end ConstantsAndHelpers

section SplayCredit

private lemma splay_body_arith
    {c_pp c_lp d_pp d_lp k_pp mod_2 p_div p0 p2 r0 rk_f rk_t k_rot C : ℕ}
    (h1 : c_pp + d_pp ≤ k_pp * mod_2 + k_pp + 2 * k_pp * p_div)
    (h2 : c_lp + d_lp + p2 + r0 + (2 * k_pp * p_div + 200 * p_div) ≤
      p0 + rk_t + (k_rot + 40) * mod_2 + 2)
    (hrk : rk_f ≤ r0)
    (hc : k_pp * mod_2 + k_pp + ((k_rot + 40) * mod_2 + 2) + 22 ≤ C) :
    (1 + ((2 + c_pp + 1) + (6 + (5 + (c_lp + 2 + 1) + 1) + 1) + 1) + 1) +
      200 * p_div + (d_lp + d_pp) + p2 + rk_f ≤ p0 + rk_t + C := by
  omega

/-- Variant of `splayBody_runs` retaining `200 * (t.depthOf x / 2)` descend-credit on the LHS. -/
theorem splayBody_credit_runs {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (h0 : SlotZeroOk mem₀ nodesBase)
    {t : AuxTree} {pp x : ℕ}
    (ht : TreeMemMatch w h L mem₀ nodesBase cap t 0 pp)
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList)
    (hhp_lt : mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x < 2 ^ w) :
    ∀ ω, ∃ st' c t',
      Runs w p ω (splayBody sp) (startState [nodesBase, x] mem₀ pos) (.returned x) st' c ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤
        mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x ∧
      TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp ∧
      t'.rootId = x ∧
      t'.toList.Perm t.toList ∧
      t'.evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L t' false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      revFlag st'.mem nodesBase x = false ∧
      nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        c + 200 * (t.depthOf x / 2) + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) +
          K_SPLAY_STEP L * t'.treePhi vSize +
          3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
          K_SPLAY_STEP L * t.treePhi vSize + 3 * K_SPLAY_STEP L * t.rank vSize +
            C_SPLAY_CONST L) := by
  intro ω
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  have hx12 := ht.nodup_perm_mem hx
  have hx_pos : x ≠ 0 := by omega
  rcases pushPathBody_runs p sp mem₀ pos hp_ok hbase hnb hL_hdr harena hz h0
      ht hnd hx (by omega) ω with
    ⟨st_pp, c_pp, t₁, hr_pp, hc_pp, hge_pp, ht₁, hperm₁, _hroot₁, heval₁, hsteps₁,
     hsz_pp, hdp_pp, hclean₁, hout₁, hstat₁, hlct₁⟩
  let st₀ := startState [nodesBase, x] mem₀ pos
  have hargs_pp : evalArgs w st₀ [.reg 0, .reg 1] = some [nodesBase, x] := by
    simp [evalArgs, Expr.eval, st₀, startState]
  let st₁ : State :=
    { mem := st_pp.mem, regs := Function.update st₀.regs 2 t.rootId, pos := st_pp.pos }
  have hr_call_pp : Runs w p ω (Stmt.call 2 sp.pushPath [.reg 0, .reg 1]) st₀ .normal st₁
      (2 + c_pp + 1) :=
    runs_call_iff.mpr
      ⟨[nodesBase, x], pushPathBody sp, .returned t.rootId, st_pp, c_pp, hargs_pp,
       hp_ok.pushPath_eq, hr_pp, rfl, rfl, by simp [argsSize, Expr.size]⟩
  let ptrX := nodesBase + NODE_STRIDE * x
  have hr₁_0 : st₁.regs 0 = nodesBase := by simp [st₁, st₀, startState]
  have hr₁_1 : st₁.regs 1 = x := by simp [st₁, st₀, startState]
  have ha3 : (nodePtrExpr 0 1).eval w st₁ = some ptrX :=
    eval_nodePtrExpr hstride hr₁_0 hr₁_1 (nodePtr_lt_pow hbase hx12.2)
  let st₃ : State := { st₁ with regs := Function.update st₁.regs 3 ptrX }
  have hr₃_3 : st₃.regs 3 = ptrX := by simp [st₃]
  have hnd₁ : t₁.toList.Nodup := hperm₁.nodup_iff.2 hnd
  have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.2 hx
  have hx₁_12 := ht₁.nodup_perm_mem hx₁
  let p₁ := t₁.parentIn x 0
  have hx_par₁ : nodeField st₁.mem nodesBase x OFF_PARENT = p₁ :=
    AuxTree.parentIn_eq_nodeField ht₁ hx₁
  have ha4 : (fieldLoadExpr 3 OFF_PARENT).eval w st₃ = some p₁ := by
    simpa [nodeField, st₃, p₁] using
      (eval_fieldLoadExpr hr₃_3 (nodeAddr_lt_pow hbase hx₁_12.2 (by decide))).trans
        (congrArg some hx_par₁)
  let st₄ : State := { st₃ with regs := Function.update st₃.regs 4 p₁ }
  have hL_hdr₁ : st₄.mem (nodesBase - 3) = L :=
    (hlct₁.2.2.2.2.2 (nodesBase - 3) (Or.inl ⟨by unfold NODE_STRIDE; omega, by omega⟩)).trans hL_hdr
  have harena₁ : nodesBase + NODE_STRIDE * (cap + 1) ≤ st₄.mem (nodesBase - 1) :=
    le_trans harena hge_pp
  have hz₁ : ZeroFrom st₄.mem (st₄.mem (nodesBase - 1)) := hlct₁.2.2.2.2.1
  have h0₁ : SlotZeroOk st₄.mem nodesBase :=
    memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct₁
  have hdep_eq : t₁.depthOf x = t.depthOf x := (hdp_pp x).1
  have hhp_lt₁ : st₄.mem (nodesBase - 1) + 8 * L * t₁.depthOf x < 2 ^ w := by
    change st_pp.mem (nodesBase - 1) + 8 * L * t₁.depthOf x < 2 ^ w
    rw [hdep_eq]; omega
  rcases splayLoop_credit_runs p sp hp_ok hbase hnb (t₁.depthOf x) x pp st₄ t₁ (Nat.le_refl _)
      hL_hdr₁ harena₁ hz₁ hhp_lt₁ h0₁ ht₁ hnd₁ hx₁ hclean₁
      (by simp [st₄, st₃, hr₁_0]) (by simp [st₄, st₃, hr₁_1])
      (by simp [st₄, hr₃_3, ptrX]) (by simp [st₄, p₁]) ω with
    ⟨st_lp, c_lp, t₂, hr_lp, _hlp0, hlp1, _hlp4, hge_lp, hle_lp, _h0_lp, ht₂, hroot₂, hperm₂,
     heval₂, hsteps₂, hns_lp, hrev_x, hht_x, hout₂, hlct₂, hphi_lp⟩
  have hr_ret : Runs w p ω (Stmt.ret (.reg 1)) st_lp (.returned x) st_lp 2 :=
    runs_ret_iff.mpr ⟨x, Expr.eval_reg_of_eq hlp1, rfl, rfl, rfl⟩
  let c_all := 1 + ((2 + c_pp + 1) + (6 + (5 + (c_lp + 2 + 1) + 1) + 1) + 1) + 1
  have hr_body : Runs w p ω (splayBody sp) st₀ (.returned x) st_lp c_all := by
    refine runs_cond_iff.mpr ⟨x, _, Expr.eval_reg_of_eq (by simp [st₀, startState]), ?_, rfl⟩
    have hloop_ret := runs_seq_iff.mpr (Or.inr ⟨st_lp, c_lp, 2, hr_lp, hr_ret, rfl⟩)
    have h4_lr := runs_seq_iff.mpr
      (Or.inr ⟨st₄, 5, _, runs_assign_iff.mpr ⟨p₁, ha4, rfl, rfl, rfl⟩, hloop_ret, rfl⟩)
    have h3_4 := runs_seq_iff.mpr
      (Or.inr ⟨st₃, 6, _, runs_assign_iff.mpr ⟨ptrX, ha3, rfl, rfl, rfl⟩, h4_lr, rfl⟩)
    have h_all := runs_seq_iff.mpr (Or.inr ⟨st₁, 2 + c_pp + 1, _, hr_call_pp, h3_4, rfl⟩)
    simpa [splayBody, hx_pos, splayLoopBody] using h_all
  have hge_all : mem₀ (nodesBase - 1) ≤ st_lp.mem (nodesBase - 1) := le_trans hge_pp hge_lp
  have hle_all : st_lp.mem (nodesBase - 1) ≤
      mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x := by
    change st_lp.mem (nodesBase - 1) ≤ st_pp.mem (nodesBase - 1) + 8 * L * t₁.depthOf x at hle_lp
    rw [hdep_eq] at hle_lp; omega
  refine ⟨st_lp, c_all, t₂, hr_body, hge_all, hle_all, ht₂, hroot₂, hperm₂.trans hperm₁,
    heval₂.trans heval₁, hsteps₂.trans hsteps₁, hrev_x, hht_x, ?_, ?_,
    lctFrame_trans hlct₁ hlct₂, fun vSize => ?_⟩
  · intro u hu_le hu_nin off hoff
    have hu₁ : u ∉ t₁.toList := fun hm => hu_nin (hperm₁.mem_iff.1 hm)
    exact (hout₂ u hu_le hu₁ off hoff).trans (hout₁ u hu_le hu_nin off hoff)
  · intro u hu_le off hoff
    exact (hns_lp u hu_le off (isStaticPayloadOff_nonStruct hoff)).trans (hstat₁ u hu_le off hoff)
  · rcases hsz_pp vSize with ⟨hsz₁, hphi₁⟩
    rcases hphi_lp vSize with ⟨hsz₂, hphi₂⟩
    have hrank_out : t₂.rank vSize = t.rank vSize := by simp [AuxTree.rank, hsz₂, hsz₁]
    have hrank_x_mul : 3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
        3 * K_SPLAY_STEP L * (t₁.findSubtree x).rank vSize :=
      Nat.mul_le_mul_left _ (AuxTree.findSubtree_rank_ge vSize hx₁)
    have hdiv_mod : t.depthOf x = 2 * (t.depthOf x / 2) + t.depthOf x % 2 := by omega
    have hmod_le : t.depthOf x % 2 ≤ 1 := by omega
    have hc_pp_bound : c_pp + (st_pp.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤
        K_PUSH_PATH L * (t.depthOf x % 2) + K_PUSH_PATH L + 2 * K_PUSH_PATH L * (t.depthOf x / 2) := by
      have h1 : K_PUSH_PATH L * (t.depthOf x + 1) =
          K_PUSH_PATH L * (2 * (t.depthOf x / 2) + t.depthOf x % 2 + 1) := by rw [← hdiv_mod]
      rw [h1] at hc_pp; clear h1
      calc c_pp + (st_pp.mem (nodesBase - 1) - mem₀ (nodesBase - 1))
          ≤ K_PUSH_PATH L * (2 * (t.depthOf x / 2) + t.depthOf x % 2 + 1) := hc_pp
        _ = K_PUSH_PATH L * (t.depthOf x % 2) + K_PUSH_PATH L +
              2 * K_PUSH_PATH L * (t.depthOf x / 2) := by ring
    have hc_const : K_PUSH_PATH L * (t.depthOf x % 2) + K_PUSH_PATH L +
        ((K_ROTATE L + 40) * (t.depthOf x % 2) + 2) + 22 ≤ C_SPLAY_CONST L := by
      have h1 := Nat.mul_le_mul_left (K_PUSH_PATH L) hmod_le
      have h2 := Nat.mul_le_mul_left (K_ROTATE L + 40) hmod_le
      have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right h1 (K_PUSH_PATH L))
        (Nat.add_le_add_right h2 2)) (le_refl 22)
      have hconst_L : K_PUSH_PATH L * 1 + K_PUSH_PATH L + ((K_ROTATE L + 40) * 1 + 2) + 22 ≤
          C_SPLAY_CONST L := by
        unfold K_PUSH_PATH K_PUSH_DOWN K_ROTATE K_PULL C_SPLAY_CONST; omega
      exact le_trans hsum hconst_L
    have hm4 : st₄.mem (nodesBase - 1) = st_pp.mem (nodesBase - 1) := rfl
    have hge_lp' : st_pp.mem (nodesBase - 1) ≤ st_lp.mem (nodesBase - 1) := hge_lp
    have hdiff_tot : st_lp.mem (nodesBase - 1) - mem₀ (nodesBase - 1) =
        (st_lp.mem (nodesBase - 1) - st_pp.mem (nodesBase - 1)) +
        (st_pp.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) := by omega
    rw [hdep_eq, hrank_out, hm4, hphi₁] at hphi₂
    refine ⟨hsz₂.trans hsz₁, ?_⟩
    dsimp only [c_all]
    rw [hdiff_tot]
    exact splay_body_arith hc_pp_bound hphi₂ hrank_x_mul hc_const

/-- LCT-aware forest splay theorem retaining `200 * (t.depthOf x / 2)` descend-credit
plus `SafeMem` preservation across `splayBody`. -/
theorem splayForest_lct_credit_runs {w h L : ℕ} (p : Program) (sp : SplayProcs)
    (mem_safe mem₀ : ℕ → ℕ) (nb cap hp0 pos : ℕ) {trees : List AuxTree}
    (hp_has : p.HasAt sp.numZero (splayBodies sp h))
    (hp_base : ∃ spB, sp = SplayProcs.atBase spB)
    (hp_ok : SplayProgramOk w h p sp)
    (hz0_safe : SlotZeroOk mem_safe nb)
    (harena_safe : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hsafe : SafeMem mem_safe nb cap hp0 mem₀)
    (hok : SplayForestOk w h L mem₀ nb cap trees)
    {t : AuxTree} {rest : List AuxTree} {x : ℕ}
    (ht_perm : trees.Perm (t :: rest)) (hx : x ∈ t.toList)
    (hhp_lt : mem₀ (nb - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x < 2 ^ w) :
    ∀ ω, ∃ st' c t',
      Runs w p ω (splayBody sp) (startState [nb, x] mem₀ pos) (.returned x) st' c ∧
      SplayForestOk w h L st'.mem nb cap (t' :: rest) ∧
      SafeMem mem_safe nb cap hp0 st'.mem ∧
      t'.rootId = x ∧
      t'.toList.Perm t.toList ∧
      t'.evalInorder (revFlag st'.mem nb) false = t.evalInorder (revFlag mem₀ nb) false ∧
      evalMemSteps st'.mem nb h L t' false 0 = evalMemSteps mem₀ nb h L t false 0 ∧
      revFlag st'.mem nb x = false ∧
      nodeField st'.mem nb x OFF_HAS_TAG = 0 ∧
      nodeField st'.mem nb x OFF_PPAR = nodeField mem₀ nb t.rootId OFF_PPAR ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nb u off = nodeField mem₀ nb u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nb u off = nodeField mem₀ nb u off) ∧
      LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem₀ st'.mem ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        c + 200 * (t.depthOf x / 2) + (st'.mem (nb - 1) - mem₀ (nb - 1)) +
          splayMemPhi (K_SPLAY_STEP L) st'.mem nb cap vSize +
          3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
          splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap vSize +
            3 * K_SPLAY_STEP L * t.rank vSize + C_SPLAY_CONST L) := by
  intro ω
  rcases hp_base with ⟨spB, rfl⟩
  have hmem_t : t ∈ trees := ht_perm.symm.subset (by simp)
  have ht_m := (SplayForestOk.trees_ok hok t hmem_t).2.2
  have hnd_all : (trees.flatMap AuxTree.toList).Nodup :=
    (SplayForestOk.perm hok).nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hnd : t.toList.Nodup := list_nodup_of_flatMap_nodup hnd_all hmem_t
  have hnb3 : 3 ≤ nb := hok.2.2.1
  have harena : nb + NODE_STRIDE * (cap + 1) ≤ mem₀ (nb - 1) := hok.2.2.2.1
  have hL : mem₀ (nb - 3) = L := hok.2.2.2.2.1
  have hmem_lt : mem₀ (nb - 1) < 2 ^ w := hok.2.2.2.2.2.1
  have hbase_lt : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := lt_of_le_of_lt harena hmem_lt
  have hz : ZeroFrom mem₀ (mem₀ (nb - 1)) := hok.2.2.2.2.2.2.1
  have hz0 : SlotZeroOk mem₀ nb := hok.2.2.2.2.2.2.2.1
  rcases splayBody_credit_runs p (SplayProcs.atBase spB) mem₀ pos hp_ok hbase_lt hnb3 hL harena
      hz hz0 ht_m hnd hx hhp_lt ω with
    ⟨st', c, t', hr, hge, hle, ht', hrt', hprm', hev', hstps', hrv', hht', hout', hstat',
     hlct', hphi'⟩
  have hx_le : x ≤ cap := by
    have hm := (SplayForestOk.perm hok).mem_iff.1 (List.mem_flatMap.2 ⟨t, hmem_t, hx⟩)
    rcases List.mem_map.1 hm with ⟨y, hy, rfl⟩; rw [List.mem_range] at hy; omega
  have hsafe' : SafeMem mem_safe nb cap hp0 st'.mem := by
    rcases hr with ⟨fuel, hex⟩
    exact (splay_safeExec (spBase := spB) hp_has hnb3 harena_safe hz0_safe hx_le
      (by simp [startState]) (by simp [startState]) hsafe hex).2
  have hpp_same : nodeField st'.mem nb x OFF_PPAR = nodeField mem₀ nb t.rootId OFF_PPAR := by
    cases ht'_eq : t' with
    | leaf => simp [ht'_eq, AuxTree.toList] at hprm'; cases t <;> simp_all [AuxTree.toList]
    | node id' l' r' =>
        have hid' : id' = x := by simpa [ht'_eq, AuxTree.rootId] using hrt'
        rw [← hid']; simp only [ht'_eq, TreeMemMatch] at ht'; exact ht'.2.2.2.2.2.1
  have hne' : t' ≠ .leaf := by
    intro hle'; subst hle'; simp [AuxTree.toList] at hprm'; cases t <;> simp_all [AuxTree.toList]
  have hpp_lt' : nodeField mem₀ nb t.rootId OFF_PPAR < 2 ^ w :=
    (SplayForestOk.trees_ok hok t hmem_t).2.1
  have hok' := SplayForestOk.replace_tree hok ht_perm hlct'
    (lt_of_le_of_lt hle hhp_lt) hne' hprm' ht' hpp_lt' hout'
  refine ⟨st', c, t', hr, hok', hsafe', hrt', hprm', hev', hstps', hrv', hht', hpp_same,
    hout', hstat', hlct', fun vSize => ?_⟩
  rcases hphi' vSize with ⟨hsz, hc_phi⟩
  have hsum_eq₀ : (trees.map (AuxTree.treePhi vSize)).sum =
      t.treePhi vSize + (rest.map (AuxTree.treePhi vSize)).sum := by
    simpa [List.map_cons, List.sum_cons] using (ht_perm.map (AuxTree.treePhi vSize)).sum_eq
  have hsum_eq₁ : ((t' :: rest).map (AuxTree.treePhi vSize)).sum =
      t'.treePhi vSize + (rest.map (AuxTree.treePhi vSize)).sum := by
    simp [List.map_cons, List.sum_cons]
  rw [splayMemPhi_eq_sum hok, splayMemPhi_eq_sum hok', hsum_eq₀, hsum_eq₁,
    Nat.mul_add, Nat.mul_add]
  exact ⟨hsz, by omega⟩

end SplayCredit

section DescendExtreme

private lemma evalInorder_ne_nil_of_ne_leaf (rev : ℕ → Bool) {s : AuxTree} (hne : s ≠ .leaf)
    (b : Bool) : s.evalInorder rev b ≠ [] := by
  intro h
  have hlen := s.length_evalInorder rev b
  rw [h, List.length_nil] at hlen
  cases s with
  | leaf => exact hne rfl
  | node id l r => simp [AuxTree.countNodes] at hlen; omega

private lemma evalInorder_children_eq (rev : ℕ → Bool) (id : ℕ) (l r : AuxTree) (b : Bool) :
    let lc := if b then r else l
    let rc := if b then l else r
    let b' := Bool.xor b (rev id)
    (AuxTree.node id l r).evalInorder rev b =
      lc.evalInorder rev b' ++ [id] ++ rc.evalInorder rev b' := by
  cases b with
  | false => simp [AuxTree.evalInorder.eq_2]
  | true => simp [AuxTree.evalInorder.eq_3]

/-- Pure downward walk to the leftmost (`goLeft = true`) or rightmost (`goLeft = false`)
node in an `AuxTree`, tracking accumulated `OFF_REV` parity without modifying memory. -/
def descendExtremeLoop (goLeft : Bool) : Stmt :=
  .loop (.reg 3)
    (.assign 4 (nodePtrExpr 0 1) ;;
     .cond (.reg 2)
       (.assign 5 (fieldLoadExpr 4 (if goLeft then OFF_RIGHT else OFF_LEFT)))
       (.assign 5 (fieldLoadExpr 4 (if goLeft then OFF_LEFT else OFF_RIGHT))) ;;
     .cond (.reg 5)
       (.assign 6 (fieldLoadExpr 4 OFF_REV) ;;
        .cond (.reg 6) (.assign 2 (.bin .sub (.const 1) (.reg 2))) .nop ;;
        .assign 1 (.reg 5))
       (.assign 3 (.const 0)))

theorem descendExtremeLoop_noRand (goLeft : Bool) : (descendExtremeLoop goLeft).NoRand := by
  simp [descendExtremeLoop, Stmt.NoRand]

/-- Execution specification for `descendExtremeLoop` on any non-empty `AuxTree`:
returns in `≤ 40 * s.depthOf x + 40` steps with zero memory writes, preserving all registers
`r ≥ 7` and returning the head (`goLeft = true`) or last (`goLeft = false`) inorder node `x`. -/
theorem runs_descendExtremeLoop {w h L nb cap : ℕ} (p : Program) (goLeft : Bool)
    (mem : ℕ → ℕ) (hbase : nb + NODE_STRIDE * (cap + 1) < 2 ^ w) :
    ∀ s parId pp (b : Bool) (st : State),
      TreeMemMatch w h L mem nb cap s parId pp → s ≠ .leaf → s.toList.Nodup →
      st.mem = mem → st.regs 0 = nb → st.regs 1 = s.rootId →
      st.regs 2 = (if b then 1 else 0) → st.regs 3 = 1 →
      ∀ ω, ∃ st' c x,
        Runs w p ω (descendExtremeLoop goLeft) st .normal st' c ∧
        st'.mem = mem ∧ st'.regs 0 = nb ∧ st'.regs 1 = x ∧ x ∈ s.toList ∧
        (∀ r, 7 ≤ r → st'.regs r = st.regs r) ∧
        c ≤ 40 * s.depthOf x + 40 ∧
        (goLeft = true → (s.evalInorder (revFlag mem nb) b).head? = some x) ∧
        (goLeft = false → (s.evalInorder (revFlag mem nb) b).getLast? = some x) := by
  intro s
  induction s with
  | leaf => intro _ _ _ _ _ hne; exact absurd rfl hne
  | node id l r ihl ihr =>
      intro parId pp b st ht _ hnd hm hr0 hr1 hr2 hr3 ω
      have hnd' := hnd
      simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨_, _, hid_nin_l⟩, _, hdisj_lr⟩
      have hid_nin_r : id ∉ r.toList := fun hr => hdisj_lr id (Or.inr rfl) id hr rfl
      have hdisj : ∀ z, z ∈ l.toList → z ∈ r.toList → False := fun z hl hr =>
        hdisj_lr z (Or.inl hl) z hr rfl
      rcases ht with ⟨hx1, hx2, hL, hR, _hP, _hPP, hrev_le, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, hml, hmr⟩
      have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
      have hcap_lt : cap < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
      have hw1 : 1 < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
      have hptr_lt : nb + NODE_STRIDE * id < 2 ^ w := nodePtr_lt_pow hbase hx2
      have hL_lt : nb + NODE_STRIDE * id + OFF_LEFT < 2 ^ w :=
        nodeAddr_lt_pow hbase hx2 (by decide)
      have hR_lt : nb + NODE_STRIDE * id + OFF_RIGHT < 2 ^ w :=
        nodeAddr_lt_pow hbase hx2 (by decide)
      have hRev_lt : nb + NODE_STRIDE * id + OFF_REV < 2 ^ w :=
        nodeAddr_lt_pow hbase hx2 (by decide)
      have he_ptr : (nodePtrExpr 0 1).eval w st = some (nb + NODE_STRIDE * id) :=
        eval_nodePtrExpr hstride hr0 (by simpa [AuxTree.rootId] using hr1) hptr_lt
      let st1 : State :=
        { mem := mem, regs := Function.update st.regs 4 (nb + NODE_STRIDE * id), pos := st.pos }
      have hrun1 : Runs w p ω (.assign 4 (nodePtrExpr 0 1)) st .normal st1 6 := by
        rw [runs_assign_iff]
        exact ⟨nb + NODE_STRIDE * id, he_ptr, rfl, by simp [st1, hm], by decide⟩
      have hst1_2 : st1.regs 2 = if b then 1 else 0 := by simp [st1, hr2]
      have hst1_4 : st1.regs 4 = nb + NODE_STRIDE * id := by simp [st1]
      let ch := if goLeft then (if b then r else l) else (if b then l else r)
      let st2 : State := { mem := mem, regs := Function.update st1.regs 5 ch.rootId, pos := st.pos }
      have hch_eq : ch.rootId =
          if b then nodeField mem nb id (if goLeft then OFF_RIGHT else OFF_LEFT)
          else nodeField mem nb id (if goLeft then OFF_LEFT else OFF_RIGHT) := by
        cases goLeft <;> cases b <;> simp [ch, hL, hR]
      have hrun2 : Runs w p ω
          (.cond (.reg 2)
            (.assign 5 (fieldLoadExpr 4 (if goLeft then OFF_RIGHT else OFF_LEFT)))
            (.assign 5 (fieldLoadExpr 4 (if goLeft then OFF_LEFT else OFF_RIGHT))))
          st1 .normal st2 7 := by
        rw [runs_cond_iff]
        refine ⟨st1.regs 2, 5, Expr.eval_reg w 2 st1, ?_, by decide⟩
        cases b <;> cases goLeft <;>
          simp only [hst1_2, Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero]
        · rw [runs_assign_iff]
          exact ⟨r.rootId, (eval_fieldLoadExpr (st := st1) hst1_4 hR_lt).trans (congrArg some hR),
            rfl, by simp [st2, st1, ch], by decide⟩
        · rw [runs_assign_iff]
          exact ⟨l.rootId, (eval_fieldLoadExpr (st := st1) hst1_4 hL_lt).trans (congrArg some hL),
            rfl, by simp [st2, st1, ch], by decide⟩
        · rw [runs_assign_iff]
          exact ⟨l.rootId, (eval_fieldLoadExpr (st := st1) hst1_4 hL_lt).trans (congrArg some hL),
            rfl, by simp [st2, st1, ch], by decide⟩
        · rw [runs_assign_iff]
          exact ⟨r.rootId, (eval_fieldLoadExpr (st := st1) hst1_4 hR_lt).trans (congrArg some hR),
            rfl, by simp [st2, st1, ch], by decide⟩
      have hst2_0 : st2.regs 0 = nb := by simp [st2, st1, hr0]
      have hst2_2 : st2.regs 2 = if b then 1 else 0 := by simp [st2, hst1_2]
      have hst2_3 : st2.regs 3 = 1 := by simp [st2, st1, hr3]
      have hst2_4 : st2.regs 4 = nb + NODE_STRIDE * id := by simp [st2, hst1_4]
      have hst2_5 : st2.regs 5 = ch.rootId := by simp [st2]
      have hst2_ge7 : ∀ reg, 7 ≤ reg → st2.regs reg = st.regs reg := fun reg hreg => by
        simp [st2, st1, Function.update_of_ne (by omega : reg ≠ 5),
          Function.update_of_ne (by omega : reg ≠ 4)]
      have hnd_l : l.toList.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
      have hnd_r : r.toList.Nodup := (List.nodup_append.mp hnd).2.1
      have hch_nd : ch.toList.Nodup := by
        cases goLeft <;> cases b <;> simp only [ch, ↓reduceIte]
        · exact hnd_r
        · exact hnd_l
        · exact hnd_l
        · exact hnd_r
      cases hch_eq_c : ch with
      | leaf =>
          have h5z : st2.regs 5 = 0 := by simp [hst2_5, hch_eq_c, AuxTree.rootId]
          let st3 : State := { mem := mem, regs := Function.update st2.regs 3 0, pos := st.pos }
          have hrun3 : Runs w p ω
              (.cond (.reg 5)
                (.assign 6 (fieldLoadExpr 4 OFF_REV) ;;
                 .cond (.reg 6) (.assign 2 (.bin .sub (.const 1) (.reg 2))) .nop ;;
                 .assign 1 (.reg 5))
                (.assign 3 (.const 0))) st2 .normal st3 4 := by
            rw [runs_cond_iff]
            refine ⟨0, 2, by simpa [h5z] using Expr.eval_reg w 5 st2, ?_, by decide⟩
            simp only [↓reduceIte]
            rw [runs_assign_iff]
            exact ⟨0, Expr.eval_const (by omega), rfl, rfl, by decide⟩
          have hbody : Runs w p ω
              (.assign 4 (nodePtrExpr 0 1) ;;
               .cond (.reg 2)
                 (.assign 5 (fieldLoadExpr 4 (if goLeft then OFF_RIGHT else OFF_LEFT)))
                 (.assign 5 (fieldLoadExpr 4 (if goLeft then OFF_LEFT else OFF_RIGHT))) ;;
               .cond (.reg 5)
                 (.assign 6 (fieldLoadExpr 4 OFF_REV) ;;
                  .cond (.reg 6) (.assign 2 (.bin .sub (.const 1) (.reg 2))) .nop ;;
                  .assign 1 (.reg 5))
                 (.assign 3 (.const 0))) st .normal st3 19 :=
            runs_seq_iff.mpr (Or.inr ⟨st1, 6, 12, hrun1,
              runs_seq_iff.mpr (Or.inr ⟨st2, 7, 4, hrun2, hrun3, rfl⟩), rfl⟩)
          have hexit : Runs w p ω (descendExtremeLoop goLeft) st3 .normal st3 2 :=
            runs_loop_iff.mpr (Or.inl ⟨by simp [st3, Expr.eval_reg], rfl, rfl, rfl⟩)
          refine ⟨st3, 23, id,
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st3, 19, 2, by simpa [hr3] using Expr.eval_reg w 3 st,
              by decide, hbody, hexit, rfl⟩)),
            rfl, by simp [st3, hst2_0], by simp [st3, st2, st1, hr1, AuxTree.rootId],
            by simp [AuxTree.toList], fun reg hreg => by simp [st3, Function.update_of_ne (by omega : reg ≠ 3), hst2_ge7 reg hreg],
            by simp [AuxTree.depthOf.eq_2], ?_, ?_⟩
          · intro hgl; subst hgl
            have hinv := evalInorder_children_eq (revFlag mem nb) id l r b
            dsimp only at hinv; rw [hinv]
            cases hb : b
            · have hleaf : l = .leaf := by simpa [ch, hb] using hch_eq_c
              simp [hleaf, AuxTree.evalInorder.eq_1]
            · have hleaf : r = .leaf := by simpa [ch, hb] using hch_eq_c
              simp [hleaf, AuxTree.evalInorder.eq_1]
          · intro hgl; subst hgl
            have hinv := evalInorder_children_eq (revFlag mem nb) id l r b
            dsimp only at hinv; rw [hinv]
            cases hb : b
            · have hleaf : r = .leaf := by simpa [ch, hb] using hch_eq_c
              simp [hleaf, AuxTree.evalInorder.eq_1]
            · have hleaf : l = .leaf := by simpa [ch, hb] using hch_eq_c
              simp [hleaf, AuxTree.evalInorder.eq_1]
      | node cid cl cr =>
          have hch_match : TreeMemMatch w h L mem nb cap ch id 0 := by
            cases goLeft <;> cases b <;> simp only [ch, ↓reduceIte]
            · exact hmr
            · exact hml
            · exact hml
            · exact hmr
          have hcid_pos : 1 ≤ cid := by
            have hm' := hch_match; rw [hch_eq_c, TreeMemMatch.eq_2] at hm'; exact hm'.1
          have h5nz : st2.regs 5 ≠ 0 := by simp [hst2_5, hch_eq_c, AuxTree.rootId]; omega
          have hch_ne : ch ≠ .leaf := by simp [hch_eq_c]
          let b' := Bool.xor b (revFlag mem nb id)
          let rval := nodeField mem nb id OFF_REV
          let st2a : State := { mem := mem, regs := Function.update st2.regs 6 rval, pos := st.pos }
          have hrun2a : Runs w p ω (.assign 6 (fieldLoadExpr 4 OFF_REV)) st2 .normal st2a 5 := by
            rw [runs_assign_iff]; exact ⟨rval, eval_fieldLoadExpr hst2_4 hRev_lt, rfl, rfl, by decide⟩
          let accNew := if b' then 1 else 0
          let st2b : State :=
            if rval = 0 then st2a
            else { mem := mem, regs := Function.update st2a.regs 2 (1 - st2a.regs 2), pos := st.pos }
          have hst2b_2 : st2b.regs 2 = accNew := by
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hrev_le with hr | hr
            · have hr0 : rval = 0 := hr
              have hbf : revFlag mem nb id = false := by simp [revFlag, hr]
              have h2a : st2b.regs 2 = st2.regs 2 := by simp [st2b, hr0, st2a]
              rw [h2a, hst2_2]
              simp only [accNew, b', hbf]; cases b <;> decide
            · have hbt : revFlag mem nb id = true := by simp [revFlag, hr]
              have h2a : st2b.regs 2 = 1 - st2.regs 2 := by
                have hne : rval ≠ 0 := by dsimp only [rval]; omega
                simp [st2b, hne, st2a]
              rw [h2a, hst2_2]
              simp only [accNew, b', hbt]; cases b <;> decide
          have hrun2b : ∃ c2b, Runs w p ω
              (.cond (.reg 6) (.assign 2 (.bin .sub (.const 1) (.reg 2))) .nop) st2a .normal st2b c2b ∧
              c2b ≤ 6 := by
            by_cases hr : rval = 0
            · refine ⟨3, ?_, by decide⟩
              rw [runs_cond_iff]
              refine ⟨0, 1, by simp [st2a, hr, Expr.eval_reg], ?_, by decide⟩
              simp [hr, st2b, runs_nop_iff]
            · refine ⟨6, ?_, by decide⟩
              rw [runs_cond_iff]
              refine ⟨rval, 4, by simp [st2a, Expr.eval_reg], ?_, by decide⟩
              simp only [hr, ↓reduceIte]
              rw [runs_assign_iff]
              refine ⟨1 - st2a.regs 2, Expr.eval_sub (Expr.eval_const hw1) (Expr.eval_reg w 2 st2a) hw1,
                rfl, ?_, by decide⟩
              simp [st2b, st2a, hr]
          rcases hrun2b with ⟨c2b, hrun2b, hc2b⟩
          let st2c : State := { mem := mem, regs := Function.update st2b.regs 1 cid, pos := st.pos }
          have hrun2c : Runs w p ω (.assign 1 (.reg 5)) st2b .normal st2c 2 := by
            rw [runs_assign_iff]
            refine ⟨cid, ?_, rfl, ?_, by decide⟩
            · have h5b : st2b.regs 5 = cid := by
                by_cases hr : rval = 0 <;> simp [st2b, hr, st2a, hst2_5, hch_eq_c, AuxTree.rootId]
              simpa [h5b] using Expr.eval_reg w 5 st2b
            · by_cases hr : rval = 0 <;> simp [st2c, st2b, hr, st2a]
          have hrun3 : ∃ c3, Runs w p ω
              (.cond (.reg 5)
                (.assign 6 (fieldLoadExpr 4 OFF_REV) ;;
                 .cond (.reg 6) (.assign 2 (.bin .sub (.const 1) (.reg 2))) .nop ;;
                 .assign 1 (.reg 5))
                (.assign 3 (.const 0))) st2 .normal st2c c3 ∧ c3 ≤ 17 :=
            ⟨1 + (5 + (c2b + 2 + 1) + 1) + 1, runs_cond_iff.mpr ⟨st2.regs 5, _,
              Expr.eval_reg w 5 st2, by
                simp only [h5nz, ↓reduceIte]
                exact runs_seq_iff.mpr (Or.inr ⟨st2a, 5, c2b + 2 + 1, hrun2a,
                  runs_seq_iff.mpr (Or.inr ⟨st2b, c2b, 2, hrun2b, hrun2c, rfl⟩), rfl⟩),
              rfl⟩, by omega⟩
          rcases hrun3 with ⟨c3, hrun3, hc3⟩
          have hbody : ∃ cbody, Runs w p ω
              (.assign 4 (nodePtrExpr 0 1) ;;
               .cond (.reg 2)
                 (.assign 5 (fieldLoadExpr 4 (if goLeft then OFF_RIGHT else OFF_LEFT)))
                 (.assign 5 (fieldLoadExpr 4 (if goLeft then OFF_LEFT else OFF_RIGHT))) ;;
               .cond (.reg 5)
                 (.assign 6 (fieldLoadExpr 4 OFF_REV) ;;
                  .cond (.reg 6) (.assign 2 (.bin .sub (.const 1) (.reg 2))) .nop ;;
                  .assign 1 (.reg 5))
                 (.assign 3 (.const 0))) st .normal st2c cbody ∧ cbody ≤ 32 :=
            ⟨6 + (7 + c3 + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨st1, 6, 7 + c3 + 1, hrun1,
              runs_seq_iff.mpr (Or.inr ⟨st2, 7, c3, hrun2, hrun3, rfl⟩), rfl⟩), by omega⟩
          rcases hbody with ⟨cbody, hbody, hcbody⟩
          have hst2c_0 : st2c.regs 0 = nb := by
            by_cases hr : rval = 0 <;> simp [st2c, st2b, hr, st2a, hst2_0]
          have hst2c_1 : st2c.regs 1 = ch.rootId := by simp [st2c, hch_eq_c, AuxTree.rootId]
          have hst2c_2 : st2c.regs 2 = if b' then 1 else 0 := by simp [st2c, hst2b_2, accNew]
          have hst2c_3 : st2c.regs 3 = 1 := by
            by_cases hr : rval = 0 <;> simp [st2c, st2b, hr, st2a, hst2_3]
          have hst2c_ge7 : ∀ reg, 7 ≤ reg → st2c.regs reg = st.regs reg := fun reg hreg => by
            dsimp only [st2c]; rw [Function.update_of_ne (by omega : reg ≠ 1)]
            by_cases hr : rval = 0
            · simp [st2b, hr, st2a, Function.update_of_ne (by omega : reg ≠ 6), hst2_ge7 reg hreg]
            · simp [st2b, hr, st2a, Function.update_of_ne (by omega : reg ≠ 2),
                Function.update_of_ne (by omega : reg ≠ 6), hst2_ge7 reg hreg]
          have hch_ih : ∃ st' c x,
              Runs w p ω (descendExtremeLoop goLeft) st2c .normal st' c ∧
              st'.mem = mem ∧ st'.regs 0 = nb ∧ st'.regs 1 = x ∧ x ∈ ch.toList ∧
              (∀ reg, 7 ≤ reg → st'.regs reg = st2c.regs reg) ∧
              c ≤ 40 * ch.depthOf x + 40 ∧
              (goLeft = true → (ch.evalInorder (revFlag mem nb) b').head? = some x) ∧
              (goLeft = false → (ch.evalInorder (revFlag mem nb) b').getLast? = some x) := by
            cases goLeft <;> cases b <;>
              simp only [ch, Bool.false_eq_true, ↓reduceIte] at hch_ne hch_nd hst2c_1
            · simpa [ch] using ihr id 0 b' st2c hmr hch_ne hch_nd rfl hst2c_0 hst2c_1 hst2c_2 hst2c_3 ω
            · simpa [ch] using ihl id 0 b' st2c hml hch_ne hch_nd rfl hst2c_0 hst2c_1 hst2c_2 hst2c_3 ω
            · simpa [ch] using ihl id 0 b' st2c hml hch_ne hch_nd rfl hst2c_0 hst2c_1 hst2c_2 hst2c_3 ω
            · simpa [ch] using ihr id 0 b' st2c hmr hch_ne hch_nd rfl hst2c_0 hst2c_1 hst2c_2 hst2c_3 ω
          rcases hch_ih with ⟨st', ctail, x, htail, hstm, hr0', hr1', hxch, hge7', hctail, hhd, hlast⟩
          have hxs : x ∈ (AuxTree.node id l r).toList := by
            cases goLeft <;> cases b <;>
              simp only [ch, Bool.false_eq_true, ↓reduceIte] at hxch <;> simp [AuxTree.toList, hxch]
          have hdepth : (AuxTree.node id l r).depthOf x = ch.depthOf x + 1 := by
            have hx_ne : x ≠ id := by
              cases goLeft <;> cases b <;>
                simp only [ch, Bool.false_eq_true, ↓reduceIte] at hxch
              · exact fun h => hid_nin_r (h ▸ hxch)
              · exact fun h => hid_nin_l id (h ▸ hxch) id rfl rfl
              · exact fun h => hid_nin_l id (h ▸ hxch) id rfl rfl
              · exact fun h => hid_nin_r (h ▸ hxch)
            rw [AuxTree.depthOf.eq_2, ite_eq_right hx_ne]
            cases goLeft <;> cases b <;>
              simp only [ch, Bool.false_eq_true, ↓reduceIte] at hxch ⊢
            · rw [ite_eq_right (fun hm => hdisj x hm hxch), ite_eq_left hxch]
            · exact ite_eq_left hxch
            · exact ite_eq_left hxch
            · rw [ite_eq_right (fun hm => hdisj x hm hxch), ite_eq_left hxch]
          refine ⟨st', 1 + cbody + ctail + 1, x,
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2c, cbody, ctail,
              by simpa [hr3] using Expr.eval_reg w 3 st, by decide, hbody, htail, rfl⟩)),
            hstm, hr0', hr1', hxs,
            fun reg hreg => (hge7' reg hreg).trans (hst2c_ge7 reg hreg),
            by rw [hdepth]; omega, ?_, ?_⟩
          · intro hgl; subst hgl
            have hhd_x := hhd rfl
            cases b
            · have hinv := evalInorder_children_eq (revFlag mem nb) id l r false
              simp only [ch, Bool.false_eq_true, ↓reduceIte] at hch_ne hhd_x
              have hne_ch : (l.evalInorder (revFlag mem nb) (Bool.xor false (revFlag mem nb id))) ≠ [] :=
                evalInorder_ne_nil_of_ne_leaf _ hch_ne _
              simp only [Bool.false_eq_true, ↓reduceIte] at hinv
              rw [hinv, List.append_assoc, List.head?_append_of_ne_nil _ hne_ch]
              exact hhd_x
            · have hinv := evalInorder_children_eq (revFlag mem nb) id l r true
              simp only [ch, ↓reduceIte] at hch_ne hhd_x
              have hne_ch : (r.evalInorder (revFlag mem nb) (Bool.xor true (revFlag mem nb id))) ≠ [] :=
                evalInorder_ne_nil_of_ne_leaf _ hch_ne _
              simp only [↓reduceIte] at hinv
              rw [hinv, List.append_assoc, List.head?_append_of_ne_nil _ hne_ch]
              exact hhd_x
          · intro hgl; subst hgl
            have hlast_x := hlast rfl
            cases b
            · have hinv := evalInorder_children_eq (revFlag mem nb) id l r false
              simp only [ch, Bool.false_eq_true, ↓reduceIte] at hch_ne hlast_x
              have hne_ch : (r.evalInorder (revFlag mem nb) (Bool.xor false (revFlag mem nb id))) ≠ [] :=
                evalInorder_ne_nil_of_ne_leaf _ hch_ne _
              simp only [Bool.false_eq_true, ↓reduceIte] at hinv
              rw [hinv, List.getLast?_append_of_ne_nil _ hne_ch]
              exact hlast_x
            · have hinv := evalInorder_children_eq (revFlag mem nb) id l r true
              simp only [ch, Bool.false_eq_true, ↓reduceIte] at hch_ne hlast_x
              have hne_ch : (l.evalInorder (revFlag mem nb) (Bool.xor true (revFlag mem nb id))) ≠ [] :=
                evalInorder_ne_nil_of_ne_leaf _ hch_ne _
              simp only [↓reduceIte] at hinv
              rw [hinv, List.getLast?_append_of_ne_nil _ hne_ch]
              exact hlast_x

end DescendExtreme

end MinCostFlow.LinkCut.Prog
