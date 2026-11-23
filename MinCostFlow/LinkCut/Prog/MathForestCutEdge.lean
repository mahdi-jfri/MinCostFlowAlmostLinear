module

public import MinCostFlow.LinkCut.Prog.MathForestCutSetup

/-!
# The edge step of `cut`

This file runs `lctCutEdgeBody`, the part of `cut` after `expose (y + 1)` has found a path with
exactly two vertices. The path is then `[z + 1, ed, y + 1]` for one vertex `z` and one edge
node `ed` (`vcnt_eq_two_path`). The program reads the endpoints of `ed`. If they are not `x` and
`y`, the forest has no edge `{x, y}` and nothing changes. Otherwise `z = x`, and the program
splays `ed` and runs the write of `cut`. The main result is `lctCutEdgeBody_runs`. It gives the
new invariants, the new edge map, and the amortized cost of this step.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section CutEdgeHelpers

/-- How the represented parent map changes in the last part of `cut`. Either nothing changes
and `F.cut x y = F`, or an edge `{x, y}` is removed: its edge node `ed` (an id above `F.n`)
and both ends lose their parents. -/
def CutParShape (par₂ par' : ℕ → ℕ) (F : MathForest) (x y : ℕ) : Prop :=
  ((∀ q, par' q = par₂ q) ∧ F.cut x y = F) ∨
  (F.cut x y ≠ F ∧ ∃ ed, F.n + 1 ≤ ed ∧
    ∀ q, par' q = if q = ed ∨ q = x + 1 ∨ q = y + 1 then 0 else par₂ q)

/-- Removing an edge whose ends are `x` and `y` changes the forest. -/
theorem cut_ne_self_of_mem {F : MathForest} {x y : ℕ} {e : ForestEdge} (he : e ∈ F.edges)
    (hend : (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x)) : F.cut x y ≠ F := by
  intro hcut
  have hmem : e ∈ (F.cut x y).edges := by rw [hcut]; exact he
  simp only [MathForest.cut, List.mem_filter] at hmem
  rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2] at hmem

/-- Writing a header word other than the heap pointer keeps the pointer fields and the heap
pointer, so it keeps `PtrFootOk`. -/
theorem ptrFootOk_update_hdr {b k v L : ℕ} {m : ℕ → ℕ} {x₀ : LctConc}
    (hk : k < LCT_HDR_SIZE - 1) (h : PtrFootOk b m x₀ L) :
    PtrFootOk b (Function.update m (b + k) v) x₀ L := by
  intro u hu off hoff
  have hall : ∀ o ∈ ptrOffs, o < NODE_STRIDE := by decide
  have hoff_lt : off < NODE_STRIDE := hall off hoff
  have hne1 : lctNodesBase b + NODE_STRIDE * u + off ≠ b + k := by
    unfold lctNodesBase LCT_HDR_SIZE at *; omega
  have hne2 : lctNodesBase b - 1 ≠ b + k := by
    unfold lctNodesBase LCT_HDR_SIZE at *; omega
  have := h u hu off hoff
  simpa only [nodeField, Function.update_of_ne hne1, Function.update_of_ne hne2] using this

theorem slotZeroOk_update_hdr {b k v : ℕ} {m : ℕ → ℕ}
    (hk : k < LCT_HDR_SIZE) (h : SlotZeroOk m (lctNodesBase b)) :
    SlotZeroOk (Function.update m (b + k) v) (lctNodesBase b) := fun off hoff => by
  have hne : lctNodesBase b + off ≠ b + k := by unfold lctNodesBase at *; omega
  rw [Function.update_of_ne hne]
  exact h off hoff

end CutEdgeHelpers

section CutEdgeRun

private lemma cut_match_cost {c_rd c_sp c_spl : ℕ} (hrd : c_rd ≤ 30) (hspl : c_spl ≤ 250) :
    c_rd + (lctCutMatchExpr.size + (2 + c_sp + 1 + c_spl + 1) + 1) + 1 ≤ c_sp + 400 := by
  simp only [lctCutMatchExpr, Expr.size]
  omega

private lemma cut_edge_budget {c c_sp s2 s3 phi2 phi3 phi_w k cs ch : ℕ}
    (hc : c ≤ c_sp + 400) (hsp : c_sp + (s3 - s2) + phi3 ≤ phi2 + k + cs)
    (hphi : phi_w ≤ phi3 + 2 * ch) :
    c + (s3 - s2) + phi_w ≤ phi2 + k + cs + 2 * ch + 400 := by
  omega

/-- The edge step of `cut`, started right after `expose (y + 1)` found a path with two
vertices. It ends with the invariants of `F.cut x y` and costs, in the amortized sense, one
splay plus `2 * C_HEAVY L + 400`. -/
theorem lctCutEdgeBody_runs {w h L P b x y hp_caller pos : ℕ}
    {F : MathForest} {x₀ x₂ : LctConc} {l₂ : AuxTree} {rest₂ : List AuxTree}
    (p : Program) (lp : LctProcs) (mem₀ mem₁ mem₂ : ℕ → ℕ) (regs₂ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hi₂ : LctExposeInvs w h L P b F.n x₀.freeEdges x₀.edgeMap
      (.node (y + 1) l₂ .leaf :: rest₂) mem₂)
    (hrep₂ : LctMemRep w h L P b F x₂ mem₂)
    (hx2 : x₂.trees = .node (y + 1) l₂ .leaf :: rest₂)
    (hsafe₂ : SafeMem mem₁ (lctNodesBase b) (lctCap F.n) hp_caller mem₂)
    (hslot₁ : SlotZeroOk mem₁ (lctNodesBase b))
    (hptr₁ : PtrFootOk b mem₁ x₀ L)
    (hag₁ : ∀ a, a < b ∨ lctArenaHi b (lctCap F.n) ≤ a ∧ a < hp_caller → mem₁ a = mem₀ a)
    (harena : lctArenaHi b (lctCap F.n) ≤ hp_caller)
    (hx : x < F.n) (hy : y < F.n)
    (hpp_y : nodeField mem₂ (lctNodesBase b) (y + 1) OFF_PPAR = 0)
    (hsame_head : F.SameComp x y →
      (AuxTree.evalInorder (revFlag mem₂ (lctNodesBase b)) (.node (y + 1) l₂ .leaf) false).head? =
        some (x + 1))
    (hlast_y : (AuxTree.evalInorder (revFlag mem₂ (lctNodesBase b))
      (.node (y + 1) l₂ .leaf) false).getLast? = some (y + 1))
    (hvcnt : nodeField mem₂ (lctNodesBase b) (y + 1) OFF_VCNT = 2)
    (hr0 : regs₂ 0 = b) (hr1 : regs₂ 1 = x) (hr2 : regs₂ 2 = y)
    (hr5 : regs₂ 5 = lctNodesBase b)
    (hr8 : regs₂ 8 = lctNodesBase b + NODE_STRIDE * (y + 1))
    (hr15 : regs₂ 15 = lctNodesBase b + NODE_STRIDE * (x + 1))
    (hroom : mem₂ (lctNodesBase b - 1) + 6000 * (L + 1) * (F.n + 2) < 2 ^ w)
    (ω : ℕ → Bool) :
    let nb := lctNodesBase b
    let cap := lctCap F.n
    ∃ st_end c free1 edgeMap1 trees1 mem_safe,
      Runs w p ω (lctCutEdgeBody lp) { mem := mem₂, regs := regs₂, pos := pos } .normal
        st_end c ∧
      st_end.regs 0 = b ∧
      LctExposeInvs w h L P b F.n free1 edgeMap1 trees1 st_end.mem ∧
      (edgeMap1.map Prod.snd).Perm (F.cut x y).edges ∧
      ((edgeMap1.map Prod.fst) ++ free1).Perm ((List.range F.n).map (F.n + 1 + ·)) ∧
      SafeMem mem_safe nb cap hp_caller st_end.mem ∧
      SlotZeroOk mem_safe nb ∧ PtrFootOk b mem_safe x₀ L ∧
      (∀ a, a < b ∨ lctArenaHi b cap ≤ a ∧ a < hp_caller → mem_safe a = mem₀ a) ∧
      mem₂ (nb - 1) ≤ st_end.mem (nb - 1) ∧
      c + (st_end.mem (nb - 1) - mem₂ (nb - 1)) + lctPhi L st_end.mem b F.n ≤
        lctPhi L mem₂ b F.n + 3 * K_SPLAY_STEP L * (Nat.log 2 (F.n + 2) + 1) +
          C_SPLAY_CONST L + 2 * C_HEAVY L + 400 ∧
      CutParShape (lctAuxParent mem₂ nb cap) (lctAuxParent st_end.mem nb cap) F x y := by
  dsimp only
  set nb := lctNodesBase b with hnb
  set cap := lctCap F.n with hcap_def
  have hhp_le : hp_caller ≤ mem₂ (nb - 1) := hsafe₂.1
  have harena_def : lctArenaHi b cap = nb + NODE_STRIDE * (cap + 1) := rfl
  have hcap : cap = 2 * F.n := rfl
  have h12000 : 12000 ≤ 6000 * (L + 1) * (F.n + 2) := by
    have hm1 : 1 ≤ L + 1 := by omega
    have hm2 : 2 ≤ F.n + 2 := by omega
    have hmul : 1 * 2 ≤ (L + 1) * (F.n + 2) := Nat.mul_le_mul hm1 hm2
    have hm3 : 6000 * (1 * 2) ≤ 6000 * ((L + 1) * (F.n + 2)) := Nat.mul_le_mul_left 6000 hmul
    rw [Nat.mul_assoc]
    omega
  have hw_big : 12000 < 2 ^ w :=
    lt_of_le_of_lt h12000 (lt_of_le_of_lt (Nat.le_add_left _ _) hroom)
  have hroom_node : ∀ u, u ≤ cap → nb + NODE_STRIDE * u + NODE_STRIDE < 2 ^ w := by
    intro u hu
    have hm := Nat.mul_le_mul_left NODE_STRIDE (by omega : u + 1 ≤ cap + 1)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  have hperme₀ := hrep₀.edgeMap_snd_perm
  have hslots₀ := hrep₀.slots_perm
  have hnd_keys : (x₀.edgeMap.map Prod.fst).Nodup :=
    (hslots₀.nodup_iff.2 ((List.nodup_range).map (fun _ _ h => by omega))).of_append_left
  have hedge_lt : ∀ q ∈ x₀.edgeMap, q.2.u < F.n ∧ q.2.v < F.n := fun q hq => by
    have hm : q.2 ∈ x₀.edgeMap.map Prod.snd := List.mem_map.2 ⟨q, hq, rfl⟩
    have hf : q.2 ∈ F.edges := hperme₀.mem_iff.1 hm
    exact ⟨(hrep₀.valid.1 q.2 hf).1, (hrep₀.valid.1 q.2 hf).2.1⟩
  obtain ⟨z, e, s, hz, hzy, hed_mem, hed_em, he_F, he_end_z, _, hseq, _, _⟩ :=
    vcnt_eq_two_path hi₂ hrep₂ hperme₀ hslots₀ (by rw [hx2]; simp) hy rfl hpp_y hlast_y hvcnt
  set ed := nodeField mem₂ nb (y + 1) OFF_MIN1_FIRST with hed_def
  have hed_ok := hi₂.edgeOk (ed, e) hed_em
  have hed_n : F.n + 1 ≤ ed := hed_ok.1
  have hed2 : ed ≤ cap := hed_ok.2.1
  have hed1 : 1 ≤ ed := by omega
  have heu : nodeField mem₂ nb ed OFF_EU = e.u := hed_ok.2.2.2.2.2.1
  have hev : nodeField mem₂ nb ed OFF_EV = e.v := hed_ok.2.2.2.2.2.2.1
  -- Read the edge node and its endpoints.
  obtain ⟨c_rd, hrun_rd, hc_rd⟩ := cut_read_runs (p := p) (ω := ω) (pos := pos) (mem := mem₂)
    hr5 hr8 rfl heu hev (hroom_node (y + 1) (by omega)) (hroom_node ed hed2)
  set regs_rd := Function.update (Function.update (Function.update
    (Function.update regs₂ 9 ed) 10 (nb + NODE_STRIDE * ed)) 11 e.u) 12 e.v with hregs_rd
  have hrd0 : regs_rd 0 = b := by simp [regs_rd, hr0]
  have hrd1 : regs_rd 1 = x := by simp [regs_rd, hr1]
  have hrd2 : regs_rd 2 = y := by simp [regs_rd, hr2]
  have hrd5 : regs_rd 5 = nb := by simp [regs_rd, hr5]
  have hrd8 : regs_rd 8 = nb + NODE_STRIDE * (y + 1) := by simp [regs_rd, hr8]
  have hrd9 : regs_rd 9 = ed := by simp [regs_rd]
  have hrd10 : regs_rd 10 = nb + NODE_STRIDE * ed := by simp [regs_rd]
  have hrd11 : regs_rd 11 = e.u := by simp [regs_rd]
  have hrd12 : regs_rd 12 = e.v := by simp [regs_rd]
  have hrd15 : regs_rd 15 = nb + NODE_STRIDE * (x + 1) := by simp [regs_rd, hr15]
  have h1w : 1 < 2 ^ w := by omega
  let st_rd : State := { mem := mem₂, regs := regs_rd, pos := pos }
  have heq_op : ∀ (r₁ r₂ : ℕ), Expr.eval w st_rd (.bin .eq (.reg r₁) (.reg r₂)) =
      some (if regs_rd r₁ = regs_rd r₂ then 1 else 0) := fun r₁ r₂ =>
    Expr.eval_eq_op (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h1w
  have hite_le : ∀ (q : Prop) [Decidable q], (if q then 1 else 0) ≤ 1 := fun q _ => by
    split_ifs <;> omega
  set m1 := (if e.u = x then 1 else 0) * (if e.v = y then 1 else 0)
  set m2 := (if e.u = y then 1 else 0) * (if e.v = x then 1 else 0)
  have hm1 : m1 ≤ 1 := by
    have := Nat.mul_le_mul (hite_le (e.u = x)) (hite_le (e.v = y)); simpa [m1] using this
  have hm2 : m2 ≤ 1 := by
    have := Nat.mul_le_mul (hite_le (e.u = y)) (hite_le (e.v = x)); simpa [m2] using this
  have hmatch_eval : Expr.eval w st_rd lctCutMatchExpr = some (m1 + m2) := by
    have h_1 := heq_op 11 1
    have h_2 := heq_op 12 2
    have h_3 := heq_op 11 2
    have h_4 := heq_op 12 1
    rw [hrd11, hrd1] at h_1
    rw [hrd12, hrd2] at h_2
    rw [hrd11, hrd2] at h_3
    rw [hrd12, hrd1] at h_4
    exact Expr.eval_add (Expr.eval_mul h_1 h_2 (by omega)) (Expr.eval_mul h_3 h_4 (by omega))
      (by omega)
  by_cases hmatch : (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x)
  · -- The edge is `{x, y}`: splay `ed` and cut.
    have hmatch_ne : m1 + m2 ≠ 0 := by
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : m1 = 1 := by simp [m1, h1, h2]
        omega
      · have : m2 = 1 := by simp [m2, h1, h2]
        omega
    have hzx : z = x := by
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he_end_z with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        omega
    subst hzx
    have hxy : z ≠ y := hzy
    have hy_free : (AuxTree.node (y + 1) l₂ .leaf).rootId ∉ x₀.freeEdges := fun hm => by
      have := (hi₂.freeNodeOk _ hm).1
      simp only [AuxTree.rootId] at this
      omega
    have harena' : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller := harena
    obtain ⟨st₃, c_sp, t', hrun_sp, hi₃', hsafe₃, hroot, _, hev_sp, _, hrev_ed, _, hpp_ed3,
        _, hfr₃, hpar_sp, _, hbd_sp⟩ :=
      splay_expose_invs_runs (b := b) (n := F.n) p lp mem₁ mem₂ hp_base hp_sp hslot₁ harena'
        hsafe₂ hi₂ (List.Perm.refl _) hed_mem hy_free hroom ω (pos := pos)
    have hev3' : t'.evalInorder (revFlag st₃.mem nb) false = [z + 1, ed, y + 1] := by
      rw [hev_sp]; exact hseq
    have hpp_ed3' : nodeField st₃.mem nb ed OFF_PPAR = 0 := hpp_ed3.trans hpp_y
    obtain ⟨ht_eq, _, _, _⟩ :=
      cut_splayed_ed_shape hi₃' hroot hrev_ed hev3' hpp_ed3'
    subst ht_eq
    have hle₃ : mem₂ (nb - 1) ≤ st₃.mem (nb - 1) := hfr₃.2.2.1
    obtain ⟨hi_w, hpar_eq, hrest_agree, hm_w_hp, hpx_w, hpy_w, hped_w, hpar3_x, hpar3_ed,
        hpar3_y⟩ :=
      cut_invs_after_write hi₃' hpp_ed3' hev3' hed_em hmatch hx hy hxy hedge_lt hslots₀
    have hed_only : ∀ q, 1 ≤ q → q ≤ lctCap F.n →
        lctAuxParent st₃.mem (lctNodesBase b) (lctCap F.n) q = ed → q = y + 1 :=
      fun q hq1 hq2 hq => cut_par_eq_ed_only hi₃' hslots₀ hed_em hmatch hpar3_x hedge_lt hq1 hq2 hq
    have hphi_w := cut_phi_le hi₃' hi_w hpar_eq hrest_agree hpp_ed3' hpx_w hpy_w hped_w
      hpar3_x hpar3_ed hpar3_y hed_only
    -- Run the splay call and the write.
    set oldFree := st₃.mem (b + LCT_HDR_FREE)
    set mem_w := lctCutWriteMem st₃.mem nb b z y oldFree ed
    let regs_c := Function.update regs_rd 25 ed
    obtain ⟨c_spl, hrun_spl, hc_spl⟩ := cut_splice_runs (p := p) (ω := ω) (pos := st₃.pos)
      (mem := st₃.mem) (regs := regs_c) (x := z) (oldFree := oldFree)
      (by simp [regs_c, hrd0]) (by simp [regs_c, hrd8, hnb]) (by simp [regs_c, hrd9])
      (by simp [regs_c, hrd10, hnb]) (by simp [regs_c, hrd15, hnb]) rfl
      (hroom_node (z + 1) (by omega)) (hroom_node (y + 1) (by omega)) (hroom_node ed hed2)
    have heval_sp : evalArgs w st_rd [.reg 5, .reg 9] = some [nb, ed] :=
      WordRAM.evalArgs_cons (Expr.eval_reg_of_eq hrd5)
        (WordRAM.evalArgs_cons (Expr.eval_reg_of_eq hrd9) (WordRAM.evalArgs_nil w _))
    have hinner := link_runs_seq_call_runs (r := 25) heval_sp hp_base.splay_ok.splay_eq
      hrun_sp hrun_spl
    have hcond : Runs w p ω
        (.cond lctCutMatchExpr (.call 25 lp.splay.splay [.reg 5, .reg 9] ;; lctCutSpliceBody)
          .nop) st_rd .normal
        { mem := mem_w, regs := Function.update regs_c 14 oldFree, pos := st₃.pos }
        (lctCutMatchExpr.size + (argsSize [.reg 5, .reg 9] + c_sp + 1 + c_spl + 1) + 1) :=
      runs_cond_iff.2 ⟨m1 + m2, _, hmatch_eval, by simp only [hmatch_ne, ↓reduceIte]; exact hinner, rfl⟩
    have hrun := link_runs_seq_normal hrun_rd hcond
    -- The safe base memory after the write.
    have hsafe_w : SafeMem (Function.update mem₁ (b + LCT_HDR_FREE) ed) nb cap hp_caller mem_w :=
      lctCutWriteMem_safeMem rfl harena' (by omega) (by omega) hed1 hed2 hsafe₃
    have hfree_lt : b + LCT_HDR_FREE < lctArenaHi b cap := by
      rw [harena_def, hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
    have hag_w : ∀ a, a < b ∨ lctArenaHi b cap ≤ a ∧ a < hp_caller →
        Function.update mem₁ (b + LCT_HDR_FREE) ed a = mem₀ a := fun a ha => by
      have hne : a ≠ b + LCT_HDR_FREE := by rcases ha with ha | ha <;> omega
      rw [Function.update_of_ne hne]
      exact hag₁ a ha
    -- The edge map and slot list after the cut.
    have hperm_cut := cut_edges_perm hrep₀.valid hperme₀ hnd_keys hed_em hmatch
    have hslots_w : (((x₀.edgeMap.filter (fun q => decide (q.1 ≠ ed))).map Prod.fst) ++
        (ed :: x₀.freeEdges)).Perm ((List.range F.n).map (F.n + 1 + ·)) := by
      have hp1 := (cut_edgeMap_perm_filter hnd_keys hed_em).map Prod.fst
      have hp2 : ((x₀.edgeMap.filter (fun q => decide (q.1 ≠ ed))).map Prod.fst ++
          (ed :: x₀.freeEdges)).Perm (x₀.edgeMap.map Prod.fst ++ x₀.freeEdges) := by
        refine List.perm_middle.trans ?_
        exact List.Perm.append_right _ hp1.symm
      exact hp2.trans hslots₀
    have hc_tot := cut_match_cost (c_sp := c_sp) hc_rd hc_spl
    have hargs : argsSize [Expr.reg 5, Expr.reg 9] = 2 := by decide
    rw [hargs] at hcond hrun
    have hbudget := cut_edge_budget hc_tot hbd_sp hphi_w
    refine ⟨_, _, ed :: x₀.freeEdges, x₀.edgeMap.filter (fun q => decide (q.1 ≠ ed)), _,
      Function.update mem₁ (b + LCT_HDR_FREE) ed, hrun, by simp [regs_c, hrd0], hi_w,
      hperm_cut, hslots_w, hsafe_w,
      slotZeroOk_update_hdr (by unfold LCT_HDR_FREE LCT_HDR_SIZE; omega) hslot₁,
      ptrFootOk_update_hdr (by unfold LCT_HDR_FREE LCT_HDR_SIZE; omega) hptr₁, hag_w,
      ?_, ?_, ?_⟩
    · have hm_w_hp' : mem_w (nb - 1) = st₃.mem (nb - 1) := hm_w_hp
      show mem₂ (nb - 1) ≤ mem_w (nb - 1)
      rw [hm_w_hp']; exact hle₃
    · have hm_w_hp' : mem_w (nb - 1) = st₃.mem (nb - 1) := hm_w_hp
      show _ + (mem_w (nb - 1) - mem₂ (nb - 1)) + lctPhi L mem_w b F.n ≤ _
      rw [hm_w_hp']
      exact hbudget
    · right
      refine ⟨cut_ne_self_of_mem he_F hmatch, ed, hed_n, fun q => ?_⟩
      rw [hpar_eq q, hpar_sp q]
  · -- The endpoints are not `x` and `y`: there is no edge `{x, y}`.
    have hm0 : m1 + m2 = 0 := by
      have h1 : m1 = 0 := by
        by_cases h1 : e.u = x
        · have : e.v ≠ y := fun h2 => hmatch (Or.inl ⟨h1, h2⟩)
          simp [m1, this]
        · simp [m1, h1]
      have h2 : m2 = 0 := by
        by_cases h1 : e.u = y
        · have : e.v ≠ x := fun h2 => hmatch (Or.inr ⟨h1, h2⟩)
          simp [m2, this]
        · simp [m2, h1]
      omega
    have hcut : F.cut x y = F := cut_eq_self_of_ne_endpoints hsame_head hseq hmatch he_end_z
    have hcond : Runs w p ω
        (.cond lctCutMatchExpr (.call 25 lp.splay.splay [.reg 5, .reg 9] ;; lctCutSpliceBody)
          .nop) st_rd .normal st_rd (lctCutMatchExpr.size + 1 + 1) :=
      runs_cond_iff.2 ⟨m1 + m2, 1, hmatch_eval,
        by simp only [hm0, ↓reduceIte]; exact runs_nop_iff.2 ⟨rfl, rfl, rfl⟩, rfl⟩
    have hrun := link_runs_seq_normal hrun_rd hcond
    refine ⟨_, _, x₀.freeEdges, x₀.edgeMap, _, mem₁, hrun, hrd0, hi₂, by rw [hcut]; exact hperme₀,
      hslots₀, hsafe₂, hslot₁, hptr₁, hag₁, le_rfl, ?_, Or.inl ⟨fun _ => rfl, hcut⟩⟩
    show _ + (mem₂ (nb - 1) - mem₂ (nb - 1)) + lctPhi L mem₂ b F.n ≤ _
    simp only [lctCutMatchExpr, Expr.size, Nat.sub_self]
    omega

end CutEdgeRun

end MinCostFlow.LinkCut.Prog
