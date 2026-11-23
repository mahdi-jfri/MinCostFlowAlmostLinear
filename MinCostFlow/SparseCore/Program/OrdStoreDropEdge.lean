module

public import MinCostFlow.SparseCore.Program.OrdStoreUnlink
public import MinCostFlow.SparseCore.Program.OrdStoreFreeTree
import Mathlib.Tactic

/-!
# Order Store `dropEdge` Procedure

This file implements and verifies `ordDropEdgeBody` on `[b, e]`: if `e < eCap`, it unlinks and
frees the node for `2 * e` (if present) and then the node for `2 * e + 1` (if present), using
`ordUnlink` and `ordFreeTree`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

def ORD_DROP_AMORT : ℕ := 22000

/-! ### Helper: dropping a single key from `OrdInv` -/

private theorem filter_ne_eq_erase {α : Type*} [DecidableEq α] {l : List α} {x : α}
    (hnd : l.Nodup) : l.filter (· != x) = l.erase x := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨ha, htl⟩
    by_cases h : a = x
    · subst h
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.erase_cons_head]
      exact List.filter_eq_self.mpr fun b hb => bne_iff_ne.mpr (fun hba => ha (hba ▸ hb))
    · simp only [List.filter_cons, bne_iff_ne.mpr h, ↓reduceIte, List.erase_cons,
        beq_eq_false_iff_ne.mpr h]
      exact congrArg (a :: ·) (ih htl)

/-- Deleting a single key `k < 2 * eCap` (if live) via `ordUnlink` + `ordFreeTree`. -/
def ordDropKeyStmt (unlinkProc freeTreeProc : ℕ) (rKey : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg rKey))) ;;
  .cond (.reg 4)
    (.call 5 unlinkProc [.reg 0, .reg 4] ;;
     .call 6 freeTreeProc [.reg 0, .reg 4])
    .nop

theorem ordDropKeyStmt_noRand (uP fP rKey : ℕ) : (ordDropKeyStmt uP fP rKey).NoRand := by
  simp [ordDropKeyStmt, Stmt.NoRand]

private theorem ordDropKeyStmt_runs
    {w b rotProc stepProc splayProc walkProc joinProc unlinkProc freeTreeProc rKey k : ℕ}
    {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc))
    (hunlink : p.procs[unlinkProc]? = some (ordUnlinkBody splayProc joinProc))
    (hfree : p.procs[freeTreeProc]? = some ordFreeTreeBody) (ω : ℕ → Bool)
    {stM : State} {ord : ℕ → List End} {S : OrdStoreState} {heap : ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S stM.mem)
    (hk : k < 2 * S.eCap) (hr0 : stM.regs 0 = b) (hrk : stM.regs rKey = k)
    (hrk_ne : rKey ≠ 3 ∧ rKey ≠ 4 ∧ rKey ≠ 5 ∧ rKey ≠ 6)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom stM.mem heap) (hw : heap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ st' c, Runs w p ω (ordDropKeyStmt unlinkProc freeTreeProc rKey) stM .normal st' c ∧
      st'.regs 0 = b ∧ (∀ r, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → st'.regs r = stM.regs r) ∧
      (∃ S' : OrdStoreState,
        OrdInv (fun u => (ord u).filter (· != endOfKey k)) S' ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap heap stM.mem st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 10600 * ordStoreLog S.eCap) := by
  classical
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  set en := ordENodeBase b S.vCap with hen
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  have hen_w : en + k < 2 ^ w := by unfold ordENodeBase at hen; omega
  have ha3 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 3)))) stM .normal
      { stM with regs := Function.update stM.regs 3 en } _ :=
    runs_assign_iff.mpr ⟨en, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_eNode, rfl, rfl, rfl⟩
  set st1 : State := { stM with regs := Function.update stM.regs 3 en }
  have hm_ek : stM.mem (en + k) = S.eNode k := harena.eNode_at k hk
  have ha4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 3) (.reg rKey)))) st1 .normal
      { st1 with regs := Function.update st1.regs 4 (S.eNode k) } _ :=
    runs_assign_iff.mpr ⟨S.eNode k, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st1]))
      (Expr.eval_reg_of_eq (by simp [st1, hrk_ne.1, hrk])) (by omega)) hm_ek, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 4 (S.eNode k) }
  rcases hinv.eNode_spec k hk with ⟨he0, hnone⟩ | ⟨v, hv, hu_mem, hu_val⟩
  · -- Key k is absent: nop
    have hcond : (Expr.reg 4).eval w st2 = some 0 := Expr.eval_reg_of_eq (by simp [st2, he0])
    have hnop : Runs w p ω
        (.cond (.reg 4) (.call 5 unlinkProc [.reg 0, .reg 4] ;; .call 6 freeTreeProc [.reg 0, .reg 4]) .nop)
        st2 .normal st2 _ :=
      ord_runs_cond_false hcond (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)
    have hfilt_eq : (fun u => (ord u).filter (· != endOfKey k)) = ord := by
      funext u
      apply List.filter_eq_self.mpr
      intro e he
      by_cases hu : u < S.vCap
      · rw [← hinv.list_eq u hu] at he
        rcases List.mem_map.mp he with ⟨x, hx, hxe⟩
        exact bne_iff_ne.mpr fun h => hnone u hu x hx (endOfKey_injective (hxe.trans h))
      · exfalso
        have := hinv.ord_unique.eq_nil_of_ge (Nat.le_of_not_lt hu)
        rw [this] at he; exact List.not_mem_nil he
    refine ⟨st2, _, ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 hnop),
      by simp [st2, st1, hr0], fun r h3 h4 _ _ => by simp [st2, st1, h3, h4],
      S, by rwa [hfilt_eq], harena, OrdFrame.refl hz, rfl, rfl, ?_⟩
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
  · -- Key k is live at node u = S.eNode k in vertex v
    set u := S.eNode k with hu_def
    have hu_nz : u ≠ 0 := SplayState.SubtreeInv_nonZero (hinv.tree_inv v hv).sub hu_mem
    have hu_b : 1 ≤ u ∧ u ≤ S.nextNode := hinv.live_le_nextNode hv hu_mem
    have hpp_v : (S.splay.nodes (S.trees v).rootId).ppar = v + 1 :=
      hinv.root_ppar v hv (by intro h; rw [h] at hu_mem; simp [AuxTree.toList] at hu_mem)
    obtain ⟨oU, stU, cU, hrunU, spU, tU, hoU, hnU, hvrU, hfrU, hokU, hlistU, hcntU, hppU,
      hu_iso, hvalU, houtU, hphiU⟩ :=
      ordUnlinkBody_runs hrot hstep hsplay hwalk hjoin ω harena.hdr_vRoot harena.hdr_nodes
        harena.nodes_at (hinv.ordTreeOk hv) hv hu_mem hpp_v hinv.next_le (by omega) hwide (pos := st2.pos)
    have hcallU : Runs w p ω (.call 5 unlinkProc [.reg 0, .reg 4]) st2 .normal
        { stU with regs := Function.update st2.regs 5 oU.value }
        (argsSize [.reg 0, .reg 4] + cU + 1) :=
      runs_call_iff.mpr ⟨[b, u], ordUnlinkBody splayProc joinProc, oU, stU, cU,
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2, st1, hr0]))
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2, hu_def])) (evalArgs_nil _ _)),
        hunlink, hrunU, rfl, rfl, rfl⟩
    set st3 : State := { stU with regs := Function.update st2.regs 5 oU.value }
    have hnot_nd : ∀ a < nb, ¬ InOrdNodes nb S.nextNode a := fun a ha h => by
      unfold InOrdNodes at h; omega
    have hstU_hdr : ∀ j < 8, stU.mem (b + j) = stM.mem (b + j) := fun j hj =>
      hfrU (b + j) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
        (by unfold ordVRootBase; omega)
    have hstU_en : ∀ j < 2 * S.eCap, stU.mem (en + j) = S.eNode j := fun j hj =>
      (hfrU (en + j) (hnot_nd _ (by rw [hnb, hen]; unfold ordENodeBase ordNodesBase; omega))
        (by rw [hen]; unfold ordVRootBase ordENodeBase; omega)).trans (harena.eNode_at j hj)
    have hsh_u : FreeTreeShape spU (.node u .leaf .leaf) :=
      ⟨hu_nz, by simp [hu_iso, AuxTree.rootId], by simp [hu_iso, AuxTree.rootId], trivial, trivial⟩
    have hu_val' : (spU.nodes u).val = k := by simp [hu_iso, hu_val]
    obtain ⟨oF, stF, cF, hrunF, ⟨fh', fl', spF, nf', eN', hfhF, hnF, henF, hfrF,
      hpermF, hflndF, hfcF, hrevF, houtF, heNF⟩, hcF⟩ :=
      ordFreeTreeBody_runs ω ((hstU_hdr 4 (by omega)).trans harena.hdr_nodes)
        ((hstU_hdr 3 (by omega)).trans harena.hdr_eNode)
        ((hstU_hdr 6 (by omega)).trans harena.hdr_free)
        hstU_en hnU (by simp [AuxTree.toList]) hsh_u rfl
        (by intro x hx; simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hx; subst hx; exact hu_b)
        (by intro x hx; simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hx; subst hx; rw [hu_val']; exact hk)
        (by intro x hx; simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hx; subst hx; exact fun hf => hinv.free_disj v hv u hf hu_mem)
        hinv.free_nodup hinv.free_chain hinv.next_le (by omega) hwide (pos := st3.pos)
    have hcallF : Runs w p ω (.call 6 freeTreeProc [.reg 0, .reg 4]) st3 .normal
        { stF with regs := Function.update st3.regs 6 oF.value }
        (argsSize [.reg 0, .reg 4] + cF + 1) :=
      runs_call_iff.mpr ⟨[b, u], ordFreeTreeBody, oF, stF, cF,
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3, st2, st1, hr0]))
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3, st2, hu_def])) (evalArgs_nil _ _)),
        hfree, hrunF, rfl, rfl, rfl⟩
    have hcond : (Expr.reg 4).eval w st2 = some u := Expr.eval_reg_of_eq (by simp [st2, hu_def])
    have hcond_run : Runs w p ω
        (.cond (.reg 4) (.call 5 unlinkProc [.reg 0, .reg 4] ;; .call 6 freeTreeProc [.reg 0, .reg 4]) .nop)
        st2 .normal { stF with regs := Function.update st3.regs 6 oF.value } _ :=
      ord_runs_cond_true hcond hu_nz (ord_runs_seq_normal hcallU hcallF)
    set S' : OrdStoreState :=
      ({ S with
        splay := spF, vRoot := Function.update S.vRoot v tU.rootId,
        eNode := eN', trees := Function.update S.trees v tU,
        freeHead := fh', freeList := fl', nextFree := nf' } : OrdStoreState)
    have hu_ntU : u ∉ tU.toList := by
      rw [hlistU, ← filter_ne_eq_erase (hinv.tree_inv v hv).nodup]; simp
    have hspF_eq_spU : ∀ x, x ≠ u → spF.nodes x = spU.nodes x := fun x hx =>
      (houtF x (by simp [AuxTree.toList, hx])).1
    have h0_nu : (0 : ℕ) ≠ u := Ne.symm hu_nz
    have hinv' : OrdInv (fun w => (ord w).filter (· != endOfKey k)) S' := by
      have hord_u : OrdUniqueWithin S.vCap S.eCap (fun w => (ord w).filter (· != endOfKey k)) :=
        ⟨⟨fun w => (hinv.ord_unique.nodup w).filter _,
          fun w hw => by dsimp only; rw [hinv.ord_unique.eq_nil_of_ge hw]; rfl,
          fun w x hx => hinv.ord_unique.edge_lt (List.mem_of_mem_filter hx)⟩,
         fun w1 w2 x h1 h2 =>
           hinv.ord_unique.unique_v (List.mem_of_mem_filter h1) (List.mem_of_mem_filter h2)⟩
      have hlist_v' : tU.toList.map (fun x => endOfKey (spF.nodes x).val) =
          (ord v).filter (· != endOfKey k) := by
        have h1 : tU.toList.map (fun x => endOfKey (spF.nodes x).val) =
            tU.toList.map (fun x => endOfKey (S.splay.nodes x).val) :=
          List.map_congr_left fun x hx => by
            rw [hspF_eq_spU x (fun h => hu_ntU (h ▸ hx)), hvalU x hx]
        rw [h1, hlistU, ← filter_ne_eq_erase (hinv.tree_inv v hv).nodup, ← hinv.list_eq v hv, List.filter_map]
        congr 1; apply List.filter_congr
        intro x hx
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply, bne_iff_ne]
        constructor
        · intro hne heq
          have hx_eq_u : x = u := by
            have := hinv.eNode_eq_of_mem hv hx
            have hxk : (S.splay.nodes x).val = k := endOfKey_injective heq
            rw [hxk] at this; exact this.symm
          exact hne hx_eq_u
        · intro hne heq; subst heq; exact hne (by rw [hu_val])
      have hlist_ne : ∀ w < S.vCap, w ≠ v →
          (S.trees w).toList.map (fun x => endOfKey (spF.nodes x).val) =
            (ord w).filter (· != endOfKey k) := fun w hw hwv => by
        have h1 : (S.trees w).toList.map (fun x => endOfKey (spF.nodes x).val) = ord w := by
          rw [← hinv.list_eq w hw]
          exact List.map_congr_left fun x hx => by
            have hnt : x ∉ (S.trees v).toList := hinv.disj_trees w v hwv x hx
            rw [hspF_eq_spU x (fun h => hnt (h ▸ hu_mem)), houtU x hnt]
        rw [h1]
        symm; apply List.filter_eq_self.mpr
        intro e he
        exact bne_iff_ne.mpr fun h => by
          have hev : endOfKey k ∈ ord v := by
            rw [← hinv.list_eq v hv]; exact List.mem_map.mpr ⟨u, hu_mem, by rw [hu_val]⟩
          exact hwv (hinv.ord_unique.unique_v (h ▸ he) hev)
      refine
        { ord_unique := hord_u
          next_le := hinv.next_le
          clean := fun x => (hrevF x).trans (hokU.clean x)
          null_node := (hspF_eq_spU 0 h0_nu).trans hokU.null_node
          tree_inv := fun w hw => by
            dsimp only [S']
            by_cases hwv : w = v
            · subst hwv; simp only [Function.update_self]
              exact ⟨hokU.inv.nodup, SplayState.SubtreeInv_agree hokU.inv.sub fun x hx =>
                (hspF_eq_spU x (fun h => hu_ntU (h ▸ hx))).symm⟩
            · simp only [Function.update_of_ne hwv]
              exact ⟨(hinv.tree_inv w hw).nodup, SplayState.SubtreeInv_agree (hinv.tree_inv w hw).sub fun x hx => by
                have hnt : x ∉ (S.trees v).toList := hinv.disj_trees w v hwv x hx
                rw [hspF_eq_spU x (fun h => hnt (h ▸ hu_mem)), houtU x hnt]⟩
          tree_out := fun w hw => by
            dsimp only [S'] at hw ⊢; rw [Function.update_of_ne (by omega)]; exact hinv.tree_out w hw
          vRoot_eq := fun w hw => by
            dsimp only [S'] at hw ⊢; by_cases hwv : w = v <;> simp [hwv, hinv.vRoot_eq w hw]
          root_ppar := fun w hw hne => by
            dsimp only [S'] at hw hne ⊢
            by_cases hwv : w = v
            · subst hwv; simp only [Function.update_self] at hne ⊢
              rw [hspF_eq_spU tU.rootId (fun h => hu_ntU (h ▸ AuxTree.rootId_mem hne))]
              exact hppU hne
            · simp only [Function.update_of_ne hwv] at hne ⊢
              have hnt : (S.trees w).rootId ∉ (S.trees v).toList :=
                hinv.disj_trees w v hwv _ (AuxTree.rootId_mem hne)
              rw [hspF_eq_spU _ (fun h => hnt (by rw [h]; exact hu_mem)), houtU _ hnt]
              exact hinv.root_ppar w hw hne
          list_eq := fun w hw => by
            dsimp only [S'] at hw ⊢; by_cases hwv : w = v
            · subst hwv; simpa using hlist_v'
            · simp only [Function.update_of_ne hwv]; exact hlist_ne w hw hwv
          disj_trees := fun w1 w2 hne x hx1 hx2 => by
            dsimp only [S'] at hx1 hx2
            have h1 : x ∈ (S.trees w1).toList := by
              by_cases h : w1 = v
              · subst h; simp only [Function.update_self] at hx1; rw [hlistU] at hx1; exact List.mem_of_mem_erase hx1
              · simpa [h] using hx1
            have h2 : x ∈ (S.trees w2).toList := by
              by_cases h : w2 = v
              · subst h; simp only [Function.update_self] at hx2; rw [hlistU] at hx2; exact List.mem_of_mem_erase hx2
              · simpa [h] using hx2
            exact hinv.disj_trees w1 w2 hne x h1 h2
          free_nodup := hflndF
          free_disj := fun w hw x hxf hxt => by
            dsimp only [S'] at hw hxf hxt
            rw [hpermF.mem_iff] at hxf
            simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_cons] at hxf
            rcases hxf with rfl | hxf'
            · by_cases hwv : w = v
              · subst hwv; simp only [Function.update_self] at hxt; exact hu_ntU hxt
              · simp only [Function.update_of_ne hwv] at hxt
                exact hinv.disj_trees v w (Ne.symm hwv) u hu_mem hxt
            · by_cases hwv : w = v
              · subst hwv; simp only [Function.update_self] at hxt; rw [hlistU] at hxt
                exact hinv.free_disj w hw x hxf' (List.mem_of_mem_erase hxt)
              · simp only [Function.update_of_ne hwv] at hxt
                exact hinv.free_disj w hw x hxf' hxt
          free_chain := hfcF
          nodes_range := fun x => by
            dsimp only [S']
            rw [← hinv.nodes_range x, hpermF.mem_iff]
            simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_cons]
            constructor
            · rintro ((rfl | hfl) | ⟨w, hw, hxw⟩)
              · exact Or.inr ⟨v, hv, hu_mem⟩
              · exact Or.inl hfl
              · by_cases hwv : w = v
                · subst hwv; simp only [Function.update_self] at hxw; rw [hlistU] at hxw
                  exact Or.inr ⟨w, hw, List.mem_of_mem_erase hxw⟩
                · simp only [Function.update_of_ne hwv] at hxw; exact Or.inr ⟨w, hw, hxw⟩
            · rintro (hfl | ⟨w, hw, hxw⟩)
              · exact Or.inl (Or.inr hfl)
              · by_cases hxu : x = u
                · exact Or.inl (Or.inl hxu)
                · by_cases hwv : w = v
                  · subst hwv; refine Or.inr ⟨w, hw, ?_⟩
                    simp only [Function.update_self]; rw [hlistU, ← filter_ne_eq_erase (hinv.tree_inv w hw).nodup]
                    exact List.mem_filter.mpr ⟨hxw, bne_iff_ne.mpr hxu⟩
                  · refine Or.inr ⟨w, hw, ?_⟩; simpa [hwv] using hxw
          key_lt := fun w hw x hxw => by
            dsimp only [S'] at hw hxw ⊢
            by_cases hwv : w = v
            · subst hwv; simp only [Function.update_self] at hxw
              rw [hspF_eq_spU x (fun h => hu_ntU (h ▸ hxw)), hvalU x hxw]
              rw [hlistU] at hxw; exact hinv.key_lt w hw x (List.mem_of_mem_erase hxw)
            · simp only [Function.update_of_ne hwv] at hxw
              have hnt : x ∉ (S.trees v).toList := hinv.disj_trees w v hwv x hxw
              rw [hspF_eq_spU x (fun h => hnt (h ▸ hu_mem)), houtU x hnt]
              exact hinv.key_lt w hw x hxw
          eNode_spec := fun j hj => by
            dsimp only [S'] at hj ⊢
            rw [heNF j hj]
            have hex : (∃ x ∈ (AuxTree.node u .leaf .leaf).toList, (spU.nodes x).val = j) ↔ j = k := by
              simp [AuxTree.toList, hu_val', eq_comm]
            by_cases hjk : j = k
            · subst hjk; rw [if_pos (hex.mpr rfl)]
              left; refine ⟨rfl, fun w hw x hxw heq => ?_⟩
              by_cases hwv : w = v
              · subst hwv; simp only [Function.update_self] at hxw
                have hne : x ≠ u := fun h => hu_ntU (h ▸ hxw)
                rw [hspF_eq_spU x hne, hvalU x hxw] at heq
                rw [hlistU] at hxw
                have := hinv.eNode_eq_of_mem hw (List.mem_of_mem_erase hxw)
                rw [heq] at this; exact hne this.symm
              · simp only [Function.update_of_ne hwv] at hxw
                have hnt : x ∉ (S.trees v).toList := hinv.disj_trees w v hwv x hxw
                rw [hspF_eq_spU x (fun h => hnt (h ▸ hu_mem)), houtU x hnt] at heq
                have := hinv.eNode_eq_of_mem hw hxw
                rw [heq] at this; exact hnt (this ▸ hu_mem)
            · simp only [hex.not.mpr hjk, ↓reduceIte]
              rcases hinv.eNode_spec j hj with ⟨h0, hnone'⟩ | ⟨w, hw, hmem', hval'⟩
              · left; refine ⟨h0, fun w hw x hxw heq => ?_⟩
                by_cases hwv : w = v
                · subst hwv; simp only [Function.update_self] at hxw
                  rw [hspF_eq_spU x (fun h => hu_ntU (h ▸ hxw)), hvalU x hxw] at heq
                  rw [hlistU] at hxw; exact hnone' w hw x (List.mem_of_mem_erase hxw) heq
                · simp only [Function.update_of_ne hwv] at hxw
                  have hnt : x ∉ (S.trees v).toList := hinv.disj_trees w v hwv x hxw
                  rw [hspF_eq_spU x (fun h => hnt (h ▸ hu_mem)), houtU x hnt] at heq
                  exact hnone' w hw x hxw heq
              · right; refine ⟨w, hw, ?_, ?_⟩
                · have hne_u : S.eNode j ≠ u := fun h => hjk (by rw [← hval', h, hu_val])
                  by_cases hwv : w = v
                  · subst hwv; simp only [Function.update_self]
                    rw [hlistU, ← filter_ne_eq_erase (hinv.tree_inv w hw).nodup]
                    exact List.mem_filter.mpr ⟨hmem', bne_iff_ne.mpr hne_u⟩
                  · simpa [hwv] using hmem'
                · have hne_u : S.eNode j ≠ u := fun h => hjk (by rw [← hval', h, hu_val])
                  rw [hspF_eq_spU _ hne_u]
                  by_cases hwv : w = v
                  · subst hwv
                    have hmemU : S.eNode j ∈ tU.toList := by
                      rw [hlistU, ← filter_ne_eq_erase (hinv.tree_inv w hw).nodup]
                      exact List.mem_filter.mpr ⟨hmem', bne_iff_ne.mpr hne_u⟩
                    rw [hvalU _ hmemU]; exact hval'
                  · rw [houtU _ (hinv.disj_trees w v hwv _ hmem')]; exact hval' }
    have hfr_all : OrdFrame b S.vCap S.eCap heap stM.mem stF.mem := by
      have h1 : ∀ a, ¬ ordFoot b S.vCap S.eCap a → stF.mem a = stM.mem a := fun a ha => by
        have hnot1 : ¬ InOrdNodes nb S.nextNode a := fun h =>
          ha ⟨by unfold InOrdNodes at h; rw [hnb] at h; unfold ordNodesBase at h; omega,
              by unfold InOrdNodes at h; have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le; rw [hnb] at h; omega⟩
        have hnot2 : ¬ (en ≤ a ∧ a < en + 2 * S.eCap) := fun h =>
          ha ⟨by rw [hen] at h; unfold ordENodeBase at h; omega,
              by rw [hen] at h; unfold ordENodeBase ordArenaSize at *; omega⟩
        have hnot3 : a ≠ b + 6 := fun h => ha ⟨by omega, by unfold ordArenaSize; omega⟩
        have hnot4 : a ≠ ordVRootBase b + v := fun h => ha (h ▸ ordFoot_vRoot hv)
        exact (hfrF a hnot1 hnot2 hnot3).trans (hfrU a hnot1 hnot4)
      exact ⟨fun a ha => (h1 a (fun hf => by unfold ordFoot at hf; omega)).trans (hz a ha),
             fun a _ hnf => h1 a hnf⟩
    have harena' : OrdArenaAt b S' stF.mem := by
      have hhdr : ∀ j < 6, stF.mem (b + j) = stM.mem (b + j) := fun j hj =>
        (hfrF (b + j) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by unfold ordENodeBase; omega) (by omega)).trans (hstU_hdr j (by omega))
      exact
        { hdr_vCap := (hhdr 0 (by omega)).trans harena.hdr_vCap
          hdr_eCap := (hhdr 1 (by omega)).trans harena.hdr_eCap
          hdr_vRoot := (hhdr 2 (by omega)).trans harena.hdr_vRoot
          hdr_eNode := (hhdr 3 (by omega)).trans harena.hdr_eNode
          hdr_nodes := (hhdr 4 (by omega)).trans harena.hdr_nodes
          hdr_next := (hhdr 5 (by omega)).trans harena.hdr_next
          hdr_free := hfhF
          vRoot_at := fun w hw => by
            dsimp only [S'] at hw ⊢
            have hstepF := hfrF (ordVRootBase b + w)
              (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))
              (by unfold ordVRootBase ordENodeBase; omega)
              (by unfold ordVRootBase; omega)
            rw [hstepF]
            by_cases hwv : w = v
            · subst hwv; simp [hvrU]
            · simp only [Function.update_of_ne hwv]
              exact (hfrU (ordVRootBase b + w)
                (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))
                (by omega)).trans (harena.vRoot_at w hw)
          eNode_at := fun j hj => henF j hj
          nodes_at := hnF }
    have hphi_upd : sumTreePhi S' + (S.trees v).treePhi (fun _ => 0) =
        sumTreePhi S + tU.treePhi (fun _ => 0) := by
      have h := sumTreePhi_update (S := S) (S' := S') hv rfl (fun u _ huv => Function.update_of_ne huv _ _)
      simpa [S'] using h
    have hcnt_upd : sumCountNodes S' + (S.trees v).countNodes =
        sumCountNodes S + tU.countNodes := by
      have h := sumCountNodes_update (S := S) (S' := S') hv rfl (fun u _ huv => Function.update_of_ne huv _ _)
      simpa [S'] using h
    refine ⟨{ stF with regs := Function.update st3.regs 6 oF.value }, _,
      ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 hcond_run),
      by simp [st3, st2, st1, hr0],
      fun r h3 h4 h5 h6 => by simp [st3, st2, st1, h3, h4, h5, h6],
      S', hinv', harena', hfr_all, rfl, rfl, ?_⟩
    unfold ordPhi
    have hmul_phi : ORD_PHI_WEIGHT * sumTreePhi S' + ORD_PHI_WEIGHT * (S.trees v).treePhi (fun _ => 0) =
        ORD_PHI_WEIGHT * sumTreePhi S + ORD_PHI_WEIGHT * tU.treePhi (fun _ => 0) := by
      have := congrArg (ORD_PHI_WEIGHT * ·) hphi_upd; ring_nf at this ⊢; exact this
    have hmul_cnt : ORD_DEL_WEIGHT * sumCountNodes S' + ORD_DEL_WEIGHT =
        ORD_DEL_WEIGHT * sumCountNodes S := by
      have h1 : sumCountNodes S' + 1 = sumCountNodes S := by omega
      have := congrArg (ORD_DEL_WEIGHT * ·) h1; ring_nf at this ⊢; exact this
    simp only [AuxTree.countNodes, ORD_FREE_PER_NODE, ORD_DEL_WEIGHT, ORD_UNLINK_AMORT,
      Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
      argsSize_cons, argsSize_nil] at hcF hphiU hmul_cnt ⊢
    omega

/-! ### `ordDropEdgeBody` -/

/-- `ordDropEdge` on `[b, e]`: drops both ends `(e, true)` and `(e, false)` (keys `2*e` and
`2*e + 1`) if `e < eCap`. -/
def ordDropEdgeBody (unlinkProc freeTreeProc : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .cond (.bin .lt (.reg 1) (.reg 2))
    (.assign 7 (.bin .add (.reg 1) (.reg 1)) ;;
     ordDropKeyStmt unlinkProc freeTreeProc 7 ;;
     .assign 7 (.bin .add (.reg 7) (.const 1)) ;;
     ordDropKeyStmt unlinkProc freeTreeProc 7 ;;
     .ret (.const 0))
    (.ret (.const 0))

theorem ordDropEdgeBody_noRand (uP fP : ℕ) : (ordDropEdgeBody uP fP).NoRand := by
  simp [ordDropEdgeBody, ordDropKeyStmt, Stmt.NoRand]

theorem ordDropEdgeBody_runs
    {w b e pos rotProc stepProc splayProc walkProc joinProc unlinkProc freeTreeProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc))
    (hunlink : p.procs[unlinkProc]? = some (ordUnlinkBody splayProc joinProc))
    (hfree : p.procs[freeTreeProc]? = some ordFreeTreeBody) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState} {heap : ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem) (he_w : e < 2 ^ w)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordDropEdgeBody unlinkProc freeTreeProc) (startState [b, e] mem pos) o st' c ∧
      (∃ S' : OrdStoreState,
        OrdInv (applyOrdEdit ord (.dropEdge e)) S' ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap heap mem st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + ORD_DROP_AMORT * ordStoreLog S.eCap) := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  set st0 : State := startState [b, e] mem pos
  have ha2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 0) (.const 1)))) st0 .normal
      { st0 with regs := Function.update st0.regs 2 S.eCap } _ :=
    runs_assign_iff.mpr ⟨S.eCap, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_eCap, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 2 S.eCap }
  unfold ordDropEdgeBody
  by_cases he : e < S.eCap
  · have hcond : (Expr.bin .lt (.reg 1) (.reg 2)).eval w st1 = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq (by simp [st1, st0, startState]))
        (Expr.eval_reg_of_eq (by simp [st1])) he (by omega)
    have ha7a : Runs w p ω (.assign 7 (.bin .add (.reg 1) (.reg 1))) st1 .normal
        { st1 with regs := Function.update st1.regs 7 (e + e) } _ :=
      runs_assign_iff.mpr ⟨e + e, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, st0, startState]))
        (Expr.eval_reg_of_eq (by simp [st1, st0, startState])) (by omega), rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 7 (e + e) }
    obtain ⟨st3, c3, hrun3, r0_3, rkeep_3, S1, hinv1, harena1, hfr1, hv1, he1, hphi1⟩ :=
      ordDropKeyStmt_runs hrot hstep hsplay hwalk hjoin hunlink hfree ω (rKey := 7) (stM := st2)
        hinv harena (k := e + e) (by omega) (by simp [st2, st1, st0, startState]) (by simp [st2])
        ⟨by decide, by decide, by decide, by decide⟩ hfoot hz hw hwide
    have ha7b : Runs w p ω (.assign 7 (.bin .add (.reg 7) (.const 1))) st3 .normal
        { st3 with regs := Function.update st3.regs 7 (e + e + 1) } _ :=
      runs_assign_iff.mpr ⟨e + e + 1, Expr.eval_add
        (Expr.eval_reg_of_eq (by rw [rkeep_3 7 (by decide) (by decide) (by decide) (by decide)]; simp [st2]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    set st4 : State := { st3 with regs := Function.update st3.regs 7 (e + e + 1) }
    obtain ⟨st5, c5, hrun5, -, -, S2, hinv2, harena2, hfr2, hv2, he2, hphi2⟩ :=
      ordDropKeyStmt_runs hrot hstep hsplay hwalk hjoin hunlink hfree ω (rKey := 7) (stM := st4)
        hinv1 harena1 (k := e + e + 1) (by omega) (by simp [st4, r0_3]) (by simp [st4])
        ⟨by decide, by decide, by decide, by decide⟩ (by rw [hv1, he1]; exact hfoot)
        hfr1.1 hw hwide
    have hret : Runs w p ω (.ret (.const 0)) st5 (.returned 0) st5 _ :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    have hbody := ord_runs_seq_normal ha7a (ord_runs_seq_normal hrun3
      (ord_runs_seq_normal ha7b (ord_runs_seq_normal hrun5 hret)))
    have hfilt_eq : (fun u => ((ord u).filter (· != endOfKey (e + e))).filter (· != endOfKey (e + e + 1))) =
        applyOrdEdit ord (.dropEdge e) := by
      funext u; simp only [applyOrdEdit, List.filter_filter]
      apply List.filter_congr; intro x _
      rcases x with ⟨ex, sx⟩
      have hk0 : endOfKey (e + e) = (e, true) := by
        unfold endOfKey; simp [show (e + e) / 2 = e by omega, show (e + e) % 2 = 0 by omega]
      have hk1 : endOfKey (e + e + 1) = (e, false) := by
        unfold endOfKey; simp [show (e + e + 1) / 2 = e by omega, show (e + e + 1) % 2 = 1 by omega]
      rw [hk0, hk1]
      apply Bool.eq_iff_iff.mpr
      cases sx <;> by_cases h : ex = e <;> simp [h]
    rw [hfilt_eq] at hinv2
    refine ⟨.returned 0, st5, _, ord_runs_seq_normal ha2 (ord_runs_cond_true hcond Nat.one_ne_zero hbody),
      S2, hinv2, harena2, hfr1.trans (by rw [hv1, he1] at hfr2; exact hfr2), hv2.trans hv1, he2.trans he1, ?_⟩
    rw [he1] at hphi2
    unfold ORD_DROP_AMORT
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega
  · -- e ≥ S.eCap: no-op
    have hcond : (Expr.bin .lt (.reg 1) (.reg 2)).eval w st1 = some 0 :=
      Expr.eval_lt_false (Expr.eval_reg_of_eq (v := e) (by simp [st1, st0, startState]))
        (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st1])) (by omega) (by omega)
    have hret : Runs w p ω (.ret (.const 0)) st1 (.returned 0) st1 _ :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    have hnoop : applyOrdEdit ord (.dropEdge e) = ord := by
      funext u; simp only [applyOrdEdit]
      exact List.filter_eq_self.mpr fun x hx => bne_iff_ne.mpr (by
        have := hinv.ord_unique.edge_lt hx; omega)
    refine ⟨.returned 0, st1, _, ord_runs_seq_normal ha2 (ord_runs_cond_false hcond hret),
      S, by rwa [hnoop], harena, OrdFrame.refl hz, rfl, rfl, ?_⟩
    unfold ORD_DROP_AMORT
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

end MinCostFlow.SparseCore.Program
