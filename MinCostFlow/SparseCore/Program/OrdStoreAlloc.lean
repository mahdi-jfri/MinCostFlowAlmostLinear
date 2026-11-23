module

public import MinCostFlow.SparseCore.Program.OrdStoreWalkJoin
import Mathlib.Tactic

/-!
# Order Store Node Allocation

This file implements and verifies `ordAllocBody` on `[b, key]`: pops a recycled node ID from
`freeHead` (or increments `nextNode` when the free list is empty), initializes the node as an
isolated singleton holding `key`, records `eNode[key] := u`, and returns `u`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

def ORD_ALLOC_COST : ℕ := 200

/-- `ordAlloc` on `[b, key]`: allocates a fresh node ID `u`, initializes its 7 live fields as an
isolated singleton holding `key`, writes `eNode[key] := u`, and returns `u`. -/
def ordAllocBody : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .cond (.reg 3)
    (.assign 4 (.reg 3) ;;
     .assign 5 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 4))) (.const 7))) ;;
     .store (.bin .add (.reg 0) (.const 6)) (.reg 5))
    (.assign 5 (.load (.bin .add (.reg 0) (.const 5))) ;;
     .assign 4 (.bin .add (.reg 5) (.const 1)) ;;
     .store (.bin .add (.reg 0) (.const 5)) (.reg 4)) ;;
  .assign 6 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 4))) ;;
  .store (.reg 6) (.const 0) ;;
  .store (.bin .add (.reg 6) (.const 1)) (.const 0) ;;
  .store (.bin .add (.reg 6) (.const 2)) (.const 0) ;;
  .store (.bin .add (.reg 6) (.const 3)) (.const 0) ;;
  .store (.bin .add (.reg 6) (.const 4)) (.const 1) ;;
  .store (.bin .add (.reg 6) (.const 5)) (.reg 1) ;;
  .store (.bin .add (.reg 6) (.const 6)) (.const 0) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .store (.bin .add (.reg 7) (.reg 1)) (.reg 4) ;;
  .ret (.reg 4)

theorem ordAllocBody_noRand : ordAllocBody.NoRand := by
  simp [ordAllocBody, Stmt.NoRand]

/-- Fresh singleton `SplayNode` holding `key`. -/
def ordFreshNode (key : ℕ) : SplayNode ℕ Unit Unit :=
  { left := 0, right := 0, par := 0, ppar := 0, sz := 1, val := key, sum := (), rev := false, tag := () }

theorem ordAllocBody_runs {w b key pos : ℕ} {p : Program} (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState} {heap : ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem)
    (hkey : key < 2 * S.eCap) (hunused : S.eNode key = 0)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω ordAllocBody (startState [b, key] mem pos) o st' c ∧
      (∃ (u : ℕ) (S' : OrdStoreState),
        o.value = u ∧
        1 ≤ u ∧ u ≤ S'.nextNode ∧ S.nextNode ≤ S'.nextNode ∧ S'.nextNode ≤ 2 * S.eCap ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        S'.vRoot = S.vRoot ∧ S'.trees = S.trees ∧
        S'.eNode = Function.update S.eNode key u ∧
        S'.splay = S.splay.updateNode u (fun _ => ordFreshNode key) ∧
        (∀ v < S.vCap, u ∉ (S.trees v).toList) ∧
        u ∉ S'.freeList ∧
        S'.freeList.Nodup ∧
        FreeChain S'.freeHead S'.nextFree S'.freeList ∧
        (∀ x ∈ S'.freeList, 1 ≤ x ∧ x ≤ S'.nextNode) ∧
        (∀ v < S.vCap, ∀ x ∈ (S.trees v).toList, x ∉ S'.freeList) ∧
        (∀ x, 1 ≤ x → x ≤ S'.nextNode →
          x = u ∨ (∃ v < S.vCap, x ∈ (S.trees v).toList) ∨ x ∈ S'.freeList) ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap heap mem st'.mem) ∧
      0 + c ≤ ORD_ALLOC_COST := by
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  have hnb_end : nb + 8 * (2 * S.eCap + 1) ≤ heap := by
    have := ordNodesBase_end b S.vCap S.eCap; rw [hnb]; omega
  have hen_w : ordENodeBase b S.vCap + key < 2 ^ w := by unfold ordENodeBase; omega
  have hsum_lt : sumCountNodes S < 2 * S.eCap := hinv.sumCountNodes_lt_of_unused_key hkey hunused
  have hsum_add : sumCountNodes S + S.freeList.length = S.nextNode := hinv.sumCountNodes_add_free
  set st0 : State := startState [b, key] mem pos
  have hld2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 0) (.const 4)))) st0 .normal
      { st0 with regs := Function.update st0.regs 2 nb } _ :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_nodes, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 2 nb }
  have hld3 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 6)))) st1 .normal
      { st1 with regs := Function.update st1.regs 3 S.freeHead } _ :=
    runs_assign_iff.mpr ⟨S.freeHead, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st1, st0, startState])) (Expr.eval_const (by omega)) (by omega))
      harena.hdr_free, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 3 S.freeHead }
  have hbranch : ∃ (u nn' fh' : ℕ) (fl' : List ℕ) (nf' : ℕ → ℕ) (st3 : State) (c3 : ℕ),
      Runs w p ω
        (.cond (.reg 3)
          (.assign 4 (.reg 3) ;;
           .assign 5 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 4))) (.const 7))) ;;
           .store (.bin .add (.reg 0) (.const 6)) (.reg 5))
          (.assign 5 (.load (.bin .add (.reg 0) (.const 5))) ;;
           .assign 4 (.bin .add (.reg 5) (.const 1)) ;;
           .store (.bin .add (.reg 0) (.const 5)) (.reg 4)))
        st2 .normal st3 c3 ∧
      c3 ≤ 45 ∧
      st3.regs 0 = b ∧ st3.regs 1 = key ∧ st3.regs 2 = nb ∧ st3.regs 4 = u ∧
      1 ≤ u ∧ u ≤ nn' ∧ S.nextNode ≤ nn' ∧ nn' ≤ 2 * S.eCap ∧
      (∀ v < S.vCap, u ∉ (S.trees v).toList) ∧
      u ∉ fl' ∧ fl'.Nodup ∧ FreeChain fh' nf' fl' ∧
      (∀ x ∈ fl', 1 ≤ x ∧ x ≤ nn') ∧
      (∀ v < S.vCap, ∀ x ∈ (S.trees v).toList, x ∉ fl') ∧
      (∀ x, 1 ≤ x → x ≤ nn' → x = u ∨ (∃ v < S.vCap, x ∈ (S.trees v).toList) ∨ x ∈ fl') ∧
      st3.mem (b + 0) = S.vCap ∧ st3.mem (b + 1) = S.eCap ∧
      st3.mem (b + 2) = ordVRootBase b ∧ st3.mem (b + 3) = ordENodeBase b S.vCap ∧
      st3.mem (b + 4) = nb ∧ st3.mem (b + 5) = nn' ∧ st3.mem (b + 6) = fh' ∧
      (∀ v < S.vCap, st3.mem (ordVRootBase b + v) = S.vRoot v) ∧
      (∀ k < 2 * S.eCap, st3.mem (ordENodeBase b S.vCap + k) = S.eNode k) ∧
      (∀ x ≤ nn', x ≠ u → OrdNodeAt st3.mem nb x (S.splay.nodes x) (nf' x)) ∧
      st3.mem (nb + 8 * u + 7) = nf' u ∧
      OrdFrame b S.vCap S.eCap heap mem st3.mem := by
    by_cases hfh : S.freeHead = 0
    · have hfl_nil : S.freeList = [] := by
        cases hfc : S.freeList with
        | nil => rfl
        | cons a tl =>
          have h1 := hinv.free_chain; rw [hfc] at h1
          exact absurd (h1.1.symm.trans hfh) h1.2.1
      have hnn_lt : S.nextNode < 2 * S.eCap := by rw [hfl_nil] at hsum_add; simp at hsum_add; omega
      have hcond : (Expr.reg 3).eval w st2 = some 0 := Expr.eval_reg_of_eq (by simp [st2, hfh])
      have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 5)))) st2 .normal
          { st2 with regs := Function.update st2.regs 5 S.nextNode } _ :=
        runs_assign_iff.mpr ⟨S.nextNode, Expr.eval_load_of_eq (Expr.eval_add
          (Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState])) (Expr.eval_const (by omega)) (by omega))
          harena.hdr_next, rfl, rfl, rfl⟩
      set st2a : State := { st2 with regs := Function.update st2.regs 5 S.nextNode }
      have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 5) (.const 1))) st2a .normal
          { st2a with regs := Function.update st2a.regs 4 (S.nextNode + 1) } _ :=
        runs_assign_iff.mpr ⟨S.nextNode + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2a]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st2b : State := { st2a with regs := Function.update st2a.regs 4 (S.nextNode + 1) }
      have hst5 : Runs w p ω (.store (.bin .add (.reg 0) (.const 5)) (.reg 4)) st2b .normal
          { st2b with mem := Function.update mem (b + 5) (S.nextNode + 1) } _ :=
        runs_store_iff.mpr ⟨b + 5, S.nextNode + 1,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2b, st2a, st2, st1, st0, startState]))
            (Expr.eval_const (by omega)) (by omega),
          Expr.eval_reg_of_eq (by simp [st2b]), rfl, rfl, rfl⟩
      set u := S.nextNode + 1
      set nf' := Function.update S.nextFree u (mem (nb + 8 * u + 7))
      have hbody := ord_runs_seq_normal ha5 (ord_runs_seq_normal ha4 hst5)
      refine ⟨u, u, 0, [], nf', _, _, ord_runs_cond_false hcond hbody,
        by simp [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const],
        by simp [st2b, st2a, st2, st1, st0, startState], by simp [st2b, st2a, st2, st1, st0, startState],
        by simp [st2b, st2a, st2, st1], by simp [st2b, u],
        by omega, le_refl _, by omega, by omega,
        fun v hv hmem => by have := (hinv.live_le_nextNode hv hmem).2; omega,
        by simp, List.nodup_nil, rfl, by simp, fun _ _ _ _ => by simp,
        fun x hx1 hxu => by
          by_cases h : x = u
          · exact Or.inl h
          · rcases (hinv.nodes_range x).mpr ⟨hx1, by omega⟩ with h2 | h1
            · rw [hfl_nil] at h2; simp at h2
            · exact Or.inr (Or.inl h1),
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_vCap,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_eCap,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_vRoot,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_eNode,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_nodes,
        by dsimp only; simp,
        by dsimp only; rw [Function.update_of_ne (by omega), ← hfh]; exact harena.hdr_free,
        fun v hv => by
          dsimp only; rw [Function.update_of_ne (by unfold ordVRootBase; omega)]; exact harena.vRoot_at v hv,
        fun k hk => by
          dsimp only; rw [Function.update_of_ne (by unfold ordENodeBase; omega)]; exact harena.eNode_at k hk,
        fun x hx hne => by
          have hxle : x ≤ S.nextNode := by omega
          have hna := harena.nodes_at x hxle
          have hnf_eq : nf' x = S.nextFree x := Function.update_of_ne hne _ _
          rw [hnf_eq]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            (dsimp only [ordNodeAddr]; rw [Function.update_of_ne (by rw [hnb]; unfold ordNodesBase; omega)])
          · exact hna.1
          · exact hna.2.1
          · exact hna.2.2.1
          · exact hna.2.2.2.1
          · exact hna.2.2.2.2.1
          · exact hna.2.2.2.2.2.1
          · exact hna.2.2.2.2.2.2.1
          · exact hna.2.2.2.2.2.2.2,
        by dsimp only; rw [Function.update_of_ne (by rw [hnb]; unfold ordNodesBase; omega)]; simp [nf'],
        OrdFrame.of_store_in_foot hz ⟨by omega, by unfold ordArenaSize; omega⟩ hfoot⟩
    · cases hfl : S.freeList with
      | nil =>
        have hfc := hinv.free_chain; rw [hfl] at hfc; exact absurd hfc hfh
      | cons u fl' =>
        have hfc := hinv.free_chain; rw [hfl] at hfc
        rcases hfc with ⟨hfh_eq, hu0, hfc'⟩
        have hnd' := List.nodup_cons.mp (hfl ▸ hinv.free_nodup)
        have hu_b : 1 ≤ u ∧ u ≤ S.nextNode := hinv.free_le_nextNode (hfl ▸ List.mem_cons_self)
        have hu_nn : u ≤ 2 * S.eCap := by have := hinv.next_le; omega
        have hm_nf : mem (nb + 8 * u + 7) = S.nextFree u := (harena.nodes_at u hu_b.2).2.2.2.2.2.2.2
        have hcond : (Expr.reg 3).eval w st2 = some u := Expr.eval_reg_of_eq (by simp [st2, hfh_eq])
        have ha4 : Runs w p ω (.assign 4 (.reg 3)) st2 .normal
            { st2 with regs := Function.update st2.regs 4 u } _ :=
          runs_assign_iff.mpr ⟨u, hcond, rfl, rfl, rfl⟩
        set st2a : State := { st2 with regs := Function.update st2.regs 4 u }
        have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 4))) (.const 7))))
            st2a .normal { st2a with regs := Function.update st2a.regs 5 (S.nextFree u) } _ :=
          runs_assign_iff.mpr ⟨S.nextFree u, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
            (Expr.eval_reg_of_eq (by simp [st2a, st2, st1]))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st2a])) (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega)) hm_nf, rfl, rfl, rfl⟩
        set st2b : State := { st2a with regs := Function.update st2a.regs 5 (S.nextFree u) }
        have hst6 : Runs w p ω (.store (.bin .add (.reg 0) (.const 6)) (.reg 5)) st2b .normal
            { st2b with mem := Function.update mem (b + 6) (S.nextFree u) } _ :=
          runs_store_iff.mpr ⟨b + 6, S.nextFree u,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2b, st2a, st2, st1, st0, startState]))
              (Expr.eval_const (by omega)) (by omega),
            Expr.eval_reg_of_eq (by simp [st2b]), rfl, rfl, rfl⟩
        have hbody := ord_runs_seq_normal ha4 (ord_runs_seq_normal ha5 hst6)
        refine ⟨u, S.nextNode, S.nextFree u, fl', S.nextFree, _, _,
          ord_runs_cond_true hcond hu0 hbody,
          by simp [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const],
          by simp [st2b, st2a, st2, st1, st0, startState], by simp [st2b, st2a, st2, st1, st0, startState],
          by simp [st2b, st2a, st2, st1], by simp [st2b, st2a],
          hu_b.1, hu_b.2, le_refl _, hinv.next_le,
          fun v hv hmem => hinv.free_disj v hv u (hfl ▸ List.mem_cons_self) hmem,
          hnd'.1, hnd'.2, hfc',
          fun x hx => hinv.free_le_nextNode (hfl ▸ List.mem_cons_of_mem u hx),
          fun v hv x hx hxf => hinv.free_disj v hv x (hfl ▸ List.mem_cons_of_mem u hxf) hx,
          fun x hx1 hxnn => by
            rcases (hinv.nodes_range x).mpr ⟨hx1, hxnn⟩ with h2 | h1
            · rw [hfl, List.mem_cons] at h2
              rcases h2 with rfl | h3
              · exact Or.inl rfl
              · exact Or.inr (Or.inr h3)
            · exact Or.inr (Or.inl h1),
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_vCap,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_eCap,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_vRoot,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_eNode,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_nodes,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact harena.hdr_next,
          by dsimp only; simp,
          fun v hv => by
            dsimp only; rw [Function.update_of_ne (by unfold ordVRootBase; omega)]; exact harena.vRoot_at v hv,
          fun k hk => by
            dsimp only; rw [Function.update_of_ne (by unfold ordENodeBase; omega)]; exact harena.eNode_at k hk,
          fun x hx _ => by
            have hna := harena.nodes_at x hx
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              (dsimp only [ordNodeAddr]; rw [Function.update_of_ne (by rw [hnb]; unfold ordNodesBase; omega)])
            · exact hna.1
            · exact hna.2.1
            · exact hna.2.2.1
            · exact hna.2.2.2.1
            · exact hna.2.2.2.2.1
            · exact hna.2.2.2.2.2.1
            · exact hna.2.2.2.2.2.2.1
            · exact hna.2.2.2.2.2.2.2,
          by dsimp only; rw [Function.update_of_ne (by rw [hnb]; unfold ordNodesBase; omega)]; exact hm_nf,
          OrdFrame.of_store_in_foot hz ⟨by omega, by unfold ordArenaSize; omega⟩ hfoot⟩
  obtain ⟨u, nn', fh', fl', nf', st3, c3, hrun3, hc3, r0, r1, r2, r4, hu1, hunn, hnn_ge, hnn_le,
    hu_nlive, hu_nfl, hfl_nd, hfc', hfl_le, hlive_fl, hpart',
    hh0, hh1, hh2, hh3, hh4, hh5, hh6, hvr3, hen3, hna3, hnf3_u, hfr3⟩ := hbranch
  -- Initialize u's 7 fields, write eNode[key] := u, return u
  have htail : ∃ o st' c, Runs w p ω
      (.assign 6 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 4))) ;;
       .store (.reg 6) (.const 0) ;;
       .store (.bin .add (.reg 6) (.const 1)) (.const 0) ;;
       .store (.bin .add (.reg 6) (.const 2)) (.const 0) ;;
       .store (.bin .add (.reg 6) (.const 3)) (.const 0) ;;
       .store (.bin .add (.reg 6) (.const 4)) (.const 1) ;;
       .store (.bin .add (.reg 6) (.const 5)) (.reg 1) ;;
       .store (.bin .add (.reg 6) (.const 6)) (.const 0) ;;
       .assign 7 (.load (.bin .add (.reg 0) (.const 3))) ;;
       .store (.bin .add (.reg 7) (.reg 1)) (.reg 4) ;;
       .ret (.reg 4)) st3 o st' c ∧
      (let S' : OrdStoreState :=
        { S with
          nextNode := nn', freeHead := fh', freeList := fl', nextFree := nf',
          eNode := Function.update S.eNode key u,
          splay := S.splay.updateNode u (fun _ => ordFreshNode key) }
       o = .returned u ∧ OrdArenaAt b S' st'.mem ∧ OrdFrame b S.vCap S.eCap heap st3.mem st'.mem) ∧
      0 + c ≤ 130 := by
    refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq r2)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r4) (by omega)) (by omega)) ?_
    refine runs_seq_store_le (Expr.eval_reg_of_eq (v := nb + 8 * u) (by simp)) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * u) (by simp)) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * u) (by simp)) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * u) (by simp)) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * u) (by simp)) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * u) (by simp)) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (v := key) (by simp [r1])) ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nb + 8 * u) (by simp)) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_const (by omega)) ?_
    set m7 := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update st3.mem (nb + 8 * u) 0) (nb + 8 * u + 1) 0)
      (nb + 8 * u + 2) 0) (nb + 8 * u + 3) 0) (nb + 8 * u + 4) 1) (nb + 8 * u + 5) key) (nb + 8 * u + 6) 0
    have hm7_hdr : ∀ j < 8, m7 (b + j) = st3.mem (b + j) := fun j hj => by
      dsimp only [m7]
      repeat rw [Function.update_of_ne (by rw [hnb]; unfold ordNodesBase; omega)]
    have hm7_en : m7 (b + 3) = ordENodeBase b S.vCap := (hm7_hdr 3 (by omega)).trans hh3
    refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := b) (by simp [r0]))
      (Expr.eval_const (by omega)) (by omega)) hm7_en) ?_
    refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := ordENodeBase b S.vCap) (by simp))
      (Expr.eval_reg_of_eq (v := key) (by simp [r1])) (by omega)) (Expr.eval_reg_of_eq (v := u) (by simp [r4])) ?_
    refine runs_ret_le (Expr.eval_reg_of_eq (v := u) (by simp [r4])) ?_ ?_
    · set m8 := Function.update m7 (ordENodeBase b S.vCap + key) u
      have hm8_hdr : ∀ j < 8, m8 (b + j) = st3.mem (b + j) := fun j hj => by
        dsimp only [m8]
        rw [Function.update_of_ne (by unfold ordENodeBase; omega)]
        exact hm7_hdr j hj
      have hfn : ∀ j < 8, ordFoot b S.vCap S.eCap (nb + 8 * u + j) := fun j hj => by
        rw [hnb]; exact ordFoot_node (by omega) hj
      have hfn0 : ordFoot b S.vCap S.eCap (nb + 8 * u) := by simpa using hfn 0 (by omega)
      have hfr8 : OrdFrame b S.vCap S.eCap heap st3.mem m8 := by
        refine ⟨fun a ha => ?_, fun a _ hnf => ?_⟩
        · have hne : ∀ addr, ordFoot b S.vCap S.eCap addr → a ≠ addr := fun addr hfa heq => by
            unfold ordFoot at hfa; omega
          dsimp only [m8, m7]
          rw [Function.update_of_ne (hne _ (ordFoot_eNode hkey)),
              Function.update_of_ne (hne _ (hfn 6 (by omega))),
              Function.update_of_ne (hne _ (hfn 5 (by omega))),
              Function.update_of_ne (hne _ (hfn 4 (by omega))),
              Function.update_of_ne (hne _ (hfn 3 (by omega))),
              Function.update_of_ne (hne _ (hfn 2 (by omega))),
              Function.update_of_ne (hne _ (hfn 1 (by omega))),
              Function.update_of_ne (hne _ hfn0)]
          exact hfr3.1 a ha
        · have hne : ∀ addr, ordFoot b S.vCap S.eCap addr → a ≠ addr := fun addr hfa heq => hnf (heq ▸ hfa)
          dsimp only [m8, m7]
          rw [Function.update_of_ne (hne _ (ordFoot_eNode hkey)),
              Function.update_of_ne (hne _ (hfn 6 (by omega))),
              Function.update_of_ne (hne _ (hfn 5 (by omega))),
              Function.update_of_ne (hne _ (hfn 4 (by omega))),
              Function.update_of_ne (hne _ (hfn 3 (by omega))),
              Function.update_of_ne (hne _ (hfn 2 (by omega))),
              Function.update_of_ne (hne _ (hfn 1 (by omega))),
              Function.update_of_ne (hne _ hfn0)]
      refine ⟨rfl, ?_, hfr8⟩
      refine
        { hdr_vCap := (hm8_hdr 0 (by omega)).trans hh0
          hdr_eCap := (hm8_hdr 1 (by omega)).trans hh1
          hdr_vRoot := (hm8_hdr 2 (by omega)).trans hh2
          hdr_eNode := (hm8_hdr 3 (by omega)).trans hh3
          hdr_nodes := (hm8_hdr 4 (by omega)).trans hh4
          hdr_next := (hm8_hdr 5 (by omega)).trans hh5
          hdr_free := (hm8_hdr 6 (by omega)).trans hh6
          vRoot_at := fun v hv => by
            dsimp only at hv ⊢
            dsimp only [m8, m7]
            rw [Function.update_of_ne (by unfold ordVRootBase ordENodeBase; omega)]
            repeat rw [Function.update_of_ne (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega)]
            exact hvr3 v hv
          eNode_at := fun k hk => by
            dsimp only at hk ⊢
            dsimp only [m8]
            by_cases hkeq : k = key
            · subst hkeq; simp
            · rw [Function.update_of_ne (by omega), Function.update_of_ne hkeq]
              dsimp only [m7]
              repeat rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
              exact hen3 k hk
          nodes_at := fun x hx => by
            dsimp only at hx ⊢
            by_cases hxu : x = u
            · rw [hxu]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · dsimp only [ordNodeAddr, m8, m7, ordFreshNode]; rw [← hnb]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                simp [SplayState.nodes_updateNode, Function.update_of_ne (by omega : nb + 8 * u ≠ nb + 8 * u + 6),
                  Function.update_of_ne (by omega : nb + 8 * u ≠ nb + 8 * u + 5),
                  Function.update_of_ne (by omega : nb + 8 * u ≠ nb + 8 * u + 4),
                  Function.update_of_ne (by omega : nb + 8 * u ≠ nb + 8 * u + 3),
                  Function.update_of_ne (by omega : nb + 8 * u ≠ nb + 8 * u + 2),
                  Function.update_of_ne (by omega : nb + 8 * u ≠ nb + 8 * u + 1)]
              · dsimp only [ordNodeAddr, m8, m7, ordFreshNode]; rw [← hnb]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                simp [SplayState.nodes_updateNode, Function.update_of_ne (by omega : nb + 8 * u + 1 ≠ nb + 8 * u + 6),
                  Function.update_of_ne (by omega : nb + 8 * u + 1 ≠ nb + 8 * u + 5),
                  Function.update_of_ne (by omega : nb + 8 * u + 1 ≠ nb + 8 * u + 4),
                  Function.update_of_ne (by omega : nb + 8 * u + 1 ≠ nb + 8 * u + 3),
                  Function.update_of_ne (by omega : nb + 8 * u + 1 ≠ nb + 8 * u + 2)]
              · dsimp only [ordNodeAddr, m8, m7, ordFreshNode]; rw [← hnb]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                simp [SplayState.nodes_updateNode, Function.update_of_ne (by omega : nb + 8 * u + 2 ≠ nb + 8 * u + 6),
                  Function.update_of_ne (by omega : nb + 8 * u + 2 ≠ nb + 8 * u + 5),
                  Function.update_of_ne (by omega : nb + 8 * u + 2 ≠ nb + 8 * u + 4),
                  Function.update_of_ne (by omega : nb + 8 * u + 2 ≠ nb + 8 * u + 3)]
              · dsimp only [ordNodeAddr, m8, m7, ordFreshNode]; rw [← hnb]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                simp [SplayState.nodes_updateNode, Function.update_of_ne (by omega : nb + 8 * u + 3 ≠ nb + 8 * u + 6),
                  Function.update_of_ne (by omega : nb + 8 * u + 3 ≠ nb + 8 * u + 5),
                  Function.update_of_ne (by omega : nb + 8 * u + 3 ≠ nb + 8 * u + 4)]
              · dsimp only [ordNodeAddr, m8, m7, ordFreshNode]; rw [← hnb]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                simp [SplayState.nodes_updateNode, Function.update_of_ne (by omega : nb + 8 * u + 4 ≠ nb + 8 * u + 6),
                  Function.update_of_ne (by omega : nb + 8 * u + 4 ≠ nb + 8 * u + 5)]
              · dsimp only [ordNodeAddr, m8, m7, ordFreshNode]; rw [← hnb]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                simp [SplayState.nodes_updateNode, Function.update_of_ne (by omega : nb + 8 * u + 5 ≠ nb + 8 * u + 6)]
              · dsimp only [ordNodeAddr, m8, m7, ordFreshNode]; rw [← hnb]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                simp
              · dsimp only [ordNodeAddr, m8, m7]; rw [← hnb]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                repeat rw [Function.update_of_ne (by omega)]
                exact hnf3_u
            · have hna := hna3 x hx hxu
              rw [SplayState.nodes_updateNode_ne _ hxu]
              have hne_all : ∀ j < 8, m8 (nb + 8 * x + j) = st3.mem (nb + 8 * x + j) := fun j hj => by
                dsimp only [m8, m7]
                rw [Function.update_of_ne (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)]
                repeat rw [Function.update_of_ne (by omega)]
              dsimp only [OrdNodeAt, ordNodeAddr]; rw [← hnb]
              refine ⟨by simpa using (hne_all 0 (by omega)).trans (by simpa [ordNodeAddr] using hna.1),
                (hne_all 1 (by omega)).trans hna.2.1,
                (hne_all 2 (by omega)).trans hna.2.2.1,
                (hne_all 3 (by omega)).trans hna.2.2.2.1,
                (hne_all 4 (by omega)).trans hna.2.2.2.2.1,
                (hne_all 5 (by omega)).trans hna.2.2.2.2.2.1,
                (hne_all 6 (by omega)).trans hna.2.2.2.2.2.2.1,
                (hne_all 7 (by omega)).trans hna.2.2.2.2.2.2.2⟩ }
    · simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]; omega
  obtain ⟨oF, stF, cF, hrunF, ⟨hoF, harenaF, hfrF⟩, hcF⟩ := htail
  have hfull := ord_runs_seq_normal hld2 (ord_runs_seq_normal hld3 (ord_runs_seq_normal hrun3 hrunF))
  set S' : OrdStoreState :=
    { S with
      nextNode := nn', freeHead := fh', freeList := fl', nextFree := nf',
      eNode := Function.update S.eNode key u,
      splay := S.splay.updateNode u (fun _ => ordFreshNode key) }
  unfold ordAllocBody
  refine ⟨oF, stF, _, hfull, ⟨u, S', by rw [hoF]; rfl, hu1, hunn, hnn_ge, hnn_le, rfl, rfl, rfl, rfl, rfl, rfl,
    hu_nlive, hu_nfl, hfl_nd, hfc', hfl_le, hlive_fl, hpart', harenaF, hfr3.trans hfrF⟩, ?_⟩
  unfold ORD_ALLOC_COST
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
  omega

end MinCostFlow.SparseCore.Program
