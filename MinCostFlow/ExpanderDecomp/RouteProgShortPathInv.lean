module

public import MinCostFlow.ExpanderDecomp.RouteProgShortPathBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Short-Path Blocking Loop Invariants and Frame Helpers (`RouteProgShortPathInv`)

Shared invariants (`SpLoopInv`, `SpLoopRegs`), `PathChainAt` endpoint bounds, `runs_seqStmts_append`,
and read-only frame extraction lemmas (`adjCsrAt_of_spFrame`, `stop_of_spFrame`,
`bfsCfg_static_of_spFrame`, `dfsCfg_static_of_spFrame`) for `shortPathBlockProc`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma pathChainAt_head_le {mem : ℕ → ℕ} {X : Finset ℕ} {lo hi head tail : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)} (h : PathChainAt mem X lo hi head tail ps) :
    head ≤ hi := by
  cases ps with
  | nil => rw [h.1]; exact Nat.zero_le _
  | cons p rest =>
    cases rest with
    | nil => have := h.2.2.1; omega
    | cons q rest' => have := h.2.1; omega

lemma pathChainAt_tail_le {mem : ℕ → ℕ} {X : Finset ℕ} {lo hi head tail : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)} (h : PathChainAt mem X lo hi head tail ps) :
    tail ≤ hi := by
  induction ps generalizing head with
  | nil => rw [h.2]; exact Nat.zero_le _
  | cons p rest ih =>
    cases rest with
    | nil => rw [← h.1]; have := h.2.2.1; omega
    | cons q rest' => exact ih h.2.2.2.2.2.2.2.2.2.2.2.2

lemma runs_seqStmts_append {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {l1 l2 : List Stmt} {st0 st1 st2 : State} {c1 c2 : ℕ}
    (h1 : l1 ≠ []) (h2 : l2 ≠ [])
    (hr1 : Runs w p ω (seqStmts l1) st0 .normal st1 c1)
    (hr2 : Runs w p ω (seqStmts l2) st1 .normal st2 c2) :
    ∃ c, Runs w p ω (seqStmts (l1 ++ l2)) st0 .normal st2 c ∧ c ≤ c1 + c2 + l1.length := by
  induction l1 generalizing st0 c1 with
  | nil => exact absurd rfl h1
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases l2 with
      | nil => exact absurd rfl h2
      | cons b rest2 =>
        exact ⟨c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hr1, hr2, rfl⟩), by simp⟩
    | cons b rest1 =>
      dsimp only [seqStmts] at hr1
      rcases runs_seq_iff.mp hr1 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
      · cases h
      obtain ⟨c', hrc', hc'⟩ := ih (by simp) hrb
      refine ⟨ca + c' + 1, ?_, by simp only [List.length_cons] at hc' ⊢; omega⟩
      have hne : ((b :: rest1) ++ l2) ≠ [] := by simp
      cases heq : (b :: rest1) ++ l2 with
      | nil => exact absurd heq hne
      | cons x xs =>
        rw [List.cons_append, heq]
        dsimp only [seqStmts]
        rw [← heq]
        exact runs_seq_iff.mpr (Or.inr ⟨sa, ca, c', hra, hrc', rfl⟩)

/-! ## 1. Loop Invariants and Frame Extraction Helpers -/

/-- State invariant for `spPhaseLoopStmt` across blocking phases. -/
structure SpLoopInv (mem mem0 : ℕ → ℕ) (X V0 S : Finset ℕ)
    (spCfg : SpCfg) (bfsCfg : BfsCfg) (dfsCfg : DfsCfg) (spCfgAddr : ℕ)
    (rem : ℕ) (V : Finset ℕ) (acc : List ((ℕ × ℕ) × List ℕ))
    (heapPtr head tail bfsGen dfsGen : ℕ) : Prop where
  V_sub : V ⊆ V0
  paths_le : acc.length ≤ (V0 \ V).card
  heap_lo : spCfg.heapIn ≤ heapPtr
  heap_hi : heapPtr ≤ spCfg.heapIn + 5 * (V0 \ V).card
  bgen_lo : spCfg.bfsGenIn ≤ bfsGen
  bgen_hi : bfsGen + rem ≤ spCfg.bfsGenIn + spCfg.d + 1
  dgen_lo : spCfg.dfsGenIn ≤ dfsGen
  dgen_hi : dfsGen + rem ≤ spCfg.dfsGenIn + spCfg.d + 1
  mask_ok : ∀ v < X.card, mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V
  mask_mono : ∀ v < X.card, mem (spCfg.maskArrAddr + v) = mem0 (spCfg.maskArrAddr + v) ∨
    mem (spCfg.maskArrAddr + v) = spCfg.maskBadVal
  sbuf_at : ListAt mem spCfg.sBufAddr (((S ∩ V).sort (· ≤ ·)).map (locOf X))
  chain : PathChainAt mem X spCfg.heapIn heapPtr head tail acc
  vis_le : ∀ v < X.card, mem (bfsCfg.visStampAddr + v) ≤ bfsGen
  cur_le : ∀ v < X.card, mem (dfsCfg.curStampAddr + v) ≤ dfsGen
  used_le : ∀ v < X.card, mem (dfsCfg.usedStampAddr + v) ≤ dfsGen
  dead_le : ∀ v < X.card, mem (dfsCfg.deadStampAddr + v) ≤ dfsGen
  frame : ∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → mem a = mem0 a

/-- Register invariant for `spPhaseLoopStmt` (`r0 .. r20`). -/
@[expose] def SpLoopRegs (regs : ℕ → ℕ) (spCfg : SpCfg) (spCfgAddr : ℕ)
    (rem sLen bfsGen dfsGen heapPtr head tail pathsCnt : ℕ) : Prop :=
  ∀ r ≤ 20, regs r =
    match r with
    | 0 => spCfgAddr | 1 => spCfg.bfsCfgAddr | 2 => spCfg.dfsCfgAddr
    | 3 => spCfg.maskArrAddr | 4 => spCfg.maskBadVal
    | 5 => spCfg.usedListAddr | 6 => spCfg.sBufAddr
    | 7 => spCfg.srcInPtr | 8 => spCfg.srcInLen
    | 9 => spCfg.d | 10 => spCfg.bfsGenIn | 11 => spCfg.dfsGenIn | 12 => spCfg.heapIn
    | 13 => rem | 14 => sLen | 15 => bfsGen | 16 => dfsGen
    | 17 => heapPtr | 18 => head | 19 => tail | _ => pathsCnt

lemma not_spWriteSet_of_ro {w nX m2 : ℕ} {spCfg : SpCfg} {bfsCfg : BfsCfg}
    {dfsCfg : DfsCfg} {spCfgAddr a : ℕ}
    (_h : SpDisj w nX m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hb : ¬ BfsWriteSet nX bfsCfg spCfg.bfsCfgAddr a)
    (hd : ¬ DfsWriteSet nX ({ dfsCfg with heapIn := spCfg.heapIn }) spCfg.dfsCfgAddr a)
    (hhp : a < spCfg.heapIn ∨ spCfg.heapIn + 10 * nX ≤ a)
    (hbc : a ≠ spCfg.bfsCfgAddr + 12 ∧ a ≠ spCfg.bfsCfgAddr + 15)
    (hdc : a ≠ spCfg.dfsCfgAddr + 8 ∧ a ≠ spCfg.dfsCfgAddr + 17 ∧ a ≠ spCfg.dfsCfgAddr + 18 ∧
      (a < spCfg.dfsCfgAddr + 20 ∨ spCfg.dfsCfgAddr + 24 ≤ a))
    (hm : a < spCfg.maskArrAddr ∨ spCfg.maskArrAddr + nX ≤ a)
    (hs : a < spCfg.sBufAddr ∨ spCfg.sBufAddr + nX ≤ a)
    (hsp : a < spCfgAddr + 12 ∨ spCfgAddr + 18 ≤ a) :
    ¬ SpWriteSet nX spCfg bfsCfg dfsCfg spCfgAddr a := by
  intro hw
  rcases hw with c | c | c | c | c | c | c | c
  · exact hb c
  · exact hd c
  · omega
  · rcases c with rfl | rfl <;> omega
  · rcases c with rfl | rfl | rfl | c <;> omega
  · omega
  · omega
  · omega

lemma adjCsrAt_of_spFrame {w m2 : ℕ} {X : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {spCfg : SpCfg} {bfsCfg : BfsCfg} {dfsCfg : DfsCfg} {spCfgAddr : ℕ} {mem mem0 : ℕ → ℕ}
    (h : SpDisj w X.card m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hcsr0 : AdjCsrAt mem0 bfsCfg.offAddr bfsCfg.nbAddr dfsCfg.edgeAddr X adj)
    (hfr : ∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → mem a = mem0 a) :
    AdjCsrAt mem bfsCfg.offAddr bfsCfg.nbAddr dfsCfg.edgeAddr X adj := by
  have hb := h.bfs_disj
  have hd := h.dfs_disj
  have hoff : ∀ k ≤ X.card, mem (bfsCfg.offAddr + k) = mem0 (bfsCfg.offAddr + k) := by
    intro k hk
    apply hfr
    have hro_b := hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (bfsCfg.offAddr + k) ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hro_d := hd.ro_off (bfsCfg.offAddr + k) ⟨by dsimp only; rw [h.dfs_off]; omega, by dsimp only; rw [h.dfs_off]; omega⟩
    exact not_spWriteSet_of_ro h hro_b hro_d
      (by rcases h.off_hp10 with x | x <;> omega)
      (by rcases h.bcfg_off with x | x <;> omega)
      (by rcases h.dcfg_off with x | x <;> omega)
      (by rcases h.mask_off with x | x <;> omega)
      (by rcases h.sbuf_off with x | x <;> omega)
      (by rcases h.sp_off with x | x <;> omega)
  have hnb : ∀ k < m2, mem (bfsCfg.nbAddr + k) = mem0 (bfsCfg.nbAddr + k) := by
    intro k hk
    apply hfr
    have hro_b := hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (bfsCfg.nbAddr + k) ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hro_d := hd.ro_nb (bfsCfg.nbAddr + k) ⟨by dsimp only; rw [h.dfs_nb]; omega, by dsimp only; rw [h.dfs_nb]; omega⟩
    exact not_spWriteSet_of_ro h hro_b hro_d
      (by rcases h.nb_hp10 with x | x <;> omega)
      (by rcases h.bcfg_nb with x | x <;> omega)
      (by rcases h.dcfg_nb with x | x <;> omega)
      (by rcases h.mask_nb with x | x <;> omega)
      (by rcases h.sbuf_nb with x | x <;> omega)
      (by rcases h.sp_nb with x | x <;> omega)
  have hedge : ∀ k < m2, mem (dfsCfg.edgeAddr + k) = mem0 (dfsCfg.edgeAddr + k) := by
    intro k hk
    apply hfr
    have hro_b := h.edge_bfsW (dfsCfg.edgeAddr + k) ⟨by omega, by omega⟩
    have hro_d := hd.ro_edge (dfsCfg.edgeAddr + k) ⟨by dsimp only; omega, by dsimp only; omega⟩
    exact not_spWriteSet_of_ro h hro_b hro_d
      (by rcases h.edge_hp10 with x | x <;> omega)
      (by rcases h.bcfg_edge with x | x <;> omega)
      (by rcases h.dcfg_edge with x | x <;> omega)
      (by rcases h.mask_edge with x | x <;> omega)
      (by rcases h.sbuf_edge with x | x <;> omega)
      (by rcases h.sp_edge with x | x <;> omega)
  refine ⟨⟨fun k hk => (hoff k hk).trans (hcsr0.1.1 k hk), ?_⟩, ?_⟩
  · intro u hu j hj
    have hlt : adjCsrOff X adj u + j < m2 := by
      have h1 : adjCsrOff X adj (u + 1) ≤ adjCsrOff X adj X.card := adjCsrOff_mono X adj (by omega)
      have h2 := adjCsrOff_succ X adj u
      omega
    rw [Nat.add_assoc]; exact (hnb _ hlt).trans (by rw [← Nat.add_assoc]; exact hcsr0.1.2 u hu j hj)
  · intro u hu j hj
    have hlt : adjCsrOff X adj u + j < m2 := by
      have h1 : adjCsrOff X adj (u + 1) ≤ adjCsrOff X adj X.card := adjCsrOff_mono X adj (by omega)
      have h2 := adjCsrOff_succ X adj u
      omega
    rw [Nat.add_assoc]; exact (hedge _ hlt).trans (by rw [← Nat.add_assoc]; exact hcsr0.2 u hu j hj)

lemma stop_of_spFrame {w m2 : ℕ} {X T : Finset ℕ}
    {spCfg : SpCfg} {bfsCfg : BfsCfg} {dfsCfg : DfsCfg} {spCfgAddr : ℕ} {mem mem0 : ℕ → ℕ}
    (h : SpDisj w X.card m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hstop0 : ∀ v < X.card, mem0 (bfsCfg.stopArrAddr + v) = bfsCfg.stopVal ↔ origOf X v ∈ T)
    (hfr : ∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → mem a = mem0 a) :
    ∀ v < X.card, mem (bfsCfg.stopArrAddr + v) = bfsCfg.stopVal ↔ origOf X v ∈ T := by
  intro v hv
  have hb := h.bfs_disj
  have hd := h.dfs_disj
  have heq : mem (bfsCfg.stopArrAddr + v) = mem0 (bfsCfg.stopArrAddr + v) := by
    apply hfr
    have hro_b := hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by dsimp only; rw [h.bfs_hasStop]; omega)
      (bfsCfg.stopArrAddr + v) ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hro_d := hd.ro_stop (bfsCfg.stopArrAddr + v)
      ⟨by dsimp only; rw [h.dfs_stop]; omega, by dsimp only; rw [h.dfs_stop]; omega⟩
    exact not_spWriteSet_of_ro h hro_b hro_d
      (by rcases h.stop_hp10 with x | x <;> omega)
      (by rcases h.bcfg_stop with x | x <;> omega)
      (by rcases h.dcfg_stop with x | x <;> omega)
      (by rcases h.mask_stop with x | x <;> omega)
      (by rcases h.sbuf_stop with x | x <;> omega)
      (by rcases h.sp_stop with x | x <;> omega)
  rw [heq]; exact hstop0 v hv

lemma bfsCfg_static_of_spFrame {w nX m2 : ℕ} {spCfg : SpCfg} {bfsCfg : BfsCfg}
    {dfsCfg : DfsCfg} {spCfgAddr : ℕ} {mem mem0 : ℕ → ℕ}
    (h : SpDisj w nX m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hfr : ∀ a, ¬ SpWriteSet nX spCfg bfsCfg dfsCfg spCfgAddr a → mem a = mem0 a)
    {i : ℕ} (hi : i < 16) (h12 : i ≠ 12) (h15 : i ≠ 15) :
    mem (spCfg.bfsCfgAddr + i) = mem0 (spCfg.bfsCfgAddr + i) := by
  apply hfr
  have hro_b := h.bfs_disj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (spCfg.bfsCfgAddr + i) ⟨by omega, by omega⟩
  have hro_d := h.bcfg_dfsW (spCfg.bfsCfgAddr + i) ⟨by omega, by omega⟩
  exact not_spWriteSet_of_ro h hro_b hro_d
    (by rcases h.bcfg_hp10 with x | x <;> omega)
    ⟨by omega, by omega⟩
    (by rcases h.bcfg_dcfg with x | x <;> omega)
    (by rcases h.mask_bcfg with x | x <;> omega)
    (by rcases h.sbuf_bcfg with x | x <;> omega)
    (by rcases h.bcfg_sp with x | x <;> omega)

lemma dfsCfg_static_of_spFrame {w nX m2 : ℕ} {spCfg : SpCfg} {bfsCfg : BfsCfg}
    {dfsCfg : DfsCfg} {spCfgAddr : ℕ} {mem mem0 : ℕ → ℕ}
    (h : SpDisj w nX m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hfr : ∀ a, ¬ SpWriteSet nX spCfg bfsCfg dfsCfg spCfgAddr a → mem a = mem0 a)
    {i : ℕ} (hi : i < 20) (h8 : i ≠ 8) (h17 : i ≠ 17) (h18 : i ≠ 18) :
    mem (spCfg.dfsCfgAddr + i) = mem0 (spCfg.dfsCfgAddr + i) := by
  apply hfr
  have hro_b := h.dcfg_bfsW (spCfg.dfsCfgAddr + i) ⟨by omega, by omega⟩
  have hro_d := h.dfs_disj.ro_cfg (spCfg.dfsCfgAddr + i) ⟨by omega, by omega⟩
  exact not_spWriteSet_of_ro h hro_b hro_d
    (by rcases h.dcfg_hp10 with x | x <;> omega)
    (by rcases h.bcfg_dcfg with x | x <;> omega)
    ⟨by omega, by omega, by omega, Or.inl (by omega)⟩
    (by rcases h.mask_dcfg with x | x <;> omega)
    (by rcases h.sbuf_dcfg with x | x <;> omega)
    (by rcases h.dcfg_sp with x | x <;> omega)

end MinCostFlow.ExpanderDecomp
