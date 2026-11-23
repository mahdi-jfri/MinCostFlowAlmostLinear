module

public import MinCostFlow.Expander.DecomposeGroupVertsProg

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Edge Grouping by Partition (`groupEdgesProc`)

Given a valid graph `curG` at `curGAddr`, partition count `k` (`1 ≤ k ≤ curG.n`), and a grouping
buffer at `bufAddr` populated by `groupVertsProc` (`grpPartId`, `grpLocalId`), `groupEdgesProc`
partitions all within-part edges of `curG` into contiguous compressed edge lists in
`grpPartEdges`, returning `0` in `O(curG.n + curG.m + 1)` Word-RAM time.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Program & Contract -/

def groupEdgesSetupStmt : Stmt :=
  seqStmts
    [ .assign 3 (.load (.reg 0))
    , .assign 4 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 5 (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 3)))
    , .assign 6 (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 3))) (.const 1))
    , .assign 7 (.bin .add (.reg 6) (.reg 3))
    , .assign 8 (.bin .add (.reg 7) (.reg 3))
    , .assign 9 (.bin .add (.bin .add (.reg 8) (.reg 3)) (.const 1))
    , .assign 10 (.bin .add (.reg 9) (.reg 3)) ]

def groupEdgesCountStmt : Stmt :=
  seqStmts
    [ forRange 11 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 7) (.reg 11)) (.const 0))
    , forRange 11 (.const 0) (.reg 4)
        (seqStmts
          [ .assign 12 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 11)))))
          , .assign 13 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 11)))))
          , .assign 14 (.load (.bin .add (.reg 5) (.reg 12)))
          , .assign 15 (.load (.bin .add (.reg 5) (.reg 13)))
          , .cond (.bin .eq (.reg 14) (.reg 15))
              (seqStmts
                [ .assign 12 (.load (.bin .add (.reg 7) (.reg 14)))
                , .store (.bin .add (.reg 7) (.reg 14)) (.bin .add (.reg 12) (.const 1)) ])
              .nop ]) ]

def groupEdgesPrefixStmt : Stmt :=
  seqStmts
    [ .store (.reg 8) (.const 0)
    , .assign 12 (.const 0)
    , forRange 11 (.const 0) (.reg 1)
        (seqStmts
          [ .assign 13 (.load (.bin .add (.reg 7) (.reg 11)))
          , .store (.bin .add (.reg 9) (.reg 11)) (.reg 12)
          , .assign 12 (.bin .add (.reg 12) (.reg 13))
          , .store (.bin .add (.reg 8) (.bin .add (.reg 11) (.const 1))) (.reg 12) ]) ]

def groupEdgesScatterStmt : Stmt :=
  forRange 11 (.const 0) (.reg 4)
    (seqStmts
      [ .assign 12 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 11)))))
      , .assign 13 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 11)))))
      , .assign 14 (.load (.bin .add (.reg 5) (.reg 12)))
      , .assign 15 (.load (.bin .add (.reg 5) (.reg 13)))
      , .cond (.bin .eq (.reg 14) (.reg 15))
          (seqStmts
            [ .assign 12 (.load (.bin .add (.reg 6) (.reg 12)))
            , .assign 13 (.load (.bin .add (.reg 6) (.reg 13)))
            , .assign 15 (.load (.bin .add (.reg 9) (.reg 14)))
            , .store (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 15))) (.reg 12)
            , .store (.bin .add (.reg 10) (.bin .add (.bin .mul (.const 2) (.reg 15)) (.const 1))) (.reg 13)
            , .store (.bin .add (.reg 9) (.reg 14)) (.bin .add (.reg 15) (.const 1)) ])
          .nop ])

/-- `groupEdgesProc`: args `[curGAddr, k, bufAddr]`. Groups within-part edges of `curG` into
`grpPartEdges` and returns `0`. -/
def groupEdgesProc : Stmt :=
  seqStmts
    [ groupEdgesSetupStmt
    , groupEdgesCountStmt
    , groupEdgesPrefixStmt
    , groupEdgesScatterStmt
    , .ret (.const 0) ]

lemma groupEdgesProc_noRand : groupEdgesProc.NoRand := by
  simp [groupEdgesProc, groupEdgesSetupStmt, groupEdgesCountStmt, groupEdgesPrefixStmt,
    groupEdgesScatterStmt, forRange, WordRAM.forUp, seqStmts, Stmt.NoRand]

/-- Contract for `groupEdgesProc`: args `[curGAddr, k, bufAddr]`. -/
def groupEdgesContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (curGAddr k bufAddr : ℕ) (G : Cited.Graph), args = [curGAddr, k, bufAddr] ∧
      1 ≤ k ∧ k ≤ G.n ∧ G.IsValid ∧
      GraphAt mem curGAddr G ∧
      curGAddr + 2 + 2 * G.m ≤ bufAddr ∧
      bufAddr + groupBufSize G.n G.m + 2 < 2 ^ w ∧
      16 ≤ 2 ^ w ∧
      (∀ u < G.n, mem (grpPartId bufAddr G.n + u) < k) ∧
      (∀ u < G.n, mem (grpLocalId bufAddr G.n + u) < G.n)
  post args mem _ mem' :=
    let curGAddr := args.getD 0 0
    let k := args.getD 1 0
    let bufAddr := args.getD 2 0
    let n := mem curGAddr
    let m := mem (curGAddr + 1)
    let partFn := fun u => mem (grpPartId bufAddr n + u)
    let localFn := fun u => mem (grpLocalId bufAddr n + u)
    mem' (grpEdgeOff bufAddr n) = 0 ∧
    mem' (grpEdgeOff bufAddr n + k) ≤ m ∧
    (∀ q < k, mem' (grpEdgeOff bufAddr n + (q + 1)) =
      mem' (grpEdgeOff bufAddr n + q) + mem' (grpEdgeCnt bufAddr n + q) ∧
      mem' (grpEdgeOff bufAddr n + q) + mem' (grpEdgeCnt bufAddr n + q) ≤ m) ∧
    (∀ q < k,
      let es := ((List.range m).filter fun j =>
        let u := mem (curGAddr + 2 + 2 * j)
        let v := mem (curGAddr + 3 + 2 * j)
        decide (partFn u = q ∧ partFn v = q)).map fun j =>
        (localFn (mem (curGAddr + 2 + 2 * j)), localFn (mem (curGAddr + 3 + 2 * j)))
      mem' (grpEdgeCnt bufAddr n + q) = es.length ∧
      ∀ t (ht : t < es.length),
        mem' (grpPartEdges bufAddr n + 2 * (mem' (grpEdgeOff bufAddr n + q) + t)) = es[t].1 ∧
        mem' (grpPartEdges bufAddr n + 2 * (mem' (grpEdgeOff bufAddr n + q) + t) + 1) = es[t].2) ∧
    MemFrame mem mem' (grpEdgeCnt bufAddr n) (bufAddr + groupBufSize n m)
  cost args mem :=
    let curGAddr := args.getD 0 0
    200 * (mem curGAddr + mem (curGAddr + 1) + 1)

/-! ## 2. Pure Edge-Bucket & Offset Helpers -/

def edgeIdxBucket (mem : ℕ → ℕ) (curGAddr bufAddr n q v : ℕ) : List ℕ :=
  (List.range v).filter fun j =>
    let u := mem (curGAddr + 2 + 2 * j)
    let wv := mem (curGAddr + 3 + 2 * j)
    decide (mem (grpPartId bufAddr n + u) = q ∧ mem (grpPartId bufAddr n + wv) = q)

lemma edgeIdxBucket_append (mem : ℕ → ℕ) (curGAddr bufAddr n q v : ℕ) :
    edgeIdxBucket mem curGAddr bufAddr n q (v + 1) =
      edgeIdxBucket mem curGAddr bufAddr n q v ++
        if mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * v)) = q ∧
            mem (grpPartId bufAddr n + mem (curGAddr + 3 + 2 * v)) = q
        then [v] else [] := by
  simp only [edgeIdxBucket, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases h : mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * v)) = q ∧
      mem (grpPartId bufAddr n + mem (curGAddr + 3 + 2 * v)) = q <;> simp [h]

lemma edgeIdxBucket_length_mono (mem : ℕ → ℕ) (curGAddr bufAddr n q : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    (edgeIdxBucket mem curGAddr bufAddr n q a).length ≤
      (edgeIdxBucket mem curGAddr bufAddr n q b).length := by
  have hs : List.range b = List.range a ++ (List.range (b - a)).map (fun x => a + x) := by
    have hr : List.range (a + (b - a)) = List.range a ++ (List.range (b - a)).map (fun x => a + x) :=
      List.range_add
    rwa [show a + (b - a) = b by omega] at hr
  simp only [edgeIdxBucket, hs, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

lemma edgeIdxBucket_length_le (mem : ℕ → ℕ) (curGAddr bufAddr n q v : ℕ) :
    (edgeIdxBucket mem curGAddr bufAddr n q v).length ≤ v := by
  simpa [edgeIdxBucket] using List.length_filter_le (p := fun j =>
    decide (mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * j)) = q ∧
      mem (grpPartId bufAddr n + mem (curGAddr + 3 + 2 * j)) = q)) (List.range v)

lemma sum_edgeIdxBucket_le (mem : ℕ → ℕ) (curGAddr bufAddr n k v : ℕ) :
    ((List.range k).map fun q => (edgeIdxBucket mem curGAddr bufAddr n q v).length).sum ≤ v := by
  induction v with
  | zero => simp [edgeIdxBucket]
  | succ v ih =>
    have hsplit : ∀ q, (edgeIdxBucket mem curGAddr bufAddr n q (v + 1)).length =
        (edgeIdxBucket mem curGAddr bufAddr n q v).length +
          if q = mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * v)) ∧
              mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * v)) =
                mem (grpPartId bufAddr n + mem (curGAddr + 3 + 2 * v))
          then 1 else 0 := by
      intro q
      rw [edgeIdxBucket_append, List.length_append]
      split_ifs with h1 h2 h2 <;> simp_all
    have sum_add : ∀ (f g : ℕ → ℕ) (m : ℕ),
        ((List.range m).map fun q => f q + g q).sum =
          ((List.range m).map f).sum + ((List.range m).map g).sum := by
      intro f g m
      induction m with
      | zero => simp
      | succ m ihm =>
        simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton, ihm]; omega
    have hsum_eq : ((List.range k).map fun q => (edgeIdxBucket mem curGAddr bufAddr n q (v + 1)).length).sum =
        ((List.range k).map fun q => (edgeIdxBucket mem curGAddr bufAddr n q v).length).sum +
        ((List.range k).map fun q =>
          if q = mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * v)) ∧
              mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * v)) =
                mem (grpPartId bufAddr n + mem (curGAddr + 3 + 2 * v))
          then 1 else 0).sum := by
      have hcongr := List.map_congr_left (fun q (_ : q ∈ List.range k) => hsplit q)
      rw [hcongr]
      exact sum_add _ _ k
    have h1_le : ∀ m c (P : Prop) [Decidable P],
        ((List.range m).map fun q => if q = c ∧ P then 1 else 0).sum ≤ 1 := by
      intro m c P _
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        by_cases hm : m = c ∧ P
        · have hz : ∀ x ∈ List.range m, (if x = c ∧ P then 1 else 0) = 0 := by
            intro x hx; have hxlt := List.mem_range.mp hx; split_ifs <;> omega
          have h0 : ((List.range m).map fun x => if x = c ∧ P then 1 else 0).sum = 0 :=
            List.sum_eq_zero (by intro y hy; rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩; exact hz x hx)
          rw [h0]
          split_ifs
          omega
        · split_ifs
          omega
    rw [hsum_eq]
    have hb := h1_le k (mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * v)))
      (mem (grpPartId bufAddr n + mem (curGAddr + 2 + 2 * v)) =
        mem (grpPartId bufAddr n + mem (curGAddr + 3 + 2 * v)))
    omega

lemma edgeOff_mono {mem : ℕ → ℕ} {bufAddr n k : ℕ}
    (hoff_step : ∀ q < k, mem (grpEdgeOff bufAddr n + (q + 1)) =
      mem (grpEdgeOff bufAddr n + q) + mem (grpEdgeCnt bufAddr n + q)) :
    ∀ a b, a ≤ b → b ≤ k → mem (grpEdgeOff bufAddr n + a) ≤ mem (grpEdgeOff bufAddr n + b) := by
  intro a b hab hbk
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.le_zero.mp hab
    subst ha0; exact le_refl _
  | succ b ih =>
    rcases Nat.le_succ_iff.mp hab with hab' | rfl
    · have h1 := ih hab' (by omega)
      have h2 := hoff_step b (by omega)
      omega
    · exact le_refl _

lemma edgeOff_disjoint_of_ne {mem : ℕ → ℕ} {bufAddr n k : ℕ}
    (hoff_step : ∀ q < k, mem (grpEdgeOff bufAddr n + (q + 1)) =
      mem (grpEdgeOff bufAddr n + q) + mem (grpEdgeCnt bufAddr n + q))
    {q₁ q₂ t₁ t₂ : ℕ} (hq₁ : q₁ < k) (hq₂ : q₂ < k) (hne : q₁ ≠ q₂)
    (ht₁ : t₁ < mem (grpEdgeCnt bufAddr n + q₁)) (ht₂ : t₂ < mem (grpEdgeCnt bufAddr n + q₂)) :
    mem (grpEdgeOff bufAddr n + q₁) + t₁ ≠ mem (grpEdgeOff bufAddr n + q₂) + t₂ := by
  rcases Nat.lt_trichotomy q₁ q₂ with h12 | rfl | h21
  · have hs := hoff_step q₁ hq₁
    have hm := edgeOff_mono hoff_step (q₁ + 1) q₂ h12 (by omega)
    omega
  · exact absurd rfl hne
  · have hs := hoff_step q₂ hq₂
    have hm := edgeOff_mono hoff_step (q₂ + 1) q₁ h21 (by omega)
    omega

/-! ## 3. Per-Stage Triple Proofs -/

lemma groupEdgesSetup_triple {w curGAddr k bufAddr : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (G : Cited.Graph) (hga : GraphAt mem curGAddr G)
    (hcb : curGAddr + 2 + 2 * G.m ≤ bufAddr) (hbuf : bufAddr + groupBufSize G.n G.m + 2 < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) :
    Triple w p
      (fun st => st = startState [curGAddr, k, bufAddr] mem pos)
      groupEdgesSetupStmt
      (normalPost fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
        st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
        st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
        st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
        st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
        st.mem = mem)
      (fun _ => 50) := by
  intro st ω hst
  subst hst
  have hn_eq : mem curGAddr = G.n := graphAt_n hga
  have hm_eq : mem (curGAddr + 1) = G.m := graphAt_m hga
  dsimp only [groupBufSize] at hbuf
  refine runs_start_le ?_
  dsimp only [groupEdgesSetupStmt, seqStmts]
  wram_step; simp only [startState, List.getD, hn_eq]
  wram_step; simp only [hm_eq]
  wram_run
  · refine ⟨by simp, by simp, by simp, by simp, by simp,
      ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      dsimp only [grpPartId, grpLocalId, grpEdgeCnt, grpEdgeOff, grpEdgeCur, grpPartEdges] <;>
      simp <;> omega
  · wram_cost

lemma groupEdgesCount_triple {w curGAddr k bufAddr : ℕ} (p : Program) (mem : ℕ → ℕ)
    (G : Cited.Graph) (hk1 : 1 ≤ k) (hkn : k ≤ G.n) (hval : G.IsValid)
    (hga : GraphAt mem curGAddr G) (hcb : curGAddr + 2 + 2 * G.m ≤ bufAddr)
    (hbuf : bufAddr + groupBufSize G.n G.m + 2 < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hpid : ∀ u < G.n, mem (grpPartId bufAddr G.n + u) < k) :
    Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
        st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
        st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
        st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
        st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
        st.mem = mem)
      groupEdgesCountStmt
      (normalPost fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
        st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
        st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
        st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
        st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
        (∀ q < k, st.mem (grpEdgeCnt bufAddr G.n + q) =
          (edgeIdxBucket mem curGAddr bufAddr G.n q G.m).length) ∧
        MemFrame mem st.mem (grpEdgeCnt bufAddr G.n) (grpEdgeOff bufAddr G.n))
      (fun _ => 15 * G.n + 65 * G.m + 25) := by
  have hw2 : 1 < 2 ^ w := by omega
  dsimp only [groupBufSize] at hbuf
  -- Loop 1: zero `edgeCnt[0..k-1]`
  let InvZ : ℕ → State → Prop := fun q st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
    st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
    st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
    st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
    st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
    st.regs 11 = q ∧
    (∀ j < q, st.mem (grpEdgeCnt bufAddr G.n + j) = 0) ∧
    MemFrame mem st.mem (grpEdgeCnt bufAddr G.n) (grpEdgeOff bufAddr G.n)
  have hzero := Triple.forRange_const (p := p) (r := 11) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 7) (.reg 11)) (.const 0))
    (P := fun st =>
      st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
      st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
      st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
      st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
      st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
      st.mem = mem)
    (Inv := InvZ)
    6 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, by simp, fun _ hj => by omega,
        by simp [hm, memFrame_refl]⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.1; eval_expr)
    (fun q _ hqlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hzq, hfr⟩
      have hfz0 : grpEdgeCnt bufAddr G.n ≤ bufAddr + 9 * G.n + 1 + q := by dsimp only [grpEdgeCnt]; omega
      have hfz1 : bufAddr + 9 * G.n + 1 + q < grpEdgeOff bufAddr G.n := by
        dsimp only [grpEdgeOff]; omega
      dsimp only [grpEdgeCnt, grpEdgeOff] at h7 h8 hzq hfr ⊢
      refine runs_start_le ?_
      wram_run
      · dsimp only [InvZ, grpEdgeCnt]
        refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
          by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
          by simp, fun j hj => ?_, ?_⟩, by simp [h11]⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj_eq
          · simp only [Function.update_of_ne (by omega :
              bufAddr + 9 * G.n + 1 + j ≠ bufAddr + 9 * G.n + 1 + q)]
            exact hzq j hj'
          · subst j; simp
        · exact memFrame_trans hfr (memFrame_update hfz0 hfz1)
      · wram_cost)
  -- Loop 2: count within-part edges
  let InvC : ℕ → State → Prop := fun j st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
    st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
    st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
    st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
    st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
    st.regs 11 = j ∧
    (∀ q < k, st.mem (grpEdgeCnt bufAddr G.n + q) =
      (edgeIdxBucket mem curGAddr bufAddr G.n q j).length) ∧
    MemFrame mem st.mem (grpEdgeCnt bufAddr G.n) (grpEdgeOff bufAddr G.n)
  have hcount := Triple.forRange_const (p := p) (r := 11) (lo := .const 0) (hi := .reg 4)
    (body := seqStmts
      [ .assign 12 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 11)))))
      , .assign 13 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 11)))))
      , .assign 14 (.load (.bin .add (.reg 5) (.reg 12)))
      , .assign 15 (.load (.bin .add (.reg 5) (.reg 13)))
      , .cond (.bin .eq (.reg 14) (.reg 15))
          (seqStmts
            [ .assign 12 (.load (.bin .add (.reg 7) (.reg 14)))
            , .store (.bin .add (.reg 7) (.reg 14)) (.bin .add (.reg 12) (.const 1)) ])
          .nop ])
    (P := InvZ k) (Inv := InvC)
    55 0 G.m (Nat.zero_le G.m) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _, hzq, hfr⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, by simp,
        fun q hqk => by simp [edgeIdxBucket, hzq q hqk], hfr⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.1; eval_expr)
    (fun j _ hjlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hcnt, hfr⟩
      dsimp only [grpPartId, grpEdgeCnt, grpEdgeOff] at h5 h7 h8 hcnt hfr ⊢
      have he_val := hval _ (List.getElem_mem hjlt)
      set u := (G.edges[j]'hjlt).1
      set v := (G.edges[j]'hjlt).2
      have hu_eq : st.mem (curGAddr + (2 + 2 * j)) = u := by
        rw [hfr _ (Or.inl (by omega)), ← Nat.add_assoc]; exact graphAt_edge_fst hga hjlt
      have hv_eq : st.mem (curGAddr + (3 + 2 * j)) = v := by
        rw [hfr _ (Or.inl (by omega)), ← Nat.add_assoc]; exact graphAt_edge_snd hga hjlt
      have hmu_eq : mem (curGAddr + 2 + 2 * j) = u := graphAt_edge_fst hga hjlt
      have hmv_eq : mem (curGAddr + 3 + 2 * j) = v := graphAt_edge_snd hga hjlt
      have hpu_mem : st.mem (bufAddr + 3 * G.n + u) = mem (grpPartId bufAddr G.n + u) := by
        dsimp only [grpPartId]; exact hfr _ (Or.inl (by omega))
      have hpv_mem : st.mem (bufAddr + 3 * G.n + v) = mem (grpPartId bufAddr G.n + v) := by
        dsimp only [grpPartId]; exact hfr _ (Or.inl (by omega))
      have hpu_k : mem (grpPartId bufAddr G.n + u) < k := hpid u he_val.1
      have hpv_k : mem (grpPartId bufAddr G.n + v) < k := hpid v he_val.2
      refine runs_start_le ?_
      dsimp only [seqStmts]
      wram_step; simp only [hu_eq]
      wram_step; simp only [h0, h11, hv_eq]
      wram_step; simp only [h5, hpu_mem]
      wram_step; simp only [h5, hpv_mem]
      wram_step
      · -- true branch: `pu = pv`
        have hpeq : mem (grpPartId bufAddr G.n + u) = mem (grpPartId bufAddr G.n + v) := hcond
        have hcnt_pu : st.mem (bufAddr + 9 * G.n + 1 + mem (grpPartId bufAddr G.n + u)) =
            (edgeIdxBucket mem curGAddr bufAddr G.n (mem (grpPartId bufAddr G.n + u)) j).length :=
          hcnt _ hpu_k
        have hle_j := edgeIdxBucket_length_le mem curGAddr bufAddr G.n
          (mem (grpPartId bufAddr G.n + u)) j
        have hfc0 : grpEdgeCnt bufAddr G.n ≤ bufAddr + 9 * G.n + 1 + mem (grpPartId bufAddr G.n + u) := by
          dsimp only [grpEdgeCnt]; omega
        have hfc1 : bufAddr + 9 * G.n + 1 + mem (grpPartId bufAddr G.n + u) < grpEdgeOff bufAddr G.n := by
          dsimp only [grpEdgeOff]; omega
        wram_step; simp only [h7, hcnt_pu]
        wram_run
        · dsimp only [InvC, grpEdgeCnt, grpEdgeOff]
          simp only [h7]
          refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
            by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
            by simp, fun q hqk => ?_, ?_⟩, by simp [h11]⟩
          · rw [edgeIdxBucket_append, hmu_eq, hmv_eq, ← hpeq, List.length_append]
            by_cases hqu : mem (grpPartId bufAddr G.n + u) = q
            · subst q
              simp only [Function.update_self]
              simp
            · simp only [Function.update_of_ne (by omega :
                bufAddr + 9 * G.n + 1 + q ≠ bufAddr + 9 * G.n + 1 + mem (grpPartId bufAddr G.n + u))]
              have hne : (if mem (grpPartId bufAddr G.n + u) = q ∧
                  mem (grpPartId bufAddr G.n + u) = q then [j] else ([] : List ℕ)) = [] := by
                simp [hqu]
              rw [hne, List.length_nil, Nat.add_zero]
              exact hcnt q hqk
          · exact memFrame_trans hfr (memFrame_update hfc0 hfc1)
        · wram_cost
      · -- false branch: `pu ≠ pv`
        have hpne : mem (grpPartId bufAddr G.n + u) ≠ mem (grpPartId bufAddr G.n + v) := hcond
        wram_run
        · dsimp only [InvC, grpEdgeCnt, grpEdgeOff]
          refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
            by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
            by simp, fun q hqk => ?_, hfr⟩, by simp [h11]⟩
          · rw [edgeIdxBucket_append, hmu_eq, hmv_eq]
            have hne_p : ¬(mem (grpPartId bufAddr G.n + u) = q ∧
                mem (grpPartId bufAddr G.n + v) = q) := fun ⟨h1, h2⟩ => hpne (h1.trans h2.symm)
            have hne : (if mem (grpPartId bufAddr G.n + u) = q ∧
                mem (grpPartId bufAddr G.n + v) = q then [j] else ([] : List ℕ)) = [] := by
              simp [hne_p]
            rw [hne, List.append_nil]
            exact hcnt q hqk
        · wram_cost)
  refine (Triple.seq_normal hzero hcount
    (T := fun _ => 15 * G.n + 65 * G.m + 25) fun _ _ _ _ => by
    have hmul : k * 15 ≤ G.n * 15 := Nat.mul_le_mul_right 15 hkn
    simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero] at *; omega).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _, hcnt, hfr⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hcnt, hfr⟩

lemma groupEdgesPrefix_triple {w curGAddr k bufAddr n m : ℕ} (p : Program) (mem : ℕ → ℕ)
    (_hk : 1 ≤ k) (hkn : k ≤ n) (hbuf : bufAddr + groupBufSize n m + 2 < 2 ^ w)
    (hsum : ((List.range k).map fun q => mem (grpEdgeCnt bufAddr n + q)).sum ≤ m) :
    Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
        st.regs 3 = n ∧ st.regs 4 = m ∧
        st.regs 5 = grpPartId bufAddr n ∧ st.regs 6 = grpLocalId bufAddr n ∧
        st.regs 7 = grpEdgeCnt bufAddr n ∧ st.regs 8 = grpEdgeOff bufAddr n ∧
        st.regs 9 = grpEdgeCur bufAddr n ∧ st.regs 10 = grpPartEdges bufAddr n ∧
        st.mem = mem)
      groupEdgesPrefixStmt
      (normalPost fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
        st.regs 3 = n ∧ st.regs 4 = m ∧
        st.regs 5 = grpPartId bufAddr n ∧ st.regs 6 = grpLocalId bufAddr n ∧
        st.regs 7 = grpEdgeCnt bufAddr n ∧ st.regs 8 = grpEdgeOff bufAddr n ∧
        st.regs 9 = grpEdgeCur bufAddr n ∧ st.regs 10 = grpPartEdges bufAddr n ∧
        st.mem (grpEdgeOff bufAddr n) = 0 ∧
        st.mem (grpEdgeOff bufAddr n + k) ≤ m ∧
        (∀ q < k,
          st.mem (grpEdgeCur bufAddr n + q) = st.mem (grpEdgeOff bufAddr n + q) ∧
          st.mem (grpEdgeOff bufAddr n + (q + 1)) =
            st.mem (grpEdgeOff bufAddr n + q) + mem (grpEdgeCnt bufAddr n + q) ∧
          st.mem (grpEdgeOff bufAddr n + q) + mem (grpEdgeCnt bufAddr n + q) ≤ m) ∧
        MemFrame mem st.mem (grpEdgeOff bufAddr n) (grpPartEdges bufAddr n))
      (fun _ => 35 * n + 20) := by
  have hw2 : 1 < 2 ^ w := by dsimp only [groupBufSize] at hbuf; omega
  dsimp only [groupBufSize] at hbuf
  let Inv : ℕ → State → Prop := fun q st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
    st.regs 3 = n ∧ st.regs 4 = m ∧
    st.regs 5 = grpPartId bufAddr n ∧ st.regs 6 = grpLocalId bufAddr n ∧
    st.regs 7 = grpEdgeCnt bufAddr n ∧ st.regs 8 = grpEdgeOff bufAddr n ∧
    st.regs 9 = grpEdgeCur bufAddr n ∧ st.regs 10 = grpPartEdges bufAddr n ∧
    st.regs 11 = q ∧
    st.regs 12 = ((List.range q).map fun j => mem (grpEdgeCnt bufAddr n + j)).sum ∧
    st.mem (grpEdgeOff bufAddr n) = 0 ∧
    st.mem (grpEdgeOff bufAddr n + q) = st.regs 12 ∧
    (∀ j < q,
      st.mem (grpEdgeCur bufAddr n + j) = st.mem (grpEdgeOff bufAddr n + j) ∧
      st.mem (grpEdgeOff bufAddr n + (j + 1)) =
        st.mem (grpEdgeOff bufAddr n + j) + mem (grpEdgeCnt bufAddr n + j) ∧
      st.mem (grpEdgeOff bufAddr n + j) + mem (grpEdgeCnt bufAddr n + j) ≤ m) ∧
    MemFrame mem st.mem (grpEdgeOff bufAddr n) (grpPartEdges bufAddr n)
  let PreA := fun st : State =>
    st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
    st.regs 3 = n ∧ st.regs 4 = m ∧
    st.regs 5 = grpPartId bufAddr n ∧ st.regs 6 = grpLocalId bufAddr n ∧
    st.regs 7 = grpEdgeCnt bufAddr n ∧ st.regs 8 = grpEdgeOff bufAddr n ∧
    st.regs 9 = grpEdgeCur bufAddr n ∧ st.regs 10 = grpPartEdges bufAddr n ∧
    st.mem (grpEdgeOff bufAddr n) = 0 ∧
    MemFrame mem st.mem (grpEdgeOff bufAddr n) (grpPartEdges bufAddr n)
  let PreL := fun st : State =>
    st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
    st.regs 3 = n ∧ st.regs 4 = m ∧
    st.regs 5 = grpPartId bufAddr n ∧ st.regs 6 = grpLocalId bufAddr n ∧
    st.regs 7 = grpEdgeCnt bufAddr n ∧ st.regs 8 = grpEdgeOff bufAddr n ∧
    st.regs 9 = grpEdgeCur bufAddr n ∧ st.regs 10 = grpPartEdges bufAddr n ∧
    st.regs 12 = 0 ∧ st.mem (grpEdgeOff bufAddr n) = 0 ∧
    MemFrame mem st.mem (grpEdgeOff bufAddr n) (grpPartEdges bufAddr n)
  have hstore : Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
        st.regs 3 = n ∧ st.regs 4 = m ∧
        st.regs 5 = grpPartId bufAddr n ∧ st.regs 6 = grpLocalId bufAddr n ∧
        st.regs 7 = grpEdgeCnt bufAddr n ∧ st.regs 8 = grpEdgeOff bufAddr n ∧
        st.regs 9 = grpEdgeCur bufAddr n ∧ st.regs 10 = grpPartEdges bufAddr n ∧ st.mem = mem)
      (.store (.reg 8) (.const 0)) (normalPost PreA) (fun _ => 3) := by
    intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩
    have hlo : grpEdgeOff bufAddr n ≤ bufAddr + 10 * n + 1 := by dsimp only [grpEdgeOff]; omega
    have hhi : bufAddr + 10 * n + 1 < grpPartEdges bufAddr n := by dsimp only [grpPartEdges]; omega
    dsimp only [grpEdgeOff, grpPartEdges] at h8 ⊢
    refine runs_start_le ?_
    wram_run
    · dsimp only [PreA, grpEdgeOff]
      exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
        by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
        Function.update_self .., by subst hm; exact memFrame_update hlo hhi⟩
    · wram_cost
  have hassign : Triple w p PreA (.assign 12 (.const 0)) (normalPost PreL) (fun _ => 2) := by
    intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hz, hfr⟩
    refine runs_start_le ?_
    wram_run
    · exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
        by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
        by simp, hz, hfr⟩
    · wram_cost
  have hpref_sum_le : ∀ r ≤ k,
      ((List.range r).map fun j => mem (grpEdgeCnt bufAddr n + j)).sum ≤ m := by
    intro r hr
    have hsplit : List.range k = List.range r ++ (List.range (k - r)).map (fun x => r + x) := by
      have hrx : List.range (r + (k - r)) = List.range r ++ (List.range (k - r)).map (fun x => r + x) :=
        List.range_add
      rwa [show r + (k - r) = k by omega] at hrx
    have hsum' := hsum
    rw [hsplit, List.map_append, List.sum_append] at hsum'
    omega
  have hloop := Triple.forRange_const (p := p) (r := 11) (lo := .const 0) (hi := .reg 1)
    (body := seqStmts
      [ .assign 13 (.load (.bin .add (.reg 7) (.reg 11)))
      , .store (.bin .add (.reg 9) (.reg 11)) (.reg 12)
      , .assign 12 (.bin .add (.reg 12) (.reg 13))
      , .store (.bin .add (.reg 8) (.bin .add (.reg 11) (.const 1))) (.reg 12) ])
    (P := PreL) (Inv := Inv) 24 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h12, hz, hfr⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, by simp,
        by simp [h12], by simpa using hz, by simpa [h12] using hz, fun _ hj => by omega, hfr⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.1; eval_expr)
    (fun q _ hqlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hz, hqoff, hp, hfr⟩
      dsimp only [grpEdgeCnt, grpEdgeOff, grpEdgeCur, grpPartEdges] at h7 h8 h9 h10 hz hqoff hp hfr ⊢
      have hcnt_eq : st.mem (bufAddr + 9 * n + 1 + q) = mem (bufAddr + 9 * n + 1 + q) :=
        hfr _ (Or.inl (by omega))
      have hsum_q1 : ((List.range (q + 1)).map fun j => mem (grpEdgeCnt bufAddr n + j)).sum ≤ m :=
        hpref_sum_le (q + 1) hqlt
      have hsum_step : ((List.range (q + 1)).map fun j => mem (grpEdgeCnt bufAddr n + j)).sum =
          st.regs 12 + mem (grpEdgeCnt bufAddr n + q) := by
        rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton, h12]
      have h12_le : st.regs 12 + mem (grpEdgeCnt bufAddr n + q) ≤ m := by rw [← hsum_step]; exact hsum_q1
      dsimp only [grpEdgeCnt] at hsum_step h12_le
      have h8lo : grpEdgeOff bufAddr n ≤ bufAddr + 10 * n + 1 + (q + 1) := by
        dsimp only [grpEdgeOff]; omega
      have h8hi : bufAddr + 10 * n + 1 + (q + 1) < grpPartEdges bufAddr n := by
        dsimp only [grpPartEdges]; omega
      have h9lo : grpEdgeOff bufAddr n ≤ bufAddr + 11 * n + 2 + q := by
        dsimp only [grpEdgeOff]; omega
      have h9hi : bufAddr + 11 * n + 2 + q < grpPartEdges bufAddr n := by
        dsimp only [grpPartEdges]; omega
      refine runs_start_le ?_
      dsimp only [seqStmts]
      wram_run
      · dsimp only [Inv, grpEdgeCnt, grpEdgeOff, grpEdgeCur]
        simp only [h8, h9, h11, h12]
        refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
          by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
          by simp, ?_, ?_, ?_, fun j hj => ?_, ?_⟩, by simp [h11]⟩
        · dsimp only [grpEdgeCnt]; simp [hcnt_eq, List.range_succ]
        · simp only [Function.update_of_ne (by omega : bufAddr + 10 * n + 1 ≠ bufAddr + 10 * n + 1 + (q + 1)),
            Function.update_of_ne (by omega : bufAddr + 10 * n + 1 ≠ bufAddr + 11 * n + 2 + q)]
          exact hz
        · simp [hcnt_eq]
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj_eq
          · have hpj := hp j hj'
            have h1e : bufAddr + 11 * n + 2 + j ≠ bufAddr + 10 * n + 1 + (q + 1) := by omega
            have h2e : bufAddr + 11 * n + 2 + j ≠ bufAddr + 11 * n + 2 + q := by omega
            have h3e : bufAddr + 10 * n + 1 + j ≠ bufAddr + 10 * n + 1 + (q + 1) := by omega
            have h4e : bufAddr + 10 * n + 1 + j ≠ bufAddr + 11 * n + 2 + q := by omega
            have h5e : bufAddr + 10 * n + 1 + (j + 1) ≠ bufAddr + 10 * n + 1 + (q + 1) := by omega
            have h6e : bufAddr + 10 * n + 1 + (j + 1) ≠ bufAddr + 11 * n + 2 + q := by omega
            simpa [Function.update_of_ne h1e, Function.update_of_ne h2e,
              Function.update_of_ne h3e, Function.update_of_ne h4e,
              Function.update_of_ne h5e, Function.update_of_ne h6e] using hpj
          · subst j
            have hne1 : bufAddr + 11 * n + 2 + q ≠ bufAddr + 10 * n + 1 + (q + 1) := by omega
            have hne2 : bufAddr + 10 * n + 1 + q ≠ bufAddr + 10 * n + 1 + (q + 1) := by omega
            have hne3 : bufAddr + 10 * n + 1 + q ≠ bufAddr + 11 * n + 2 + q := by omega
            simp only [Function.update_of_ne hne1, Function.update_self,
              Function.update_of_ne hne2, Function.update_of_ne hne3, hqoff]
            exact ⟨h12.symm, by simp [h12, hcnt_eq], h12_le⟩
        · exact memFrame_trans hfr (memFrame_trans (memFrame_update h9lo h9hi) (memFrame_update h8lo h8hi))
      · wram_cost)
  have htail := Triple.seq_normal hassign hloop (T := fun _ => 35 * n + 15)
    (fun _ _ _ _ => by simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega)
  refine (Triple.seq_normal hstore htail (T := fun _ => 35 * n + 20)
    (fun _ _ _ _ => by omega)).conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _, h12, hz, hqoff, hp, hfr⟩
    have hk_le := hpref_sum_le k (le_refl k)
    refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hz, ?_, ?_, hfr⟩
    · rw [hqoff, h12]; exact hk_le
    · intro q hqk
      have hq := hp q hqk
      exact ⟨hq.1, hq.2.1, hq.2.2⟩

end MinCostFlow.Expander
