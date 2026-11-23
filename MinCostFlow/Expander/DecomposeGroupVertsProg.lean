module

public import MinCostFlow.Expander.DecomposeGroupVertsBase

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Vertex Grouping Scatter & Combined `groupVerts_spec`

Proves `groupVertsScatter_triple` and combines all stages from `DecomposeGroupVertsBase` with
`heapSort_spec`, `dedup_spec`, and `binSearch_spec` to establish `groupVerts_spec`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited

/-! ## 1. Pure Helpers for Scatter & Partition Bounds -/

private lemma bucketVerts_pairwise_lt (f : ℕ → ℕ) (p v : ℕ) :
    ((List.range v).filter fun u => decide (f u = p)).Pairwise (· < ·) :=
  List.Pairwise.filter _ (List.pairwise_lt_range)

private lemma bucketVerts_mem_iff (f : ℕ → ℕ) (p v u : ℕ) :
    u ∈ ((List.range v).filter fun x => decide (f x = p)) ↔ u < v ∧ f u = p := by
  simp [List.mem_filter, List.mem_range]

private lemma bucketVerts_length_mono (f : ℕ → ℕ) (p : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ((List.range a).filter fun u => decide (f u = p)).length ≤
      ((List.range b).filter fun u => decide (f u = p)).length := by
  have hs : List.range b = List.range a ++ (List.range (b - a)).map (fun x => a + x) := by
    have hr : List.range (a + (b - a)) = List.range a ++ (List.range (b - a)).map (fun x => a + x) :=
      List.range_add
    rwa [show a + (b - a) = b by omega] at hr
  rw [hs, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

private lemma bucketVerts_getElem_self (f : ℕ → ℕ) (p u : ℕ) (hf : f u = p) :
    ∀ v, u < v →
      ((List.range v).filter fun x => decide (f x = p))[(
        (List.range u).filter fun x => decide (f x = p)).length]? = some u := by
  intro v huv
  induction v with
  | zero => exact False.elim (Nat.not_lt_zero u huv)
  | succ v ih =>
    rw [bucketVerts_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp huv with huv' | rfl
    · have hlen : ((List.range u).filter fun x => decide (f x = p)).length <
          ((List.range v).filter fun x => decide (f x = p)).length := by
        have hstep : ((List.range (u + 1)).filter fun x => decide (f x = p)).length =
            ((List.range u).filter fun x => decide (f x = p)).length + 1 := by
          rw [bucketVerts_append, hf]; simp
        have hle := bucketVerts_length_mono f p (Nat.lt_iff_add_one_le.mp huv')
        omega
      rw [List.getElem?_append_left hlen]
      exact ih huv'
    · simp [hf]

private lemma partOff_mono {mem : ℕ → ℕ} {bufAddr n k : ℕ}
    (hoff_step : ∀ q < k, mem (grpPartOff bufAddr n + (q + 1)) =
      mem (grpPartOff bufAddr n + q) + mem (grpPartCnt bufAddr n + q)) :
    ∀ a b, a ≤ b → b ≤ k → mem (grpPartOff bufAddr n + a) ≤ mem (grpPartOff bufAddr n + b) := by
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

private lemma partOff_disjoint_of_ne {mem : ℕ → ℕ} {bufAddr n k : ℕ}
    (hoff_step : ∀ q < k, mem (grpPartOff bufAddr n + (q + 1)) =
      mem (grpPartOff bufAddr n + q) + mem (grpPartCnt bufAddr n + q))
    {q₁ q₂ t₁ t₂ : ℕ} (hq₁ : q₁ < k) (hq₂ : q₂ < k) (hne : q₁ ≠ q₂)
    (ht₁ : t₁ < mem (grpPartCnt bufAddr n + q₁)) (ht₂ : t₂ < mem (grpPartCnt bufAddr n + q₂)) :
    mem (grpPartOff bufAddr n + q₁) + t₁ ≠ mem (grpPartOff bufAddr n + q₂) + t₂ := by
  rcases Nat.lt_trichotomy q₁ q₂ with h12 | rfl | h21
  · have hs := hoff_step q₁ hq₁
    have hm := partOff_mono hoff_step (q₁ + 1) q₂ h12 (by omega)
    omega
  · exact absurd rfl hne
  · have hs := hoff_step q₂ hq₂
    have hm := partOff_mono hoff_step (q₂ + 1) q₁ h21 (by omega)
    omega

/-! ## 2. Scatter Stage Triple -/

lemma groupVertsScatter_triple {w n k lblAddr bufAddr : ℕ} (p : Program) (mem : ℕ → ℕ)
    (_hk : 1 ≤ k) (hkn : k ≤ n) (hb : bufAddr + 9 * n + 3 < 2 ^ w)
    (hpid : ∀ u < n, mem (grpPartId bufAddr n + u) < k)
    (hoff_step : ∀ q < k, mem (grpPartOff bufAddr n + (q + 1)) =
      mem (grpPartOff bufAddr n + q) + mem (grpPartCnt bufAddr n + q))
    (hoff_cur : ∀ q < k, mem (grpPartCur bufAddr n + q) = mem (grpPartOff bufAddr n + q) ∧
      mem (grpPartOff bufAddr n + q) + mem (grpPartCnt bufAddr n + q) ≤ n)
    (hcnt : ∀ q < k, mem (grpPartCnt bufAddr n + q) =
      ((List.range n).filter fun u => decide (mem (grpPartId bufAddr n + u) = q)).length) :
    Triple w p
      (fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        st.mem = mem)
      groupVertsScatterStmt
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        (∀ q < k,
          let cnt := mem (grpPartCnt bufAddr n + q)
          let off := mem (grpPartOff bufAddr n + q)
          let verts := tab cnt fun t => st.mem (grpPartVerts bufAddr n + off + t)
          verts.Pairwise (· < ·) ∧
          (∀ u, u ∈ verts ↔ u < n ∧ mem (grpPartId bufAddr n + u) = q)) ∧
        (∀ u < n,
          let q := mem (grpPartId bufAddr n + u)
          let off := mem (grpPartOff bufAddr n + q)
          let lid := st.mem (grpLocalId bufAddr n + u)
          lid < mem (grpPartCnt bufAddr n + q) ∧
          st.mem (grpPartVerts bufAddr n + off + lid) = u) ∧
        MemFrame mem st.mem (grpPartCur bufAddr n) (grpEdgeCnt bufAddr n))
      (fun _ => 50 * n + 10) := by
  have hw2 : 1 < 2 ^ w := by omega
  let partFn : ℕ → ℕ := fun u => mem (grpPartId bufAddr n + u)
  let bucket : ℕ → ℕ → List ℕ := fun q v => (List.range v).filter fun u => decide (partFn u = q)
  let Inv : ℕ → State → Prop := fun v st =>
    st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
    st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
    st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
    st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
    st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
    st.regs 12 = v ∧
    (∀ q < k, st.mem (grpPartCur bufAddr n + q) = mem (grpPartOff bufAddr n + q) + (bucket q v).length) ∧
    (∀ q < k, ∀ t (ht : t < (bucket q v).length),
      st.mem (grpPartVerts bufAddr n + mem (grpPartOff bufAddr n + q) + t) = (bucket q v)[t]) ∧
    (∀ u < v, st.mem (grpLocalId bufAddr n + u) = (bucket (partFn u) u).length) ∧
    MemFrame mem st.mem (grpPartCur bufAddr n) (grpEdgeCnt bufAddr n)
  have hloop := Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 0)
    (body := seqStmts
      [ .assign 13 (.load (.bin .add (.reg 6) (.reg 12)))
      , .assign 14 (.load (.bin .add (.reg 9) (.reg 13)))
      , .store (.bin .add (.reg 10) (.reg 14)) (.reg 12)
      , .assign 15 (.load (.bin .add (.reg 8) (.reg 13)))
      , .store (.bin .add (.reg 11) (.reg 12)) (.bin .sub (.reg 14) (.reg 15))
      , .store (.bin .add (.reg 9) (.reg 13)) (.bin .add (.reg 14) (.const 1)) ])
    (P := fun st =>
      st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
      st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
      st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
      st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
      st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
      st.mem = mem)
    (Inv := Inv)
    40 0 n (Nat.zero_le n) hw2 (fun _ => by omega)
    (fun st hP => by
      rcases hP with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩
      refine ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by simp, ?_, ?_,
        fun _ hu => by omega, ?_⟩
      · intro q hqk; simp [bucket, hm, (hoff_cur q hqk).1]
      · intro q _ t ht; simp [bucket] at ht
      · simp [hm, memFrame_refl])
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.1; eval_expr)
    (fun v _ hvlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hcur, hverts, hlid, hfr⟩
      dsimp only [grpPartId, grpPartCnt, grpPartOff, grpPartCur, grpPartVerts, grpLocalId,
        grpEdgeCnt] at h6 h7 h8 h9 h10 h11 hcur hverts hlid hfr ⊢
      set q0 := partFn v
      have hq0_k : q0 < k := hpid v hvlt
      have hcnt_q0 := hcnt q0 hq0_k
      have hlen_lt_cnt : (bucket q0 v).length < mem (bufAddr + 4 * n + q0) := by
        dsimp only [grpPartCnt] at hcnt_q0
        rw [hcnt_q0]
        have hsucc : (bucket q0 (v + 1)).length = (bucket q0 v).length + 1 := by
          simp [bucket, bucketVerts_append, q0]
        have hle := bucketVerts_length_mono partFn q0 (a := v + 1) (b := n) hvlt
        dsimp only [bucket, partFn, grpPartId] at hsucc hle ⊢
        omega
      have hbound_q0 := (hoff_cur q0 hq0_k).2
      dsimp only [grpPartOff, grpPartCnt] at hbound_q0
      have hcur_q0 : st.mem (bufAddr + 6 * n + 1 + q0) =
          mem (bufAddr + 5 * n + q0) + (bucket q0 v).length := hcur q0 hq0_k
      have hpid_eq : st.mem (bufAddr + 3 * n + v) = q0 := by
        dsimp only [partFn, grpPartId] at *
        exact hfr (bufAddr + 3 * n + v) (Or.inl (by omega))
      have hoff_eq : st.mem (bufAddr + 5 * n + q0) = mem (bufAddr + 5 * n + q0) :=
        hfr (bufAddr + 5 * n + q0) (Or.inl (by omega))
      have hpos0_lt : mem (bufAddr + 5 * n + q0) + (bucket q0 v).length < n := by omega
      have ha1_lo : bufAddr + 6 * n + 1 ≤
          bufAddr + 7 * n + 1 + (mem (bufAddr + 5 * n + q0) + (bucket q0 v).length) := by omega
      have ha1_hi : bufAddr + 7 * n + 1 + (mem (bufAddr + 5 * n + q0) + (bucket q0 v).length) <
          bufAddr + 9 * n + 1 := by omega
      have ha2_lo : bufAddr + 6 * n + 1 ≤ bufAddr + 8 * n + 1 + v := by omega
      have ha2_hi : bufAddr + 8 * n + 1 + v < bufAddr + 9 * n + 1 := by omega
      have ha3_lo : bufAddr + 6 * n + 1 ≤ bufAddr + 6 * n + 1 + q0 := by omega
      have ha3_hi : bufAddr + 6 * n + 1 + q0 < bufAddr + 9 * n + 1 := by omega
      refine runs_start_le ?_
      dsimp only [seqStmts]
      wram_step; simp only [hpid_eq]
      wram_step; simp only [h9, hcur_q0]
      wram_step; simp only [h10]
      wram_step
      dsimp only
      simp only [h8]
      simp only [Function.update_of_ne (by omega :
          bufAddr + 5 * n + q0 ≠ bufAddr + 7 * n + 1 + (mem (bufAddr + 5 * n + q0) + (bucket q0 v).length)),
        hoff_eq]
      wram_run
      · dsimp only [Inv, grpPartId, grpPartCnt, grpPartOff, grpPartCur, grpPartVerts, grpLocalId,
          grpEdgeCnt]
        simp only [h9, h11, h12]
        refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
          by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
          by simp [h11], by simp, fun q hqk => ?_, fun q hqk t ht => ?_, fun u hu => ?_, ?_⟩,
          by simp [h12]⟩
        · by_cases hqq0 : q = q0
          · subst q
            have hsucc : (bucket q0 (v + 1)).length = (bucket q0 v).length + 1 := by
              simp [bucket, bucketVerts_append, q0]
            simp only [Function.update_self]
            omega
          · have hne : bufAddr + 6 * n + 1 + q ≠ bufAddr + 6 * n + 1 + q0 := by omega
            have hne1 : bufAddr + 6 * n + 1 + q ≠ bufAddr + 8 * n + 1 + v := by omega
            have hne2 : bufAddr + 6 * n + 1 + q ≠
                bufAddr + 7 * n + 1 + (mem (bufAddr + 5 * n + q0) + (bucket q0 v).length) := by omega
            have hsame : (bucket q (v + 1)).length = (bucket q v).length := by
              simp [bucket, bucketVerts_append, show partFn v ≠ q by exact Ne.symm hqq0]
            simp only [Function.update_of_ne hne, Function.update_of_ne hne1, Function.update_of_ne hne2,
              hsame]
            exact hcur q hqk
        · by_cases hqq0 : q = q0
          · subst q
            have hsucc : bucket q0 (v + 1) = bucket q0 v ++ [v] := by
              simp [bucket, bucketVerts_append, q0]
            have ht' : t < (bucket q0 v).length + 1 := by simpa [hsucc] using ht
            have hm_lt_n : mem (bufAddr + 5 * n + q0) + t < n := by omega
            have hne_c : bufAddr + 7 * n + 1 + mem (bufAddr + 5 * n + q0) + t ≠
                bufAddr + 6 * n + 1 + q0 := by omega
            have hne_l : bufAddr + 7 * n + 1 + mem (bufAddr + 5 * n + q0) + t ≠
                bufAddr + 8 * n + 1 + v := by omega
            simp only [Function.update_of_ne hne_c, Function.update_of_ne hne_l]
            rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht_old | rfl
            · have hne_p : bufAddr + 7 * n + 1 + mem (bufAddr + 5 * n + q0) + t ≠
                  bufAddr + 7 * n + 1 + (mem (bufAddr + 5 * n + q0) + (bucket q0 v).length) := by omega
              simp only [Function.update_of_ne hne_p]
              rw [hverts q0 hq0_k t ht_old]
              simp only [hsucc, List.getElem_append_left ht_old]
            · have heq_p : bufAddr + 7 * n + 1 + mem (bufAddr + 5 * n + q0) + (bucket q0 v).length =
                  bufAddr + 7 * n + 1 + (mem (bufAddr + 5 * n + q0) + (bucket q0 v).length) := by omega
              simp only [heq_p, Function.update_self]
              simp only [hsucc, List.getElem_append_right (le_refl _), Nat.sub_self,
                List.getElem_singleton]
          · have hsame : bucket q (v + 1) = bucket q v := by
              simp [bucket, bucketVerts_append, show partFn v ≠ q by exact Ne.symm hqq0]
            have ht' : t < (bucket q v).length := by simpa [hsame] using ht
            have ht_cnt : t < mem (grpPartCnt bufAddr n + q) := by
              have hle := bucketVerts_length_mono partFn q (a := v) (b := n) (Nat.le_of_lt hvlt)
              have hcq := hcnt q hqk
              dsimp only [bucket, partFn, grpPartId, grpPartCnt] at ht' hle hcq ⊢
              omega
            have hdisj := partOff_disjoint_of_ne hoff_step hqk hq0_k hqq0 ht_cnt hlen_lt_cnt
            dsimp only [grpPartOff] at hdisj
            have hm_q_lt : mem (bufAddr + 5 * n + q) + t < n := by
              have := (hoff_cur q hqk).2; dsimp only [grpPartOff, grpPartCnt] at this ht_cnt ⊢; omega
            have hne1 : bufAddr + 7 * n + 1 + mem (bufAddr + 5 * n + q) + t ≠
                bufAddr + 6 * n + 1 + q0 := by omega
            have hne2 : bufAddr + 7 * n + 1 + mem (bufAddr + 5 * n + q) + t ≠
                bufAddr + 8 * n + 1 + v := by omega
            have hne3 : bufAddr + 7 * n + 1 + mem (bufAddr + 5 * n + q) + t ≠
                bufAddr + 7 * n + 1 + (mem (bufAddr + 5 * n + q0) + (bucket q0 v).length) := by omega
            simp only [Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_of_ne hne3]
            simpa [hsame] using hverts q hqk t ht'
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu' | hu_eq
          · have hne1 : bufAddr + 8 * n + 1 + u ≠ bufAddr + 6 * n + 1 + q0 := by omega
            have hne2 : bufAddr + 8 * n + 1 + u ≠ bufAddr + 8 * n + 1 + v := by omega
            have hne3 : bufAddr + 8 * n + 1 + u ≠
                bufAddr + 7 * n + 1 + (mem (bufAddr + 5 * n + q0) + (bucket q0 v).length) := by omega
            simp only [Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_of_ne hne3]
            exact hlid u hu'
          · subst u
            have hne1 : bufAddr + 8 * n + 1 + v ≠ bufAddr + 6 * n + 1 + q0 := by omega
            simp only [Function.update_of_ne hne1, Function.update_self]
            dsimp only [partFn, q0, grpPartId] at *
            omega
        · exact memFrame_trans hfr
            (memFrame_trans (memFrame_update ha1_lo ha1_hi)
              (memFrame_trans (memFrame_update ha2_lo ha2_hi) (memFrame_update ha3_lo ha3_hi)))
      · wram_cost)
  refine hloop.conseq (T' := fun _ => 50 * n + 10) (fun _ h => h) ?_
    (fun _ _ => by simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _, hcur, hverts, hlid, hfr⟩
    refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, hfr⟩
    · intro q hqk
      dsimp only
      have htab_eq : tab (mem (grpPartCnt bufAddr n + q))
          (fun t => st'.mem (grpPartVerts bufAddr n + mem (grpPartOff bufAddr n + q) + t)) =
          bucket q n := by
        have hlen : (bucket q n).length = mem (grpPartCnt bufAddr n + q) := (hcnt q hqk).symm
        refine List.ext_getElem (by simp [tab, hlen]) fun t ht1 ht2 => ?_
        simp only [tab, List.getElem_map, List.getElem_range]
        exact hverts q hqk t ht2
      rw [htab_eq]
      refine ⟨bucketVerts_pairwise_lt partFn q n, ?_⟩
      intro u
      exact bucketVerts_mem_iff partFn q n u
    · intro u hu
      have hqu : partFn u < k := hpid u hu
      have hlid_u := hlid u hu
      have hget := bucketVerts_getElem_self partFn (partFn u) u rfl n hu
      rcases List.getElem?_eq_some_iff.mp hget with ⟨hlt_len, hval_u⟩
      refine ⟨by rw [hlid_u, hcnt (partFn u) hqu]; exact hlt_len, ?_⟩
      rw [hlid_u]
      simpa [bucket, partFn, hval_u] using hverts (partFn u) hqu _ hlt_len

/-! ## 3. Combined `groupVerts_spec` -/

theorem groupVerts_spec {w : ℕ} {p : Program} {b_sort b_dedup b_bs b_gv : ℕ}
    (hp : p.procs[b_gv]? = some (groupVertsProc b_sort b_dedup b_bs))
    (hsort : MeetsContract w p b_sort (heapSortContract w))
    (hdedup : MeetsContract w p b_dedup (dedupContract w))
    (hbs : MeetsContract w p b_bs (binSearchContract w)) :
    MeetsContract w p b_gv (groupVertsContract w) := by
  refine meetsContract_of_runs hp ?_
  intro args mem pos ω _ hpre
  dsimp only [groupVertsContract] at hpre
  rcases hpre with ⟨n, lblAddr, bufAddr, label, rfl, hn, hlist, hlen, hmem_lt, hlb, hb, hw16⟩
  have hw4 : 4 ≤ 2 ^ w := by omega
  -- Stage 1: setup
  have h1 := groupVertsSetup_triple (w := w) (lblAddr := lblAddr) p mem pos hb
  -- Stage 2: copy
  have h2 := groupVertsCopy_triple (w := w) p (fun a => mem a) hmem_lt hlb hb
  have h12 : Triple w p (fun st => st = startState [n, lblAddr, bufAddr] mem pos)
      (seqStmts [groupVertsSetupStmt, groupVertsCopyStmt])
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        (∀ u < n,
          (st.mem (grpSameTwin bufAddr n + u) ≠ 0 ↔ mem (lblAddr + 2 * u) = mem (lblAddr + 2 * u + 1)) ∧
          st.mem (grpSortBuf bufAddr n + u) = mem (lblAddr + 2 * u) ∧
          st.mem (grpSortBuf bufAddr n + u) < 2 ^ w) ∧
        MemFrame mem st.mem bufAddr (bufAddr + 2 * n))
      (fun _ => 45 * n + 60) :=
    (Triple.seq_normal h1 h2 (T := fun _ => 45 * n + 60) fun _ _ _ _ => by omega).conseq
      (fun _ h => h) (fun o _ h => by cases o with | normal => exact h | returned _ => exact False.elim h) (fun _ _ => le_rfl)
  -- Execute setup + copy on `startState [n, lblAddr, bufAddr] mem pos`
  rcases h12 (startState [n, lblAddr, bufAddr] mem pos) ω rfl with
    ⟨o12, st2, c12, hr12, hpost12, hc12⟩
  cases o12 with
  | returned _ => exact False.elim hpost12
  | normal =>
    rcases hpost12 with ⟨r0, r1, r2, r4, r5, r6, r7, r8, r9, r10, r11, hcp, hfr2⟩
    -- Stage 3: `.call 12 b_sort [.reg 4, .reg 0]`
    have hwords3 : ∀ a ∈ [grpSortBuf bufAddr n, n], a < 2 ^ w := by
      intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> (try dsimp only [grpSortBuf]) <;> omega
    have hpre3 : (heapSortContract w).pre [grpSortBuf bufAddr n, n] st2.mem := by
      refine ⟨grpSortBuf bufAddr n, n, rfl, ?_, by omega, hw4, fun u hu => (hcp u hu).2.2⟩
      dsimp only [grpSortBuf]; omega
    rcases runs_call_of_meetsContract (r := 12) (args := [.reg 4, .reg 0])
      (vs := [grpSortBuf bufAddr n, n]) hsort
      (by simp [evalArgs, Expr.eval, r4, r0]) hwords3 hpre3 ω with
      ⟨st3', c3', v3', hrc3, hcpost3, h3r12, h3oth, hc3'⟩
    dsimp only [heapSortContract] at hcpost3
    rcases hcpost3 with ⟨_, hperm3, hsorted3, hlt3, hfr3⟩
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hperm3 hsorted3 hlt3 hfr3 hc3'
    have h3_regs : ∀ r, r ≠ 12 → st3'.regs r = st2.regs r := h3oth
    -- Stage 4: `.call 3 b_dedup [.reg 4, .reg 0, .reg 5]`
    have hwords4 : ∀ a ∈ [grpSortBuf bufAddr n, n, grpUniqLbl bufAddr n], a < 2 ^ w := by
      intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> (try dsimp only [grpSortBuf, grpUniqLbl]) <;> omega
    have hpre4 : (dedupContract w).pre [grpSortBuf bufAddr n, n, grpUniqLbl bufAddr n] st3'.mem := by
      refine ⟨grpSortBuf bufAddr n, n, grpUniqLbl bufAddr n, rfl, ?_, ?_, hw4, hlt3, hsorted3⟩
      · dsimp only [grpSortBuf, grpUniqLbl]; omega
      · dsimp only [grpUniqLbl]; omega
    rcases runs_call_of_meetsContract (r := 3) (args := [.reg 4, .reg 0, .reg 5])
      (vs := [grpSortBuf bufAddr n, n, grpUniqLbl bufAddr n]) hdedup
      (by simp [evalArgs, Expr.eval, h3_regs 4 (by decide), h3_regs 0 (by decide),
        h3_regs 5 (by decide), r4, r0, r5])
      hwords4 hpre4 ω with ⟨st4, c4, k, hrc4, hcpost4, h4r3, h4oth, hc4⟩
    dsimp only [dedupContract] at hcpost4
    rcases hcpost4 with ⟨hkn, huniq_nd, huniq_iff, huniq_lt, hfr4⟩
    simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hkn huniq_nd huniq_iff huniq_lt hfr4 hc4
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have h0 : k = 0 := by omega
      subst h0
      have hmem0 : mem (lblAddr + 2 * 0) ∈ tab n (fun i => st3'.mem (grpSortBuf bufAddr n + i)) := by
        rw [hperm3.mem_iff]
        simp only [tab, List.mem_map, List.mem_range]
        exact ⟨0, hn, (hcp 0 hn).2.1⟩
      have := (huniq_iff (mem (lblAddr + 2 * 0))).mpr hmem0
      simp [tab] at this
    have hlbl_mem : ∀ u < n, mem (lblAddr + 2 * u) ∈ tab k fun q => st4.mem (grpUniqLbl bufAddr n + q) := by
      intro u hu
      rw [huniq_iff, hperm3.mem_iff]
      simp only [tab, List.mem_map, List.mem_range]
      exact ⟨u, hu, (hcp u hu).2.1⟩
    have hlbl_eq4 : ∀ u < n, st4.mem (lblAddr + 2 * u) = mem (lblAddr + 2 * u) := by
      intro u hu
      have ha1 : st3'.mem (lblAddr + 2 * u) = st2.mem (lblAddr + 2 * u) :=
        hfr3 (lblAddr + 2 * u) (Or.inl (by dsimp only [grpSortBuf]; omega))
      have ha2 : st2.mem (lblAddr + 2 * u) = mem (lblAddr + 2 * u) :=
        hfr2 (lblAddr + 2 * u) (Or.inl (by omega))
      have ha3 : st4.mem (lblAddr + 2 * u) = st3'.mem (lblAddr + 2 * u) :=
        hfr4 (lblAddr + 2 * u) (Or.inl (by dsimp only [grpUniqLbl]; omega))
      rw [ha3, ha1, ha2]
    have hlbl_lt4 : ∀ u < n, st4.mem (lblAddr + 2 * u) < 2 ^ w := by
      intro u hu; rw [hlbl_eq4 u hu]; exact hmem_lt (2 * u) (by omega)
    -- Stages 5-7: count + prefix + scatter + `.ret (.reg 3)`
    have h4_regs : ∀ r, r ≠ 3 → r ≠ 12 → st4.regs r = st2.regs r := fun r hr3 hr12 =>
      (h4oth r hr3).trans (h3_regs r hr12)
    have h5 := groupVertsCount_triple (w := w) hbs st4.mem hn hk1 hkn hb huniq_nd huniq_lt
      (fun u hu => by rw [hlbl_eq4 u hu]; exact hlbl_mem u hu) hlbl_lt4 hlb
    have h5res := h5 st4 ω ⟨by rw [h4_regs 0 (by decide) (by decide), r0],
      by rw [h4_regs 1 (by decide) (by decide), r1],
      by rw [h4_regs 2 (by decide) (by decide), r2], h4r3,
      by rw [h4_regs 4 (by decide) (by decide), r4],
      by rw [h4_regs 5 (by decide) (by decide), r5],
      by rw [h4_regs 6 (by decide) (by decide), r6],
      by rw [h4_regs 7 (by decide) (by decide), r7],
      by rw [h4_regs 8 (by decide) (by decide), r8],
      by rw [h4_regs 9 (by decide) (by decide), r9],
      by rw [h4_regs 10 (by decide) (by decide), r10],
      by rw [h4_regs 11 (by decide) (by decide), r11], rfl⟩
    rcases h5res with ⟨o5, st5, c5, hr5, hpost5, hc5⟩
    cases o5 with
    | returned _ => exact False.elim hpost5
    | normal =>
      rcases hpost5 with ⟨s5_0, s5_1, s5_2, s5_3, s5_4, s5_5, s5_6, s5_7, s5_8, s5_9, s5_10, s5_11,
        hpid5, hcnt5, hfr5⟩
      have hcnt5_le : ∀ q < k, st5.mem (grpPartCnt bufAddr n + q) ≤ n := by
        intro q hqk
        rw [hcnt5 q hqk]
        exact le_trans (Finset.card_filter_le _ _) (by simp)
      have hsum5 : ((List.range k).map fun q => st5.mem (grpPartCnt bufAddr n + q)).sum = n := by
        have hm : ((List.range k).map fun q => st5.mem (grpPartCnt bufAddr n + q)) =
            ((List.range k).map fun q => ((Finset.range n).filter fun u =>
              (tab k fun j => st4.mem (grpUniqLbl bufAddr n + j)).idxOf (st4.mem (lblAddr + 2 * u)) = q).card) := by
          refine List.ext_getElem (by simp) fun q hq1 _ => ?_
          simp only [List.getElem_map, List.getElem_range]
          exact hcnt5 q (by simpa using hq1)
        rw [hm]
        exact sum_fibers_eq_n _ n k fun u hu => by
          have hmem : st4.mem (lblAddr + 2 * u) ∈ tab k fun j => st4.mem (grpUniqLbl bufAddr n + j) := by
            rw [hlbl_eq4 u hu]; exact hlbl_mem u hu
          have := List.idxOf_lt_length_iff.mpr hmem
          simpa [tab] using this
      have h6 := groupVertsPrefix_triple (w := w) (lblAddr := lblAddr) p st5.mem hk1 hkn hb hcnt5_le hsum5
      rcases h6 st5 ω ⟨s5_0, s5_1, s5_2, s5_3, s5_4, s5_5, s5_6, s5_7, s5_8, s5_9, s5_10, s5_11, rfl⟩ with
        ⟨o6, st6, c6, hr6, hpost6, hc6⟩
      cases o6 with
      | returned _ => exact False.elim hpost6
      | normal =>
        rcases hpost6 with ⟨s6_0, s6_1, s6_2, s6_3, s6_4, s6_5, s6_6, s6_7, s6_8, s6_9, s6_10, s6_11,
          hz6, hkn6, hcur6, hfr6⟩
        have hpid6 : ∀ u < n, st6.mem (grpPartId bufAddr n + u) < k := by
          intro u hu
          rw [hfr6 (grpPartId bufAddr n + u) (Or.inl (by dsimp only [grpPartId, grpPartOff]; omega))]
          exact (hpid5 u hu).2
        have hoff_step6 : ∀ q < k, st6.mem (grpPartOff bufAddr n + (q + 1)) =
            st6.mem (grpPartOff bufAddr n + q) + st6.mem (grpPartCnt bufAddr n + q) := by
          intro q hqk
          have heq := hfr6 (grpPartCnt bufAddr n + q) (Or.inl (by dsimp only [grpPartCnt, grpPartOff]; omega))
          rw [heq]; exact (hcur6 q hqk).2.1
        have hoff_cur6 : ∀ q < k, st6.mem (grpPartCur bufAddr n + q) = st6.mem (grpPartOff bufAddr n + q) ∧
            st6.mem (grpPartOff bufAddr n + q) + st6.mem (grpPartCnt bufAddr n + q) ≤ n := by
          intro q hqk
          have heq := hfr6 (grpPartCnt bufAddr n + q) (Or.inl (by dsimp only [grpPartCnt, grpPartOff]; omega))
          rw [heq]; exact ⟨(hcur6 q hqk).1, (hcur6 q hqk).2.2⟩
        have hcnt6 : ∀ q < k, st6.mem (grpPartCnt bufAddr n + q) =
            ((List.range n).filter fun u => decide (st6.mem (grpPartId bufAddr n + u) = q)).length := by
          intro q hqk
          rw [hfr6 (grpPartCnt bufAddr n + q) (Or.inl (by dsimp only [grpPartCnt, grpPartOff]; omega)),
            hcnt5 q hqk, ← bucketVerts_length_eq_card]
          congr 1
          refine List.filter_congr fun u hu => ?_
          have hu' : u < n := List.mem_range.mp hu
          have heq1 := hfr6 (grpPartId bufAddr n + u) (Or.inl (by dsimp only [grpPartId, grpPartOff]; omega))
          rw [heq1, (hpid5 u hu').1]
        have h7 := groupVertsScatter_triple (w := w) (lblAddr := lblAddr) p st6.mem hk1 hkn hb hpid6 hoff_step6 hoff_cur6 hcnt6
        rcases h7 st6 ω ⟨s6_0, s6_1, s6_2, s6_3, s6_4, s6_5, s6_6, s6_7, s6_8, s6_9, s6_10, s6_11, rfl⟩ with
          ⟨o7, st7, c7, hr7, hpost7, hc7⟩
        cases o7 with
        | returned _ => exact False.elim hpost7
        | normal =>
          rcases hpost7 with ⟨_, _, _, s7_3, _, _, _, _, _, _, _, _, hparts7, hlids7, hfr7⟩
          -- `.ret (.reg 3)`
          have hret : Runs w p ω (.ret (.reg 3)) st7 (.returned k) st7 2 :=
            runs_ret_iff.mpr ⟨k, by simp [Expr.eval, s7_3], rfl, rfl, by simp [Expr.size]⟩
          -- Compose the full execution along `groupVertsProc`
          have hfull : Runs w p ω (groupVertsProc b_sort b_dedup b_bs)
              (startState [n, lblAddr, bufAddr] mem pos) (.returned k) st7
              (c12 + (c3' + (c4 + (c5 + (c6 + (c7 + 2 + 1) + 1) + 1) + 1) + 1) + 1) := by
            have hseq7 : Runs w p ω (seqStmts [groupVertsScatterStmt, .ret (.reg 3)]) st6 (.returned k) st7
                (c7 + 2 + 1) :=
              runs_seq_iff.mpr (Or.inr ⟨st7, c7, 2, hr7, hret, rfl⟩)
            have hseq6 : Runs w p ω (seqStmts [groupVertsPrefixStmt, groupVertsScatterStmt, .ret (.reg 3)])
                st5 (.returned k) st7 (c6 + (c7 + 2 + 1) + 1) :=
              runs_seq_iff.mpr (Or.inr ⟨st6, c6, _, hr6, hseq7, rfl⟩)
            have hseq5 : Runs w p ω
                (seqStmts [groupVertsCountStmt b_bs, groupVertsPrefixStmt, groupVertsScatterStmt, .ret (.reg 3)])
                st4 (.returned k) st7 (c5 + (c6 + (c7 + 2 + 1) + 1) + 1) :=
              runs_seq_iff.mpr (Or.inr ⟨st5, c5, _, hr5, hseq6, rfl⟩)
            have hseq4 : Runs w p ω
                (seqStmts [.call 3 b_dedup [.reg 4, .reg 0, .reg 5], groupVertsCountStmt b_bs,
                  groupVertsPrefixStmt, groupVertsScatterStmt, .ret (.reg 3)])
                st3' (.returned k) st7 (c4 + (c5 + (c6 + (c7 + 2 + 1) + 1) + 1) + 1) :=
              runs_seq_iff.mpr (Or.inr ⟨st4, c4, _, hrc4, hseq5, rfl⟩)
            have hseq3 : Runs w p ω
                (seqStmts [.call 12 b_sort [.reg 4, .reg 0],
                  .call 3 b_dedup [.reg 4, .reg 0, .reg 5], groupVertsCountStmt b_bs,
                  groupVertsPrefixStmt, groupVertsScatterStmt, .ret (.reg 3)])
                st2 (.returned k) st7 (c3' + (c4 + (c5 + (c6 + (c7 + 2 + 1) + 1) + 1) + 1) + 1) :=
              runs_seq_iff.mpr (Or.inr ⟨st3', c3', _, hrc3, hseq4, rfl⟩)
            rcases runs_seq_iff.mp hr12 with ⟨_, _, _, hbad, _⟩ | ⟨st1, c1', c2', hr1', hr2', rfl⟩
            · simp at hbad
            · have h2toend : Runs w p ω
                  (seqStmts [groupVertsCopyStmt,
                    .call 12 b_sort [.reg 4, .reg 0],
                    .call 3 b_dedup [.reg 4, .reg 0, .reg 5], groupVertsCountStmt b_bs,
                    groupVertsPrefixStmt, groupVertsScatterStmt, .ret (.reg 3)])
                  st1 (.returned k) st7 (c2' + (c3' + (c4 + (c5 + (c6 + (c7 + 2 + 1) + 1) + 1) + 1) + 1) + 1) :=
                runs_seq_iff.mpr (Or.inr ⟨st2, c2', _, hr2', hseq3, rfl⟩)
              simpa [groupVertsProc, seqStmts, Nat.add_assoc] using
                runs_seq_iff.mpr (Or.inr ⟨st1, c1', _, hr1', h2toend, by omega⟩)
          refine ⟨.returned k, st7, _, hfull, ?_, ?_⟩
          · -- Prove `groupVertsContract.post`
            dsimp only [groupVertsContract]
            simp only [Outcome.value, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.getD_some]
            have hmem74 : ∀ a, a < bufAddr + 3 * n → st7.mem a = st4.mem a := by
              intro a ha
              rw [hfr7 a (Or.inl (by dsimp only [grpPartCur]; omega)),
                hfr6 a (Or.inl (by dsimp only [grpPartOff]; omega)),
                hfr5 a (Or.inl (by dsimp only [grpPartId]; omega))]
            have hmem75 : ∀ a, a < bufAddr + 5 * n → st7.mem a = st5.mem a := by
              intro a ha
              rw [hfr7 a (Or.inl (by dsimp only [grpPartCur]; omega)),
                hfr6 a (Or.inl (by dsimp only [grpPartOff]; omega))]
            have hmem76 : ∀ a, a < bufAddr + 6 * n + 1 → st7.mem a = st6.mem a := fun a ha =>
              hfr7 a (Or.inl (by dsimp only [grpPartCur]; omega))
            have huniq_eq : (tab k fun q => st7.mem (grpUniqLbl bufAddr n + q)) =
                tab k fun q => st4.mem (grpUniqLbl bufAddr n + q) := by
              refine List.ext_getElem (by simp [tab]) fun q hq _ => ?_
              simp only [tab, List.getElem_map, List.getElem_range]
              have hqk : q < k := by simpa [tab] using hq
              exact hmem74 _ (by dsimp only [grpUniqLbl]; omega)
            refine ⟨hk1, hkn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [huniq_eq]; exact huniq_nd
            · intro u hu
              have hsame : st7.mem (grpSameTwin bufAddr n + u) = st2.mem (grpSameTwin bufAddr n + u) := by
                rw [hmem74 _ (by dsimp only [grpSameTwin]; omega),
                  hfr4 _ (Or.inl (by dsimp only [grpSameTwin, grpUniqLbl]; omega)),
                  hfr3 _ (Or.inl (by dsimp only [grpSameTwin, grpSortBuf]; omega))]
              have hmem_uniq : mem (lblAddr + 2 * u) ∈ tab k fun q => st7.mem (grpUniqLbl bufAddr n + q) := by
                rw [huniq_eq]; exact hlbl_mem u hu
              have hpid_eq : st7.mem (grpPartId bufAddr n + u) = st5.mem (grpPartId bufAddr n + u) :=
                hmem75 _ (by dsimp only [grpPartId]; omega)
              refine ⟨by rw [hsame]; exact (hcp u hu).1, hmem_uniq, ?_, ?_⟩
              · rw [hpid_eq, (hpid5 u hu).1, huniq_eq, hlbl_eq4 u hu]
              · rw [hpid_eq]; exact (hpid5 u hu).2
            · intro p hp_in
              rw [huniq_eq] at hp_in
              have hp_s3 := (huniq_iff p).mp hp_in
              rw [hperm3.mem_iff] at hp_s3
              simp only [tab, List.mem_map, List.mem_range] at hp_s3
              rcases hp_s3 with ⟨u, hu, rfl⟩
              exact ⟨u, hu, (hcp u hu).2.1.symm⟩
            · rw [hmem76 _ (by dsimp only [grpPartOff]; omega)]; exact hz6
            · rw [hmem76 _ (by dsimp only [grpPartOff]; omega)]; exact hkn6
            · intro q hqk
              rw [hmem76 _ (by dsimp only [grpPartOff]; omega),
                hmem76 _ (by dsimp only [grpPartOff]; omega),
                hmem76 _ (by dsimp only [grpPartCnt]; omega)]
              exact hoff_step6 q hqk
            · intro q hqk
              have hc := hparts7 q hqk
              have hcnt_q : st7.mem (grpPartCnt bufAddr n + q) = st6.mem (grpPartCnt bufAddr n + q) :=
                hmem76 _ (by dsimp only [grpPartCnt]; omega)
              have hoff_q : st7.mem (grpPartOff bufAddr n + q) = st6.mem (grpPartOff bufAddr n + q) :=
                hmem76 _ (by dsimp only [grpPartOff]; omega)
              have hverts_eq : (tab (st7.mem (grpPartCnt bufAddr n + q))
                    fun t => st7.mem (grpPartVerts bufAddr n + st7.mem (grpPartOff bufAddr n + q) + t)) =
                  tab (st6.mem (grpPartCnt bufAddr n + q))
                    fun t => st7.mem (grpPartVerts bufAddr n + st6.mem (grpPartOff bufAddr n + q) + t) := by
                rw [hcnt_q, hoff_q]
              rw [hverts_eq]
              refine ⟨hc.1, by rw [hcnt_q, hoff_q]; exact (hoff_cur6 q hqk).2, fun u => ?_⟩
              rw [hc.2 u]
              refine ⟨fun ⟨hu, heq⟩ => ⟨hu, ?_⟩, fun ⟨hu, heq⟩ => ⟨hu, ?_⟩⟩
              · rwa [hmem75 _ (by dsimp only [grpPartId]; omega),
                  ← hfr6 (grpPartId bufAddr n + u) (Or.inl (by dsimp only [grpPartId, grpPartOff]; omega))]
              · rwa [hfr6 (grpPartId bufAddr n + u) (Or.inl (by dsimp only [grpPartId, grpPartOff]; omega)),
                  ← hmem75 (grpPartId bufAddr n + u) (by dsimp only [grpPartId]; omega)]
            · intro u hu
              have hu7 := hlids7 u hu
              have hpid_eq : st7.mem (grpPartId bufAddr n + u) = st6.mem (grpPartId bufAddr n + u) :=
                hmem76 _ (by dsimp only [grpPartId]; omega)
              have hcnt_eq : st7.mem (grpPartCnt bufAddr n + st6.mem (grpPartId bufAddr n + u)) =
                  st6.mem (grpPartCnt bufAddr n + st6.mem (grpPartId bufAddr n + u)) :=
                hmem76 _ (by dsimp only [grpPartCnt]; have := hpid6 u hu; omega)
              have hoff_eq : st7.mem (grpPartOff bufAddr n + st6.mem (grpPartId bufAddr n + u)) =
                  st6.mem (grpPartOff bufAddr n + st6.mem (grpPartId bufAddr n + u)) :=
                hmem76 _ (by dsimp only [grpPartOff]; have := hpid6 u hu; omega)
              simpa [hpid_eq, hcnt_eq, hoff_eq] using hu7
            · intro addr ha
              have ha_out : ∀ a b, bufAddr ≤ a → b ≤ bufAddr + 9 * n + 1 → addr < a ∨ b ≤ addr := by
                intro a b hab hbb
                rcases ha with h | h
                · left; omega
                · right; omega
              have h3eq := hfr3 addr (by dsimp only [grpSortBuf]; exact ha_out _ _ (by omega) (by omega))
              have h4eq := hfr4 addr (by dsimp only [grpUniqLbl]; exact ha_out _ _ (by omega) (by omega))
              have h5eq := hfr5 addr (by dsimp only [grpPartId, grpPartOff]; exact ha_out _ _ (by omega) (by omega))
              have h6eq := hfr6 addr (by dsimp only [grpPartOff, grpPartVerts]; exact ha_out _ _ (by omega) (by omega))
              have h7eq := hfr7 addr (by dsimp only [grpPartCur, grpEdgeCnt]; exact ha_out _ _ (by omega) (by omega))
              rw [h7eq, h6eq, h5eq, h4eq, h3eq]
              exact hfr2 addr (ha_out _ _ (by omega) (by omega))
          · -- Total cycle bound
            dsimp only [groupVertsContract]
            simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
            simp only [heapSortContract, dedupContract, List.getD, List.getElem?_cons_zero,
              List.getElem?_cons_succ, Option.getD_some, argsSize_cons, argsSize_nil,
              Expr.size_reg] at hc3' hc4
            dsimp only at hc12 hc6 hc7
            have hlog_n1 : Nat.log 2 (n + 2) ≤ 2 * Nat.log 2 (n + 2) + 1 := by omega
            have hmul_log : n * Nat.log 2 (n + 2) ≤ n * (2 * Nat.log 2 (n + 2) + 1) :=
              Nat.mul_le_mul_left n hlog_n1
            have hmul_1 : n ≤ n * (2 * Nat.log 2 (n + 2) + 1) := by
              conv_lhs => rw [← Nat.mul_one n]
              exact Nat.mul_le_mul_left n (by omega)
            have h1_mul : 35 * (n * Nat.log 2 (n + 2)) ≤ 35 * (n * (2 * Nat.log 2 (n + 2) + 1)) :=
              Nat.mul_le_mul_left 35 hmul_log
            have h2_mul : 310 * n ≤ 310 * (n * (2 * Nat.log 2 (n + 2) + 1)) :=
              Nat.mul_le_mul_left 310 hmul_1
            have hc5' : c5 ≤ 35 * (n * Nat.log 2 (n + 2)) + 145 * n + 40 := by
              have hc5_eq : n * (35 * (Nat.log 2 (n + 2) + 2) + 55) + 20 * n + 40 =
                  35 * (n * Nat.log 2 (n + 2)) + 145 * n + 40 := by ring
              dsimp only at hc5
              omega
            omega

end MinCostFlow.Expander
