module

public import MinCostFlow.Expander.DecomposeGroupEdgesProg

import Mathlib.Tactic.Linarith

/-!
# Edge Grouping Scatter & Combined `groupEdges_spec`

Proves `groupEdgesScatter_triple` and combines the four stages of `groupEdgesProc` into
`groupEdges_spec`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma groupEdgesScatter_triple {w curGAddr k bufAddr : ℕ} (p : Program) (mem : ℕ → ℕ)
    (G : Cited.Graph) (hga : GraphAt mem curGAddr G) (hval : G.IsValid)
    (_hk : 1 ≤ k) (_hkn : k ≤ G.n)
    (hcur : curGAddr + 2 + 2 * G.m ≤ bufAddr)
    (hbuf : bufAddr + groupBufSize G.n G.m + 2 < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hpid : ∀ u < G.n, mem (grpPartId bufAddr G.n + u) < k)
    (hlid : ∀ u < G.n, mem (grpLocalId bufAddr G.n + u) < G.n)
    (hcnt : ∀ q < k, mem (grpEdgeCnt bufAddr G.n + q) =
      (edgeIdxBucket mem curGAddr bufAddr G.n q G.m).length)
    (hcur_init : ∀ q < k, mem (grpEdgeCur bufAddr G.n + q) = mem (grpEdgeOff bufAddr G.n + q))
    (hoff_step : ∀ q < k,
      mem (grpEdgeOff bufAddr G.n + (q + 1)) =
        mem (grpEdgeOff bufAddr G.n + q) + mem (grpEdgeCnt bufAddr G.n + q) ∧
      mem (grpEdgeOff bufAddr G.n + q) + mem (grpEdgeCnt bufAddr G.n + q) ≤ G.m) :
    Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
        st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
        st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
        st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
        st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
        st.mem = mem)
      groupEdgesScatterStmt
      (normalPost fun st =>
        (∀ q < k,
          let b := edgeIdxBucket mem curGAddr bufAddr G.n q G.m
          ∀ t (ht : t < b.length),
            st.mem (grpPartEdges bufAddr G.n + 2 * (mem (grpEdgeOff bufAddr G.n + q) + t)) =
              mem (grpLocalId bufAddr G.n + mem (curGAddr + 2 + 2 * b[t])) ∧
            st.mem (grpPartEdges bufAddr G.n + 2 * (mem (grpEdgeOff bufAddr G.n + q) + t) + 1) =
              mem (grpLocalId bufAddr G.n + mem (curGAddr + 3 + 2 * b[t]))) ∧
        MemFrame mem st.mem (grpEdgeCur bufAddr G.n) (bufAddr + groupBufSize G.n G.m))
      (fun _ => 100 * G.m + 10) := by
  dsimp only [groupBufSize] at hbuf ⊢
  have hw2 : 1 < 2 ^ w := by omega
  have hm_lt : G.m < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
    st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
    st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
    st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
    st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
    st.regs 11 = j ∧
    (∀ q < k,
      let b := edgeIdxBucket mem curGAddr bufAddr G.n q j
      st.mem (grpEdgeCur bufAddr G.n + q) = mem (grpEdgeOff bufAddr G.n + q) + b.length ∧
      ∀ t (ht : t < b.length),
        st.mem (grpPartEdges bufAddr G.n + 2 * (mem (grpEdgeOff bufAddr G.n + q) + t)) =
          mem (grpLocalId bufAddr G.n + mem (curGAddr + 2 + 2 * b[t])) ∧
        st.mem (grpPartEdges bufAddr G.n + 2 * (mem (grpEdgeOff bufAddr G.n + q) + t) + 1) =
          mem (grpLocalId bufAddr G.n + mem (curGAddr + 3 + 2 * b[t]))) ∧
    MemFrame mem st.mem (grpEdgeCur bufAddr G.n) (bufAddr + (12 * G.n + 2 * G.m + 2))
  let body := seqStmts
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
        .nop ]
  have hloop := Triple.forRange_const (p := p) (r := 11) (lo := .const 0) (hi := .reg 4)
    (body := body) (P := fun st =>
      st.regs 0 = curGAddr ∧ st.regs 1 = k ∧ st.regs 2 = bufAddr ∧
      st.regs 3 = G.n ∧ st.regs 4 = G.m ∧
      st.regs 5 = grpPartId bufAddr G.n ∧ st.regs 6 = grpLocalId bufAddr G.n ∧
      st.regs 7 = grpEdgeCnt bufAddr G.n ∧ st.regs 8 = grpEdgeOff bufAddr G.n ∧
      st.regs 9 = grpEdgeCur bufAddr G.n ∧ st.regs 10 = grpPartEdges bufAddr G.n ∧
      st.mem = mem)
    (Inv := Inv) 90 0 G.m (Nat.zero_le G.m) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩ => by
      refine ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, by simp, fun q hqk => ?_, ?_⟩
      · simp [edgeIdxBucket, hm, hcur_init q hqk]
      · simpa [hm] using memFrame_refl st.mem _ _)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.1; eval_expr)
    (fun j _ hjlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hinv, hfr⟩
      dsimp only [grpPartId, grpLocalId, grpEdgeOff, grpEdgeCur, grpPartEdges]
        at h5 h6 h8 h9 h10 hinv hfr ⊢
      have he_val := hval _ (List.getElem_mem hjlt)
      set u := (G.edges[j]'hjlt).1
      set v := (G.edges[j]'hjlt).2
      have hmu_eq : mem (curGAddr + 2 + 2 * j) = u := graphAt_edge_fst hga hjlt
      have hmv_eq : mem (curGAddr + 3 + 2 * j) = v := graphAt_edge_snd hga hjlt
      have hu_eq : st.mem (curGAddr + (2 + 2 * j)) = u := by
        rw [hfr _ (Or.inl (by omega)), ← Nat.add_assoc]; exact hmu_eq
      have hv_eq : st.mem (curGAddr + (3 + 2 * j)) = v := by
        rw [hfr _ (Or.inl (by omega)), ← Nat.add_assoc]; exact hmv_eq
      have hpu_mem : st.mem (bufAddr + 3 * G.n + u) = mem (grpPartId bufAddr G.n + u) := by
        dsimp only [grpPartId]; exact hfr _ (Or.inl (by omega))
      have hpv_mem : st.mem (bufAddr + 3 * G.n + v) = mem (grpPartId bufAddr G.n + v) := by
        dsimp only [grpPartId]; exact hfr _ (Or.inl (by omega))
      have hpu_k : mem (grpPartId bufAddr G.n + u) < k := hpid u he_val.1
      have hpv_k : mem (grpPartId bufAddr G.n + v) < k := hpid v he_val.2
      refine runs_start_le ?_
      dsimp only [body, seqStmts]
      wram_step; simp only [hu_eq]
      wram_step; simp only [h0, h11, hv_eq]
      wram_step; simp only [h5, hpu_mem]
      wram_step; simp only [h5, hpv_mem]
      wram_step
      · -- true branch: `pu = pv`
        set pu := mem (grpPartId bufAddr G.n + u)
        have hpu_def : mem (grpPartId bufAddr G.n + u) = pu := rfl
        have hpeq : pu = mem (grpPartId bufAddr G.n + v) := hcond
        have hlu_mem : st.mem (bufAddr + 8 * G.n + 1 + u) = mem (grpLocalId bufAddr G.n + u) := by
          dsimp only [grpLocalId]; exact hfr _ (Or.inl (by omega))
        have hlv_mem : st.mem (bufAddr + 8 * G.n + 1 + v) = mem (grpLocalId bufAddr G.n + v) := by
          dsimp only [grpLocalId]; exact hfr _ (Or.inl (by omega))
        have hinv_pu := hinv pu hpu_k
        have hcur_pu : st.mem (bufAddr + 11 * G.n + 2 + pu) =
            mem (bufAddr + 10 * G.n + 1 + pu) +
              (edgeIdxBucket mem curGAddr bufAddr G.n pu j).length :=
          hinv_pu.1
        have hsucc_le : (edgeIdxBucket mem curGAddr bufAddr G.n pu j).length + 1 ≤
            (edgeIdxBucket mem curGAddr bufAddr G.n pu G.m).length := by
          have hm := edgeIdxBucket_length_mono mem curGAddr bufAddr G.n pu (Nat.succ_le_of_lt hjlt)
          rw [edgeIdxBucket_append, hmu_eq, hmv_eq, ← hpeq, hpu_def] at hm
          simpa using hm
        have hcnt_pu : (edgeIdxBucket mem curGAddr bufAddr G.n pu G.m).length =
            mem (grpEdgeCnt bufAddr G.n + pu) := (hcnt pu hpu_k).symm
        have hoff_le : mem (grpEdgeOff bufAddr G.n + pu) + mem (grpEdgeCnt bufAddr G.n + pu) ≤ G.m :=
          (hoff_step pu hpu_k).2
        set pos0 := mem (bufAddr + 10 * G.n + 1 + pu) +
          (edgeIdxBucket mem curGAddr bufAddr G.n pu j).length
        have hpos0_lt : pos0 < G.m := by
          dsimp only [grpEdgeOff, grpEdgeCnt] at hoff_le hcnt_pu
          dsimp only [pos0]; omega
        have hlu_lt : mem (grpLocalId bufAddr G.n + u) < G.n := hlid u he_val.1
        have hlv_lt : mem (grpLocalId bufAddr G.n + v) < G.n := hlid v he_val.2
        have hf10 : grpEdgeCur bufAddr G.n ≤ bufAddr + 12 * G.n + 2 + 2 * pos0 := by
          dsimp only [grpEdgeCur]; omega
        have hf11 : bufAddr + 12 * G.n + 2 + 2 * pos0 < bufAddr + (12 * G.n + 2 * G.m + 2) := by omega
        have hf20 : grpEdgeCur bufAddr G.n ≤ bufAddr + 12 * G.n + 2 + 2 * pos0 + 1 := by
          dsimp only [grpEdgeCur]; omega
        have hf21 : bufAddr + 12 * G.n + 2 + 2 * pos0 + 1 < bufAddr + (12 * G.n + 2 * G.m + 2) := by
          omega
        have hf30 : grpEdgeCur bufAddr G.n ≤ bufAddr + 11 * G.n + 2 + pu := by
          dsimp only [grpEdgeCur]; omega
        have hf31 : bufAddr + 11 * G.n + 2 + pu < bufAddr + (12 * G.n + 2 * G.m + 2) := by omega
        wram_step; simp only [h6, hlu_mem]
        wram_step; simp only [h6, hlv_mem]
        wram_step; simp only [h9, hcur_pu]
        wram_run
        · dsimp only [Inv, grpEdgeOff, grpEdgeCur, grpPartEdges]
          simp only [h9, h10]
          refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
            by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
            by simp, fun q hqk => ?_, ?_⟩, by simp [h11]⟩
          · rw [edgeIdxBucket_append, hmu_eq, hmv_eq, ← hpeq, hpu_def]
            by_cases hqu : pu = q
            · subst q
              have hif : (if pu = pu ∧ pu = pu then [j] else ([] : List ℕ)) = [j] := by simp
              rw [hif]
              refine ⟨?_, fun t ht => ?_⟩
              · rw [List.length_append, List.length_singleton]
                have hne1 : bufAddr + 11 * G.n + 2 + pu ≠
                    bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) := by omega
                have hne2 : bufAddr + 11 * G.n + 2 + pu ≠
                    bufAddr + 12 * G.n + 2 + 2 * pos0 := by omega
                simp only [Function.update_self]
                dsimp only [pos0]; omega
              · rw [List.length_append, List.length_singleton] at ht
                rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
                · rw [List.getElem_append_left ht']
                  have hprev := hinv_pu.2 t ht'
                  have ha : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + pu) + t) ≠
                      bufAddr + 11 * G.n + 2 + pu := by omega
                  have hb : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + pu) + t) ≠
                      bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) := by omega
                  have hc : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + pu) + t) ≠
                      bufAddr + 12 * G.n + 2 + 2 * pos0 := by omega
                  have hd : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + pu) + t) + 1 ≠
                      bufAddr + 11 * G.n + 2 + pu := by omega
                  have he : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + pu) + t) + 1 ≠
                      bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) := by omega
                  have hf : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + pu) + t) + 1 ≠
                      bufAddr + 12 * G.n + 2 + 2 * pos0 := by omega
                  simpa [Function.update_of_ne ha, Function.update_of_ne hb, Function.update_of_ne hc,
                    Function.update_of_ne hd, Function.update_of_ne he, Function.update_of_ne hf] using hprev
                · simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
                    List.getElem_singleton, hmu_eq, hmv_eq]
                  have heq_pos : mem (bufAddr + 10 * G.n + 1 + pu) +
                      (edgeIdxBucket mem curGAddr bufAddr G.n pu j).length = pos0 := rfl
                  rw [heq_pos]
                  have hg1 : bufAddr + 12 * G.n + 2 + 2 * pos0 ≠ bufAddr + 11 * G.n + 2 + pu := by omega
                  have hg2 : bufAddr + 12 * G.n + 2 + 2 * pos0 ≠
                      bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) := by omega
                  have hg3 : bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) ≠
                      bufAddr + 11 * G.n + 2 + pu := by omega
                  have hg4 : bufAddr + 12 * G.n + 2 + 2 * pos0 + 1 =
                      bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) := by omega
                  rw [hg4]
                  simp only [Function.update_of_ne hg1, Function.update_of_ne hg2, Function.update_self,
                    Function.update_of_ne hg3]
                  try exact ⟨rfl, rfl⟩
                  try exact ⟨trivial, rfl⟩
                  try exact ⟨trivial, trivial⟩
            · have hif : (if pu = q ∧ pu = q then [j] else ([] : List ℕ)) = [] := by simp [hqu]
              rw [hif, List.append_nil]
              have hinv_q := hinv q hqk
              refine ⟨?_, fun t ht => ?_⟩
              · have ha : bufAddr + 11 * G.n + 2 + q ≠ bufAddr + 11 * G.n + 2 + pu := by omega
                have hb : bufAddr + 11 * G.n + 2 + q ≠ bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) := by omega
                have hc : bufAddr + 11 * G.n + 2 + q ≠ bufAddr + 12 * G.n + 2 + 2 * pos0 := by omega
                simpa [Function.update_of_ne ha, Function.update_of_ne hb, Function.update_of_ne hc]
                  using hinv_q.1
              · have hq_le_cnt : (edgeIdxBucket mem curGAddr bufAddr G.n q j).length ≤
                    mem (grpEdgeCnt bufAddr G.n + q) := by
                  rw [hcnt q hqk]
                  exact edgeIdxBucket_length_mono mem curGAddr bufAddr G.n q hjlt.le
                have hle2 : (edgeIdxBucket mem curGAddr bufAddr G.n pu j).length <
                    mem (grpEdgeCnt bufAddr G.n + pu) := by rw [← hcnt_pu]; exact hsucc_le
                have hne_off := edgeOff_disjoint_of_ne (fun x hx => (hoff_step x hx).1)
                  (t₁ := t) (t₂ := (edgeIdxBucket mem curGAddr bufAddr G.n pu j).length)
                  hqk hpu_k (Ne.symm hqu) (lt_of_lt_of_le ht hq_le_cnt) hle2
                dsimp only [grpEdgeOff] at hne_off
                have ha : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + q) + t) ≠
                    bufAddr + 11 * G.n + 2 + pu := by omega
                have hb : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + q) + t) ≠
                    bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) := by omega
                have hc : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + q) + t) ≠
                    bufAddr + 12 * G.n + 2 + 2 * pos0 := by omega
                have hd : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + q) + t) + 1 ≠
                    bufAddr + 11 * G.n + 2 + pu := by omega
                have he : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + q) + t) + 1 ≠
                    bufAddr + 12 * G.n + 2 + (2 * pos0 + 1) := by omega
                have hf : bufAddr + 12 * G.n + 2 + 2 * (mem (bufAddr + 10 * G.n + 1 + q) + t) + 1 ≠
                    bufAddr + 12 * G.n + 2 + 2 * pos0 := by omega
                simpa [Function.update_of_ne ha, Function.update_of_ne hb, Function.update_of_ne hc,
                  Function.update_of_ne hd, Function.update_of_ne he, Function.update_of_ne hf]
                  using hinv_q.2 t ht
          · exact memFrame_trans hfr (memFrame_trans (memFrame_update hf10 hf11)
              (memFrame_trans (memFrame_update hf20 hf21) (memFrame_update hf30 hf31)))
        · wram_cost
      · -- false branch: `pu ≠ pv`
        have hpne : mem (grpPartId bufAddr G.n + u) ≠ mem (grpPartId bufAddr G.n + v) := hcond
        wram_run
        · dsimp only [Inv, grpEdgeOff, grpEdgeCur, grpPartEdges]
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
            exact hinv q hqk
        · wram_cost)
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by
    simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hinv, hfr⟩
    exact ⟨fun q hqk t ht => (hinv q hqk).2 t ht, hfr⟩

theorem groupEdges_spec {w : ℕ} {p : Program} {b_ge : ℕ}
    (hp : p.procs[b_ge]? = some groupEdgesProc) :
    MeetsContract w p b_ge (groupEdgesContract w) := by
  refine meetsContract_of_runs hp ?_
  intro args mem pos ω _ hpre
  dsimp only [groupEdgesContract] at hpre
  rcases hpre with ⟨curGAddr, k, bufAddr, G, rfl, hk, hkn, hval, hga, hcur, hbuf, hw16, hpid, hlid⟩
  have hm_eq : mem (curGAddr + 1) = G.m := graphAt_m hga
  have hn_eq : mem curGAddr = G.n := graphAt_n hga
  have h1 := groupEdgesSetup_triple (w := w) (k := k) p mem pos G hga hcur hbuf hw16
  rcases h1 (startState [curGAddr, k, bufAddr] mem pos) ω rfl with ⟨o1, st1, t1, hr1, ho1, hc1⟩
  cases o1 with
  | returned _ => exact False.elim ho1
  | normal =>
    rcases ho1 with ⟨s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6, s1_7, s1_8, s1_9, s1_10, hm1⟩
    have h2 := groupEdgesCount_triple (w := w) (curGAddr := curGAddr) (k := k) (bufAddr := bufAddr)
      p mem G hk hkn hval hga hcur hbuf hw16 hpid
    rcases h2 st1 ω ⟨s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6, s1_7, s1_8, s1_9, s1_10, hm1⟩ with
      ⟨o2, st2, t2, hr2, ho2, hc2⟩
    cases o2 with
    | returned _ => exact False.elim ho2
    | normal =>
      rcases ho2 with ⟨s2_0, s2_1, s2_2, s2_3, s2_4, s2_5, s2_6, s2_7, s2_8, s2_9, s2_10, hcnt2, hfr2⟩
      have hga2 : GraphAt st2.mem curGAddr G :=
        GraphAt.of_agree_below (bound := bufAddr) hga
          (by rw [graph_encode_length]; omega) fun a ha =>
          hfr2 a (Or.inl (by dsimp only [grpEdgeCnt]; omega))
      have hsum2 : ((List.range k).map fun q => st2.mem (grpEdgeCnt bufAddr G.n + q)).sum ≤ G.m := by
        have heq : ∀ q ∈ List.range k, st2.mem (grpEdgeCnt bufAddr G.n + q) =
            (edgeIdxBucket mem curGAddr bufAddr G.n q G.m).length := fun q hq => by
          rw [hcnt2 q (List.mem_range.mp hq)]
        rw [List.map_congr_left heq]
        exact sum_edgeIdxBucket_le mem curGAddr bufAddr G.n k G.m
      have h3 := groupEdgesPrefix_triple (w := w) (curGAddr := curGAddr) (k := k)
        (bufAddr := bufAddr) (n := G.n) (m := G.m) p st2.mem hk hkn hbuf hsum2
      rcases h3 st2 ω ⟨s2_0, s2_1, s2_2, s2_3, s2_4, s2_5, s2_6, s2_7, s2_8, s2_9, s2_10, rfl⟩ with
        ⟨o3, st3, t3, hr3, ho3, hc3⟩
      cases o3 with
      | returned _ => exact False.elim ho3
      | normal =>
        rcases ho3 with ⟨s3_0, s3_1, s3_2, s3_3, s3_4, s3_5, s3_6, s3_7, s3_8, s3_9, s3_10,
          hz3, hmk3, hp3, hfr3⟩
        have hfr23 : MemFrame mem st3.mem (grpEdgeCnt bufAddr G.n)
            (bufAddr + groupBufSize G.n G.m) :=
          memFrame_trans
            (memFrame_mono hfr2 (le_refl _) (by
              dsimp only [grpEdgeOff, groupBufSize]; omega))
            (memFrame_mono hfr3 (by dsimp only [grpEdgeCnt, grpEdgeOff]; omega)
              (by dsimp only [grpPartEdges, groupBufSize]; omega))
        have hga3 : GraphAt st3.mem curGAddr G :=
          GraphAt.of_agree_below (bound := bufAddr) hga
            (by rw [graph_encode_length]; omega) fun a ha =>
            hfr23 a (Or.inl (by dsimp only [grpEdgeCnt]; omega))
        have hmem_low : ∀ a < grpEdgeCnt bufAddr G.n, st3.mem a = mem a := fun a ha =>
          hfr23 a (Or.inl ha)
        have hfst_eq : ∀ j < G.m, st3.mem (curGAddr + 2 + 2 * j) = mem (curGAddr + 2 + 2 * j) :=
          fun j hj => hmem_low _ (by dsimp only [grpEdgeCnt]; omega)
        have hsnd_eq : ∀ j < G.m, st3.mem (curGAddr + 3 + 2 * j) = mem (curGAddr + 3 + 2 * j) :=
          fun j hj => hmem_low _ (by dsimp only [grpEdgeCnt]; omega)
        have hpid_eq : ∀ u < G.n, st3.mem (grpPartId bufAddr G.n + u) = mem (grpPartId bufAddr G.n + u) :=
          fun u hu => hmem_low _ (by dsimp only [grpPartId, grpEdgeCnt]; omega)
        have hlid_eq : ∀ u < G.n, st3.mem (grpLocalId bufAddr G.n + u) = mem (grpLocalId bufAddr G.n + u) :=
          fun u hu => hmem_low _ (by dsimp only [grpLocalId, grpEdgeCnt]; omega)
        have hcnt3 : ∀ q < k, st3.mem (grpEdgeCnt bufAddr G.n + q) =
            (edgeIdxBucket st3.mem curGAddr bufAddr G.n q G.m).length := fun q hqk => by
          have hfr_cnt : st3.mem (grpEdgeCnt bufAddr G.n + q) = st2.mem (grpEdgeCnt bufAddr G.n + q) :=
            hfr3 _ (Or.inl (by dsimp only [grpEdgeCnt, grpEdgeOff]; omega))
          rw [hfr_cnt, hcnt2 q hqk]
          congr 1
          simp only [edgeIdxBucket]
          apply List.filter_congr
          intro j hj
          have hjlt := List.mem_range.mp hj
          have hev := hval _ (List.getElem_mem hjlt)
          have hu_lt : mem (curGAddr + 2 + 2 * j) < G.n := by
            rw [graphAt_edge_fst hga hjlt]; exact hev.1
          have hv_lt : mem (curGAddr + 3 + 2 * j) < G.n := by
            rw [graphAt_edge_snd hga hjlt]; exact hev.2
          rw [hfst_eq j hjlt, hsnd_eq j hjlt, hpid_eq _ hu_lt, hpid_eq _ hv_lt]
        have hpid3 : ∀ u < G.n, st3.mem (grpPartId bufAddr G.n + u) < k := fun u hu => by
          rw [hpid_eq u hu]; exact hpid u hu
        have hlid3 : ∀ u < G.n, st3.mem (grpLocalId bufAddr G.n + u) < G.n := fun u hu => by
          rw [hlid_eq u hu]; exact hlid u hu
        have h4 := groupEdgesScatter_triple (w := w) (curGAddr := curGAddr) (k := k)
          (bufAddr := bufAddr) p st3.mem G hga3 hval hk hkn hcur hbuf hw16 hpid3 hlid3 hcnt3
          (fun q hqk => (hp3 q hqk).1)
          (fun q hqk => by
            have hcnt_32 : st3.mem (grpEdgeCnt bufAddr G.n + q) =
                st2.mem (grpEdgeCnt bufAddr G.n + q) :=
              hfr3 _ (Or.inl (by dsimp only [grpEdgeCnt, grpEdgeOff]; omega))
            rw [hcnt_32]
            exact ⟨(hp3 q hqk).2.1, (hp3 q hqk).2.2⟩)
        rcases h4 st3 ω ⟨s3_0, s3_1, s3_2, s3_3, s3_4, s3_5, s3_6, s3_7, s3_8, s3_9, s3_10, rfl⟩ with
          ⟨o4, st4, t4, hr4, ho4, hc4⟩
        cases o4 with
        | returned _ => exact False.elim ho4
        | normal =>
          rcases ho4 with ⟨hscat4, hfr4⟩
          have hret : Runs w p ω (.ret (.const 0)) st4 (.returned 0) st4 2 :=
            runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
          have hseq4 : Runs w p ω (seqStmts [groupEdgesScatterStmt, .ret (.const 0)]) st3
              (.returned 0) st4 (t4 + 2 + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st4, t4, 2, hr4, hret, rfl⟩)
          have hseq3 : Runs w p ω
              (seqStmts [groupEdgesPrefixStmt, groupEdgesScatterStmt, .ret (.const 0)]) st2
              (.returned 0) st4 (t3 + (t4 + 2 + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st3, t3, _, hr3, hseq4, rfl⟩)
          have hseq2 : Runs w p ω
              (seqStmts [groupEdgesCountStmt, groupEdgesPrefixStmt,
                groupEdgesScatterStmt, .ret (.const 0)]) st1
              (.returned 0) st4 (t2 + (t3 + (t4 + 2 + 1) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st2, t2, _, hr2, hseq3, rfl⟩)
          have hfull : Runs w p ω groupEdgesProc (startState [curGAddr, k, bufAddr] mem pos)
              (.returned 0) st4 (t1 + (t2 + (t3 + (t4 + 2 + 1) + 1) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st1, t1, _, hr1, hseq2, rfl⟩)
          have hd0 : [curGAddr, k, bufAddr].getD 0 0 = curGAddr := rfl
          have hd1 : [curGAddr, k, bufAddr].getD 1 0 = k := rfl
          have hd2 : [curGAddr, k, bufAddr].getD 2 0 = bufAddr := rfl
          refine ⟨.returned 0, st4, t1 + (t2 + (t3 + (t4 + 2 + 1) + 1) + 1) + 1, hfull, ?_, ?_⟩
          · dsimp only [groupEdgesContract]
            rw [hd0, hd1, hd2, hn_eq, hm_eq]
            have hfr34 : MemFrame mem st4.mem (grpEdgeCnt bufAddr G.n)
                (bufAddr + groupBufSize G.n G.m) :=
              memFrame_trans hfr23 (memFrame_mono hfr4
                (by dsimp only [grpEdgeCnt, grpEdgeCur]; omega) (le_refl _))
            have hoff_eq : ∀ q ≤ k,
                st4.mem (grpEdgeOff bufAddr G.n + q) = st3.mem (grpEdgeOff bufAddr G.n + q) :=
              fun q hq => hfr4 _ (Or.inl (by dsimp only [grpEdgeOff, grpEdgeCur]; omega))
            have hcnt_eq : ∀ q < k,
                st4.mem (grpEdgeCnt bufAddr G.n + q) = st3.mem (grpEdgeCnt bufAddr G.n + q) :=
              fun q hq => hfr4 _ (Or.inl (by dsimp only [grpEdgeCnt, grpEdgeCur]; omega))
            refine ⟨by rw [hoff_eq 0 (Nat.zero_le k), hz3],
              by rw [hoff_eq k (le_refl k)]; exact hmk3, fun q hqk => ?_, fun q hqk => ?_, hfr34⟩
            · have hq3 := hp3 q hqk
              have hcnt_32 : st3.mem (grpEdgeCnt bufAddr G.n + q) =
                  st2.mem (grpEdgeCnt bufAddr G.n + q) :=
                hfr3 _ (Or.inl (by dsimp only [grpEdgeCnt, grpEdgeOff]; omega))
              rw [hoff_eq (q + 1) hqk, hoff_eq q hqk.le, hcnt_eq q hqk, hcnt_32]
              exact ⟨hq3.2.1, hq3.2.2⟩
            · have b_eq : ((List.range G.m).filter fun j =>
                  decide (mem (grpPartId bufAddr G.n + mem (curGAddr + 2 + 2 * j)) = q ∧
                    mem (grpPartId bufAddr G.n + mem (curGAddr + 3 + 2 * j)) = q)) =
                  edgeIdxBucket st3.mem curGAddr bufAddr G.n q G.m := by
                simp only [edgeIdxBucket]
                apply List.filter_congr
                intro j hj
                have hjlt := List.mem_range.mp hj
                have hev := hval _ (List.getElem_mem hjlt)
                have hu_lt : mem (curGAddr + 2 + 2 * j) < G.n := by
                  rw [graphAt_edge_fst hga hjlt]; exact hev.1
                have hv_lt : mem (curGAddr + 3 + 2 * j) < G.n := by
                  rw [graphAt_edge_snd hga hjlt]; exact hev.2
                rw [hfst_eq j hjlt, hsnd_eq j hjlt, hpid_eq _ hu_lt, hpid_eq _ hv_lt]
              rw [b_eq]
              refine ⟨by rw [hcnt_eq q hqk, hcnt3 q hqk, List.length_map], fun t ht => ?_⟩
              rw [List.length_map] at ht
              have hsc := hscat4 q hqk t ht
              rw [hoff_eq q hqk.le]
              have hb_mem : (edgeIdxBucket st3.mem curGAddr bufAddr G.n q G.m)[t]'ht ∈
                  edgeIdxBucket st3.mem curGAddr bufAddr G.n q G.m := List.getElem_mem ht
              have hbj_lt : (edgeIdxBucket st3.mem curGAddr bufAddr G.n q G.m)[t]'ht < G.m := by
                simp only [edgeIdxBucket, List.mem_filter, List.mem_range] at hb_mem; exact hb_mem.1
              have hev := hval _ (List.getElem_mem hbj_lt)
              have hu_lt : mem (curGAddr + 2 + 2 *
                  (edgeIdxBucket st3.mem curGAddr bufAddr G.n q G.m)[t]'ht) < G.n := by
                rw [graphAt_edge_fst hga hbj_lt]; exact hev.1
              have hv_lt : mem (curGAddr + 3 + 2 *
                  (edgeIdxBucket st3.mem curGAddr bufAddr G.n q G.m)[t]'ht) < G.n := by
                rw [graphAt_edge_snd hga hbj_lt]; exact hev.2
              simp only [List.getElem_map]
              rw [hfst_eq _ hbj_lt, hsnd_eq _ hbj_lt] at hsc
              rw [hlid_eq _ hu_lt, hlid_eq _ hv_lt] at hsc
              exact hsc
          · dsimp only [groupEdgesContract]
            rw [hd0, hn_eq, hm_eq]
            dsimp only at hc1 hc2 hc3 hc4
            omega

end MinCostFlow.Expander
