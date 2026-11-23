module

public import MinCostFlow.Expander.PruningBucketBase

/-!
# O(1) Unlink Primitive for Pruning Level Buckets in WordRAM
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

theorem unlinkLvl_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (huN : u < cfg.G.n) (huR : s.inR u = true) (hhPos : 1 ≤ s.h u) :
    let ℓ := s.h u
    let n := cfg.G.n
    let m := cfg.G.m
    let H := cfg.H
    let lvlVolAddr := wLvlVol workAddr n m H
    let lvlHeadAddr := wLvlHead workAddr n m H
    let lvlNextAddr := wLvlNext workAddr n m H
    let lvlPrevAddr := wLvlPrev workAddr n m H
    Triple w p
      (fun st => st = st₀ ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st ∧
        st.regs prU = u)
      unlinkLvlStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 → r ≠ prSuf → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        BucketMemPreserved st₀.mem st'.mem workAddr n m H ℓ ∧
        st'.mem (lvlVolAddr + ℓ) = st₀.mem (lvlVolAddr + ℓ) - cfg.degX u ∧
        (∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
          DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (buckets ℓ') n (st'.mem (lvlHeadAddr + ℓ'))) ∧
        DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n ((buckets ℓ).erase u) n (st'.mem (lvlHeadAddr + ℓ)))
      (fun _ => 80) := by
  dsimp only
  intro st ω ⟨hst, hinv, hru⟩
  subst st
  set ℓ := s.h u
  set n := cfg.G.n
  set m := cfg.G.m
  set H := cfg.H
  set hAddr := wHArr workAddr n m H
  set degXAddr := wDegX workAddr n m H
  set lvlNextAddr := wLvlNext workAddr n m H
  set lvlPrevAddr := wLvlPrev workAddr n m H
  set lvlVolAddr := wLvlVol workAddr n m H
  set lvlHeadAddr := wLvlHead workAddr n m H
  have hℓH : ℓ < H := hinv.prune_inv.h_lt_H u huR
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have hval_pow : ∀ x, x ≤ 2 * m + n + H + 1 → x < 2 ^ w := fun x hx => by omega
  have hu_mem : u ∈ buckets ℓ := (hinv.buckets_mem ℓ hhPos hℓH u).mpr ⟨huN, huR, rfl⟩
  have hdl_ℓ := hinv.buckets_dl ℓ hhPos hℓH
  have hsplit := doublyLinked_split_vals hu_mem hdl_ℓ
  set prv := st₀.mem (lvlPrevAddr + u)
  set nxt := st₀.mem (lvlNextAddr + u)
  have hprv_le : prv ≤ n := by rcases hsplit.1 with h | h <;> omega
  have hnxt_le : nxt ≤ n := by rcases hsplit.2 with h | h <;> omega
  have hdeg_le : cfg.degX u ≤ 2 * m := hinv.degX_le_two_mul_m huN
  have hvol_le : st₀.mem (lvlVolAddr + ℓ) ≤ 2 * m := by
    rw [hinv.lvlVol_eq ℓ hhPos hℓH]
    exact hinv.volAtLevel_le_two_mul_m ℓ
  have hvol_sub_le : st₀.mem (lvlVolAddr + ℓ) - cfg.degX u ≤ 2 * m := by omega
  have hvol_sub_lt : st₀.mem (lvlVolAddr + ℓ) - cfg.degX u < 2 ^ w := hval_pow _ (by omega)
  have hh_lt : hAddr + u < 2 ^ w := hlt_pow _ (by dsimp [hAddr, wHArr]; omega)
  have hlv_lt : lvlVolAddr + ℓ < 2 ^ w := hlt_pow _ (by dsimp [lvlVolAddr, wLvlVol]; omega)
  have hdx_lt : degXAddr + u < 2 ^ w := hlt_pow _ (by dsimp [degXAddr, wDegX]; omega)
  have hlp_lt : lvlPrevAddr + u < 2 ^ w := hlt_pow _ (by dsimp [lvlPrevAddr, wLvlPrev]; omega)
  have hln_lt : lvlNextAddr + u < 2 ^ w := hlt_pow _ (by dsimp [lvlNextAddr, wLvlNext]; omega)
  have hhead_lt : lvlHeadAddr + ℓ < 2 ^ w := hlt_pow _ (by dsimp [lvlHeadAddr, wLvlHead]; omega)
  have hℓ_lt : ℓ < 2 ^ w := hval_pow _ (by omega)
  have hdeg_lt : cfg.degX u < 2 ^ w := hval_pow _ (by omega)
  have hvol_lt : st₀.mem (lvlVolAddr + ℓ) < 2 ^ w := hval_pow _ (by omega)
  have hprv_lt : prv < 2 ^ w := hval_pow _ (by omega)
  have hnxt_lt : nxt < 2 ^ w := hval_pow _ (by omega)
  have hu_lt : u < 2 ^ w := hval_pow _ (by omega)
  have hn_lt : n < 2 ^ w := hval_pow _ (by omega)
  have hHead_lt : lvlHeadAddr < 2 ^ w := hlt_pow _ (by dsimp [lvlHeadAddr, wLvlHead]; omega)
  have hVolBase_lt : lvlVolAddr < 2 ^ w := hlt_pow _ (by dsimp [lvlVolAddr, wLvlVol]; omega)
  have hNextBase_lt : lvlNextAddr < 2 ^ w := hlt_pow _ (by dsimp [lvlNextAddr, wLvlNext]; omega)
  have hPrevBase_lt : lvlPrevAddr < 2 ^ w := hlt_pow _ (by dsimp [lvlPrevAddr, wLvlPrev]; omega)
  have hm_h : st₀.mem (hAddr + u) = ℓ := hinv.h_eq u huN
  have hm_dx : st₀.mem (degXAddr + u) = cfg.degX u := hinv.degX_eq u huN
  refine runs_start_le ?_
  dsimp only [unlinkLvlStmt, seqStmts]
  -- 1. prTmp2 := h[u]
  apply runs_seq_assign_le
  · exact eval_load_add_regs hinv.reg_hArr hru hh_lt hm_h hℓ_lt
  -- 2. prTmp1 := lvlVol + prTmp2
  apply runs_seq_assign_le
  · exact eval_add_regs (by simp; exact hinv.reg_lvlVol) (by simp) hlv_lt
  -- 3. prTmp3 := mem[prTmp1]
  apply runs_seq_assign_le
  · simp only [Expr.eval, Function.update_self, Option.map_some]; rfl
  -- 4. prSuf := degX[u]
  apply runs_seq_assign_le
  · exact eval_load_add_regs (by simp; exact hinv.reg_degX) (by simp [hru])
      hdx_lt hm_dx hdeg_lt
  -- 5. store mem[prTmp1] := prTmp3 - prSuf
  apply runs_seq_store_le
  · exact eval_reg (by simp) hlv_lt
  · simp only [Expr.eval, Function.update_self, Function.update_of_ne (by decide : prTmp3 ≠ prSuf),
      WordRAM.BinOp.eval, hvol_sub_lt, ↓reduceIte]; rfl
  -- 6. prTmp3 := lvlPrev[u]
  have hne_prev : lvlVolAddr + ℓ ≠ lvlPrevAddr + u := by
    dsimp [lvlVolAddr, lvlPrevAddr, wLvlVol, wLvlPrev]; omega
  have hne_next : lvlVolAddr + ℓ ≠ lvlNextAddr + u := by
    dsimp [lvlVolAddr, lvlNextAddr, wLvlVol, wLvlNext]; omega
  apply runs_seq_assign_le
  · exact eval_load_add_regs (by simp; exact hinv.reg_lvlPrev) (by simp [hru]) hlp_lt
      (by simp [Function.update_of_ne hne_prev.symm]; rfl) hprv_lt
  -- 7. prSuf := lvlNext[u]
  apply runs_seq_assign_le
  · exact eval_load_add_regs (by simp; exact hinv.reg_lvlNext) (by simp [hru]) hln_lt
      (by simp [Function.update_of_ne hne_next.symm]; rfl) hnxt_lt
  -- Setup mem1 after store 5
  set mem1 := Function.update st₀.mem (lvlVolAddr + ℓ) (st₀.mem (lvlVolAddr + ℓ) - cfg.degX u)
  -- Build cond1 and cond2 sub-triples
  have hcond1 : Triple w p
      (fun st =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 → r ≠ prSuf → st.regs r = st₀.regs r) ∧
        st.regs prTmp2 = ℓ ∧ st.regs prTmp3 = prv ∧ st.regs prSuf = nxt ∧
        st.pos = st₀.pos ∧ st.mem = mem1)
      (.cond (.bin .eq (.reg prTmp3) (.reg prN))
        (.store (.bin .add (.reg prLvlHead) (.reg prTmp2)) (.reg prSuf))
        (.store (.bin .add (.reg prLvlNext) (.reg prTmp3)) (.reg prSuf)))
      (normalPost fun st =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 → r ≠ prSuf → st.regs r = st₀.regs r) ∧
        st.regs prTmp2 = ℓ ∧ st.regs prTmp3 = prv ∧ st.regs prSuf = nxt ∧
        st.pos = st₀.pos ∧
        st.mem = (if prv = n then Function.update mem1 (lvlHeadAddr + ℓ) nxt
                  else Function.update mem1 (lvlNextAddr + prv) nxt))
      (fun _ => 15) := by
    apply (Triple.cond_const (val := fun st => if st.regs prTmp3 = st.regs prN then 1 else 0)
      (c_t := 5) (c_f := 5)
      (fun st ⟨hr, _, h3, _, _, _⟩ => by
        have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_n
        have h0lt : 0 < 2 ^ w := by omega
        have h1lt : 1 < 2 ^ w := by omega
        simp only [Expr.eval, h3, hrn, WordRAM.BinOp.eval]
        by_cases hcmp : prv = n <;> simp [hcmp, h1lt, h0lt])
      ?_ ?_).mono_cost (fun _ _ => by simp [Expr.size])
    · apply Triple.store (addr := fun _ => lvlHeadAddr + ℓ) (val := fun _ => nxt)
        (fun st ⟨⟨hr, h2, _, _, _, _⟩, _⟩ => by
          have hrh : st.regs prLvlHead = lvlHeadAddr :=
            (hr prLvlHead (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_lvlHead
          exact eval_add_regs hrh h2 hhead_lt)
        (fun st ⟨⟨_, _, _, hs, _, _⟩, _⟩ => eval_reg hs hnxt_lt)
        (fun st ⟨⟨hr, h2, h3, hs, hp, hm⟩, hne⟩ => by
          have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_n
          have hpn : prv = n := by by_contra h'; rw [h3, hrn] at hne; simp [h'] at hne
          refine ⟨hr, h2, h3, hs, hp, ?_⟩
          simp only [hm, hpn, ↓reduceIte])
    · apply Triple.store (addr := fun _ => lvlNextAddr + prv) (val := fun _ => nxt)
        (fun st ⟨⟨hr, _, h3, _, _, _⟩, heq⟩ => by
          have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_n
          have hpn : prv < n := by
            by_contra h'
            have hpeq : prv = n := by omega
            simp only [h3, hrn, hpeq, ↓reduceIte] at heq
            exact Nat.one_ne_zero heq
          have hrln : st.regs prLvlNext = lvlNextAddr :=
            (hr prLvlNext (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_lvlNext
          exact eval_add_regs hrln h3 (hlt_pow _ (by dsimp [lvlNextAddr, wLvlNext]; omega)))
        (fun st ⟨⟨_, _, _, hs, _, _⟩, _⟩ => eval_reg hs hnxt_lt)
        (fun st ⟨⟨hr, h2, h3, hs, hp, hm⟩, heq⟩ => by
          have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_n
          have hpne : prv ≠ n := by
            intro hpeq
            simp only [h3, hrn, hpeq, ↓reduceIte] at heq
            exact Nat.one_ne_zero heq
          refine ⟨hr, h2, h3, hs, hp, ?_⟩
          simp only [hm, hpne, ↓reduceIte])
  set mem2 := if prv = n then Function.update mem1 (lvlHeadAddr + ℓ) nxt
              else Function.update mem1 (lvlNextAddr + prv) nxt
  have hcond2 : Triple w p
      (fun st =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 → r ≠ prSuf → st.regs r = st₀.regs r) ∧
        st.regs prTmp2 = ℓ ∧ st.regs prTmp3 = prv ∧ st.regs prSuf = nxt ∧
        st.pos = st₀.pos ∧ st.mem = mem2)
      (.cond (.bin .lt (.reg prSuf) (.reg prN))
        (.store (.bin .add (.reg prLvlPrev) (.reg prSuf)) (.reg prTmp3))
        .nop)
      (normalPost fun st =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 → r ≠ prSuf → st.regs r = st₀.regs r) ∧
        st.pos = st₀.pos ∧
        st.mem = (if nxt < n then Function.update mem2 (lvlPrevAddr + nxt) prv else mem2))
      (fun _ => 15) := by
    apply (Triple.cond_const (val := fun st => if st.regs prSuf < st.regs prN then 1 else 0)
      (c_t := 5) (c_f := 1)
      (fun st ⟨hr, _, _, hs, _, _⟩ => by
        have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_n
        have h0lt : 0 < 2 ^ w := by omega
        have h1lt : 1 < 2 ^ w := by omega
        simp only [Expr.eval, hs, hrn, WordRAM.BinOp.eval]
        by_cases hcmp : nxt < n <;> simp [hcmp, h1lt, h0lt])
      ?_ ?_).mono_cost (fun _ _ => by simp [Expr.size])
    · apply Triple.store (addr := fun _ => lvlPrevAddr + nxt) (val := fun _ => prv)
        (fun st ⟨⟨hr, _, _, hs, _, _⟩, hne⟩ => by
          have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_n
          have hnn : nxt < n := by
            by_contra h'; rw [hs, hrn] at hne; simp [h'] at hne
          have hrlp : st.regs prLvlPrev = lvlPrevAddr :=
            (hr prLvlPrev (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_lvlPrev
          exact eval_add_regs hrlp hs (hlt_pow _ (by dsimp [lvlPrevAddr, wLvlPrev]; omega)))
        (fun st ⟨⟨_, _, h3, _, _, _⟩, _⟩ => eval_reg h3 hprv_lt)
        (fun st ⟨⟨hr, _, _, hs, hp, hm⟩, hne⟩ => by
          have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_n
          have hnn : nxt < n := by
            by_contra h'; rw [hs, hrn] at hne; simp [h'] at hne
          refine ⟨hr, hp, ?_⟩
          simp only [hm, hnn, ↓reduceIte])
    · exact Triple.nop fun st ⟨⟨hr, _, _, hs, hp, hm⟩, heq⟩ => by
        have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide)).trans hinv.reg_n
        have hnot : ¬(nxt < n) := by
          intro hlt
          rw [hs, hrn] at heq
          simp [hlt] at heq
        refine ⟨hr, hp, ?_⟩
        simp only [hm, hnot, ↓reduceIte]
  -- 8. cond1 ;; cond2 via runs_seq_triple_le + hcond2.runs
  apply runs_seq_triple_le hcond1
  · refine ⟨fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], ?_, ?_, ?_, rfl, rfl⟩ <;> simp
  intro st2 ⟨hr2, h2_2, h3_2, hs_2, hp2, hm2⟩
  obtain ⟨o, st', c2, hrun2, hpost2, hc2⟩ :=
    hcond2.runs ω ⟨hr2, h2_2, h3_2, hs_2, hp2, hm2⟩
  cases o with
  | returned _ => exact absurd hpost2 (by simp [normalPost])
  | normal =>
      dsimp only [normalPost] at hpost2
      rcases hpost2 with ⟨hr', hp', hm'⟩
      refine ⟨.normal, st', c2, hrun2, ?_, by simp only [Expr.size] at *; omega⟩
      dsimp only [normalPost]
      have hbmp1 : BucketMemPreserved st₀.mem mem1 workAddr n m H ℓ := by
        refine ⟨memFrame_update_in (by dsimp only [lvlVolAddr, lvlNextAddr, wLvlVol, wLvlNext]; omega)
            (by dsimp only [lvlVolAddr, lvlHeadAddr, wLvlVol, wLvlHead]; omega),
          fun k _ hk2 => Function.update_of_ne (by dsimp only [lvlVolAddr, wLvlVol] at hk2 ⊢; omega) _ _,
          fun ℓ' _ hne => ⟨Function.update_of_ne (by omega) _ _,
            Function.update_of_ne (by dsimp only [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol]; omega) _ _⟩⟩
      have hbmp2 : BucketMemPreserved mem1 mem2 workAddr n m H ℓ := by
        dsimp only [mem2]
        split_ifs with hpn
        · refine ⟨memFrame_update_in (by dsimp only [lvlHeadAddr, lvlNextAddr, wLvlHead, wLvlNext]; omega)
              (by dsimp only [lvlHeadAddr, wLvlHead]; omega),
            fun k _ hk2 => Function.update_of_ne (by dsimp only [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol] at hk2 ⊢; omega) _ _,
            fun ℓ' _ hne => ⟨Function.update_of_ne (by dsimp only [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol]; omega) _ _,
              Function.update_of_ne (by omega) _ _⟩⟩
        · have hpn' : prv < n := by omega
          refine ⟨memFrame_update_in (by dsimp only [lvlNextAddr, wLvlNext]; omega)
              (by dsimp only [lvlNextAddr, lvlHeadAddr, wLvlNext, wLvlHead]; omega),
            fun k hk1 _ => Function.update_of_ne (by dsimp only [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev] at hk1 ⊢; omega) _ _,
            fun ℓ' _ _ => ⟨Function.update_of_ne (by dsimp only [lvlVolAddr, lvlNextAddr, wLvlVol, wLvlNext]; omega) _ _,
              Function.update_of_ne (by dsimp only [lvlHeadAddr, lvlNextAddr, wLvlHead, wLvlNext]; omega) _ _⟩⟩
      have hbmp3 : BucketMemPreserved mem2 st'.mem workAddr n m H ℓ := by
        rw [hm']
        split_ifs with hnn
        · refine ⟨memFrame_update_in (by dsimp only [lvlPrevAddr, lvlNextAddr, wLvlPrev, wLvlNext]; omega)
              (by dsimp only [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega),
            fun k hk1 _ => Function.update_of_ne (by dsimp only [lvlPrevAddr, wLvlPrev] at hk1 ⊢; omega) _ _,
            fun ℓ' _ _ => ⟨Function.update_of_ne (by dsimp only [lvlVolAddr, lvlPrevAddr, wLvlVol, wLvlPrev]; omega) _ _,
              Function.update_of_ne (by dsimp only [lvlHeadAddr, lvlPrevAddr, wLvlHead, wLvlPrev]; omega) _ _⟩⟩
        · exact bucketMemPreserved_refl mem2 workAddr n m H ℓ
      have hbmp : BucketMemPreserved st₀.mem st'.mem workAddr n m H ℓ :=
        bucketMemPreserved_trans hbmp1 (bucketMemPreserved_trans hbmp2 hbmp3)
      have hvol_final : st'.mem (lvlVolAddr + ℓ) = st₀.mem (lvlVolAddr + ℓ) - cfg.degX u := by
        rw [hm']
        have h1' : lvlVolAddr + ℓ ≠ lvlPrevAddr + nxt := by
          dsimp [lvlVolAddr, lvlPrevAddr, wLvlVol, wLvlPrev]; omega
        have h2' : mem2 (lvlVolAddr + ℓ) = mem1 (lvlVolAddr + ℓ) := by
          dsimp only [mem2]
          split_ifs
          · exact Function.update_of_ne (by dsimp [lvlVolAddr, lvlHeadAddr, wLvlVol, wLvlHead]; omega) _ _
          · exact Function.update_of_ne (by dsimp [lvlVolAddr, lvlNextAddr, wLvlVol, wLvlNext]; omega) _ _
        split_ifs
        · rw [Function.update_of_ne h1', h2']; simp [mem1]
        · rw [h2']; simp [mem1]
      have hhead_ℓ : st'.mem (lvlHeadAddr + ℓ) =
          if st₀.mem (lvlPrevAddr + u) = n then st₀.mem (lvlNextAddr + u)
          else st₀.mem (lvlHeadAddr + ℓ) := by
        rw [hm']
        have hne_lp : lvlHeadAddr + ℓ ≠ lvlPrevAddr + nxt := by
          dsimp [lvlHeadAddr, lvlPrevAddr, wLvlHead, wLvlPrev]; omega
        have hpost_lp : ∀ (f : ℕ → ℕ), (if nxt < n then Function.update f (lvlPrevAddr + nxt) prv else f) (lvlHeadAddr + ℓ) =
            f (lvlHeadAddr + ℓ) := fun f => by
          split_ifs
          · exact Function.update_of_ne hne_lp _ _
          · rfl
        rw [hpost_lp]
        dsimp only [mem2, prv, nxt]
        split_ifs with hpn
        · simp
        · rw [Function.update_of_ne (by dsimp [lvlHeadAddr, lvlNextAddr, wLvlHead, wLvlNext]; omega)]
          exact Function.update_of_ne (by dsimp [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol]; omega) _ _
      have hdl_other : ∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
          DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (buckets ℓ') n (st'.mem (lvlHeadAddr + ℓ')) := by
        intro ℓ' h1 h2 hne
        rw [(hbmp.2.2 ℓ' (by omega) hne).2]
        apply doublyLinked_congr_disjoint _ _ (hinv.buckets_dl ℓ' h1 h2)
        · intro y hy
          change st'.mem (lvlNextAddr + y) = st₀.mem (lvlNextAddr + y)
          have hy_lt : y < n := doublyLinked_mem_lt (hinv.buckets_dl ℓ' h1 h2) hy
          have hy_ne_prv : y ≠ prv := by
            intro heq
            rcases hsplit.1 with hpn | _
            · omega
            · have hp_mem : prv ∈ buckets ℓ := by
                rcases List.append_of_mem hu_mem with ⟨l1, l2, hl⟩
                have hs := doublyLinked_append_split l1 l2 u n (st₀.mem (lvlHeadAddr + ℓ)) (hl ▸ hdl_ℓ)
                cases l1 with
                | nil => have := (hs.2.1 rfl).2; change prv = n at this; omega
                | cons a as =>
                    rcases hs.2.2.1 (List.cons_ne_nil a as) with ⟨p, hp, _, hp2⟩
                    change prv = p at hp2
                    rw [hp2, hl]
                    exact List.mem_append_left _ hp
              have hpy := ((hinv.buckets_mem ℓ hhPos hℓH prv).mp hp_mem).2.2
              have hyy := ((hinv.buckets_mem ℓ' h1 h2 y).mp hy).2.2
              exact hne (by rw [← hyy, heq, hpy])
          rw [hm']
          have hf1 : ∀ (f : ℕ → ℕ), (if nxt < n then Function.update f (lvlPrevAddr + nxt) prv else f) (lvlNextAddr + y) =
              f (lvlNextAddr + y) := fun f => by
            split_ifs
            · exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev]; omega) _ _
            · rfl
          rw [hf1]
          dsimp only [mem2]
          split_ifs
          · rw [Function.update_of_ne (by dsimp [lvlNextAddr, lvlHeadAddr, wLvlNext, wLvlHead]; omega)]
            exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlVolAddr, wLvlNext, wLvlVol]; omega) _ _
          · rw [Function.update_of_ne (by omega)]
            exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlVolAddr, wLvlNext, wLvlVol]; omega) _ _
        · intro y hy
          change st'.mem (lvlPrevAddr + y) = st₀.mem (lvlPrevAddr + y)
          have hy_lt : y < n := doublyLinked_mem_lt (hinv.buckets_dl ℓ' h1 h2) hy
          have hy_ne_nxt : y ≠ nxt := by
            intro heq
            rcases hsplit.2 with hnn | _
            · omega
            · have hn_mem : nxt ∈ buckets ℓ := by
                rcases List.append_of_mem hu_mem with ⟨l1, l2, hl⟩
                have hs := doublyLinked_append_split l1 l2 u n (st₀.mem (lvlHeadAddr + ℓ)) (hl ▸ hdl_ℓ)
                cases l2 with
                | nil => have := hs.2.2.2; change nxt = n at this; omega
                | cons b bs =>
                    have := hs.2.2.2.1
                    change nxt = b at this
                    rw [this, hl]
                    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hny := ((hinv.buckets_mem ℓ hhPos hℓH nxt).mp hn_mem).2.2
              have hyy := ((hinv.buckets_mem ℓ' h1 h2 y).mp hy).2.2
              exact hne (by rw [← hyy, heq, hny])
          rw [hm']
          have hf1 : ∀ (f : ℕ → ℕ), (if nxt < n then Function.update f (lvlPrevAddr + nxt) prv else f) (lvlPrevAddr + y) =
              f (lvlPrevAddr + y) := fun f => by
            split_ifs
            · exact Function.update_of_ne (by omega) _ _
            · rfl
          rw [hf1]
          dsimp only [mem2]
          split_ifs
          · rw [Function.update_of_ne (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega)]
            exact Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega) _ _
          · rw [Function.update_of_ne (by dsimp [lvlPrevAddr, lvlNextAddr, wLvlPrev, wLvlNext]; omega)]
            exact Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega) _ _
      have hdl_erase : DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n ((buckets ℓ).erase u) n
          (st'.mem (lvlHeadAddr + ℓ)) := by
        apply doublyLinked_erase (hinv.buckets_nodup ℓ hhPos hℓH) hu_mem hdl_ℓ hhead_ℓ
        · intro y hy
          change st'.mem (lvlNextAddr + y) = if y = prv then nxt else st₀.mem (lvlNextAddr + y)
          have hy_lt : y < n := doublyLinked_mem_lt hdl_ℓ (List.mem_of_mem_erase hy)
          rw [hm']
          have hf1 : ∀ (f : ℕ → ℕ), (if nxt < n then Function.update f (lvlPrevAddr + nxt) prv else f) (lvlNextAddr + y) =
              f (lvlNextAddr + y) := fun f => by
            split_ifs
            · exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev]; omega) _ _
            · rfl
          rw [hf1]
          dsimp only [mem2]
          by_cases hpn : prv = n <;> by_cases hyp : y = prv
          · exfalso; omega
          · have hy_ne_n : y ≠ n := by omega
            simp only [hpn, hy_ne_n, ↓reduceIte]
            rw [Function.update_of_ne (by dsimp [lvlNextAddr, lvlHeadAddr, wLvlNext, wLvlHead]; omega)]
            exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlVolAddr, wLvlNext, wLvlVol]; omega) _ _
          · simp [hpn, hyp]
          · simp only [hpn, hyp, ↓reduceIte]
            rw [Function.update_of_ne (by omega)]
            exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlVolAddr, wLvlNext, wLvlVol]; omega) _ _
        · intro y hy
          change st'.mem (lvlPrevAddr + y) = if y = nxt then prv else st₀.mem (lvlPrevAddr + y)
          have hy_lt : y < n := doublyLinked_mem_lt hdl_ℓ (List.mem_of_mem_erase hy)
          have hmem2_prev : mem2 (lvlPrevAddr + y) = st₀.mem (lvlPrevAddr + y) := by
            dsimp only [mem2]
            split_ifs
            · rw [Function.update_of_ne (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega)]
              exact Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega) _ _
            · rw [Function.update_of_ne (by dsimp [lvlPrevAddr, lvlNextAddr, wLvlPrev, wLvlNext]; omega)]
              exact Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega) _ _
          rw [hm']
          by_cases hnn : nxt < n <;> by_cases hyn : y = nxt
          · simp [hnn, hyn]
          · simp [hnn, hyn, hmem2_prev]
          · exfalso; rcases hsplit.2 with h | h <;> omega
          · simp [hnn, hyn, hmem2_prev]
      exact ⟨hr', hp', hbmp, hvol_final, hdl_other, hdl_erase⟩


end MinCostFlow.Expander
