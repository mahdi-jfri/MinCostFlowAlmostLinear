module

public import MinCostFlow.Expander.PruningUnlinkProg

/-!
# O(1) Link Primitive for Pruning Level Buckets in WordRAM
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

theorem linkLvl_triple_raw {w : ℕ} {p : Program}
    {n m C_cap H workAddr u ℓ : ℕ} (degXu : ℕ) (L : List ℕ) (bucketsOther : ℕ → List ℕ)
    (st₀ : State)
    (hw : PruneWordBound w n m C_cap H workAddr) (hC4 : 4 ≤ C_cap)
    (huN : u < n) (hℓ1 : 1 ≤ ℓ) (hℓH : ℓ < H) (hL_nd : L.Nodup) (huNot : u ∉ L)
    (hother : ∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
      u ∉ bucketsOther ℓ' ∧ (∀ x ∈ L, x ∉ bucketsOther ℓ') ∧
      DoublyLinked st₀.mem (wLvlNext workAddr n m H) (wLvlPrev workAddr n m H) n
        (bucketsOther ℓ') n (st₀.mem (wLvlHead workAddr n m H + ℓ')))
    (hdeg_le : degXu ≤ 2 * m) (hvol_le : st₀.mem (wLvlVol workAddr n m H + ℓ) ≤ 2 * m)
    (hdeg_mem : st₀.mem (wDegX workAddr n m H + u) = degXu)
    (hrN : st₀.regs prN = n)
    (hrDX : st₀.regs prDegX = wDegX workAddr n m H)
    (hrLN : st₀.regs prLvlNext = wLvlNext workAddr n m H)
    (hrLP : st₀.regs prLvlPrev = wLvlPrev workAddr n m H)
    (hrLV : st₀.regs prLvlVol = wLvlVol workAddr n m H)
    (hrLH : st₀.regs prLvlHead = wLvlHead workAddr n m H)
    (hdl_ℓ : DoublyLinked st₀.mem (wLvlNext workAddr n m H) (wLvlPrev workAddr n m H)
      n L n (st₀.mem (wLvlHead workAddr n m H + ℓ))) :
    let lvlVolAddr := wLvlVol workAddr n m H
    let lvlHeadAddr := wLvlHead workAddr n m H
    let lvlNextAddr := wLvlNext workAddr n m H
    let lvlPrevAddr := wLvlPrev workAddr n m H
    Triple w p
      (fun st => st = st₀ ∧ st.regs prU = u ∧ st.regs prTmp2 = ℓ)
      linkLvlStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp3 → r ≠ prSuf → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        BucketMemPreserved st₀.mem st'.mem workAddr n m H ℓ ∧
        st'.mem (lvlVolAddr + ℓ) = st₀.mem (lvlVolAddr + ℓ) + degXu ∧
        (∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
          DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (bucketsOther ℓ') n (st'.mem (lvlHeadAddr + ℓ'))) ∧
        DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (u :: L) n (st'.mem (lvlHeadAddr + ℓ)))
      (fun _ => 95) := by
  dsimp only
  intro st ω ⟨hst, hru, hr2⟩
  subst st
  set degXAddr := wDegX workAddr n m H
  set lvlNextAddr := wLvlNext workAddr n m H
  set lvlPrevAddr := wLvlPrev workAddr n m H
  set lvlVolAddr := wLvlVol workAddr n m H
  set lvlHeadAddr := wLvlHead workAddr n m H
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have hmC : 32 * m ≤ 8 * C_cap * m := by nlinarith
  have hval_pow : ∀ x, x ≤ 4 * m + n + H + 1 → x < 2 ^ w := fun x hx => by omega
  set oldHead := st₀.mem (lvlHeadAddr + ℓ)
  have hold_le : oldHead ≤ n := by
    cases hL : L with
    | nil =>
        have : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n [] n oldHead := hL ▸ hdl_ℓ
        exact le_of_eq this
    | cons b bs =>
        have : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n (b :: bs) n oldHead := hL ▸ hdl_ℓ
        exact le_of_lt (this.1 ▸ this.2.1)
  have hvol_add_lt : st₀.mem (lvlVolAddr + ℓ) + degXu < 2 ^ w := hval_pow _ (by omega)
  have hlhead_lt : lvlHeadAddr + ℓ < 2 ^ w := hlt_pow _ (by dsimp [lvlHeadAddr, wLvlHead]; omega)
  have hlv_lt : lvlVolAddr + ℓ < 2 ^ w := hlt_pow _ (by dsimp [lvlVolAddr, wLvlVol]; omega)
  have hln_lt : lvlNextAddr + u < 2 ^ w := hlt_pow _ (by dsimp [lvlNextAddr, wLvlNext]; omega)
  have hlp_lt : lvlPrevAddr + u < 2 ^ w := hlt_pow _ (by dsimp [lvlPrevAddr, wLvlPrev]; omega)
  have hdx_lt : degXAddr + u < 2 ^ w := hlt_pow _ (by dsimp [degXAddr, wDegX]; omega)
  have hold_lt : oldHead < 2 ^ w := hval_pow _ (by omega)
  have hu_lt : u < 2 ^ w := hval_pow _ (by omega)
  have hn_lt : n < 2 ^ w := hval_pow _ (by omega)
  have hdeg_lt : degXu < 2 ^ w := hval_pow _ (by omega)
  have hvol_lt : st₀.mem (lvlVolAddr + ℓ) < 2 ^ w := hval_pow _ (by omega)
  set mem1 := Function.update (Function.update st₀.mem (lvlNextAddr + u) oldHead) (lvlPrevAddr + u) n
  have hcond : Triple w p
      (fun st =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp3 → r ≠ prSuf → st.regs r = st₀.regs r) ∧
        st.regs prTmp1 = lvlHeadAddr + ℓ ∧ st.regs prSuf = oldHead ∧
        st.pos = st₀.pos ∧ st.mem = mem1)
      (.cond (.bin .lt (.reg prSuf) (.reg prN))
        (.store (.bin .add (.reg prLvlPrev) (.reg prSuf)) (.reg prU))
        .nop)
      (normalPost fun st =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp3 → r ≠ prSuf → st.regs r = st₀.regs r) ∧
        st.regs prTmp1 = lvlHeadAddr + ℓ ∧ st.regs prSuf = oldHead ∧
        st.pos = st₀.pos ∧
        st.mem = (if oldHead < n then Function.update mem1 (lvlPrevAddr + oldHead) u else mem1))
      (fun _ => 15) := by
    apply (Triple.cond_const (val := fun st => if st.regs prSuf < st.regs prN then 1 else 0)
      (c_t := 5) (c_f := 1)
      (fun st ⟨hr, _, hs, _, _⟩ => by
        have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide)).trans hrN
        have h0lt : 0 < 2 ^ w := by omega
        have h1lt : 1 < 2 ^ w := by omega
        simp only [Expr.eval, hs, hrn, WordRAM.BinOp.eval]
        by_cases hcmp : oldHead < n <;> simp [hcmp, h1lt, h0lt])
      ?_ ?_).mono_cost (fun _ _ => by simp [Expr.size])
    · apply Triple.store (addr := fun _ => lvlPrevAddr + oldHead) (val := fun _ => u)
        (fun st ⟨⟨hr, _, hs, _, _⟩, hne⟩ => by
          have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide)).trans hrN
          have hlt : oldHead < n := by by_contra h'; rw [hs, hrn] at hne; simp [h'] at hne
          have hrlp : st.regs prLvlPrev = lvlPrevAddr :=
            (hr prLvlPrev (by decide) (by decide) (by decide)).trans hrLP
          exact eval_add_regs hrlp hs (hlt_pow _ (by dsimp [lvlPrevAddr, wLvlPrev]; omega)))
        (fun st ⟨⟨hr, _, _, _, _⟩, _⟩ => by
          have hru' : st.regs prU = u := (hr prU (by decide) (by decide) (by decide)).trans hru
          exact eval_reg hru' hu_lt)
        (fun st ⟨⟨hr, h1, hs, hp, hm⟩, hne⟩ => by
          have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide)).trans hrN
          have hlt : oldHead < n := by by_contra h'; rw [hs, hrn] at hne; simp [h'] at hne
          refine ⟨hr, h1, hs, hp, ?_⟩
          simp only [hm, hlt, ↓reduceIte])
    · exact Triple.nop fun st ⟨⟨hr, h1, hs, hp, hm⟩, heq⟩ => by
        have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide)).trans hrN
        have hnot : ¬(oldHead < n) := by
          intro hlt; rw [hs, hrn] at heq; simp [hlt] at heq
        refine ⟨hr, h1, hs, hp, ?_⟩
        simp only [hm, hnot, ↓reduceIte]
  set mem2 := if oldHead < n then Function.update mem1 (lvlPrevAddr + oldHead) u else mem1
  have htail : Triple w p
      (fun st =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp3 → r ≠ prSuf → st.regs r = st₀.regs r) ∧
        st.regs prTmp1 = lvlHeadAddr + ℓ ∧ st.pos = st₀.pos ∧ st.mem = mem2)
      (seqStmts [
        .store (.reg prTmp1) (.reg prU),
        .assign prTmp1 (.bin .add (.reg prLvlVol) (.reg prTmp2)),
        .assign prTmp3 (.load (.reg prTmp1)),
        .assign prSuf (.load (.bin .add (.reg prDegX) (.reg prU))),
        .store (.reg prTmp1) (.bin .add (.reg prTmp3) (.reg prSuf))
      ])
      (normalPost fun st =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp3 → r ≠ prSuf → st.regs r = st₀.regs r) ∧
        st.pos = st₀.pos ∧
        st.mem = Function.update (Function.update mem2 (lvlHeadAddr + ℓ) u)
          (lvlVolAddr + ℓ) (st₀.mem (lvlVolAddr + ℓ) + degXu))
      (fun _ => 45) := by
    intro st2 ω2 ⟨hr_2, h1_2, hp2, hm2⟩
    have hru2 : st2.regs prU = u := (hr_2 prU (by decide) (by decide) (by decide)).trans hru
    have hr2_2 : st2.regs prTmp2 = ℓ := (hr_2 prTmp2 (by decide) (by decide) (by decide)).trans hr2
    have hrv2 : st2.regs prLvlVol = lvlVolAddr :=
      (hr_2 prLvlVol (by decide) (by decide) (by decide)).trans hrLV
    have hrdx2 : st2.regs prDegX = degXAddr :=
      (hr_2 prDegX (by decide) (by decide) (by decide)).trans hrDX
    have hmem2_vol : mem2 (lvlVolAddr + ℓ) = st₀.mem (lvlVolAddr + ℓ) := by
      have h1 : mem1 (lvlVolAddr + ℓ) = st₀.mem (lvlVolAddr + ℓ) := by
        dsimp only [mem1]
        rw [Function.update_of_ne (by dsimp [lvlVolAddr, lvlPrevAddr, wLvlVol, wLvlPrev]; omega)]
        exact Function.update_of_ne (by dsimp [lvlVolAddr, lvlNextAddr, wLvlVol, wLvlNext]; omega) _ _
      dsimp only [mem2]
      split_ifs
      · rw [Function.update_of_ne (by dsimp [lvlVolAddr, lvlPrevAddr, wLvlVol, wLvlPrev]; omega), h1]
      · exact h1
    have hne_hv : lvlHeadAddr + ℓ ≠ lvlVolAddr + ℓ := by
      dsimp [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol]; omega
    have hne_hd : lvlHeadAddr + ℓ ≠ degXAddr + u := by
      dsimp [lvlHeadAddr, degXAddr, wLvlHead, wDegX]; omega
    have hmem2_dx : mem2 (degXAddr + u) = degXu := by
      have h1 : mem1 (degXAddr + u) = st₀.mem (degXAddr + u) := by
        dsimp only [mem1]
        rw [Function.update_of_ne (by dsimp [degXAddr, lvlPrevAddr, wDegX, wLvlPrev]; omega)]
        exact Function.update_of_ne (by dsimp [degXAddr, lvlNextAddr, wDegX, wLvlNext]; omega) _ _
      dsimp only [mem2]
      split_ifs
      · rw [Function.update_of_ne (by dsimp [degXAddr, lvlPrevAddr, wDegX, wLvlPrev]; omega), h1]
        exact hdeg_mem
      · rw [h1]; exact hdeg_mem
    refine runs_start_le ?_
    dsimp only [seqStmts]
    apply runs_seq_store_le (x := lvlHeadAddr + ℓ) (v := u)
    · exact eval_reg h1_2 hlhead_lt
    · exact eval_reg hru2 hu_lt
    apply runs_seq_assign_le (v := lvlVolAddr + ℓ)
    · exact eval_add_regs (by simp [hrv2]) (by simp [hr2_2]) hlv_lt
    apply runs_seq_assign_le (v := st₀.mem (lvlVolAddr + ℓ))
    · simp only [Expr.eval, Function.update_self, Option.map_some, hm2,
        Function.update_of_ne hne_hv.symm, hmem2_vol]
    apply runs_seq_assign_le (v := degXu)
    · exact eval_load_add_regs (by simp [hrdx2]) (by simp [hru2])
        hdx_lt (by simp [hm2, Function.update_of_ne hne_hd.symm, hmem2_dx]) hdeg_lt
    apply runs_store_le (x := lvlVolAddr + ℓ) (v := st₀.mem (lvlVolAddr + ℓ) + degXu)
    · exact eval_reg (by simp) hlv_lt
    · simp only [Expr.eval, Function.update_self, Function.update_of_ne (by decide : prTmp3 ≠ prSuf),
        WordRAM.BinOp.eval, hvol_add_lt, ↓reduceIte]
    · simp only [normalPost]
      exact ⟨fun r h1 h3 hs => by simp [h1, h3, hs, hr_2 r h1 h3 hs], hp2, by simp [hm2]⟩
    · simp only [Expr.size]; omega
  refine runs_start_le ?_
  dsimp only [linkLvlStmt, seqStmts]
  apply runs_seq_assign_le (v := lvlHeadAddr + ℓ)
  · exact eval_add_regs hrLH hr2 hlhead_lt
  apply runs_seq_assign_le (v := oldHead)
  · simp only [Expr.eval, Function.update_self, Option.map_some]; rfl
  apply runs_seq_store_le (x := lvlNextAddr + u) (v := oldHead)
  · exact eval_add_regs (by simp; exact hrLN) (by simp [hru]) hln_lt
  · exact eval_reg (by simp) hold_lt
  apply runs_seq_store_le (x := lvlPrevAddr + u) (v := n)
  · exact eval_add_regs (by simp; exact hrLP) (by simp [hru]) hlp_lt
  · exact eval_reg (by simp; exact hrN) hn_lt
  apply runs_seq_triple_le hcond
  · refine ⟨fun r h1 h3 hs => by simp [h1, hs], by simp, by simp, rfl, rfl⟩
  intro st2 ⟨hr2', h1_2, _, hp2, hm2⟩
  obtain ⟨o, st', c2, hrun2, hpost2, hc2⟩ :=
    htail.runs ω ⟨hr2', h1_2, hp2, hm2⟩
  cases o with
  | returned _ => exact absurd hpost2 (by simp [normalPost])
  | normal =>
      dsimp only [normalPost] at hpost2
      rcases hpost2 with ⟨hr', hp', hm'⟩
      refine ⟨.normal, st', c2, hrun2, ?_, by simp only [Expr.size] at *; omega⟩
      dsimp only [normalPost]
      have hbmp1 : BucketMemPreserved st₀.mem mem1 workAddr n m H ℓ := by
        dsimp only [mem1]
        refine ⟨memFrame_trans
            (memFrame_update_in (by dsimp [lvlNextAddr, wLvlNext]; omega)
              (by dsimp [lvlNextAddr, lvlHeadAddr, wLvlNext, wLvlHead]; omega))
            (memFrame_update_in (by dsimp [lvlPrevAddr, lvlNextAddr, wLvlPrev, wLvlNext]; omega)
              (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega)),
          fun k hk1 _ => by
            rw [Function.update_of_ne (by dsimp [lvlPrevAddr, wLvlPrev] at hk1 ⊢; omega),
                Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev] at hk1 ⊢; omega)],
          fun ℓ' _ _ => ⟨by
            rw [Function.update_of_ne (by dsimp [lvlVolAddr, lvlPrevAddr, wLvlVol, wLvlPrev]; omega),
                Function.update_of_ne (by dsimp [lvlVolAddr, lvlNextAddr, wLvlVol, wLvlNext]; omega)],
            by
            rw [Function.update_of_ne (by dsimp [lvlHeadAddr, lvlPrevAddr, wLvlHead, wLvlPrev]; omega),
                Function.update_of_ne (by dsimp [lvlHeadAddr, lvlNextAddr, wLvlHead, wLvlNext]; omega)]⟩⟩
      have hbmp2 : BucketMemPreserved mem1 mem2 workAddr n m H ℓ := by
        dsimp only [mem2]
        split_ifs with holdn
        · refine ⟨memFrame_update_in (by dsimp [lvlPrevAddr, lvlNextAddr, wLvlPrev, wLvlNext]; omega)
              (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega),
            fun k hk1 _ => Function.update_of_ne (by dsimp [lvlPrevAddr, wLvlPrev] at hk1 ⊢; omega) _ _,
            fun ℓ' _ _ => ⟨Function.update_of_ne (by dsimp [lvlVolAddr, lvlPrevAddr, wLvlVol, wLvlPrev]; omega) _ _,
              Function.update_of_ne (by dsimp [lvlHeadAddr, lvlPrevAddr, wLvlHead, wLvlPrev]; omega) _ _⟩⟩
        · exact bucketMemPreserved_refl mem1 workAddr n m H ℓ
      have hbmp3 : BucketMemPreserved mem2 st'.mem workAddr n m H ℓ := by
        rw [hm']
        refine ⟨memFrame_trans
            (memFrame_update_in (by dsimp [lvlHeadAddr, lvlNextAddr, wLvlHead, wLvlNext]; omega)
              (by dsimp [lvlHeadAddr, wLvlHead]; omega))
            (memFrame_update_in (by dsimp [lvlVolAddr, lvlNextAddr, wLvlVol, wLvlNext]; omega)
              (by dsimp [lvlVolAddr, lvlHeadAddr, wLvlVol, wLvlHead]; omega)),
          fun k _ hk2 => by
            rw [Function.update_of_ne (by dsimp [lvlVolAddr, wLvlVol] at hk2 ⊢; omega),
                Function.update_of_ne (by dsimp [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol] at hk2 ⊢; omega)],
          fun ℓ' _ hne => ⟨by
            rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by dsimp [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol]; omega)],
            by
            rw [Function.update_of_ne (by dsimp [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol]; omega),
                Function.update_of_ne (by omega)]⟩⟩
      have hbmp : BucketMemPreserved st₀.mem st'.mem workAddr n m H ℓ :=
        bucketMemPreserved_trans hbmp1 (bucketMemPreserved_trans hbmp2 hbmp3)
      have hvol_final : st'.mem (lvlVolAddr + ℓ) = st₀.mem (lvlVolAddr + ℓ) + degXu := by
        rw [hm', Function.update_self]
      have hhead_ℓ : st'.mem (lvlHeadAddr + ℓ) = u := by
        rw [hm', Function.update_of_ne (by dsimp [lvlVolAddr, lvlHeadAddr, wLvlVol, wLvlHead]; omega),
          Function.update_self]
      have hdl_other : ∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
          DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (bucketsOther ℓ') n (st'.mem (lvlHeadAddr + ℓ')) := by
        intro ℓ' h1 h2 hne
        rw [(hbmp.2.2 ℓ' (by omega) hne).2]
        have huNot' := (hother ℓ' h1 h2 hne).1
        have hdl_ℓ' := (hother ℓ' h1 h2 hne).2.2
        have hold_ne : ∀ y ∈ bucketsOther ℓ', oldHead ≠ y := by
          intro y hy heq
          cases hL : L with
          | nil =>
              have hnil : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n [] n oldHead := hL ▸ hdl_ℓ
              have hold_eq : oldHead = n := hnil
              have hylt := doublyLinked_mem_lt hdl_ℓ' hy
              omega
          | cons b bs =>
              have hdlb : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n (b :: bs) n oldHead := hL ▸ hdl_ℓ
              have hb_mem : b ∈ L := hL ▸ List.mem_cons_self
              simp only [hdlb.1] at heq
              exact (hother ℓ' h1 h2 hne).2.1 b hb_mem (heq ▸ hy)
        apply doublyLinked_congr_disjoint _ _ hdl_ℓ'
        · intro y hy
          have hne_uy : y ≠ u := fun h => huNot' (h ▸ hy)
          have hne_lt : y < n := doublyLinked_mem_lt hdl_ℓ' hy
          rw [hm']
          rw [Function.update_of_ne (by dsimp [lvlNextAddr, lvlVolAddr, wLvlNext, wLvlVol]; omega),
              Function.update_of_ne (by dsimp [lvlNextAddr, lvlHeadAddr, wLvlNext, wLvlHead]; omega)]
          have hmem2_eq : mem2 (lvlNextAddr + y) = mem1 (lvlNextAddr + y) := by
            dsimp only [mem2]; split_ifs
            · exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev]; omega) _ _
            · rfl
          rw [hmem2_eq]; dsimp only [mem1]
          rw [Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev]; omega)]
          exact Function.update_of_ne (by omega) _ _
        · intro y hy
          have hne_uy : y ≠ u := fun h => huNot' (h ▸ hy)
          have hne_oh : y ≠ oldHead := (hold_ne y hy).symm
          have hne_lt : y < n := doublyLinked_mem_lt hdl_ℓ' hy
          rw [hm']
          rw [Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega),
              Function.update_of_ne (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega)]
          have hmem2_eq : mem2 (lvlPrevAddr + y) = mem1 (lvlPrevAddr + y) := by
            dsimp only [mem2]; split_ifs
            · exact Function.update_of_ne (by omega) _ _
            · rfl
          rw [hmem2_eq]; dsimp only [mem1]
          rw [Function.update_of_ne (by omega)]
          exact Function.update_of_ne (by dsimp [lvlPrevAddr, lvlNextAddr, wLvlPrev, wLvlNext]; omega) _ _
      have hdl_new : DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (u :: L) n
          (st'.mem (lvlHeadAddr + ℓ)) := by
        apply doublyLinked_push_front hL_nd huN huNot hdl_ℓ hhead_ℓ
        · rw [hm', Function.update_of_ne (by dsimp [lvlNextAddr, lvlVolAddr, wLvlNext, wLvlVol]; omega),
            Function.update_of_ne (by dsimp [lvlNextAddr, lvlHeadAddr, wLvlNext, wLvlHead]; omega)]
          have : mem2 (lvlNextAddr + u) = mem1 (lvlNextAddr + u) := by
            dsimp only [mem2]; split_ifs
            · exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev]; omega) _ _
            · rfl
          rw [this]; dsimp only [mem1]
          rw [Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev]; omega),
            Function.update_self]
        · rw [hm', Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega),
            Function.update_of_ne (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega)]
          have hne_ou : oldHead ≠ u := by
            intro heq
            cases hL : L with
            | nil =>
                have hnil : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n [] n oldHead := hL ▸ hdl_ℓ
                have hold_eq : oldHead = n := hnil
                omega
            | cons b bs =>
                have hdlb : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n (b :: bs) n oldHead := hL ▸ hdl_ℓ
                exact huNot (hL ▸ heq ▸ hdlb.1 ▸ List.mem_cons_self)
          have : mem2 (lvlPrevAddr + u) = mem1 (lvlPrevAddr + u) := by
            dsimp only [mem2]; split_ifs
            · exact Function.update_of_ne (by omega) _ _
            · rfl
          rw [this]; dsimp only [mem1]; exact Function.update_self ..
        · intro h heq hlt
          have heq' : oldHead = h := heq
          have hlt' : oldHead < n := by rw [heq']; exact hlt
          rw [← heq', hm', Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega),
            Function.update_of_ne (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega)]
          dsimp only [mem2]
          simp [hlt']
        · intro y hy
          have hne_uy : y ≠ u := fun h => huNot (h ▸ hy)
          have hne_lt : y < n := doublyLinked_mem_lt hdl_ℓ hy
          rw [hm', Function.update_of_ne (by dsimp [lvlNextAddr, lvlVolAddr, wLvlNext, wLvlVol]; omega),
            Function.update_of_ne (by dsimp [lvlNextAddr, lvlHeadAddr, wLvlNext, wLvlHead]; omega)]
          have hmem2_eq : mem2 (lvlNextAddr + y) = mem1 (lvlNextAddr + y) := by
            dsimp only [mem2]; split_ifs
            · exact Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev]; omega) _ _
            · rfl
          rw [hmem2_eq]; dsimp only [mem1]
          rw [Function.update_of_ne (by dsimp [lvlNextAddr, lvlPrevAddr, wLvlNext, wLvlPrev]; omega)]
          exact Function.update_of_ne (by omega) _ _
        · intro y hy hne_oh
          have hne_oh' : oldHead ≠ y := hne_oh
          have hne_uy : y ≠ u := fun h => huNot (h ▸ hy)
          have hne_lt : y < n := doublyLinked_mem_lt hdl_ℓ hy
          rw [hm', Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega),
            Function.update_of_ne (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega)]
          have hmem2_eq : mem2 (lvlPrevAddr + y) = mem1 (lvlPrevAddr + y) := by
            dsimp only [mem2]; split_ifs
            · exact Function.update_of_ne (by omega) _ _
            · rfl
          rw [hmem2_eq]; dsimp only [mem1]
          rw [Function.update_of_ne (by omega)]
          exact Function.update_of_ne (by dsimp [lvlPrevAddr, lvlNextAddr, wLvlPrev, wLvlNext]; omega) _ _
      exact ⟨hr', hp', hbmp, hvol_final, hdl_other, hdl_new⟩

theorem linkLvl_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u ℓ : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (huN : u < cfg.G.n) (hℓ1 : 1 ≤ ℓ) (hℓH : ℓ < cfg.H) (huNot : u ∉ buckets ℓ)
    (hother : ∀ ℓ', 1 ≤ ℓ' → ℓ' < cfg.H → ℓ' ≠ ℓ → u ∉ buckets ℓ') :
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
        st.regs prU = u ∧ st.regs prTmp2 = ℓ)
      linkLvlStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp1 → r ≠ prTmp3 → r ≠ prSuf → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        BucketMemPreserved st₀.mem st'.mem workAddr n m H ℓ ∧
        st'.mem (lvlVolAddr + ℓ) = st₀.mem (lvlVolAddr + ℓ) + cfg.degX u ∧
        (∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
          DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (buckets ℓ') n (st'.mem (lvlHeadAddr + ℓ'))) ∧
        DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (u :: buckets ℓ) n (st'.mem (lvlHeadAddr + ℓ)))
      (fun _ => 95) := by
  dsimp only
  intro st ω ⟨hst, hinv, hru, hr2⟩
  subst st
  exact (linkLvl_triple_raw (cfg.degX u) (buckets ℓ) buckets st₀ hw hinv.cfg_valid.2.2.1
    huN hℓ1 hℓH (hinv.buckets_nodup ℓ hℓ1 hℓH) huNot
    (fun ℓ' h1 h2 hne => ⟨hother ℓ' h1 h2 hne, fun x hx hmem => by
      have hx_eq := ((hinv.buckets_mem ℓ hℓ1 hℓH x).mp hx).2.2
      have hy_eq := ((hinv.buckets_mem ℓ' h1 h2 x).mp hmem).2.2
      exact hne (hy_eq.symm.trans hx_eq),
      hinv.buckets_dl ℓ' h1 h2⟩)
    (hinv.degX_le_two_mul_m huN)
    (by rw [hinv.lvlVol_eq ℓ hℓ1 hℓH]; exact hinv.volAtLevel_le_two_mul_m ℓ)
    (hinv.degX_eq u huN) hinv.reg_n hinv.reg_degX hinv.reg_lvlNext hinv.reg_lvlPrev
    hinv.reg_lvlVol hinv.reg_lvlHead (hinv.buckets_dl ℓ hℓ1 hℓH)).runs ω ⟨rfl, hru, hr2⟩


end MinCostFlow.Expander
