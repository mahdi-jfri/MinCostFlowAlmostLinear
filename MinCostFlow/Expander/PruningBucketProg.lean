module

public import MinCostFlow.Expander.PruningLinkProg

/-!
# Bucket Walk Primitive for Pruning Level Buckets in WordRAM
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

theorem walkBucket_triple_raw {w : ℕ} {p : Program}
    {n m C_cap H workAddr ℓ : ℕ} (L : List ℕ) (bucketsOther : ℕ → List ℕ) {pref : List ℕ}
    (st₀ : State)
    (hw : PruneWordBound w n m C_cap H workAddr)
    (hℓ1 : 1 ≤ ℓ) (hℓH : ℓ < H)
    (hfit : pref.length + L.length ≤ n)
    (hrN : st₀.regs prN = n)
    (hrRA : st₀.regs prRemArr = wRemArr workAddr n m H)
    (hrLN : st₀.regs prLvlNext = wLvlNext workAddr n m H)
    (hrLV : st₀.regs prLvlVol = wLvlVol workAddr n m H)
    (hrLH : st₀.regs prLvlHead = wLvlHead workAddr n m H)
    (hdl_ℓ : DoublyLinked st₀.mem (wLvlNext workAddr n m H) (wLvlPrev workAddr n m H)
      n L n (st₀.mem (wLvlHead workAddr n m H + ℓ)))
    (hother_dl : ∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
      DoublyLinked st₀.mem (wLvlNext workAddr n m H) (wLvlPrev workAddr n m H)
        n (bucketsOther ℓ') n (st₀.mem (wLvlHead workAddr n m H + ℓ'))) :
    let remAddr := wRemArr workAddr n m H
    let lvlVolAddr := wLvlVol workAddr n m H
    let lvlHeadAddr := wLvlHead workAddr n m H
    let lvlNextAddr := wLvlNext workAddr n m H
    let lvlPrevAddr := wLvlPrev workAddr n m H
    Triple w p
      (fun st => st = st₀ ∧
        st.regs prStart = ℓ ∧ st.regs prEnd = pref.length ∧
        (∀ k < pref.length, st.mem (remAddr + k) = pref.getD k 0))
      walkBucketStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prU → r ≠ prEnd → st'.regs r = st₀.regs r) ∧
        st'.regs prEnd = pref.length + L.length ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem remAddr (lvlHeadAddr + H + 1) ∧
        (∀ k, wFlowEnc workAddr n m H ≤ k → k < lvlVolAddr → st'.mem k = st₀.mem k) ∧
        (∀ k, lvlVolAddr ≤ k → k < lvlHeadAddr + H + 1 →
          k ≠ lvlVolAddr + ℓ → k ≠ lvlHeadAddr + ℓ → st'.mem k = st₀.mem k) ∧
        st'.mem (lvlVolAddr + ℓ) = 0 ∧
        st'.mem (lvlHeadAddr + ℓ) = n ∧
        (∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
          DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (bucketsOther ℓ') n (st'.mem (lvlHeadAddr + ℓ'))) ∧
        (∀ k < pref.length + L.length,
          st'.mem (remAddr + k) = (pref ++ L).getD k 0))
      (fun _ => 25 * L.length + 30) := by
  dsimp only
  intro st ω ⟨hst, hst_start, hst_end, hpref⟩
  subst st
  set remAddr := wRemArr workAddr n m H
  set lvlNextAddr := wLvlNext workAddr n m H
  set lvlPrevAddr := wLvlPrev workAddr n m H
  set flowEncAddr := wFlowEnc workAddr n m H
  set lvlVolAddr := wLvlVol workAddr n m H
  set lvlHeadAddr := wLvlHead workAddr n m H
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have hval_pow : ∀ x, x ≤ 2 * m + n + H + 1 → x < 2 ^ w := fun x hx => by omega
  have hn_lt : n < 2 ^ w := hval_pow _ (by omega)
  have hℓ_lt : ℓ < 2 ^ w := hval_pow _ (by omega)
  have hlhead_lt : lvlHeadAddr + ℓ < 2 ^ w := hlt_pow _ (by dsimp [lvlHeadAddr, wLvlHead]; omega)
  have hlv_lt : lvlVolAddr + ℓ < 2 ^ w := hlt_pow _ (by dsimp [lvlVolAddr, wLvlVol]; omega)
  have hhead_le : st₀.mem (lvlHeadAddr + ℓ) ≤ n := by
    have hdl0 : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n L n (st₀.mem (lvlHeadAddr + ℓ)) := hdl_ℓ
    cases hL : L with
    | nil =>
        have hnil : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n [] n (st₀.mem (lvlHeadAddr + ℓ)) := hL ▸ hdl0
        exact le_of_eq hnil
    | cons b bs =>
        have hdlb : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n (b :: bs) n _ := hL ▸ hdl0
        exact le_of_lt (hdlb.1 ▸ hdlb.2.1)
  have hhead_lt : st₀.mem (lvlHeadAddr + ℓ) < 2 ^ w := hval_pow _ (by omega)
  -- Loop invariant over `(pv, done, rem)` with `done ++ rem = L`
  let Inv : ℕ × List ℕ × List ℕ → State → Prop := fun ⟨pv, done, rem⟩ st =>
    done ++ rem = L ∧
    DoublyLinked st.mem lvlNextAddr lvlPrevAddr n rem pv (st.regs prU) ∧
    (∀ r, r ≠ prU → r ≠ prEnd → st.regs r = st₀.regs r) ∧
    st.regs prEnd = pref.length + done.length ∧
    st.pos = st₀.pos ∧
    MemFrame st₀.mem st.mem remAddr (remAddr + n) ∧
    (∀ k < pref.length + done.length, st.mem (remAddr + k) = (pref ++ done).getD k 0)
  let eCond : Expr := .bin .lt (.reg prU) (.reg prN)
  have heSize : eCond.size = 3 := rfl
  have hloop : Triple w p (Inv (n, [], L))
      (.loop eCond (seqStmts [
        .store (.bin .add (.reg prRemArr) (.reg prEnd)) (.reg prU),
        .assign prEnd (.bin .add (.reg prEnd) (.const 1)),
        .assign prU (.load (.bin .add (.reg prLvlNext) (.reg prU)))
      ]))
      (normalPost fun st =>
        (∀ r, r ≠ prU → r ≠ prEnd → st.regs r = st₀.regs r) ∧
        st.regs prEnd = pref.length + L.length ∧
        st.pos = st₀.pos ∧
        MemFrame st₀.mem st.mem remAddr (remAddr + n) ∧
        (∀ k < pref.length + L.length,
          st.mem (remAddr + k) = (pref ++ L).getD k 0))
      (fun _ => 25 * L.length + 4) := by
    apply (Triple.loop_inv (α := ℕ × List ℕ × List ℕ)
      (m := fun x => x.2.2.length)
      (rem := fun x => 25 * x.2.2.length + 4)
      (condVal := fun st => if st.regs prU < st.regs prN then 1 else 0)
      (Inv := Inv)
      ?_ ?_ ?_ (n, [], L)).mono_cost (fun _ _ => le_rfl)
    · rintro ⟨pv, done, rem⟩ st ⟨_, _, hr, _, _, _, _⟩
      have hrn : st.regs prN = n := (hr prN (by decide) (by decide)).trans hrN
      have h0lt : 0 < 2 ^ w := by omega
      have h1lt : 1 < 2 ^ w := by omega
      simp only [eCond, Expr.eval, hrn, WordRAM.BinOp.eval]
      by_cases hcmp : st.regs prU < n <;> simp [hcmp, h1lt, h0lt]
    · rintro ⟨pv, done, rem⟩ st ⟨hcat, hdl, hr, hend, hp, hmf, hrem⟩ heq
      have hrn : st.regs prN = n := (hr prN (by decide) (by decide)).trans hrN
      have hrem_nil : rem = [] := by
        cases rem with
        | nil => rfl
        | cons a as =>
            have hlt : st.regs prU < st.regs prN := by rw [hdl.1, hrn]; exact hdl.2.1
            simp [hlt] at heq
      subst hrem_nil
      rw [List.append_nil] at hcat
      rw [← hcat]
      exact ⟨⟨hr, hend, hp, hmf, hrem⟩, by simp [eCond, Expr.size]⟩
    · rintro ⟨pv, done, rem⟩ st ⟨hcat, hdl, hr, hend, hp, hmf, hrem⟩ hne
      cases rem with
      | nil =>
          have hrn : st.regs prN = n := (hr prN (by decide) (by decide)).trans hrN
          exfalso; apply hne
          have hln : ¬(st.regs prU < st.regs prN) := by rw [hdl, hrn]; exact Nat.lt_irrefl n
          simp [hln]
      | cons a as =>
          refine ⟨21, ?_⟩
          intro st1 ω2 hst1
          subst st1
          rcases hdl with ⟨ha_u, ha_n, _, hdl_as⟩
          have ha_lt : a < 2 ^ w := hval_pow _ (by omega)
          have hlen_lt : pref.length + done.length < n := by
            have hcat_len : done.length + (as.length + 1) = L.length := by
              rw [← hcat, List.length_append, List.length_cons]
            omega
          have hidx_lt : pref.length + done.length < 2 ^ w := hval_pow _ (by omega)
          have hidx1_lt : pref.length + done.length + 1 < 2 ^ w := hval_pow _ (by omega)
          have hrem_a_lt : remAddr + (pref.length + done.length) < 2 ^ w :=
            hlt_pow _ (by dsimp [remAddr, wRemArr]; omega)
          have hr_rem : st.regs prRemArr = remAddr :=
            (hr prRemArr (by decide) (by decide)).trans hrRA
          have hr_ln : st.regs prLvlNext = lvlNextAddr :=
            (hr prLvlNext (by decide) (by decide)).trans hrLN
          have hln_a_lt : lvlNextAddr + a < 2 ^ w :=
            hlt_pow _ (by dsimp [lvlNextAddr, wLvlNext]; omega)
          have hnxt_eq : st.mem (lvlNextAddr + a) = st₀.mem (lvlNextAddr + a) :=
            hmf (lvlNextAddr + a) (Or.inl (by dsimp [lvlNextAddr, remAddr, wLvlNext, wRemArr]; omega))
          have hnxt_val_le : st.mem (lvlNextAddr + a) ≤ n := by
            cases as with
            | nil => exact le_of_eq hdl_as
            | cons b bs => exact le_of_lt (hdl_as.1 ▸ hdl_as.2.1)
          have hnxt_val_lt : st.mem (lvlNextAddr + a) < 2 ^ w := hval_pow _ (by omega)
          have h1lt : 1 < 2 ^ w := by omega
          have hbody_step : ∃ o st' c1,
              Runs w p ω2 (seqStmts [
                .store (.bin .add (.reg prRemArr) (.reg prEnd)) (.reg prU),
                .assign prEnd (.bin .add (.reg prEnd) (.const 1)),
                .assign prU (.load (.bin .add (.reg prLvlNext) (.reg prU)))
              ]) st o st' c1 ∧
              normalPost (fun st' => Inv (a, done ++ [a], as) st') o st' ∧ c1 ≤ 21 := by
            dsimp only [seqStmts]
            refine runs_start_le (T := 21) ?_
            apply runs_seq_store_le (x := remAddr + (pref.length + done.length)) (v := a)
            · exact eval_add_regs hr_rem hend hrem_a_lt
            · exact eval_reg ha_u ha_lt
            apply runs_seq_assign_le (v := pref.length + done.length + 1)
            · simp only [Expr.eval, hend, WordRAM.BinOp.eval, h1lt, hidx1_lt, ↓reduceIte]
            apply runs_assign_le (v := st.mem (lvlNextAddr + a))
            · have hne_mem : lvlNextAddr + a ≠ remAddr + (pref.length + done.length) := by
                dsimp [lvlNextAddr, remAddr, wLvlNext, wRemArr]; omega
              exact eval_load_add_regs (by simp [hr_ln]) (by simp [ha_u]) hln_a_lt
                (by simp [Function.update_of_ne hne_mem]) hnxt_val_lt
            · simp only [normalPost]
              refine ⟨by simpa [List.append_assoc] using hcat, ?_, ?_, ?_, hp, ?_, ?_⟩
              · simp only [Function.update_self]
                apply doublyLinked_congr_disjoint
                · intro x hx
                  have hxlt := doublyLinked_mem_lt hdl_as hx
                  exact Function.update_of_ne (by dsimp [lvlNextAddr, remAddr, wLvlNext, wRemArr]; omega) _ _
                · intro x hx
                  have hxlt := doublyLinked_mem_lt hdl_as hx
                  exact Function.update_of_ne (by dsimp [lvlPrevAddr, remAddr, wLvlPrev, wRemArr]; omega) _ _
                · exact hdl_as
              · intro r hru' hre'
                dsimp only
                rw [Function.update_of_ne hru', Function.update_of_ne hre']
                exact hr r hru' hre'
              · simp only [Function.update_of_ne (by decide : prEnd ≠ prU), Function.update_self,
                  List.length_append, List.length_cons, List.length_nil]
                omega
              · exact memFrame_trans hmf (memFrame_update_in (by omega) (by omega))
              · intro k hk
                dsimp only
                by_cases hkEq : k = pref.length + done.length
                · subst hkEq
                  rw [Function.update_self, List.getD_eq_getElem?_getD, ← List.append_assoc]
                  have hlen_p : (pref ++ done).length = pref.length + done.length := List.length_append
                  rw [List.getElem?_append_right (by omega), hlen_p, Nat.sub_self]
                  simp
                · have hkLt : k < pref.length + done.length := by
                    simp only [List.length_append, List.length_cons, List.length_nil] at hk
                    omega
                  rw [Function.update_of_ne (by omega), hrem k hkLt]
                  conv_rhs =>
                    rw [List.getD_eq_getElem?_getD, ← List.append_assoc,
                      List.getElem?_append_left (by rw [List.length_append]; exact hkLt)]
                  rw [List.getD_eq_getElem?_getD]
            · simp only [Expr.size]; omega
          obtain ⟨o, st_next, c_b, hrun_b, hpost_b, hc_b⟩ := hbody_step
          cases o with
          | returned _ => exact absurd hpost_b (by simp [normalPost])
          | normal =>
              refine ⟨.normal, st_next, c_b, hrun_b,
                ⟨(a, done ++ [a], as), hpost_b, by simp,
                  by simp only [eCond, Expr.size, List.length_cons]; omega⟩,
                hc_b⟩
  refine runs_start_le ?_
  dsimp only [walkBucketStmt, seqStmts]
  apply runs_seq_assign_le (v := st₀.mem (lvlHeadAddr + ℓ))
  · exact eval_load_add_regs hrLH hst_start hlhead_lt rfl hhead_lt
  apply runs_seq_triple_le hloop
  · refine ⟨rfl, ?_, fun r h1 _ => Function.update_of_ne h1 _ _, by simp [hst_end], rfl, fun _ _ => rfl, ?_⟩
    · have hdl0 : DoublyLinked st₀.mem lvlNextAddr lvlPrevAddr n L n (st₀.mem (lvlHeadAddr + ℓ)) := hdl_ℓ
      simpa only [Function.update_self] using hdl0
    · intro k hk
      simpa only [List.append_nil] using hpref k hk
  intro st1 ⟨hr1, hend1, hp1, hmf1, hrem1⟩
  have hr_lv1 : st1.regs prLvlVol = lvlVolAddr := (hr1 prLvlVol (by decide) (by decide)).trans hrLV
  have hr_lh1 : st1.regs prLvlHead = lvlHeadAddr := (hr1 prLvlHead (by decide) (by decide)).trans hrLH
  have hr_st1 : st1.regs prStart = ℓ := (hr1 prStart (by decide) (by decide)).trans hst_start
  have hr_n1 : st1.regs prN = n := (hr1 prN (by decide) (by decide)).trans hrN
  apply runs_seq_store_le (x := lvlVolAddr + ℓ) (v := 0)
  · exact eval_add_regs hr_lv1 hr_st1 hlv_lt
  · simp only [Expr.eval, (by omega : 0 < 2 ^ w), ↓reduceIte]
  apply runs_store_le (x := lvlHeadAddr + ℓ) (v := n)
  · exact eval_add_regs hr_lh1 hr_st1 hlhead_lt
  · exact eval_reg hr_n1 hn_lt
  · dsimp only [normalPost]
    have hmf_all : MemFrame st₀.mem
        (Function.update (Function.update st1.mem (lvlVolAddr + ℓ) 0) (lvlHeadAddr + ℓ) n)
        remAddr (lvlHeadAddr + H + 1) := by
      apply memFrame_trans
      · intro k hk
        exact hmf1 k (by rcases hk with h | h <;> [exact Or.inl h; exact Or.inr (by dsimp [remAddr, lvlHeadAddr, wRemArr, wLvlHead] at *; omega)])
      · exact memFrame_trans
          (memFrame_update_in (by dsimp [lvlVolAddr, remAddr, wLvlVol, wRemArr]; omega)
            (by dsimp [lvlVolAddr, lvlHeadAddr, wLvlVol, wLvlHead]; omega))
          (memFrame_update_in (by dsimp [lvlHeadAddr, remAddr, wLvlHead, wRemArr]; omega)
            (by dsimp [lvlHeadAddr, wLvlHead]; omega))
    refine ⟨hr1, hend1, hp1, hmf_all, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk1 hk2
      rw [Function.update_of_ne (by dsimp only [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol] at hk2 ⊢; omega),
          Function.update_of_ne (by dsimp only [lvlVolAddr, wLvlVol] at hk2 ⊢; omega)]
      exact hmf1 k (Or.inr (by dsimp only [flowEncAddr, remAddr, wFlowEnc, wRemArr] at hk1 ⊢; omega))
    · intro k hk1 hk2 hne1 hne2
      rw [Function.update_of_ne hne2, Function.update_of_ne hne1]
      exact hmf1 k (Or.inr (by dsimp only [lvlVolAddr, remAddr, wLvlVol, wRemArr] at hk1 ⊢; omega))
    · rw [Function.update_of_ne (by dsimp only [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol]; omega),
          Function.update_self]
    · exact Function.update_self ..
    · intro ℓ' h1 h2 hne
      have hheq : Function.update (Function.update st1.mem (lvlVolAddr + ℓ) 0) (lvlHeadAddr + ℓ) n (lvlHeadAddr + ℓ') =
          st₀.mem (lvlHeadAddr + ℓ') := by
        rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp [lvlHeadAddr, lvlVolAddr, wLvlHead, wLvlVol]; omega)]
        exact hmf1 _ (Or.inr (by dsimp [lvlHeadAddr, remAddr, wLvlHead, wRemArr]; omega))
      rw [hheq]
      apply doublyLinked_congr_disjoint _ _ (hother_dl ℓ' h1 h2 hne)
      · intro y hy
        change Function.update (Function.update st1.mem (lvlVolAddr + ℓ) 0) (lvlHeadAddr + ℓ) n (lvlNextAddr + y) =
          st₀.mem (lvlNextAddr + y)
        have hylt := doublyLinked_mem_lt (hother_dl ℓ' h1 h2 hne) hy
        rw [Function.update_of_ne (by dsimp [lvlNextAddr, lvlHeadAddr, wLvlNext, wLvlHead]; omega),
            Function.update_of_ne (by dsimp [lvlNextAddr, lvlVolAddr, wLvlNext, wLvlVol]; omega)]
        exact hmf1 _ (Or.inl (by dsimp [lvlNextAddr, remAddr, wLvlNext, wRemArr]; omega))
      · intro y hy
        change Function.update (Function.update st1.mem (lvlVolAddr + ℓ) 0) (lvlHeadAddr + ℓ) n (lvlPrevAddr + y) =
          st₀.mem (lvlPrevAddr + y)
        have hylt := doublyLinked_mem_lt (hother_dl ℓ' h1 h2 hne) hy
        rw [Function.update_of_ne (by dsimp [lvlPrevAddr, lvlHeadAddr, wLvlPrev, wLvlHead]; omega),
            Function.update_of_ne (by dsimp [lvlPrevAddr, lvlVolAddr, wLvlPrev, wLvlVol]; omega)]
        exact hmf1 _ (Or.inl (by dsimp [lvlPrevAddr, remAddr, wLvlPrev, wRemArr]; omega))
    · intro k hk
      have hkl : k < n := by omega
      rw [Function.update_of_ne (by dsimp [lvlHeadAddr, remAddr, wLvlHead, wRemArr]; omega),
          Function.update_of_ne (by dsimp [lvlVolAddr, remAddr, wLvlVol, wRemArr]; omega)]
      exact hrem1 k hk
  · simp only [Expr.size]; omega

theorem walkBucket_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr ℓ : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {pref : List ℕ} (st₀ : State)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hℓ1 : 1 ≤ ℓ) (hℓH : ℓ < cfg.H)
    (hfit : pref.length + (buckets ℓ).length ≤ cfg.G.n) :
    let n := cfg.G.n
    let m := cfg.G.m
    let H := cfg.H
    let remAddr := wRemArr workAddr n m H
    let lvlVolAddr := wLvlVol workAddr n m H
    let lvlHeadAddr := wLvlHead workAddr n m H
    let lvlNextAddr := wLvlNext workAddr n m H
    let lvlPrevAddr := wLvlPrev workAddr n m H
    Triple w p
      (fun st => st = st₀ ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st ∧
        st.regs prStart = ℓ ∧ st.regs prEnd = pref.length ∧
        (∀ k < pref.length, st.mem (remAddr + k) = pref.getD k 0))
      walkBucketStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prU → r ≠ prEnd → st'.regs r = st₀.regs r) ∧
        st'.regs prEnd = pref.length + (buckets ℓ).length ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem remAddr (lvlHeadAddr + H + 1) ∧
        (∀ k, wFlowEnc workAddr n m H ≤ k → k < lvlVolAddr → st'.mem k = st₀.mem k) ∧
        (∀ k, lvlVolAddr ≤ k → k < lvlHeadAddr + H + 1 →
          k ≠ lvlVolAddr + ℓ → k ≠ lvlHeadAddr + ℓ → st'.mem k = st₀.mem k) ∧
        st'.mem (lvlVolAddr + ℓ) = 0 ∧
        st'.mem (lvlHeadAddr + ℓ) = n ∧
        (∀ ℓ', 1 ≤ ℓ' → ℓ' < H → ℓ' ≠ ℓ →
          DoublyLinked st'.mem lvlNextAddr lvlPrevAddr n (buckets ℓ') n (st'.mem (lvlHeadAddr + ℓ'))) ∧
        (∀ k < pref.length + (buckets ℓ).length,
          st'.mem (remAddr + k) = (pref ++ buckets ℓ).getD k 0))
      (fun _ => 25 * (buckets ℓ).length + 30) := by
  dsimp only
  intro st ω ⟨hst, hinv, hst_start, hst_end, hpref⟩
  subst st
  exact (walkBucket_triple_raw (buckets ℓ) buckets st₀ hw hℓ1 hℓH hfit hinv.reg_n
    hinv.reg_remArr hinv.reg_lvlNext hinv.reg_lvlVol hinv.reg_lvlHead
    (hinv.buckets_dl ℓ hℓ1 hℓH) (fun ℓ' h1 h2 _ => hinv.buckets_dl ℓ' h1 h2)).runs
    ω ⟨rfl, hst_start, hst_end, hpref⟩


end MinCostFlow.Expander
