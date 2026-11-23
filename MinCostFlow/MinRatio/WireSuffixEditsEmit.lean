module

public import MinCostFlow.MinRatio.WireSuffixEditsBase
import WordRAM.Tactic

/-!
# Multi-forest suffix tree-edit packer: emit pass (`WireSuffixEditsEmit`)

Proves `emitForestListDiffStmt_runs` for Pass 3–4 of `wireSuffixPackEditsBody`
(`WireSuffixEditsBase.lean`): scans a list of `DynGraphAt` forests and emits deduplicated
`TreeEditsAt` records for edges not marked in `otherMark`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program

private lemma emitEdgeList_runs {w otherBase emitBase outBuf eList tag intCap initLen maxOut : ℕ}
    {otherSet emitted0 : Finset ℕ} {eL : List ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h11 : st.regs 11 = otherBase) (h7 : st.regs 7 = emitBase) (h8 : st.regs 8 = outBuf)
    (h9 : st.regs 9 = initLen) (h20 : st.regs 20 = tag)
    (h16 : st.regs 16 = eL.length) (h17 : st.regs 17 = eList) (h18 : st.regs 18 = 0)
    (heL : ListAt st.mem eList eL) (hCap : ∀ e ∈ eL, e < intCap)
    (hOther : ∀ e < intCap, st.mem (otherBase + e) = if e ∈ otherSet then 1 else 0)
    (hEmit : ∀ e < intCap, st.mem (emitBase + e) = if e ∈ emitted0 then 1 else 0)
    (hSepO : eList + eL.length ≤ emitBase ∧ (otherBase + intCap ≤ emitBase ∨ emitBase + intCap ≤ otherBase))
    (hSepOut : eList + eL.length ≤ outBuf ∧ otherBase + intCap ≤ outBuf ∧ emitBase + intCap ≤ outBuf)
    (hBound : initLen + eL.length ≤ maxOut)
    (hOutW : outBuf + 2 * maxOut < 2 ^ w) (hEmitW : emitBase + intCap < 2 ^ w)
    (hOtherW : otherBase + intCap < 2 ^ w) (hLenW : eL.length < 2 ^ w) (hw2 : 2 < 2 ^ w)
    (htag : tag = 0 ∨ tag = 1) :
    let added := emitScanList otherSet emitted0 eL
    let tc := fun e => if tag = 0 then TreeChange.delete e else TreeChange.insert e
    ∃ out c,
      Runs w p ω
        (.loop (.bin .lt (.reg 18) (.reg 16))
          (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
           .cond (.bin .eq (.load (.bin .add (.reg 11) (.reg 19))) (.const 0))
             (.cond (.bin .eq (.load (.bin .add (.reg 7) (.reg 19))) (.const 0))
               (.store (.bin .add (.reg 7) (.reg 19)) (.const 1) ;;
                .store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.reg 20) ;;
                .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.const 1))
                  (.reg 19) ;;
                .assign 9 (.bin .add (.reg 9) (.const 1)))
               .nop)
             .nop ;;
           .assign 18 (.bin .add (.reg 18) (.const 1))))
        st .normal out c ∧
      c ≤ 60 * eL.length + 5 ∧
      out.regs 9 = initLen + added.length ∧
      TreeEditsAt out.mem (outBuf + 2 * initLen) (added.map tc) ∧
      (∀ e < intCap, out.mem (emitBase + e) =
        if e ∈ emitted0 ∪ added.toFinset then 1 else 0) ∧
      (∀ a, (a < emitBase ∨ emitBase + intCap ≤ a) →
        (a < outBuf + 2 * initLen ∨ outBuf + 2 * (initLen + added.length) ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, r ≠ 9 → r ≠ 18 → r ≠ 19 → out.regs r = st.regs r) := by
  have hwne0 : w ≠ 0 := by intro h; subst h; omega
  let tc := fun e => if tag = 0 then TreeChange.delete e else TreeChange.insert e
  suffices hLoop : ∀ (rest done : List ℕ) (s : State) (curEmitted : Finset ℕ) (curAdded : List ℕ),
      done ++ rest = eL →
      curAdded = emitScanList otherSet emitted0 done →
      curEmitted = emitted0 ∪ curAdded.toFinset →
      s.regs 11 = otherBase → s.regs 7 = emitBase → s.regs 8 = outBuf →
      s.regs 9 = initLen + curAdded.length → s.regs 20 = tag →
      s.regs 16 = eL.length → s.regs 17 = eList → s.regs 18 = done.length →
      TreeEditsAt s.mem (outBuf + 2 * initLen) (curAdded.map tc) →
      (∀ e < intCap, s.mem (emitBase + e) = if e ∈ curEmitted then 1 else 0) →
      (∀ a, (a < emitBase ∨ emitBase + intCap ≤ a) →
        (a < outBuf + 2 * initLen ∨ outBuf + 2 * (initLen + curAdded.length) ≤ a) →
        s.mem a = st.mem a) →
      ∃ out c,
        Runs w p ω
          (.loop (.bin .lt (.reg 18) (.reg 16))
            (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
             .cond (.bin .eq (.load (.bin .add (.reg 11) (.reg 19))) (.const 0))
               (.cond (.bin .eq (.load (.bin .add (.reg 7) (.reg 19))) (.const 0))
                 (.store (.bin .add (.reg 7) (.reg 19)) (.const 1) ;;
                  .store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.reg 20) ;;
                  .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.const 1))
                    (.reg 19) ;;
                  .assign 9 (.bin .add (.reg 9) (.const 1)))
                 .nop)
               .nop ;;
             .assign 18 (.bin .add (.reg 18) (.const 1))))
          s .normal out c ∧
        c ≤ 60 * rest.length + 5 ∧
        out.regs 9 = initLen + (emitScanList otherSet emitted0 eL).length ∧
        TreeEditsAt out.mem (outBuf + 2 * initLen) ((emitScanList otherSet emitted0 eL).map tc) ∧
        (∀ e < intCap, out.mem (emitBase + e) =
          if e ∈ emitted0 ∪ (emitScanList otherSet emitted0 eL).toFinset then 1 else 0) ∧
        (∀ a, (a < emitBase ∨ emitBase + intCap ≤ a) →
          (a < outBuf + 2 * initLen ∨ outBuf + 2 * (initLen + (emitScanList otherSet emitted0 eL).length) ≤ a) →
          out.mem a = st.mem a) ∧
        (∀ r, r ≠ 9 → r ≠ 18 → r ≠ 19 → out.regs r = s.regs r) by
    exact hLoop eL [] st emitted0 [] rfl rfl (by simp) h11 h7 h8 (by simp [h9]) h20 h16 h17 h18
      (by simp [TreeEditsAt, ListAt]) hEmit (fun _ _ _ => rfl)
  intro rest
  induction rest with
  | nil =>
    intro done s curEm curAd happ hAd hEm _ _ _ h9' _ h16' _ h18' hEd hEmAt hFr
    have hdEq : done = eL := by simpa using happ
    subst hdEq; subst hAd; subst hEm
    exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, h18', h16'], rfl, rfl, by simp [Expr.size]⟩),
      by omega, h9', hEd, hEmAt, hFr, fun _ _ _ _ => rfl⟩
  | cons e rest ih =>
    intro done s curEm curAd happ hAd hEm h11' h7' h8' h9' h20' h16' h17' h18' hEd hEmAt hFr
    have hLen : done.length + rest.length + 1 = eL.length := by
      have := congrArg List.length happ; simp at this; omega
    have hAdLe : curAd.length ≤ done.length := hAd ▸ (emitScanList_props otherSet emitted0 done).2.2
    have heMem : e ∈ eL := by rw [← happ]; simp
    have heCap : e < intCap := hCap e heMem
    have heAt : s.mem (eList + done.length) = e := by
      rw [hFr _ (Or.inl (by omega)) (Or.inl (by omega))]
      have hget := heL done.length (by omega)
      have heq : eL[done.length]'(by omega) = e := by
        have h1 : (done ++ e :: rest)[done.length]'(by simp) = e := by simp
        simpa [happ] using h1
      exact hget.trans heq
    let s1 := { s with regs := Function.update s.regs 19 e }
    have r1 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 17) (.reg 18)))) s .normal s1 5 :=
      runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, h17', h18',
        show eList + done.length < 2 ^ w by omega, heAt], rfl, rfl, rfl⟩
    have hOAt : s.mem (otherBase + e) = if e ∈ otherSet then 1 else 0 := by
      rw [hFr _ (by rcases hSepO.2 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
        (Or.inl (by omega))]
      exact hOther e heCap
    have hEAt : s.mem (emitBase + e) = if e ∈ curEm then 1 else 0 := hEmAt e heCap
    have hAppScan : emitScanList otherSet emitted0 (done ++ [e]) =
        curAd ++ (if e ∉ otherSet ∧ e ∉ curEm then [e] else []) := by
      rw [emitScanList_append, ← hAd, ← hEm]; simp [emitScanList]
    have hPos : 2 * (initLen + curAd.length) < 2 ^ w := by omega
    have hPos1 : outBuf + 2 * (initLen + curAd.length) < 2 ^ w := by omega
    have hPos2 : outBuf + 2 * (initLen + curAd.length) + 1 < 2 ^ w := by omega
    let emitStmt : Stmt :=
      .cond (.bin .eq (.load (.bin .add (.reg 11) (.reg 19))) (.const 0))
        (.cond (.bin .eq (.load (.bin .add (.reg 7) (.reg 19))) (.const 0))
          (.store (.bin .add (.reg 7) (.reg 19)) (.const 1) ;;
           .store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.reg 20) ;;
           .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.const 1))
             (.reg 19) ;;
           .assign 9 (.bin .add (.reg 9) (.const 1)))
          .nop)
        .nop
    have hStep : ∃ s2 cCond,
        Runs w p ω emitStmt s1 .normal s2 cCond ∧
        cCond ≤ 44 ∧
        s2.regs 9 = initLen + (emitScanList otherSet emitted0 (done ++ [e])).length ∧
        (∀ r ≠ 9, s2.regs r = s1.regs r) ∧
        TreeEditsAt s2.mem (outBuf + 2 * initLen) ((emitScanList otherSet emitted0 (done ++ [e])).map tc) ∧
        (∀ f < intCap, s2.mem (emitBase + f) =
          if f ∈ emitted0 ∪ (emitScanList otherSet emitted0 (done ++ [e])).toFinset then 1 else 0) ∧
        (∀ a, (a < emitBase ∨ emitBase + intCap ≤ a) →
          (a < outBuf + 2 * initLen ∨
            outBuf + 2 * (initLen + (emitScanList otherSet emitted0 (done ++ [e])).length) ≤ a) →
          s2.mem a = st.mem a) := by
      by_cases hO : e ∈ otherSet
      · have hApp' : emitScanList otherSet emitted0 (done ++ [e]) = curAd := by
          simp [hAppScan, hO]
        refine ⟨s1, 8, runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, s1,
          Function.update_of_ne, h11', show otherBase + e < 2 ^ w by omega, hOAt, hO],
          by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
          by omega, ?_, fun _ _ => rfl, ?_, ?_, ?_⟩
        · rw [hApp']; simp [s1, Function.update_of_ne, h9']
        · rw [hApp']; exact hEd
        · intro f hf; rw [hApp', ← hEm]; exact hEmAt f hf
        · intro a ha1 ha2; rw [hApp'] at ha2; exact hFr a ha1 ha2
      · by_cases hE : e ∈ curEm
        · have hApp' : emitScanList otherSet emitted0 (done ++ [e]) = curAd := by
            simp [hAppScan, hE]
          refine ⟨s1, 15, runs_cond_iff.mpr ⟨1, 8, by simp [Expr.eval, BinOp.eval, s1,
              Function.update_of_ne, h11', show otherBase + e < 2 ^ w by omega, hOAt, hO, hwne0],
              by
                simp only [Nat.one_ne_zero, ↓reduceIte]
                exact runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, s1, Function.update_of_ne,
                  h7', show emitBase + e < 2 ^ w by omega, hEAt, hE],
                  by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
              by simp [Expr.size]⟩,
              by omega, ?_, fun _ _ => rfl, ?_, ?_, ?_⟩
          · rw [hApp']; simp [s1, Function.update_of_ne, h9']
          · rw [hApp']; exact hEd
          · intro f hf; rw [hApp', ← hEm]; exact hEmAt f hf
          · intro a ha1 ha2; rw [hApp'] at ha2; exact hFr a ha1 ha2
        · let m1 := Function.update s1.mem (emitBase + e) 1
          let m2 := Function.update m1 (outBuf + 2 * (initLen + curAd.length)) tag
          let m3 := Function.update m2 (outBuf + 2 * (initLen + curAd.length) + 1) e
          let u1 := { s1 with mem := m1 }
          let u2 := { u1 with mem := m2 }
          let u3 := { u2 with mem := m3 }
          let u4 := { u3 with regs := Function.update u3.regs 9 (initLen + curAd.length + 1) }
          have ru1 : Runs w p ω (.store (.bin .add (.reg 7) (.reg 19)) (.const 1)) s1 .normal u1 5 :=
            runs_store_iff.mpr ⟨emitBase + e, 1, by simp [Expr.eval, BinOp.eval, s1,
              Function.update_of_ne, h7', show emitBase + e < 2 ^ w by omega],
              by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
          have ru2 : Runs w p ω (.store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.reg 20))
              u1 .normal u2 7 :=
            runs_store_iff.mpr ⟨outBuf + 2 * (initLen + curAd.length), tag,
              by simp [Expr.eval, BinOp.eval, u1, s1, Function.update_of_ne, h8', h9', hw2, hPos, hPos1],
              by simp [Expr.eval, u1, s1, Function.update_of_ne, h20'], rfl, rfl, rfl⟩
          have ru3 : Runs w p ω
              (.store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.const 1)) (.reg 19))
              u2 .normal u3 9 :=
            runs_store_iff.mpr ⟨outBuf + 2 * (initLen + curAd.length) + 1, e,
              by simp [Expr.eval, BinOp.eval, u2, u1, s1, Function.update_of_ne, h8', h9', hw2,
                show 1 < 2 ^ w by omega, hPos, hPos1, hPos2],
              by simp [Expr.eval, u2, u1, s1], rfl, rfl, rfl⟩
          have ru4 : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) u3 .normal u4 4 :=
            runs_assign_iff.mpr ⟨initLen + curAd.length + 1, by simp [Expr.eval, BinOp.eval,
              u3, u2, u1, s1, Function.update_of_ne, h9', show 1 < 2 ^ w by omega,
              show initLen + curAd.length + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
          have rEmitB : Runs w p ω
              (.store (.bin .add (.reg 7) (.reg 19)) (.const 1) ;;
               .store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.reg 20) ;;
               .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.const 1))
                 (.reg 19) ;;
               .assign 9 (.bin .add (.reg 9) (.const 1)))
              s1 .normal u4 (5 + (7 + (9 + 4 + 1) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨u1, 5, _, ru1,
            runs_seq_iff.mpr (Or.inr ⟨u2, 7, _, ru2,
            runs_seq_iff.mpr (Or.inr ⟨u3, 9, 4, ru3, ru4, rfl⟩), rfl⟩), rfl⟩)
          have rCond : Runs w p ω emitStmt s1 .normal u4 ((((5 + (7 + (9 + 4 + 1) + 1) + 1) + 6) + 1) + 6 + 1) :=
            runs_cond_iff.mpr ⟨1, ((5 + (7 + (9 + 4 + 1) + 1) + 1) + 6) + 1,
              by simp [Expr.eval, BinOp.eval, s1, Function.update_of_ne,
                h11', show otherBase + e < 2 ^ w by omega, hOAt, hO, hwne0],
              by
                simp only [Nat.one_ne_zero, ↓reduceIte]
                exact runs_cond_iff.mpr ⟨1, 5 + (7 + (9 + 4 + 1) + 1) + 1,
                  by simp [Expr.eval, BinOp.eval, s1, Function.update_of_ne,
                    h7', show emitBase + e < 2 ^ w by omega, hEAt, hE, hwne0],
                  by simpa only [Nat.one_ne_zero, ↓reduceIte] using rEmitB,
                  by simp [Expr.size]⟩,
              by simp [Expr.size]⟩
          have hApp' : emitScanList otherSet emitted0 (done ++ [e]) = curAd ++ [e] := by
            simp [hAppScan, hO, hE]
          refine ⟨u4, _, rCond, by omega, by rw [hApp']; simp [u4]; omega,
            fun r hr => by simp [u4, u3, u2, u1, Function.update_of_ne hr], ?_, ?_, ?_⟩
          · rw [hApp', List.map_append, List.map_singleton, TreeEditsAt, List.flatMap_append,
              List.flatMap_singleton]
            apply listAt_append.mpr
            constructor
            · intro i hi
              rw [treeEditWords_length, List.length_map] at hi
              have hm3 : u4.mem (outBuf + 2 * initLen + i) = s.mem (outBuf + 2 * initLen + i) := by
                change Function.update (Function.update (Function.update s.mem (emitBase + e) 1) _ _) _ _ _ = _
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
              rw [hm3]; exact hEd i (by rw [treeEditWords_length, List.length_map]; exact hi)
            · have hbase : outBuf + 2 * initLen + ((curAd.map tc).flatMap treeEditWords).length =
                  outBuf + 2 * (initLen + curAd.length) := by
                rw [treeEditWords_length, List.length_map]; omega
              rw [hbase]
              have htw : treeEditWords (tc e) = [tag, e] := by
                rcases htag with rfl | rfl <;> simp [tc, treeEditWords]
              rw [htw]
              intro i hi
              simp only [List.length_cons, List.length_nil] at hi
              rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
              · simp [u4, u3, m3, m2]
              · simp [u4, u3, m3]
          · intro f hf
            rw [hApp']
            change Function.update (Function.update (Function.update s.mem (emitBase + e) 1) _ _) _ _ (emitBase + f) = _
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            by_cases hfe : f = e
            · subst hfe; simp
            · rw [Function.update_of_ne (by omega), hEmAt f hf, hEm]
              simp [hfe]
          · intro a ha1 ha2
            rw [hApp', List.length_append, List.length_singleton] at ha2
            change Function.update (Function.update (Function.update s.mem (emitBase + e) 1) _ _) _ _ a = _
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hFr a ha1 (by omega)
    obtain ⟨s2, cCond, rCond, hcCond, hs2_9, hs2_regs, hEd2, hEmAt2, hFr2⟩ := hStep
    let s3 := { s2 with regs := Function.update s2.regs 18 (done.length + 1) }
    have hs2_18 : s2.regs 18 = done.length := by
      rw [hs2_regs 18 (by decide)]; simp [s1, Function.update_of_ne, h18']
    have r3 : Runs w p ω (.assign 18 (.bin .add (.reg 18) (.const 1))) s2 .normal s3 4 :=
      runs_assign_iff.mpr ⟨done.length + 1, by simp [Expr.eval, BinOp.eval, hs2_18,
        show 1 < 2 ^ w by omega, show done.length + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rBody : Runs w p ω _ s .normal s3 (5 + (cCond + 4 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, cCond, 4, rCond, r3, rfl⟩), rfl⟩)
    obtain ⟨out, cRest, rRest, hcRest, hout9, hEdEnd, hEmEnd, hFrEnd, hRegsEnd⟩ :=
      ih (done ++ [e]) s3 (emitted0 ∪ (emitScanList otherSet emitted0 (done ++ [e])).toFinset)
        (emitScanList otherSet emitted0 (done ++ [e])) (by simpa [List.append_assoc] using happ)
        rfl rfl
        (by simp [s3, hs2_regs 11 (by decide), s1, Function.update_of_ne, h11'])
        (by simp [s3, hs2_regs 7 (by decide), s1, Function.update_of_ne, h7'])
        (by simp [s3, hs2_regs 8 (by decide), s1, Function.update_of_ne, h8'])
        (by simp [s3, hs2_9])
        (by simp [s3, hs2_regs 20 (by decide), s1, Function.update_of_ne, h20'])
        (by simp [s3, hs2_regs 16 (by decide), s1, Function.update_of_ne, h16'])
        (by simp [s3, hs2_regs 17 (by decide), s1, Function.update_of_ne, h17'])
        (by simp [s3]) hEd2 hEmAt2 hFr2
    refine ⟨out, (5 + (cCond + 4 + 1) + 1) + cRest + 4,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s3, _, cRest,
        by simp [Expr.eval, BinOp.eval, h18', h16', show done.length < eL.length by omega, hwne0],
        by decide, rBody, rRest, by simp [Expr.size]; omega⟩)),
      by simp only [List.length_cons]; omega, hout9, hEdEnd, hEmEnd, hFrEnd,
      fun r hr9 hr18 hr19 => by
        rw [hRegsEnd r hr9 hr18 hr19]
        change Function.update s2.regs 18 _ r = _
        rw [Function.update_of_ne hr18, hs2_regs r hr9]
        exact Function.update_of_ne hr19 _ _⟩

/-- Execution theorem for `emitForestListDiffStmt`: emits deduplicated `TreeEditsAt` records
for all edges in `graphListEdgeUnion Fs \ (otherSet ∪ emitted0)`. -/
theorem emitForestListDiffStmt_runs
    {w ptrs otherBase emitBase outBuf intCap initLen maxOut tag : ℕ}
    {Fs : List MGraph} {otherSet emitted0 : Finset ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h10 : st.regs 10 = ptrs) (h2 : st.regs 2 = Fs.length) (h11 : st.regs 11 = otherBase)
    (h7 : st.regs 7 = emitBase) (h8 : st.regs 8 = outBuf)
    (h9 : st.regs 9 = initLen) (h20 : st.regs 20 = tag)
    (htag : tag = 0 ∨ tag = 1)
    (hFs : ForestPtrListAt st.mem ptrs Fs intCap emitBase)
    (hOther : ∀ e < intCap, st.mem (otherBase + e) = if e ∈ otherSet then 1 else 0)
    (hEmit : ∀ e < intCap, st.mem (emitBase + e) = if e ∈ emitted0 then 1 else 0)
    (hSepO : otherBase + intCap ≤ emitBase ∨ emitBase + intCap ≤ otherBase)
    (hSepOut : emitBase + intCap ≤ outBuf ∧ otherBase + intCap ≤ outBuf)
    (hBound : initLen + graphListEdgeSum Fs ≤ maxOut)
    (hOutW : outBuf + 2 * maxOut < 2 ^ w) (hEmitW : emitBase + intCap < 2 ^ w)
    (hOtherW : otherBase + intCap < 2 ^ w) (hw7 : 7 < 2 ^ w) :
    let tc := fun e => if tag = 0 then TreeChange.delete e else TreeChange.insert e
    ∃ (out : State) (c : ℕ) (added : List ℕ),
      Runs w p ω emitForestListDiffStmt st .normal out c ∧
      c ≤ 60 * graphListEdgeSum Fs + 52 * Fs.length + 10 ∧
      added.Nodup ∧
      (∀ e, e ∈ added ↔ e ∈ graphListEdgeUnion Fs ∧ e ∉ otherSet ∧ e ∉ emitted0) ∧
      added.length ≤ graphListEdgeSum Fs ∧
      out.regs 9 = initLen + added.length ∧
      TreeEditsAt out.mem (outBuf + 2 * initLen) (added.map tc) ∧
      (∀ e < intCap, out.mem (emitBase + e) =
        if e ∈ emitted0 ∪ added.toFinset then 1 else 0) ∧
      (∀ a, (a < emitBase ∨ emitBase + intCap ≤ a) →
        (a < outBuf + 2 * initLen ∨ outBuf + 2 * (initLen + added.length) ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, (r < 12 ∧ r ≠ 9) ∨ 20 ≤ r → out.regs r = st.regs r) := by
  have hwne0 : w ≠ 0 := by intro h; subst h; omega
  let tc := fun e => if tag = 0 then TreeChange.delete e else TreeChange.insert e
  let s0 := { st with regs := Function.update st.regs 12 0 }
  have r0 : Runs w p ω (.assign 12 (.const 0)) st .normal s0 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  suffices hLoop : ∀ (rest done : List MGraph) (s : State) (curAdded : List ℕ),
      done ++ rest = Fs →
      curAdded.Nodup →
      (∀ e, e ∈ curAdded ↔ e ∈ graphListEdgeUnion done ∧ e ∉ otherSet ∧ e ∉ emitted0) →
      curAdded.length ≤ graphListEdgeSum done →
      s.regs 10 = ptrs → s.regs 2 = Fs.length → s.regs 11 = otherBase →
      s.regs 7 = emitBase → s.regs 8 = outBuf →
      s.regs 9 = initLen + curAdded.length → s.regs 20 = tag → s.regs 12 = done.length →
      TreeEditsAt s.mem (outBuf + 2 * initLen) (curAdded.map tc) →
      (∀ e < intCap, s.mem (emitBase + e) = if e ∈ emitted0 ∪ curAdded.toFinset then 1 else 0) →
      (∀ a, (a < emitBase ∨ emitBase + intCap ≤ a) →
        (a < outBuf + 2 * initLen ∨ outBuf + 2 * (initLen + curAdded.length) ≤ a) →
        s.mem a = st.mem a) →
      ∃ (out : State) (c : ℕ) (added : List ℕ),
        Runs w p ω
          (.loop (.bin .lt (.reg 12) (.reg 2))
            (.assign 13 (.load (.bin .add (.reg 10) (.reg 12))) ;;
             .assign 14 (.load (.reg 13)) ;;
             .assign 15 (.load (.bin .add (.reg 13) (.const 1))) ;;
             .assign 16 (.load (.bin .add (.reg 13) (.const 3))) ;;
             .assign 17 (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4))
               (.bin .mul (.const 7) (.reg 14))) (.reg 15)) ;;
             .assign 18 (.const 0) ;;
             .loop (.bin .lt (.reg 18) (.reg 16))
               (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
                .cond (.bin .eq (.load (.bin .add (.reg 11) (.reg 19))) (.const 0))
                  (.cond (.bin .eq (.load (.bin .add (.reg 7) (.reg 19))) (.const 0))
                    (.store (.bin .add (.reg 7) (.reg 19)) (.const 1) ;;
                     .store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.reg 20) ;;
                     .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.const 1))
                       (.reg 19) ;;
                     .assign 9 (.bin .add (.reg 9) (.const 1)))
                    .nop)
                  .nop ;;
                .assign 18 (.bin .add (.reg 18) (.const 1))) ;;
             .assign 12 (.bin .add (.reg 12) (.const 1))))
          s .normal out c ∧
        c ≤ 60 * graphListEdgeSum rest + 52 * rest.length + 5 ∧
        added.Nodup ∧
        (∀ e, e ∈ added ↔ e ∈ graphListEdgeUnion Fs ∧ e ∉ otherSet ∧ e ∉ emitted0) ∧
        added.length ≤ graphListEdgeSum Fs ∧
        out.regs 9 = initLen + added.length ∧
        TreeEditsAt out.mem (outBuf + 2 * initLen) (added.map tc) ∧
        (∀ e < intCap, out.mem (emitBase + e) = if e ∈ emitted0 ∪ added.toFinset then 1 else 0) ∧
        (∀ a, (a < emitBase ∨ emitBase + intCap ≤ a) →
          (a < outBuf + 2 * initLen ∨ outBuf + 2 * (initLen + added.length) ≤ a) →
          out.mem a = st.mem a) ∧
        (∀ r, (r < 12 ∧ r ≠ 9) ∨ 20 ≤ r → out.regs r = s.regs r) by
    obtain ⟨out, cL, added, rL, hcL, hnd, hmem, hle, h9E, hEdE, hEmE, hFrE, hRegsE⟩ :=
      hLoop Fs [] s0 [] rfl List.nodup_nil (by simp [graphListEdgeUnion]) (by simp)
        (by simp [s0, Function.update_of_ne, h10]) (by simp [s0, Function.update_of_ne, h2])
        (by simp [s0, Function.update_of_ne, h11]) (by simp [s0, Function.update_of_ne, h7])
        (by simp [s0, Function.update_of_ne, h8]) (by simp [s0, Function.update_of_ne, h9])
        (by simp [s0, Function.update_of_ne, h20]) (by simp [s0])
        (by simp [TreeEditsAt, ListAt]) (by simpa [s0] using hEmit) (fun _ _ _ => rfl)
    refine ⟨out, 2 + cL + 1, added, runs_seq_iff.mpr (Or.inr ⟨s0, 2, cL, r0, rL, rfl⟩),
      by omega, hnd, hmem, hle, h9E, hEdE, hEmE, hFrE, fun r hr => by
        rw [hRegsE r hr]; exact Function.update_of_ne (by omega) _ _⟩
  intro rest
  induction rest with
  | nil =>
    intro done s curAd happ hnd hmem hle _ h2' _ _ _ h9' _ h12' hEd hEm hFr
    have hdEq : done = Fs := by simpa using happ
    subst hdEq
    exact ⟨s, 4, curAd, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, h12', h2'], rfl, rfl, by simp [Expr.size]⟩),
      by simp [graphListEdgeSum], hnd, hmem, hle, h9', hEd, hEm, hFr, fun _ _ => rfl⟩
  | cons F rest ih =>
    intro done s curAd happ hnd hmem hle h10' h2' h11' h7' h8' h9' h20' h12' hEd hEm hFr
    have hLen : done.length + rest.length + 1 = Fs.length := by
      have := congrArg List.length happ; simp at this; omega
    have hSumEq : graphListEdgeSum done + F.m + graphListEdgeSum rest = graphListEdgeSum Fs := by
      rw [← happ, graphListEdgeSum_append]; simp [graphListEdgeSum]; omega
    have hFsEq : Fs[done.length]'(by omega) = F := by
      have h1 : (done ++ F :: rest)[done.length]'(by simp) = F := by simp
      simpa [happ] using h1
    obtain ⟨vc, ec, hG0, hGEnd, hFCap⟩ := hFs.2 done.length (by omega)
    rw [hFsEq] at hG0 hFCap
    let ptr := st.mem (ptrs + done.length)
    have hptrEq : s.mem (ptrs + done.length) = ptr :=
      hFr _ (Or.inl (by have := hFs.1; omega)) (Or.inl (by have := hFs.1; omega))
    have hG : DynGraphAt s.mem ptr vc ec F :=
      dynGraphAt_of_agree hG0 (fun a h1 h2 => hFr a (Or.inl (by omega)) (Or.inl (by omega)))
    obtain ⟨eL, heLLen, _, heLMem, heLAt, _⟩ := hG.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hdgSz : dynGraphSize vc ec = 4 + 7 * vc + 9 * ec := rfl
    have hptrW : ptrs + done.length < 2 ^ w := by have := hFs.1; omega
    let eList := dgEListBase ptr vc ec
    let s1 := { s with regs := Function.update s.regs 13 ptr }
    let s2 := { s1 with regs := Function.update s1.regs 14 vc }
    let s3 := { s2 with regs := Function.update s2.regs 15 ec }
    let s4 := { s3 with regs := Function.update s3.regs 16 F.m }
    let s5 := { s4 with regs := Function.update s4.regs 17 eList }
    let s6 := { s5 with regs := Function.update s5.regs 18 0 }
    have r1 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 10) (.reg 12)))) s .normal s1 5 :=
      runs_assign_iff.mpr ⟨ptr, by simp [Expr.eval, BinOp.eval, h10', h12', hptrW, hptrEq], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 14 (.load (.reg 13))) s1 .normal s2 3 :=
      runs_assign_iff.mpr ⟨vc, by simp [Expr.eval, s1]; exact hG.2.2.2.1, rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 13) (.const 1)))) s2 .normal s3 5 :=
      runs_assign_iff.mpr ⟨ec, by simp [Expr.eval, BinOp.eval, s2, s1, Function.update_of_ne,
        show 1 < 2 ^ w by omega, show ptr + 1 < 2 ^ w by omega]; exact hG.2.2.2.2.1, rfl, rfl, rfl⟩
    have r4 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 13) (.const 3)))) s3 .normal s4 5 :=
      runs_assign_iff.mpr ⟨F.m, by simp [Expr.eval, BinOp.eval, s3, s2, s1, Function.update_of_ne,
        show 3 < 2 ^ w by omega, show ptr + 3 < 2 ^ w by omega]; exact hG.2.2.2.2.2.2.1, rfl, rfl, rfl⟩
    have r5 : Runs w p ω
        (.assign 17 (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4))
          (.bin .mul (.const 7) (.reg 14))) (.reg 15))) s4 .normal s5 10 :=
      runs_assign_iff.mpr ⟨eList, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, Function.update_of_ne,
        show 4 < 2 ^ w by omega, hw7, show ptr + 4 < 2 ^ w by omega, show 7 * vc < 2 ^ w by omega,
        show ptr + 4 + 7 * vc < 2 ^ w by omega, show ptr + 4 + 7 * vc + ec < 2 ^ w by omega,
        eList, dgEListBase], rfl, rfl, rfl⟩
    have r6 : Runs w p ω (.assign 18 (.const 0)) s5 .normal s6 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
    have hmLeEc : F.m ≤ ec := by
      have hsub : F.E ⊆ Finset.range ec := fun x hx => Finset.mem_range.mpr (hG.2.2.1 x hx)
      simpa [MGraph.m] using Finset.card_le_card hsub
    have hO6 : ∀ e < intCap, s6.mem (otherBase + e) = if e ∈ otherSet then 1 else 0 := fun e he => by
      change s.mem (otherBase + e) = _
      rw [hFr _ (by rcases hSepO with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
        (Or.inl (by omega))]
      exact hOther e he
    let curEm := emitted0 ∪ curAd.toFinset
    let stepAd := emitScanList otherSet curEm eL
    obtain ⟨s7, cIn, rIn, hcIn, hs7_9, hEdStep, hEm7, hFr7, hRegs7⟩ :=
      emitEdgeList_runs (w := w) (otherBase := otherBase) (emitBase := emitBase)
        (outBuf := outBuf) (eList := eList) (tag := tag) (intCap := intCap)
        (initLen := initLen + curAd.length) (maxOut := maxOut) (otherSet := otherSet)
        (emitted0 := curEm) (eL := eL) (st := s6)
        (by simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h11'])
        (by simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h7'])
        (by simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h8'])
        (by simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h9'])
        (by simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h20'])
        (by simp [s6, s5, s4, Function.update_of_ne, heLLen])
        (by simp [s6, s5, Function.update_of_ne]) (by simp [s6]) heLAt
        (fun e he => hFCap e ((heLMem e).mp he)) hO6 hEm
        ⟨by unfold eList dgEListBase; omega, hSepO⟩
        ⟨by unfold eList dgEListBase; omega, hSepOut.2, hSepOut.1⟩
        (by omega) hOutW hEmitW hOtherW (by omega) (by omega) htag
    let s8 := { s7 with regs := Function.update s7.regs 12 (done.length + 1) }
    have hs7_12 : s7.regs 12 = done.length := by
      rw [hRegs7 12 (by decide) (by decide) (by decide)]
      simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h12']
    have r8 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 1))) s7 .normal s8 4 :=
      runs_assign_iff.mpr ⟨done.length + 1, by simp [Expr.eval, BinOp.eval, hs7_12,
        show 1 < 2 ^ w by omega, show done.length + 1 < 2 ^ w by have := hFs.1; omega], rfl, rfl, rfl⟩
    have rBody : Runs w p ω _ s .normal s8 (5 + (3 + (5 + (5 + (10 + (2 + (cIn + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 3, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 10, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, cIn, 4, rIn, r8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨hStepNd, hStepMem, hStepLe⟩ := emitScanList_props otherSet curEm eL
    have hNewNd : (curAd ++ stepAd).Nodup := by
      rw [List.nodup_append]
      refine ⟨hnd, hStepNd, fun a ha b hb heq => ?_⟩
      subst heq
      have := ((hStepMem a).mp hb).2.2
      exact this (Finset.mem_union_right _ (List.mem_toFinset.mpr ha))
    have hNewMem : ∀ e, e ∈ curAd ++ stepAd ↔
        e ∈ graphListEdgeUnion (done ++ [F]) ∧ e ∉ otherSet ∧ e ∉ emitted0 := by
      intro e
      rw [List.mem_append, hmem, hStepMem, graphListEdgeUnion_append,
        show graphListEdgeUnion [F] = F.E by simp [graphListEdgeUnion], Finset.mem_union]
      simp only [Finset.mem_union, List.mem_toFinset, not_or, heLMem, hmem]
      tauto
    have hNewEd : TreeEditsAt s8.mem (outBuf + 2 * initLen) ((curAd ++ stepAd).map tc) := by
      rw [List.map_append, TreeEditsAt, List.flatMap_append]
      apply listAt_append.mpr
      constructor
      · intro i hi
        rw [treeEditWords_length, List.length_map] at hi
        change s7.mem (outBuf + 2 * initLen + i) = _
        rw [hFr7 _ (Or.inr (by omega)) (Or.inl (by omega))]
        exact hEd i (by rw [treeEditWords_length, List.length_map]; exact hi)
      · have hbase : outBuf + 2 * initLen + ((curAd.map tc).flatMap treeEditWords).length =
            outBuf + 2 * (initLen + curAd.length) := by
          rw [treeEditWords_length, List.length_map]; omega
        rw [hbase]; exact hEdStep
    have hNewEm : ∀ e < intCap, s8.mem (emitBase + e) =
        if e ∈ emitted0 ∪ (curAd ++ stepAd).toFinset then 1 else 0 := fun e he => by
      change s7.mem (emitBase + e) = _
      rw [hEm7 e he]
      have hset : curEm ∪ stepAd.toFinset = emitted0 ∪ (curAd ++ stepAd).toFinset := by
        ext x; simp [curEm, Finset.mem_union, List.mem_toFinset]
      rw [hset]
    have hs7_9' : s7.regs 9 = initLen + curAd.length + stepAd.length := hs7_9
    have hFr7' : ∀ a, (a < emitBase ∨ emitBase + intCap ≤ a) →
        (a < outBuf + 2 * (initLen + curAd.length) ∨
          outBuf + 2 * (initLen + curAd.length + stepAd.length) ≤ a) → s7.mem a = s6.mem a := hFr7
    have hSingSum : graphListEdgeSum [F] = F.m := by simp [graphListEdgeSum]
    obtain ⟨out, cRest, added, rRest, hcRest, hndE, hmemE, hleE, h9E, hEdE, hEmE, hFrE, hRegsE⟩ :=
      ih (done ++ [F]) s8 (curAd ++ stepAd) (by simpa [List.append_assoc] using happ)
        hNewNd hNewMem
        (by rw [List.length_append, graphListEdgeSum_append, hSingSum]; omega)
        (by simp [s8, hRegs7 10 (by decide) (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h10'])
        (by simp [s8, hRegs7 2 (by decide) (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h2'])
        (by simp [s8, hRegs7 11 (by decide) (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h11'])
        (by simp [s8, hRegs7 7 (by decide) (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h7'])
        (by simp [s8, hRegs7 8 (by decide) (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h8'])
        (by simp [s8, hs7_9', List.length_append]; omega)
        (by simp [s8, hRegs7 20 (by decide) (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h20'])
        (by simp [s8]) hNewEd hNewEm
        (fun a ha1 ha2 => by
          change s7.mem a = st.mem a
          rw [List.length_append] at ha2
          rw [hFr7' a ha1 (by omega)]
          exact hFr a ha1 (by omega))
    refine ⟨out, (5 + (3 + (5 + (5 + (10 + (2 + (cIn + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + cRest + 4,
      added, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s8, _, cRest,
        by simp [Expr.eval, BinOp.eval, h12', h2', show done.length < Fs.length by omega, hwne0],
        by decide, rBody, rRest, by simp [Expr.size]; omega⟩)),
      ?_, hndE, hmemE, hleE, h9E, hEdE, hEmE, hFrE, fun r hr => by
        rw [hRegsE r hr]
        change Function.update s7.regs 12 _ r = _
        rw [Function.update_of_ne (by omega), hRegs7 r (by omega) (by omega) (by omega)]
        simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne (by omega : r ≠ 18),
          Function.update_of_ne (by omega : r ≠ 17), Function.update_of_ne (by omega : r ≠ 16),
          Function.update_of_ne (by omega : r ≠ 15), Function.update_of_ne (by omega : r ≠ 14),
          Function.update_of_ne (by omega : r ≠ 13)]⟩
    simp only [graphListEdgeSum, List.map_cons, List.sum_cons, List.length_cons] at hcRest ⊢
    rw [heLLen] at hcIn
    omega

end MinCostFlow.MinRatio
