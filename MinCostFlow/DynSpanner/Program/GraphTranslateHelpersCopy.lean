module

public import MinCostFlow.DynSpanner.Program.GraphTranslateOps

/-!
# Copy and fill loops for the forward translation

Part 1 of `GraphTranslateHelpers.lean`: the loop lemmas `gtCopyRange_triple` and
`gtFillTailHead_triple` used by the preparation phases. See `GraphTranslateHelpers.lean` for the
overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

public section

lemma gtCopyRange_triple {w : ℕ} {p : Program} (srcReg dstReg lenReg : ℕ)
    (hs15 : srcReg ≠ 15) (hd15 : dstReg ≠ 15) (hl15 : lenReg ≠ 15)
    {srcPtr dstPtr len : ℕ} {L : List ℕ} {mem : ℕ → ℕ} {rOrig : ℕ → ℕ}
    (hw : 1 < 2 ^ w) (hlen_ltw : len < 2 ^ w)
    (hsrcB : srcPtr + len < 2 ^ w) (hdstB : dstPtr + len < 2 ^ w)
    (hLen : L.length = len) (hAt : ListAt mem srcPtr L)
    (hDisj : ∀ i < len, ∀ j < len, srcPtr + i ≠ dstPtr + j) :
    let Inv : ℕ → State → Prop := fun k s =>
      s.regs srcReg = srcPtr ∧ s.regs dstReg = dstPtr ∧ s.regs lenReg = len ∧
      s.regs 15 = k ∧ (∀ r < 14, s.regs r = rOrig r) ∧
      (∀ i < k, ∀ hi : i < L.length, s.mem (dstPtr + i) = L[i]'hi) ∧
      ∀ addr, addr < dstPtr ∨ dstPtr + k ≤ addr → s.mem addr = mem addr
    Triple w p
      (fun st => st.mem = mem ∧ st.regs srcReg = srcPtr ∧ st.regs dstReg = dstPtr ∧
        st.regs lenReg = len ∧ ∀ r < 14, st.regs r = rOrig r)
      (forRange 15 (.const 0) (.reg lenReg)
        (.store (.bin .add (.reg dstReg) (.reg 15)) (.load (.bin .add (.reg srcReg) (.reg 15)))))
      (normalPost (Inv len))
      (fun _ => len * 18 + 7) := by
  intro Inv
  have hzero_lt : (0 : ℕ) < 2 ^ w := by omega
  refine (Triple.forRange_const 9 0 len (Nat.zero_le _) hw (fun _ => hlen_ltw)
    (fun s ⟨hm, hrs, hrd, hrl, hOrig⟩ => ⟨by simp [Expr.eval, hzero_lt],
      ⟨by simp [Function.update_of_ne hs15, hrs],
       by simp [Function.update_of_ne hd15, hrd],
       by simp [Function.update_of_ne hl15, hrl],
       by simp,
       fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hOrig r hr,
       fun i hi => by omega,
       fun addr _ => hm ▸ rfl⟩⟩)
    (fun k s _ _ hI => hI.2.2.2.1)
    (fun k s _ _ hI => by have h := hI.2.2.1; simp [Expr.eval, h])
    ?_).mono_cost ?_
  · intro i _ hi_lt s ω ⟨hrs, hrd, hrl, hr15, hOrigI, hdstI, hfrI⟩
    have hi_len : i < L.length := by omega
    have hsi_ltw : srcPtr + i < 2 ^ w := by omega
    have hdi_ltw : dstPtr + i < 2 ^ w := by omega
    have hm_src : s.mem (srcPtr + i) = L[i]'hi_len := by
      have ha : srcPtr + i < dstPtr ∨ dstPtr + i ≤ srcPtr + i := by
        by_cases hlt : srcPtr + i < dstPtr
        · exact Or.inl hlt
        · right
          by_cases hlt2 : srcPtr + i < dstPtr + i
          · exfalso; exact hDisj i hi_lt (srcPtr + i - dstPtr) (by omega) (by omega)
          · omega
      rw [hfrI _ ha]
      exact hAt i hi_len
    refine runs_start_le ?_
    refine runs_store_le (x := dstPtr + i) (v := L[i]'hi_len)
      (by simp only [Expr.eval, BinOp.eval, hrd, hr15]
          exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad hdi_ltw))
      (by simp only [Expr.eval, BinOp.eval, hrs, hr15, Option.map_eq_some_iff]
          refine ⟨srcPtr + i, ite_eq_left_iff.mpr fun hbad => False.elim (hbad hsi_ltw), hm_src⟩)
      ⟨⟨by simp [Function.update_of_ne hs15, hrs],
        by simp [Function.update_of_ne hd15, hrd],
        by simp [Function.update_of_ne hl15, hrl],
        by simp,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hOrigI r hr,
        fun u hu hu' => by
          by_cases heq : u = i
          · subst heq; simp [Function.update_self]
          · simp [Function.update_of_ne (by omega : dstPtr + u ≠ dstPtr + i), hdstI u (by omega) hu'],
        fun addr ha => by
          dsimp only
          rw [Function.update_of_ne (by rcases ha with h | h <;> omega)]
          exact hfrI addr (by rcases ha with h | h <;> [left; right] <;> omega)⟩, hr15⟩
      (by simp only [Expr.size]; omega)
  · intro _ _
    simp only [Expr.size]
    omega

lemma gtFillTailHead_triple {w vCapJ eCapJ : ℕ} {p : Program} {bOps : ℕ}
    {J : MGraph} {jEs : List ℕ} {jPtr jEsPtr jTailsPtr jHeadsPtr : ℕ} {mem : ℕ → ℕ}
    {rOrig : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hjB : jPtr + dynGraphSize vCapJ eCapJ < 2 ^ w)
    (hjEB : jEsPtr + jEs.length < 2 ^ w) (hjTB : jTailsPtr + jEs.length < 2 ^ w)
    (hjHB : jHeadsPtr + jEs.length < 2 ^ w)
    (hjE_iff : ∀ e, e ∈ jEs ↔ e ∈ J.E) (hDynJ : DynGraphAt mem jPtr vCapJ eCapJ J)
    (hjEAt : ListAt mem jEsPtr jEs)
    (hdisjT_J : ∀ i < jEs.length, ∀ k < dynGraphSize vCapJ eCapJ, jPtr + k ≠ jTailsPtr + i)
    (hdisjH_J : ∀ i < jEs.length, ∀ k < dynGraphSize vCapJ eCapJ, jPtr + k ≠ jHeadsPtr + i)
    (hdisjT_E : ∀ i < jEs.length, ∀ k < jEs.length, jEsPtr + k ≠ jTailsPtr + i)
    (hdisjH_E : ∀ i < jEs.length, ∀ k < jEs.length, jEsPtr + k ≠ jHeadsPtr + i)
    (hdisjTH : ∀ i < jEs.length, ∀ k < jEs.length, jTailsPtr + k ≠ jHeadsPtr + i) :
    let jTails := jEs.map J.tail
    let jHeads := jEs.map J.head
    let Inv : ℕ → State → Prop := fun k s =>
      s.regs 1 = jPtr ∧ s.regs 8 = jEs.length ∧ s.regs 10 = jEsPtr ∧
      s.regs 11 = jTailsPtr ∧ s.regs 12 = jHeadsPtr ∧ s.regs 15 = k ∧
      (∀ r < 14, s.regs r = rOrig r) ∧
      (∀ i < k, ∀ hi : i < jEs.length,
                s.mem (jTailsPtr + i) = jTails[i]'(by dsimp [jTails]; simp; exact hi) ∧
                s.mem (jHeadsPtr + i) = jHeads[i]'(by dsimp [jHeads]; simp; exact hi)) ∧
      ∀ addr, (addr < jTailsPtr ∨ jTailsPtr + k ≤ addr) →
        (addr < jHeadsPtr ∨ jHeadsPtr + k ≤ addr) → s.mem addr = mem addr
    Triple w p
      (fun st => st.mem = mem ∧ st.regs 1 = jPtr ∧ st.regs 8 = jEs.length ∧
        st.regs 10 = jEsPtr ∧ st.regs 11 = jTailsPtr ∧ st.regs 12 = jHeadsPtr ∧
        ∀ r < 14, st.regs r = rOrig r)
      (forRange 15 (.const 0) (.reg 8)
        (.assign 16 (.load (.bin .add (.reg 10) (.reg 15))) ;;
         .call 17 (bOps + dgIdxGetTail) [.reg 1, .reg 16] ;;
         .store (.bin .add (.reg 11) (.reg 15)) (.reg 17) ;;
         .call 17 (bOps + dgIdxGetHead) [.reg 1, .reg 16] ;;
         .store (.bin .add (.reg 12) (.reg 15)) (.reg 17)))
      (normalPost (Inv jEs.length))
      (fun _ => jEs.length * 125 + 7) := by
  intro jTails jHeads Inv
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have hjP_ltw : jPtr < 2 ^ w := by unfold dynGraphSize at hjB; omega
  have hmJ_ltw : jEs.length < 2 ^ w := by omega
  refine (Triple.forRange_const 116 0 jEs.length (Nat.zero_le _) h1_lt (fun _ => hmJ_ltw)
    (fun s ⟨hm, r1, r8, r10, r11, r12, hOrig⟩ => ⟨by simp [Expr.eval, h0_lt],
      ⟨by simp [Function.update_of_ne, r1],
       by simp [Function.update_of_ne, r8],
       by simp [Function.update_of_ne, r10],
       by simp [Function.update_of_ne, r11],
       by simp [Function.update_of_ne, r12],
       by simp,
       fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hOrig r hr,
       fun i hi => by omega,
       fun addr _ _ => hm ▸ rfl⟩⟩)
    (fun k s _ _ hI => hI.2.2.2.2.2.1)
    (fun k s _ _ hI => by have h := hI.2.1; simp [Expr.eval, h])
    ?_).mono_cost ?_
  · intro i _ hi_lt s ω ⟨r1, r8, r10, r11, r12, r15, hOrigI, hfill, hfr⟩
    set e := jEs[i]'hi_lt
    have heJ : e ∈ J.E := (hjE_iff e).mp (List.getElem_mem hi_lt)
    have he_ltw : e < 2 ^ w := by
      have := hDynJ.2.2.1 e heJ
      have : eCapJ ≤ dynGraphSize vCapJ eCapJ := by unfold dynGraphSize; omega
      omega
    have hjE_ltw : jEsPtr + i < 2 ^ w := by omega
    have hjTi_ltw : jTailsPtr + i < 2 ^ w := by omega
    have hjHi_ltw : jHeadsPtr + i < 2 ^ w := by omega
    have hm_e : s.mem (jEsPtr + i) = e := by
      rw [hfr _
        (by by_cases h : jEsPtr + i < jTailsPtr
            · exact Or.inl h
            · right; by_cases h2 : jEsPtr + i < jTailsPtr + i
              · exfalso; exact hdisjT_E (jEsPtr + i - jTailsPtr) (by omega) i hi_lt (by omega)
              · omega)
        (by by_cases h : jEsPtr + i < jHeadsPtr
            · exact Or.inl h
            · right; by_cases h2 : jEsPtr + i < jHeadsPtr + i
              · exfalso; exact hdisjH_E (jEsPtr + i - jHeadsPtr) (by omega) i hi_lt (by omega)
              · omega)]
      exact hjEAt i hi_lt
    have hDyn_cur : DynGraphAt s.mem jPtr vCapJ eCapJ J := by
      refine hDynJ.of_agree fun addr ha1 ha2 => hfr addr ?_ ?_
      · by_cases h : addr < jTailsPtr
        · exact Or.inl h
        · right
          by_cases h2 : addr < jTailsPtr + i
          · exfalso; exact hdisjT_J (addr - jTailsPtr) (by omega) (addr - jPtr) (by omega) (by omega)
          · omega
      · by_cases h : addr < jHeadsPtr
        · exact Or.inl h
        · right
          by_cases h2 : addr < jHeadsPtr + i
          · exfalso; exact hdisjH_J (addr - jHeadsPtr) (by omega) (addr - jPtr) (by omega) (by omega)
          · omega
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := e)
      (by simp only [Expr.eval, BinOp.eval, r10, r15, Option.map_eq_some_iff]
          exact ⟨jEsPtr + i, ite_eq_left_iff.mpr fun hbad => False.elim (hbad hjE_ltw), hm_e⟩) ?_
    refine runs_seq_call_le (dgGetTail_meetsContract (G := J) hpOps)
      (vs := [jPtr, e])
      (by simp only [evalArgs, Expr.eval]; simp (disch := decide) only [Function.update_of_ne, Function.update_self, r1])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      ⟨jPtr, e, rfl, hw16, hjB, heJ, hDyn_cur⟩
      ?_
    intro t mem1 pos1 ⟨_, _, hargs1, hmem1_eq, hm1_eq⟩
    simp only [List.cons.injEq, and_true] at hargs1
    rcases hargs1 with ⟨rfl, rfl⟩
    dsimp only at hmem1_eq
    subst hmem1_eq
    subst hm1_eq
    have ht_ltw : J.tail e < 2 ^ w := by
      have : J.tail e ∈ J.V := (hDynJ.1 e heJ).1
      have := hDynJ.2.1 _ this
      have : vCapJ ≤ dynGraphSize vCapJ eCapJ := by unfold dynGraphSize; omega
      omega
    refine runs_seq_store_le (x := jTailsPtr + i) (v := J.tail e)
      (by simp only [Expr.eval, BinOp.eval]; simp (disch := decide) only [Function.update_of_ne, r11, r15]
          exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad hjTi_ltw))
      (by simp [Expr.eval, Function.update_self])
      ?_
    set memT := Function.update s.mem (jTailsPtr + i) (J.tail e)
    have hDyn_T : DynGraphAt memT jPtr vCapJ eCapJ J := by
      refine hDyn_cur.of_agree fun addr ha1 ha2 => ?_
      dsimp only [memT]
      rw [Function.update_of_ne (by intro heq; exact hdisjT_J i hi_lt (addr - jPtr) (by omega) (by omega))]
    refine runs_seq_call_le (dgGetHead_meetsContract (G := J) hpOps)
      (vs := [jPtr, e])
      (by simp only [evalArgs, Expr.eval]; simp (disch := decide) only [Function.update_of_ne, Function.update_self, r1])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      ⟨jPtr, e, rfl, hw16, hjB, heJ, hDyn_T⟩
      ?_
    intro h mem2 pos2 ⟨_, _, hargs2, hmem2_eq, hm2_eq⟩
    simp only [List.cons.injEq, and_true] at hargs2
    rcases hargs2 with ⟨rfl, rfl⟩
    dsimp only at hmem2_eq
    subst hmem2_eq
    subst hm2_eq
    refine runs_store_le (x := jHeadsPtr + i) (v := J.head e)
      (by simp only [Expr.eval, BinOp.eval]; simp (disch := decide) only [Function.update_of_ne, r12, r15]
          exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad hjHi_ltw))
      (by simp [Expr.eval, Function.update_self])
      ⟨⟨by simp (disch := decide) only [Function.update_of_ne, r1],
        by simp (disch := decide) only [Function.update_of_ne, r8],
        by simp (disch := decide) only [Function.update_of_ne, r10],
        by simp (disch := decide) only [Function.update_of_ne, r11],
        by simp (disch := decide) only [Function.update_of_ne, r12],
        by simp (disch := decide) only [Function.update_self],
        fun r hr => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hOrigI r hr,
        fun u hu hu' => by
          have hneTH : jTailsPtr + u ≠ jHeadsPtr + i := hdisjTH i hi_lt u (by omega)
          by_cases heq : u = i
          · subst heq
            simp [Function.update_of_ne hneTH, memT, Function.update_self, jTails, jHeads, e]
          · have hne1 : jTailsPtr + u ≠ jTailsPtr + i := by omega
            have hne2 : jHeadsPtr + u ≠ jHeadsPtr + i := by omega
            have hne3 : jHeadsPtr + u ≠ jTailsPtr + i := by
              intro hbad; exact hdisjTH u (by omega) i hi_lt hbad.symm
            rcases hfill u (by omega) hu' with ⟨htU, hhU⟩
            exact ⟨by dsimp only; rw [Function.update_of_ne hneTH]; dsimp [memT]; rw [Function.update_of_ne hne1]; exact htU,
              by dsimp only; rw [Function.update_of_ne hne2]; dsimp [memT]; rw [Function.update_of_ne hne3]; exact hhU⟩,
        fun addr haT haH => by
          have hneH : addr ≠ jHeadsPtr + i := by rcases haH with h | h <;> omega
          have hneT : addr ≠ jTailsPtr + i := by rcases haT with h | h <;> omega
          dsimp only; rw [Function.update_of_ne hneH]; dsimp [memT]; rw [Function.update_of_ne hneT]
          exact hfr addr (by rcases haT with h | h <;> [left; right] <;> omega)
            (by rcases haH with h | h <;> [left; right] <;> omega)⟩,
       by simp (disch := decide) only [Function.update_of_ne, r15]⟩
      (by dsimp only [dgGetTailContract, dgGetHeadContract, argsSize, Expr.size]; omega)
  · intro _ _
    simp only [Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
