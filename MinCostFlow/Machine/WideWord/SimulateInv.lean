module

public import MinCostFlow.Machine.WideWord.SimulateExpr

/-!
# Frame invariant, loop simulation, and procedure wrappers

This file provides the shared simulation infrastructure for `compile`:
* `SimFrameInv` and `FrameWordBounds`: frame, control-block, and lazy-trie invariants.
* `SimFrameInv.of_mem_scratch_and_reg`, `SimFrameInv.of_mem_scratch_only`,
  `SimFrameInv.congr_gst_pos`: frame-preservation helpers.
* `evalExprAndIsZero_runs` and `evalE_runs`: evaluating condition expressions via `idxIsZero`.
* `CompileStmtPost`, `CompileStmtProp`, `compileProc_from_stmt`, `compileLoop_runs`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Basic helpers -/

theorem readWord_const_false (pos : ℕ) : ∀ k : ℕ, readWord (fun _ => false) pos k = 0
  | 0 => rfl
  | k + 1 => by simp [readWord, readWord_const_false (pos + 1) k]

theorem mul_Lw'_bound {a b c L w' : ℕ} (hL1 : 1 ≤ L) (hw'1 : 1 ≤ w')
    (hab : a + b ≤ c) : a * L + b ≤ c * L * w' := by
  have hL : L ≤ L * w' := Nat.le_mul_of_pos_right L hw'1
  have h1 : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
  calc a * L + b ≤ a * (L * w') + b * (L * w') :=
        Nat.add_le_add (Nat.mul_le_mul_left a hL) (Nat.le_mul_of_pos_right b h1)
    _ = (a + b) * (L * w') := by ring
    _ ≤ c * (L * w') := Nat.mul_le_mul_right _ hab
    _ = c * L * w' := by ring

theorem scale_Lh_ge_one (Q : Program) (L h c : ℕ) (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) :
    1 ≤ simScale Q * L * 2 ^ h * c := by
  have hS : 1 ≤ simScale Q := by have := frameSlots_lt_simScale Q; omega
  have h2h : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by norm_num)
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hS hL1) h2h) hc1

theorem runs_seq3_assoc {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₃ s₄ : Stmt} {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h123 : Runs w p ω (s₁ ;; s₂ ;; s₃) st .normal st₁ c₁)
    (h4 : Runs w p ω s₄ st₁ o st₂ c₂) :
    Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄) st o st₂ (c₁ + c₂ + 1) := by
  rcases runs_seq_iff.mp h123 with ⟨_, _, _, hno, _⟩ | ⟨stA, cA, c23, hr1, hr23, rfl⟩
  · cases hno
  · rcases runs_seq_iff.mp hr23 with ⟨_, _, _, hno, _⟩ | ⟨stB, cB, cC, hr2, hr3, rfl⟩
    · cases hno
    · refine runs_seq_iff.mpr (Or.inr ⟨stA, cA, cB + (cC + c₂ + 1) + 1, hr1,
        runs_seq_iff.mpr (Or.inr ⟨stB, cB, cC + c₂ + 1, hr2,
          runs_seq_iff.mpr (Or.inr ⟨st₁, cC, c₂, hr3, h4, rfl⟩), rfl⟩), ?_⟩)
      omega

/-! ### Frame invariant and word-size bounds -/

/-- Per-frame invariant relating a host `State` (at width `w`) and a guest `State` (at width `w'`). -/
structure SimFrameInv (w w' L h : ℕ) (Q : Program) (ctrl framePtr retDst : ℕ)
    (st gst : State) : Prop where
  r0 : st.regs 0 = ctrl
  r1 : st.regs 1 = retDst
  r2 : st.regs 2 = framePtr
  r3 : st.regs 3 = ctrl
  r4 : st.regs 4 = ctrl + 1
  r5 : st.regs 5 = L
  r6 : st.regs 6 = h
  r7 : st.regs 7 = 2 ^ h
  mem2 : st.mem (ctrl + 2) = L
  mem3 : st.mem (ctrl + 3) = h
  mem4 : st.mem (ctrl + 4) = 2 ^ h
  ctrl_lt_frame : ctrl + 5 ≤ framePtr
  ret_lt_frame : retDst + L ≤ framePtr
  ret_disj_ctrl : retDst + L ≤ ctrl ∨ ctrl + 5 ≤ retDst
  frame_le_hp : framePtr + frameSlots Q * L ≤ st.mem (ctrl + 1)
  trie : TrieRep st.mem L h (st.mem (ctrl + 1)) (st.mem ctrl) gst.mem
  inTrie_disj : ∀ p, InTrie st.mem L h L (st.mem ctrl) p →
    (p < ctrl ∨ ctrl + 5 ≤ p) ∧
    (p < retDst ∨ retDst + L ≤ p) ∧
    (p < framePtr ∨ framePtr + frameSlots Q * L ≤ p)
  reg_lt : ∀ r < Q.regBound, gst.regs r < 2 ^ w'
  reg_limbs : ∀ r < Q.regBound, LimbsAt st.mem (framePtr + r * L) L h (gst.regs r)
  mem_lt : ∀ a, gst.mem a < 2 ^ w'

structure FrameWordBounds (w L h : ℕ) (Q : Program) (ctrl framePtr retDst hp : ℕ) : Prop where
  hw1 : 1 < 2 ^ w
  h16 : 16 ≤ 2 ^ w
  hLh : L * h < 2 ^ w
  hL_w : L < 2 ^ w
  hH_w : h < 2 ^ w
  hH2_w : 2 ^ h < 2 ^ w
  hslots_w : frameSlots Q < 2 ^ w
  hframe_w : framePtr + frameSlots Q * L < 2 ^ w
  hctrl_w : ctrl + 5 < 2 ^ w
  hret_w : retDst + L < 2 ^ w
  hhp_w : hp < 2 ^ w

theorem frame_word_bounds {w L h : ℕ} {Q : Program} {ctrl framePtr retDst hp c : ℕ}
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hc1 : 1 ≤ c)
    (hctrl : ctrl + 5 ≤ framePtr) (hret : retDst + L ≤ framePtr)
    (hf : framePtr + frameSlots Q * L ≤ hp)
    (hbound : hp + simScale Q * L * 2 ^ h * c < 2 ^ w) :
    FrameWordBounds w L h Q ctrl framePtr retDst hp := by
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have h16 : 16 ≤ 2 ^ w := two_pow_four_le_of_hw2 hh hw2
  have hS : 1 ≤ simScale Q := by have := frameSlots_lt_simScale Q; omega
  have hLh : L * h < 2 ^ w := by
    have : simScale Q * L * 2 ^ h * c < 2 ^ w := by omega
    exact hLh_lt_two_pow_of_scale hS hc1 this
  have h2h1 : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by norm_num)
  have hSL : simScale Q ≤ simScale Q * L * 2 ^ h * c := by
    have : L * 2 ^ h * c ≥ 1 := Nat.mul_pos (Nat.mul_pos hL1 h2h1) hc1
    calc simScale Q = simScale Q * 1 := by ring
      _ ≤ simScale Q * (L * 2 ^ h * c) := Nat.mul_le_mul_left _ this
      _ = simScale Q * L * 2 ^ h * c := by ring
  have h2hc : 2 ^ h ≤ simScale Q * L * 2 ^ h * c := by
    have : simScale Q * L * c ≥ 1 := Nat.mul_pos (Nat.mul_pos hS hL1) hc1
    calc 2 ^ h = 2 ^ h * 1 := by ring
      _ ≤ 2 ^ h * (simScale Q * L * c) := Nat.mul_le_mul_left _ this
      _ = simScale Q * L * 2 ^ h * c := by ring
  have hLc : L ≤ simScale Q * L * 2 ^ h * c := by
    have : simScale Q * 2 ^ h * c ≥ 1 := Nat.mul_pos (Nat.mul_pos hS h2h1) hc1
    calc L = L * 1 := by ring
      _ ≤ L * (simScale Q * 2 ^ h * c) := Nat.mul_le_mul_left _ this
      _ = simScale Q * L * 2 ^ h * c := by ring
  have hslots_lt : frameSlots Q < simScale Q := frameSlots_lt_simScale Q
  have hH2_w : 2 ^ h < 2 ^ w := lt_of_le_of_lt h2hc (by omega)
  exact ⟨hw1, h16, hLh, lt_of_le_of_lt hLc (by omega), lt_trans Nat.lt_two_pow_self hH2_w,
    hH2_w, lt_trans hslots_lt (lt_of_le_of_lt hSL (by omega)),
    by omega, by omega, by omega, by omega⟩

theorem SimFrameInv.congr_gst_pos {w w' L h : ℕ} {Q : Program} {ctrl framePtr retDst pos' : ℕ}
    {st gst : State} (hinv : SimFrameInv w w' L h Q ctrl framePtr retDst st gst) :
    SimFrameInv w w' L h Q ctrl framePtr retDst st { gst with pos := pos' } :=
  ⟨hinv.r0, hinv.r1, hinv.r2, hinv.r3, hinv.r4, hinv.r5, hinv.r6, hinv.r7,
   hinv.mem2, hinv.mem3, hinv.mem4, hinv.ctrl_lt_frame, hinv.ret_lt_frame, hinv.ret_disj_ctrl,
   hinv.frame_le_hp, hinv.trie, hinv.inTrie_disj, hinv.reg_lt, hinv.reg_limbs, hinv.mem_lt⟩

theorem SimFrameInv.ctrl_mem_eq_of_frame {w w' L h : ℕ} {Q : Program}
    {ctrl framePtr retDst j : ℕ} {st gst : State} {mem' : ℕ → ℕ}
    (hinv : SimFrameInv w w' L h Q ctrl framePtr retDst st gst)
    (hj2 : 2 ≤ j) (hj5 : j < 5)
    (hfr : ∀ q, q < st.mem (ctrl + 1) → q ≠ ctrl → q ≠ ctrl + 1 →
      ¬ InTrie st.mem L h L (st.mem ctrl) q →
      (q < retDst ∨ retDst + L ≤ q) →
      (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) →
      mem' q = st.mem q) :
    mem' (ctrl + j) = st.mem (ctrl + j) := by
  have hcf := hinv.ctrl_lt_frame
  have hfh := hinv.frame_le_hp
  refine hfr (ctrl + j) (by omega) (by omega) (by omega) ?_ ?_ (Or.inl (by omega))
  · intro hin; rcases (hinv.inTrie_disj (ctrl + j) hin).1 with hlt | hge <;> omega
  · rcases hinv.ret_disj_ctrl with hlt | hge
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

theorem SimFrameInv.of_mem_scratch_and_reg {w w' L h : ℕ} {Q : Program}
    {ctrl framePtr retDst rReg val : ℕ} {st st' gst : State}
    (hinv : SimFrameInv w w' L h Q ctrl framePtr retDst st gst)
    (hregs : ∀ r < 16, r ≠ 8 → st'.regs r = st.regs r)
    (hframe : ∀ q, (q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q) →
      (q < framePtr + rReg * L ∨ framePtr + rReg * L + L ≤ q) → st'.mem q = st.mem q)
    (hr_bound : rReg < Q.regBound)
    (hval_lt : val < 2 ^ w')
    (hval_lim : LimbsAt st'.mem (framePtr + rReg * L) L h val) :
    SimFrameInv w w' L h Q ctrl framePtr retDst st'
      { gst with regs := Function.update gst.regs rReg val } := by
  have hQslots := frameSlots_ge Q
  have hfr_sub : framePtr + rReg * L + L ≤ framePtr + frameSlots Q * L := by
    have := slot_end_le_frame (by omega : rReg < frameSlots Q) (L := L); omega
  have hno_below : ∀ q, q < framePtr → st'.mem q = st.mem q := fun q hq =>
    hframe q (Or.inl (by omega)) (Or.inl (by omega))
  have hno_above : ∀ q, st.mem (ctrl + 1) ≤ q → st'.mem q = st.mem q := fun q hq =>
    hframe q (Or.inr (by have := hinv.frame_le_hp; omega))
      (Or.inr (by have := hinv.frame_le_hp; omega))
  have hno_inTrie : ∀ q, InTrie st.mem L h L (st.mem ctrl) q → st'.mem q = st.mem q := by
    intro q hq
    have hd := (hinv.inTrie_disj q hq).2.2
    refine hframe q ?_ ?_
    · rcases hd with hlt | hge
      · exact Or.inl (by omega)
      · exact Or.inr hge
    · rcases hd with hlt | hge
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have hctrl_m : st'.mem ctrl = st.mem ctrl := hno_below ctrl (by have := hinv.ctrl_lt_frame; omega)
  have hhp_m : st'.mem (ctrl + 1) = st.mem (ctrl + 1) :=
    hno_below (ctrl + 1) (by have := hinv.ctrl_lt_frame; omega)
  refine ⟨by rw [hregs 0 (by omega) (by omega), hinv.r0],
    by rw [hregs 1 (by omega) (by omega), hinv.r1],
    by rw [hregs 2 (by omega) (by omega), hinv.r2],
    by rw [hregs 3 (by omega) (by omega), hinv.r3],
    by rw [hregs 4 (by omega) (by omega), hinv.r4],
    by rw [hregs 5 (by omega) (by omega), hinv.r5],
    by rw [hregs 6 (by omega) (by omega), hinv.r6],
    by rw [hregs 7 (by omega) (by omega), hinv.r7],
    by rw [hno_below (ctrl + 2) (by have := hinv.ctrl_lt_frame; omega), hinv.mem2],
    by rw [hno_below (ctrl + 3) (by have := hinv.ctrl_lt_frame; omega), hinv.mem3],
    by rw [hno_below (ctrl + 4) (by have := hinv.ctrl_lt_frame; omega), hinv.mem4],
    hinv.ctrl_lt_frame, hinv.ret_lt_frame, hinv.ret_disj_ctrl,
    by rw [hhp_m]; exact hinv.frame_le_hp,
    ⟨by rw [hhp_m]; exact hinv.trie.1,
      by rw [hctrl_m, hhp_m]; exact subtrie_congr_mem hno_inTrie hinv.trie.2.1,
      by rw [hhp_m]; intro q hq; rw [hno_above q hq]; exact hinv.trie.2.2 q hq⟩,
    fun p hp => by
      rw [hctrl_m, inTrie_congr_mem L (st.mem ctrl) hno_inTrie p] at hp
      exact hinv.inTrie_disj p hp,
    fun r hr => by
      dsimp only
      by_cases hre : r = rReg
      · subst hre; rw [Function.update_self]; exact hval_lt
      · rw [Function.update_of_ne hre]; exact hinv.reg_lt r hr,
    fun r hr => by
      dsimp only
      by_cases hre : r = rReg
      · subst hre; rw [Function.update_self]; exact hval_lim
      · rw [Function.update_of_ne hre]
        refine (hinv.reg_limbs r hr).congr fun q hq1 hq2 => hframe q ?_ ?_
        · have := slot_end_le_frame hr (L := L); exact Or.inl (by omega)
        · rcases lt_or_gt_of_ne hre with hlt | hgt
          · have := slot_end_le_frame hlt (L := L); exact Or.inl (by omega)
          · have := slot_end_le_frame hgt (L := L); exact Or.inr (by omega),
    hinv.mem_lt⟩

theorem SimFrameInv.of_mem_scratch_only {w w' L h : ℕ} {Q : Program}
    {ctrl framePtr retDst : ℕ} {st st' gst : State}
    (hinv : SimFrameInv w w' L h Q ctrl framePtr retDst st gst)
    (hregs : ∀ r < 16, r ≠ 8 → st'.regs r = st.regs r)
    (hframe : ∀ q, (q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q) →
      st'.mem q = st.mem q) :
    SimFrameInv w w' L h Q ctrl framePtr retDst st' gst := by
  have hQpos := one_le_program_regBound Q
  have hin : SimFrameInv w w' L h Q ctrl framePtr retDst st'
      { gst with regs := Function.update gst.regs 0 (gst.regs 0) } :=
    hinv.of_mem_scratch_and_reg hregs (fun q hq _ => hframe q hq) hQpos
      (hinv.reg_lt 0 hQpos) (by
        refine (hinv.reg_limbs 0 hQpos).congr fun q hq1 hq2 => hframe q ?_
        have := slot_end_le_frame hQpos (L := L); exact Or.inl (by omega))
  simpa [Function.update_eq_self] using hin

/-- Evaluates guest expression `e` into scratch slot `Q.regBound` and tests `idxIsZero`,
returning `st'.regs 8 = if v = 0 then 1 else 0` while preserving `SimFrameInv`. -/
theorem evalExprAndIsZero_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {base w' L h ctrl framePtr retDst v : ℕ} {Q : Program} {e : Expr} {st gst : State}
    (hComp : p.HasAt base (compile Q base))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h)
    (hinv : SimFrameInv w w' L h Q ctrl framePtr retDst st gst)
    (hheap : st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * (e.size + 1) < 2 ^ w)
    (he_eval : e.eval w' gst = some v) (he_rb : e.regBound ≤ Q.regBound)
    (he_td : exprTempDepth e + 1 ≤ max 1 (programTempBound Q)) :
    ∃ st' c, Runs w p ω
      (compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
       .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5])
      st .normal st' c ∧
      (∀ r, r ≠ 8 → st'.regs r = st.regs r) ∧
      st'.regs 8 = (if v = 0 then 1 else 0) ∧
      SimFrameInv w w' L h Q ctrl framePtr retDst st' gst ∧
      (∀ q, q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q → st'.mem q = st.mem q) ∧
      c ≤ 800 * L * w' * e.size + 16 * L + 28 := by
  have hcf := hinv.ctrl_lt_frame
  have hrf := hinv.ret_lt_frame
  have hfh := hinv.frame_le_hp
  have hb := frame_word_bounds hL1 hh hw2 (by omega : 1 ≤ e.size + 1) hcf hrf hfh hheap
  have hfw := hb.hframe_w
  have hArith := arithModule_hasAt_of_compile hComp
  have hTrie := trieModule_hasAt_of_compile hComp
  have hts : Q.regBound + 1 + exprTempDepth e ≤ frameSlots Q := by
    dsimp only [frameSlots]; omega
  obtain ⟨st₁, c₁, hr₁, hreg₁, hlim₁, hfr₁, hc₁⟩ :=
    compileExpr_runs (ω := ω) hArith hTrie hL1 hh hw2 hw'1 hw'_lh hb.hLh hb.hslots_w hb.hL_w hb.hH_w
      hb.hH2_w hb.hhp_w (by omega) hfw e Q.regBound (Q.regBound + 1) v st gst he_eval
      he_rb (le_refl _) (by omega) hts hinv.r2 hinv.r3 hinv.r5 hinv.r6 hinv.r7 rfl
      hinv.trie.2.1 (fun q hq => (hinv.inTrie_disj q hq).2.2) hinv.reg_lt hinv.reg_limbs hinv.mem_lt
  have hQ_slots : Q.regBound < frameSlots Q := frameSlots_ge Q
  have r2_1 : st₁.regs 2 = framePtr := by rw [hreg₁ 2 (by omega), hinv.r2]
  have r5_1 : st₁.regs 5 = L := by rw [hreg₁ 5 (by omega), hinv.r5]
  have hslot_eval : (slotAddr 2 Q.regBound).eval w st₁ = some (framePtr + Q.regBound * L) :=
    eval_slotAddr r2_1 r5_1 hQ_slots hb.hslots_w hb.hL_w hfw
  have hargs : evalArgs w st₁ [slotAddr 2 Q.regBound, .reg 5] =
      some [framePtr + Q.regBound * L, L] :=
    evalArgs_cons hslot_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
  have hb_end : framePtr + Q.regBound * L + L < 2 ^ w := by
    have := slot_end_le_frame hQ_slots (L := L); omega
  have hpre : (mwIsZeroContract w).pre [framePtr + Q.regBound * L, L] st₁.mem :=
    ⟨framePtr + Q.regBound * L, L, rfl, hb.hw1, hb_end⟩
  obtain ⟨st₂, c₂, bval, hcall, hpost₂, hv₂, hother₂, hc₂⟩ :=
    runs_call_of_meetsContract (r := 8) (mwIsZero_of_arithModule hArith) hargs
      (by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> omega)
      hpre ω
  rcases hpost₂ with ⟨_, _, heq₂, hmem₂, hbv⟩
  simp only [List.cons.injEq, and_true] at heq₂
  rcases heq₂ with ⟨rfl, rfl⟩
  have hbval : bval = if v = 0 then 1 else 0 := by
    have hiff : (∀ i < L, st₁.mem (framePtr + Q.regBound * L + i) = 0) ↔ v = 0 :=
      ⟨fun hz => hlim₁.ext (limbsAt_zero_iff.mpr (WordRAM.listAt_replicate.mpr hz)),
       fun hv0 i hi => by subst hv0; exact WordRAM.listAt_replicate.mp (limbsAt_zero_iff.mp hlim₁) i hi⟩
    by_cases hv0 : v = 0
    · simp_all
    · have hneq : ¬ ∀ i < L, st₁.mem (framePtr + Q.regBound * L + i) = 0 := mt hiff.mp hv0
      simp_all
  have hmem_fr : ∀ q, q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q →
      st₂.mem q = st.mem q := by
    intro q hq
    rw [hmem₂]
    rcases hq with hlt | hge
    · exact hfr₁ q (Or.inl hlt) (Or.inl (by
        have := slot_mul_le_mul (by omega : Q.regBound ≤ Q.regBound + 1) (L := L); omega))
    · have h1 : framePtr + Q.regBound * L + L ≤ framePtr + frameSlots Q * L := by
        have := slot_end_le_frame hQ_slots (L := L); omega
      have h2 : framePtr + (Q.regBound + 1 + exprTempDepth e) * L ≤ framePtr + frameSlots Q * L := by
        have := slot_mul_le_mul hts (L := L); omega
      exact hfr₁ q (Or.inr (by omega)) (Or.inr (by omega))
  have hregs₂ : ∀ r, r ≠ 8 → st₂.regs r = st.regs r := fun r hd =>
    (hother₂ r hd).trans (hreg₁ r hd)
  have hinv₂ : SimFrameInv w w' L h Q ctrl framePtr retDst st₂ gst :=
    hinv.of_mem_scratch_only (fun r _ => hregs₂ r) hmem_fr
  refine ⟨st₂, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hcall, rfl⟩),
    hregs₂, by rw [hv₂, hbval], hinv₂, hmem_fr, ?_⟩
  dsimp only [mwIsZeroContract] at hc₂
  simp only [slotAddr, Expr.size, argsSize] at hc₂
  omega

/-- Runs `compileExpr ... e ;; idxIsZero ... ;; assign rFlag (.bin .eq (.reg 8) (.const 0))`,
leaving `rFlag` as `if v = 0 then 0 else 1` while preserving `SimFrameInv`. -/
theorem evalE_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {base w' L h ctrl framePtr retDst depth v : ℕ} {Q : Program} {e : Expr} {st gst : State}
    (hComp : p.HasAt base (compile Q base))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h)
    (hinv : SimFrameInv w w' L h Q ctrl framePtr retDst st gst)
    (hheap : st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * (e.size + 1) < 2 ^ w)
    (he_eval : e.eval w' gst = some v) (he_rb : e.regBound ≤ Q.regBound)
    (he_td : exprTempDepth e + 1 ≤ max 1 (programTempBound Q)) :
    ∃ st' c, Runs w p ω
      (compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
       .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5] ;;
       .assign (16 + depth) (.bin .eq (.reg 8) (.const 0)))
      st .normal st' c ∧
      (∀ r < 16 + depth, r ≠ 8 → st'.regs r = st.regs r) ∧
      st'.regs (16 + depth) = (if v = 0 then 0 else 1) ∧
      SimFrameInv w w' L h Q ctrl framePtr retDst st' gst ∧
      (∀ q, q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q → st'.mem q = st.mem q) ∧
      c ≤ 850 * L * w' * e.size + 55 * L * w' := by
  have hb := frame_word_bounds hL1 hh hw2 (by omega : 1 ≤ e.size + 1)
    hinv.ctrl_lt_frame hinv.ret_lt_frame hinv.frame_le_hp hheap
  obtain ⟨st₁, c₁, hr₁, hreg₁, hr8_1, hinv₁, hmem_fr, hc₁⟩ :=
    evalExprAndIsZero_runs (ω := ω) hComp hL1 hh hw2 hw'1 hw'_lh hinv hheap he_eval he_rb he_td
  rcases runs_seq_iff.mp hr₁ with ⟨_, _, _, hno, _⟩ | ⟨stA, cA, cB, hrA, hrB, rfl⟩
  · cases hno
  · set flag := if v = 0 then 0 else 1
    have hflag_eq : BinOp.eq.eval (if v = 0 then 1 else 0) 0 = flag := by
      by_cases hv0 : v = 0 <;> simp [BinOp.eval, hv0, flag]
    have hflag_w : flag < 2 ^ w := by
      have : flag ≤ 1 := by by_cases hv0 : v = 0 <;> simp [flag, hv0]
      have := hb.hw1; omega
    have heq_eval : (Expr.bin .eq (.reg 8) (.const 0)).eval w st₁ = some flag := by
      by_cases hv0 : v = 0 <;> simp [Expr.eval, BinOp.eval, hr8_1, hv0, hb.hw1, flag]
    set st₂ : State :=
      { mem := st₁.mem, regs := Function.update st₁.regs (16 + depth) flag, pos := st₁.pos }
    have hass : Runs w p ω (.assign (16 + depth) (.bin .eq (.reg 8) (.const 0))) st₁ .normal st₂ 4 :=
      runs_assign_iff.mpr ⟨flag, heq_eval, rfl, rfl, rfl⟩
    have hr_comb : Runs w p ω
        (compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
         .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5] ;;
         .assign (16 + depth) (.bin .eq (.reg 8) (.const 0)))
        st .normal st₂ (cA + (cB + 4 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨stA, cA, cB + 4 + 1, hrA,
        runs_seq_iff.mpr (Or.inr ⟨st₁, cB, 4, hrB, hass, rfl⟩), rfl⟩)
    have hregs₂ : ∀ r < 16 + depth, r ≠ 8 → st₂.regs r = st.regs r := fun r hr hd => by
      dsimp only [st₂]; rw [Function.update_of_ne (by omega), hreg₁ r hd]
    have hinv₂ : SimFrameInv w w' L h Q ctrl framePtr retDst st₂ gst :=
      hinv₁.of_mem_scratch_only (fun r hr _ => by
        dsimp only [st₂]; rw [Function.update_of_ne (by omega)]) (fun _ _ => rfl)
    refine ⟨st₂, _, hr_comb, hregs₂, by dsimp only [st₂]; rw [Function.update_self],
      hinv₂, hmem_fr, ?_⟩
    have h55 : 16 * L + 35 ≤ 55 * L * w' := mul_Lw'_bound hL1 hw'1 (by omega)
    have h850 : 800 * L * w' * e.size ≤ 850 * L * w' * e.size :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
    omega

/-! ### Statement specification, procedure wrapper, and loop simulation -/

/-- Exact simulation postcondition for `compileStmt`. -/
def CompileStmtPost (w w' L h base : ℕ) (p Q : Program) (ω : ℕ → Bool)
    (depth : ℕ) (s : Stmt) (ctrl framePtr retDst : ℕ) (st : State)
    (o_G : Outcome) (gst' : State) (c_G : ℕ) : Prop :=
  ∃ o_H st' c_H,
    Runs w p ω (compileStmt Q (base + 1) (base + 19) (base + 21) depth s) st o_H st' c_H ∧
    c_H ≤ simScale Q * L * w' * c_G ∧
    st.mem (ctrl + 1) ≤ st'.mem (ctrl + 1) ∧
    st'.mem (ctrl + 1) ≤ st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * c_G ∧
    (∀ r < 16 + depth, r ≠ 8 → st'.regs r = st.regs r) ∧
    (∀ q, InTrie st'.mem L h L (st'.mem ctrl) q →
      InTrie st.mem L h L (st.mem ctrl) q ∨ (st.mem (ctrl + 1) ≤ q ∧ q < st'.mem (ctrl + 1))) ∧
    (∀ q, q < st.mem (ctrl + 1) → q ≠ ctrl → q ≠ ctrl + 1 →
      ¬ InTrie st.mem L h L (st.mem ctrl) q →
      (q < retDst ∨ retDst + L ≤ q) →
      (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) →
      st'.mem q = st.mem q) ∧
    match o_G with
    | .normal =>
        o_H = .normal ∧ SimFrameInv w w' L h Q ctrl framePtr retDst st' gst'
    | .returned u =>
        o_H = .returned 0 ∧ u < 2 ^ w' ∧ LimbsAt st'.mem retDst L h u ∧
        TrieRep st'.mem L h (st'.mem (ctrl + 1)) (st'.mem ctrl) gst'.mem ∧
        (∀ p, InTrie st'.mem L h L (st'.mem ctrl) p →
          (p < ctrl ∨ ctrl + 5 ≤ p) ∧
          (p < retDst ∨ retDst + L ≤ p) ∧
          (p < framePtr ∨ framePtr + frameSlots Q * L ≤ p)) ∧
        (∀ a, gst'.mem a < 2 ^ w')

def CompileStmtProp (w w' L h base : ℕ) (p Q : Program) (ω : ℕ → Bool) (fuel : ℕ) : Prop :=
  ∀ s depth ctrl framePtr retDst st gst o_G gst' c_G,
    exec w' Q (fun _ => false) fuel s gst = some (o_G, gst', c_G) →
    s.regBound ≤ Q.regBound →
    stmtTempDepth s ≤ programTempBound Q →
    SimFrameInv w w' L h Q ctrl framePtr retDst st gst →
    st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * c_G < 2 ^ w →
    CompileStmtPost w w' L h base p Q ω depth s ctrl framePtr retDst st o_G gst' c_G

def procEntryRegs (ctrl retDst framePtr L h : ℕ) : ℕ → ℕ
  | 0 => ctrl
  | 1 => retDst
  | 2 => framePtr
  | 3 => ctrl
  | 4 => ctrl + 1
  | 5 => L
  | 6 => h
  | 7 => 2 ^ h
  | _ => 0

theorem compileProc_from_stmt {w w' L h base : ℕ} {p Q : Program} {ω : ℕ → Bool}
    {body : Stmt} {ctrl retDst framePtr pos₀ : ℕ} {mem₀ : ℕ → ℕ} {gst gst' : State}
    {o_G : Outcome} {c_G : ℕ}
    (hComp : p.HasAt base (compile Q base))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w')
    (hm2 : mem₀ (ctrl + 2) = L) (hm3 : mem₀ (ctrl + 3) = h) (hm4 : mem₀ (ctrl + 4) = 2 ^ h)
    (hctrl : ctrl + 5 ≤ framePtr) (hret : retDst + L ≤ framePtr)
    (hret_ctrl : retDst + L ≤ ctrl ∨ ctrl + 5 ≤ retDst)
    (hf : framePtr + frameSlots Q * L ≤ mem₀ (ctrl + 1))
    (htrie : TrieRep mem₀ L h (mem₀ (ctrl + 1)) (mem₀ ctrl) gst.mem)
    (hin_disj : ∀ q, InTrie mem₀ L h L (mem₀ ctrl) q →
      (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q) ∧
      (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q))
    (hreg_lt : ∀ r < Q.regBound, gst.regs r < 2 ^ w')
    (hreg_lim : ∀ r < Q.regBound, LimbsAt mem₀ (framePtr + r * L) L h (gst.regs r))
    (hmem_lt : ∀ a, gst.mem a < 2 ^ w')
    (hc1 : 1 ≤ c_G)
    (hheap : mem₀ (ctrl + 1) + simScale Q * L * 2 ^ h * c_G < 2 ^ w)
    (hstmt : SimFrameInv w w' L h Q ctrl framePtr retDst
      { mem := mem₀, regs := procEntryRegs ctrl retDst framePtr L h, pos := pos₀ } gst →
      CompileStmtPost w w' L h base p Q ω 0 body ctrl framePtr retDst
        { mem := mem₀, regs := procEntryRegs ctrl retDst framePtr L h, pos := pos₀ }
        o_G gst' c_G) :
    ∃ st' c_H,
      Runs w p ω (compileProc Q (base + 1) (base + 19) (base + 21) body)
        (startState [ctrl, retDst, framePtr] mem₀ pos₀) (.returned 0) st' c_H ∧
      c_H ≤ simScale Q * L * w' * c_G + 80 * L * w' ∧
      mem₀ (ctrl + 1) ≤ st'.mem (ctrl + 1) ∧
      st'.mem (ctrl + 1) ≤ mem₀ (ctrl + 1) + simScale Q * L * 2 ^ h * c_G ∧
      LimbsAt st'.mem retDst L h o_G.value ∧
      o_G.value < 2 ^ w' ∧
      TrieRep st'.mem L h (st'.mem (ctrl + 1)) (st'.mem ctrl) gst'.mem ∧
      (∀ q, InTrie st'.mem L h L (st'.mem ctrl) q →
        InTrie mem₀ L h L (mem₀ ctrl) q ∨ (mem₀ (ctrl + 1) ≤ q ∧ q < st'.mem (ctrl + 1))) ∧
      (∀ q, InTrie st'.mem L h L (st'.mem ctrl) q →
        (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q) ∧
        (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q)) ∧
      (∀ a, gst'.mem a < 2 ^ w') ∧
      (∀ q, q < mem₀ (ctrl + 1) → q ≠ ctrl → q ≠ ctrl + 1 →
        ¬ InTrie mem₀ L h L (mem₀ ctrl) q →
        (q < retDst ∨ retDst + L ≤ q) →
        (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) →
        st'.mem q = mem₀ q) := by
  have hb := frame_word_bounds hL1 hh hw2 hc1 hctrl hret hf hheap
  set st₀ : State := startState [ctrl, retDst, framePtr] mem₀ pos₀
  have hst0_r0 : st₀.regs 0 = ctrl := rfl
  have hst0_r1 : st₀.regs 1 = retDst := rfl
  have hst0_r2 : st₀.regs 2 = framePtr := rfl
  set st₁ : State := { st₀ with regs := Function.update st₀.regs 3 ctrl }
  set st₂ : State := { st₁ with regs := Function.update st₁.regs 4 (ctrl + 1) }
  set st₃ : State := { st₂ with regs := Function.update st₂.regs 5 L }
  set st₄ : State := { st₃ with regs := Function.update st₃.regs 6 h }
  set st₅ : State := { st₄ with regs := Function.update st₄.regs 7 (2 ^ h) }
  have h16 := hb.h16
  have ha3 : Runs w p ω (.assign 3 (.reg 0)) st₀ .normal st₁ 2 :=
    runs_assign_iff.mpr ⟨ctrl, by simp [Expr.eval, hst0_r0], rfl, rfl, rfl⟩
  have hr0_1 : st₁.regs 0 = ctrl := by simp [st₁, hst0_r0]
  have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 0) (.const 1))) st₁ .normal st₂ 4 :=
    runs_assign_iff.mpr ⟨ctrl + 1, Expr.eval_add (by eval_expr)
      (by simp [Expr.eval, hb.hw1]) (by omega), rfl, rfl, rfl⟩
  have hr0_2 : st₂.regs 0 = ctrl := by simp [st₂, hr0_1]
  have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 2)))) st₂ .normal st₃ 5 :=
    runs_assign_iff.mpr ⟨L, Expr.eval_load_of_eq
      (Expr.eval_add (by eval_expr) (by simp [Expr.eval]; omega) (by omega)) hm2, rfl, rfl, rfl⟩
  have hr0_3 : st₃.regs 0 = ctrl := by simp [st₃, hr0_2]
  have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const 3)))) st₃ .normal st₄ 5 :=
    runs_assign_iff.mpr ⟨h, Expr.eval_load_of_eq
      (Expr.eval_add (by eval_expr) (by simp [Expr.eval]; omega) (by omega)) hm3, rfl, rfl, rfl⟩
  have hr0_4 : st₄.regs 0 = ctrl := by simp [st₄, hr0_3]
  have ha7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 4)))) st₄ .normal st₅ 5 :=
    runs_assign_iff.mpr ⟨2 ^ h, Expr.eval_load_of_eq
      (Expr.eval_add (by eval_expr) (by simp [Expr.eval]; omega) (by omega)) hm4, rfl, rfl, rfl⟩
  set stInit : State :=
    { mem := mem₀, regs := procEntryRegs ctrl retDst framePtr L h, pos := pos₀ }
  have hst5_eq : st₅ = stInit := by
    dsimp only [st₅, st₄, st₃, st₂, st₁, st₀, startState, stInit]
    congr 1
    funext a
    rcases a with _ | _ | _ | _ | _ | _ | _ | _ | n <;>
      simp [procEntryRegs, List.getD]
  rw [hst5_eq] at ha7
  have hinvInit : SimFrameInv w w' L h Q ctrl framePtr retDst stInit gst :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm2, hm3, hm4, hctrl, hret, hret_ctrl,
     hf, htrie, hin_disj, hreg_lt, hreg_lim, hmem_lt⟩
  obtain ⟨o_H, stB, cB, hrunB, hcB, hhp_lo, hhp_hi, hregB, hin_subB, hfrB, houtB⟩ := hstmt hinvInit
  have hArith := arithModule_hasAt_of_compile hComp
  have hw'pos : 0 < 2 ^ w' := Nat.two_pow_pos _
  cases o_G with
  | returned u =>
    rcases houtB with ⟨rfl, hu_lt, hlimB, htrieB, hinB_disj, hmemB_lt⟩
    have hrest : Runs w p ω
        (compileStmt Q (base + 1) (base + 19) (base + 21) 0 body ;;
         .call 8 (base + 1 + idxZero) [.reg 1, .reg 5] ;;
         .ret (.const 0))
        stInit (.returned 0) stB (cB + 1) :=
      runs_seq_iff.mpr (Or.inl ⟨0, cB, hrunB, rfl, rfl⟩)
    have hpro : Runs w p ω (compileProc Q (base + 1) (base + 19) (base + 21) body)
        st₀ (.returned 0) stB (2 + (4 + (5 + (5 + (5 + (cB + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st₁, 2, _, ha3,
        runs_seq_iff.mpr (Or.inr ⟨st₂, 4, _, ha4,
          runs_seq_iff.mpr (Or.inr ⟨st₃, 5, _, ha5,
            runs_seq_iff.mpr (Or.inr ⟨st₄, 5, _, ha6,
              runs_seq_iff.mpr (Or.inr ⟨stInit, 5, _, ha7, hrest, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨stB, _, hpro, ?_, hhp_lo, hhp_hi, hlimB, hu_lt, htrieB, hin_subB, hinB_disj,
      hmemB_lt, hfrB⟩
    have h80 : 27 ≤ 80 * L * w' := by
      have h1 : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
      have h80' : 27 ≤ 80 * (L * w') := Nat.le_trans (by omega) (Nat.mul_le_mul_left 80 h1)
      calc 27 ≤ 80 * (L * w') := h80'
        _ = 80 * L * w' := by ring
    omega
  | normal =>
    rcases houtB with ⟨rfl, hinvB⟩
    have r1_B : stB.regs 1 = retDst := hinvB.r1
    have r5_B : stB.regs 5 = L := hinvB.r5
    have hargsZ : evalArgs w stB [.reg 1, .reg 5] = some [retDst, L] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
    have hpreZ : (mwZeroContract w).pre [retDst, L] stB.mem :=
      ⟨retDst, L, rfl, hb.hw1, hb.hret_w⟩
    obtain ⟨stZ, cZ, _, hcallZ, hpostZ, _, _, hcZ⟩ :=
      runs_call_of_meetsContract (r := 8) (mwZero_of_arithModule hArith) hargsZ
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> omega)
        hpreZ ω
    rcases hpostZ with ⟨_, _, heqZ, _, hzero_list, hfrZ⟩
    simp only [List.cons.injEq, and_true] at heqZ
    rcases heqZ with ⟨rfl, rfl⟩
    have hret_stmt : Runs w p ω (.ret (.const 0)) stZ (.returned 0) stZ 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
    have hepil : Runs w p ω
        (compileStmt Q (base + 1) (base + 19) (base + 21) 0 body ;;
         .call 8 (base + 1 + idxZero) [.reg 1, .reg 5] ;;
         .ret (.const 0))
        stInit (.returned 0) stZ (cB + (cZ + 2 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨stB, cB, cZ + 2 + 1, hrunB,
        runs_seq_iff.mpr (Or.inr ⟨stZ, cZ, 2, hcallZ, hret_stmt, rfl⟩), rfl⟩)
    have hpro : Runs w p ω (compileProc Q (base + 1) (base + 19) (base + 21) body)
        st₀ (.returned 0) stZ (2 + (4 + (5 + (5 + (5 + (cB + (cZ + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st₁, 2, _, ha3,
        runs_seq_iff.mpr (Or.inr ⟨st₂, 4, _, ha4,
          runs_seq_iff.mpr (Or.inr ⟨st₃, 5, _, ha5,
            runs_seq_iff.mpr (Or.inr ⟨st₄, 5, _, ha6,
              runs_seq_iff.mpr (Or.inr ⟨stInit, 5, _, ha7, hepil, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hctrlZ : stZ.mem ctrl = stB.mem ctrl := by
      refine hfrZ ctrl ?_
      rcases hret_ctrl with hlt | hge <;> [exact Or.inr hlt; exact Or.inl (by omega)]
    have hhpZ : stZ.mem (ctrl + 1) = stB.mem (ctrl + 1) := by
      refine hfrZ (ctrl + 1) ?_
      rcases hret_ctrl with hlt | hge <;> [exact Or.inr (by omega); exact Or.inl (by omega)]
    have hno_inTrieB : ∀ q, InTrie stB.mem L h L (stB.mem ctrl) q → stZ.mem q = stB.mem q :=
      fun q hq => hfrZ q (hinvB.inTrie_disj q hq).2.1
    have htrieZ : TrieRep stZ.mem L h (stZ.mem (ctrl + 1)) (stZ.mem ctrl) gst'.mem := by
      refine ⟨by rw [hhpZ]; exact hinvB.trie.1, ?_, ?_⟩
      · rw [hctrlZ, hhpZ]
        exact subtrie_congr_mem hno_inTrieB hinvB.trie.2.1
      · rw [hhpZ]
        intro q hq
        rw [hfrZ q (Or.inr (by have := hinvB.frame_le_hp; omega))]
        exact hinvB.trie.2.2 q hq
    have hinZ_sub : ∀ q, InTrie stZ.mem L h L (stZ.mem ctrl) q →
        InTrie mem₀ L h L (mem₀ ctrl) q ∨ (mem₀ (ctrl + 1) ≤ q ∧ q < stZ.mem (ctrl + 1)) := by
      intro q hq
      rw [hctrlZ, inTrie_congr_mem L (stB.mem ctrl) hno_inTrieB q] at hq
      rw [hhpZ]
      exact hin_subB q hq
    have hinZ_disj : ∀ q, InTrie stZ.mem L h L (stZ.mem ctrl) q →
        (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q) ∧
        (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) := by
      intro q hq
      rw [hctrlZ, inTrie_congr_mem L (stB.mem ctrl) hno_inTrieB q] at hq
      exact hinvB.inTrie_disj q hq
    refine ⟨stZ, _, hpro, ?_, by rw [hhpZ]; exact hhp_lo, by rw [hhpZ]; exact hhp_hi,
      limbsAt_zero_iff.mpr hzero_list, hw'pos, htrieZ, hinZ_sub, hinZ_disj, hinvB.mem_lt, ?_⟩
    · dsimp only [mwZeroContract] at hcZ
      simp only [argsSize, Expr.size] at hcZ
      have h80 : 14 * L + 45 ≤ 80 * L * w' := mul_Lw'_bound hL1 hw'1 (by omega)
      omega
    · intro q hq hqc0 hqc1 hqi hqr hqf
      rw [hfrZ q hqr, hfrB q hq hqc0 hqc1 hqi hqr hqf]

/-- Loop simulation for the `.loop (.reg (16 + depth)) (...)` node generated by `compileStmt`. -/
theorem compileLoop_runs {w w' L h base : ℕ} {p Q : Program} {ω : ℕ → Bool}
    (hComp : p.HasAt base (compile Q base))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h) :
    ∀ (fuel : ℕ), (∀ f < fuel, CompileStmtProp w w' L h base p Q ω f) →
    ∀ (e : Expr) (body : Stmt) (depth ctrl framePtr retDst : ℕ) (st gst : State)
      (o_G : Outcome) (gst' : State) (c_G v : ℕ),
      exec w' Q (fun _ => false) fuel (.loop e body) gst = some (o_G, gst', c_G) →
      e.eval w' gst = some v →
      e.regBound ≤ Q.regBound →
      body.regBound ≤ Q.regBound →
      exprTempDepth e + 1 ≤ max 1 (programTempBound Q) →
      stmtTempDepth body ≤ programTempBound Q →
      SimFrameInv w w' L h Q ctrl framePtr retDst st gst →
      st.regs (16 + depth) = (if v = 0 then 0 else 1) →
      st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * c_G < 2 ^ w →
      ∃ o_H st' c_H,
        Runs w p ω
          (.loop (.reg (16 + depth))
            (compileStmt Q (base + 1) (base + 19) (base + 21) (depth + 1) body ;;
             compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
             .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5] ;;
             .assign (16 + depth) (.bin .eq (.reg 8) (.const 0))))
          st o_H st' c_H ∧
        c_H + (850 * L * w' * e.size + 60 * L * w') ≤ simScale Q * L * w' * c_G ∧
        st.mem (ctrl + 1) ≤ st'.mem (ctrl + 1) ∧
        st'.mem (ctrl + 1) ≤ st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * c_G ∧
        (∀ r < 16 + depth, r ≠ 8 → st'.regs r = st.regs r) ∧
        (∀ q, InTrie st'.mem L h L (st'.mem ctrl) q →
          InTrie st.mem L h L (st.mem ctrl) q ∨ (st.mem (ctrl + 1) ≤ q ∧ q < st'.mem (ctrl + 1))) ∧
        (∀ q, q < st.mem (ctrl + 1) → q ≠ ctrl → q ≠ ctrl + 1 →
          ¬ InTrie st.mem L h L (st.mem ctrl) q →
          (q < retDst ∨ retDst + L ≤ q) →
          (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) →
          st'.mem q = st.mem q) ∧
        match o_G with
        | .normal =>
            o_H = .normal ∧ SimFrameInv w w' L h Q ctrl framePtr retDst st' gst'
        | .returned u =>
            o_H = .returned 0 ∧ u < 2 ^ w' ∧ LimbsAt st'.mem retDst L h u ∧
            TrieRep st'.mem L h (st'.mem (ctrl + 1)) (st'.mem ctrl) gst'.mem ∧
            (∀ p, InTrie st'.mem L h L (st'.mem ctrl) p →
              (p < ctrl ∨ ctrl + 5 ≤ p) ∧
              (p < retDst ∨ retDst + L ≤ p) ∧
              (p < framePtr ∨ framePtr + frameSlots Q * L ≤ p)) ∧
            (∀ a, gst'.mem a < 2 ^ w') := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ e body depth ctrl framePtr retDst st gst o_G gst' c_G v he_loop
    simp [exec] at he_loop
  | succ fuel ih_loop =>
    intro h_stmt e body depth ctrl framePtr retDst st gst o_G gst' c_G v he_loop
      he_eval he_rb hbody_rb he_td hbody_td hinv hrFlag hheap
    simp only [exec, he_eval] at he_loop
    by_cases hv0 : v = 0
    · subst hv0
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at he_loop
      rcases he_loop with ⟨rfl, rfl, rfl⟩
      have hr0_eval : (Expr.reg (16 + depth)).eval w st = some 0 := by
        simp [Expr.eval, hrFlag]
      have hrun_exit : Runs w p ω
          (.loop (.reg (16 + depth))
            (compileStmt Q (base + 1) (base + 19) (base + 21) (depth + 1) body ;;
             compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
             .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5] ;;
             .assign (16 + depth) (.bin .eq (.reg 8) (.const 0))))
          st .normal st 2 :=
        runs_loop_iff.mpr (Or.inl ⟨hr0_eval, rfl, rfl, rfl⟩)
      refine ⟨.normal, st, 2, hrun_exit, ?_, le_refl _, Nat.le_add_right _ _,
        fun _ _ _ => rfl, fun _ hq => Or.inl hq, fun _ _ _ _ _ _ _ => rfl, rfl, hinv⟩
      have hS : 1000 ≤ simScale Q := by
        dsimp only [simScale]; have := one_le_program_regBound Q; omega
      have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
      have h850 : 850 * L * w' * e.size ≤ simScale Q * L * w' * e.size :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
      have h60 : 2 + 60 * L * w' ≤ simScale Q * L * w' := by
        have h62 : 62 * (L * w') ≤ simScale Q * (L * w') := Nat.mul_le_mul_right _ (by omega)
        have h2 : 2 ≤ 2 * (L * w') := Nat.le_mul_of_pos_right 2 h1w'
        have hS' : simScale Q * (L * w') = simScale Q * L * w' := by ring
        have h60' : 60 * (L * w') = 60 * L * w' := by ring
        omega
      have hdist : simScale Q * L * w' * (e.size + 1) =
          simScale Q * L * w' * e.size + simScale Q * L * w' := by ring
      omega
    · simp only [hv0, ↓reduceIte] at he_loop
      have hr1_eval : (Expr.reg (16 + depth)).eval w st = some 1 := by
        simp [Expr.eval, hrFlag, hv0]
      cases hbody_exec : exec w' Q (fun _ => false) fuel body gst with
      | none => simp [hbody_exec] at he_loop
      | some res₁ =>
        rcases res₁ with ⟨o₁, gst₁, c₁⟩
        have hc1_pos : 1 ≤ c₁ := exec_cost_pos hbody_exec
        cases o₁ with
        | returned u =>
          simp only [hbody_exec, Option.some.injEq, Prod.mk.injEq] at he_loop
          rcases he_loop with ⟨rfl, rfl, rfl⟩
          have hbody_post := h_stmt fuel (Nat.lt_succ_self fuel) body (depth + 1)
            ctrl framePtr retDst st gst (.returned u) gst₁ c₁ hbody_exec hbody_rb hbody_td hinv
            (by
              have := scale_Lh_ge_one Q L h 1 hL1 (by omega)
              have hdist : simScale Q * L * 2 ^ h * (e.size + c₁ + 1) =
                  simScale Q * L * 2 ^ h * c₁ + simScale Q * L * 2 ^ h * (e.size + 1) := by ring
              omega)
          rcases hbody_post with ⟨o_Hb, st₁, c_Hb, hrB, hcB, hhpB_lo, hhpB_hi, hregB, hinB_sub, hfrB, houtB⟩
          rcases houtB with ⟨rfl, hu_lt, hlimB, htrieB, hinB_disj, hmemB_lt⟩
          have hr_seq_ret : Runs w p ω
              (compileStmt Q (base + 1) (base + 19) (base + 21) (depth + 1) body ;;
               compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
               .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5] ;;
               .assign (16 + depth) (.bin .eq (.reg 8) (.const 0)))
              st (.returned 0) st₁ (c_Hb + 1) :=
            runs_seq_iff.mpr (Or.inl ⟨0, c_Hb, hrB, rfl, rfl⟩)
          have hrun_loop_ret : Runs w p ω
              (.loop (.reg (16 + depth))
                (compileStmt Q (base + 1) (base + 19) (base + 21) (depth + 1) body ;;
                 compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
                 .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5] ;;
                 .assign (16 + depth) (.bin .eq (.reg 8) (.const 0))))
              st (.returned 0) st₁ (1 + (c_Hb + 1) + 1) :=
            runs_loop_iff.mpr (Or.inr (Or.inl ⟨1, 0, c_Hb + 1, hr1_eval, by omega,
              hr_seq_ret, rfl, rfl⟩))
          refine ⟨.returned 0, st₁, _, hrun_loop_ret, ?_, hhpB_lo, ?_,
            fun r hr hd => hregB r (by omega) hd, hinB_sub, hfrB,
            rfl, hu_lt, hlimB, htrieB, hinB_disj, hmemB_lt⟩
          · have hS : 1000 ≤ simScale Q := by
              dsimp only [simScale]; have := one_le_program_regBound Q; omega
            have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
            have h850 : 850 * L * w' * e.size ≤ simScale Q * L * w' * e.size :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
            have h63 : 3 + 60 * L * w' ≤ simScale Q * L * w' := by
              have h63' : 63 * (L * w') ≤ simScale Q * (L * w') := Nat.mul_le_mul_right _ (by omega)
              have h3 : 3 ≤ 3 * (L * w') := Nat.le_mul_of_pos_right 3 h1w'
              have hS' : simScale Q * (L * w') = simScale Q * L * w' := by ring
              have h60' : 60 * (L * w') = 60 * L * w' := by ring
              omega
            have hdist : simScale Q * L * w' * (e.size + c₁ + 1) =
                simScale Q * L * w' * c₁ + simScale Q * L * w' * e.size + simScale Q * L * w' := by ring
            omega
          · have hle : c₁ ≤ e.size + c₁ + 1 := by omega
            have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) hle
            omega
        | normal =>
          simp only [hbody_exec] at he_loop
          cases hnext_exec : exec w' Q (fun _ => false) fuel (.loop e body) gst₁ with
          | none => simp [hnext_exec] at he_loop
          | some res₂ =>
            rcases res₂ with ⟨o₂, gst₂, c₂⟩
            simp only [hnext_exec, Option.some.injEq, Prod.mk.injEq] at he_loop
            rcases he_loop with ⟨rfl, rfl, rfl⟩
            have hc2_pos : 1 ≤ c₂ := exec_cost_pos hnext_exec
            have hbody_post := h_stmt fuel (Nat.lt_succ_self fuel) body (depth + 1)
              ctrl framePtr retDst st gst .normal gst₁ c₁ hbody_exec hbody_rb hbody_td hinv
              (by
                have hle : c₁ ≤ e.size + c₁ + c₂ + 1 := by omega
                have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) hle
                omega)
            rcases hbody_post with ⟨o_Hb, st₁, c_Hb, hrB, hcB, hhpB_lo, hhpB_hi, hregB, hinB_sub, hfrB, rfl, hinv₁⟩
            cases hf_next : fuel with
            | zero => simp [hf_next, exec] at hnext_exec
            | succ fuel' =>
              have hnext_copy := hnext_exec
              rw [hf_next] at hnext_copy
              simp only [exec] at hnext_copy
              cases he1 : e.eval w' gst₁ with
              | none => simp [he1] at hnext_copy
              | some v₁ =>
                have hheap₁ : st₁.mem (ctrl + 1) + simScale Q * L * 2 ^ h * (e.size + 1) < 2 ^ w := by
                  have h1_c2 : e.size + 1 ≤ c₂ := by
                    simp only [he1] at hnext_copy
                    by_cases hv1 : v₁ = 0
                    · simp only [hv1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hnext_copy
                      omega
                    · simp only [hv1, ↓reduceIte] at hnext_copy
                      cases hb' : exec w' Q (fun _ => false) fuel' body gst₁ with
                      | none => simp [hb'] at hnext_copy
                      | some resb =>
                        rcases resb with ⟨ob, gstb, cb⟩
                        cases ob with
                        | returned ub =>
                          simp only [hb', Option.some.injEq, Prod.mk.injEq] at hnext_copy; omega
                        | normal =>
                          simp only [hb'] at hnext_copy
                          cases hl' : exec w' Q (fun _ => false) fuel' (.loop e body) gstb with
                          | none => simp [hl'] at hnext_copy
                          | some resl =>
                            rcases resl with ⟨ol, gstl, cl⟩
                            simp only [hl', Option.some.injEq, Prod.mk.injEq] at hnext_copy; omega
                  have hle1 : simScale Q * L * 2 ^ h * (e.size + 1) ≤ simScale Q * L * 2 ^ h * c₂ :=
                    Nat.mul_le_mul_left _ h1_c2
                  have hle2 : simScale Q * L * 2 ^ h * c₁ + simScale Q * L * 2 ^ h * c₂ ≤
                      simScale Q * L * 2 ^ h * (e.size + c₁ + c₂ + 1) := by
                    have : simScale Q * L * 2 ^ h * (e.size + c₁ + c₂ + 1) =
                        simScale Q * L * 2 ^ h * c₁ + simScale Q * L * 2 ^ h * c₂ +
                        simScale Q * L * 2 ^ h * (e.size + 1) := by ring
                    omega
                  omega
                obtain ⟨st₂, c_ev, hr_ev, hreg_ev, hrFlag₂, hinv₂, hmem_ev, hc_ev⟩ :=
                  evalE_runs (depth := depth) hComp hL1 hh hw2 hw'1 hw'_lh hinv₁ hheap₁ he1 he_rb he_td
                have hhp₂_eq : st₂.mem (ctrl + 1) = st₁.mem (ctrl + 1) :=
                  hmem_ev (ctrl + 1) (Or.inl (by have := hinv₁.ctrl_lt_frame; omega))
                have hctrl₂_eq : st₂.mem ctrl = st₁.mem ctrl :=
                  hmem_ev ctrl (Or.inl (by have := hinv₁.ctrl_lt_frame; omega))
                have hheap₂ : st₂.mem (ctrl + 1) + simScale Q * L * 2 ^ h * c₂ < 2 ^ w := by
                  have hdist : simScale Q * L * 2 ^ h * (e.size + c₁ + c₂ + 1) =
                      simScale Q * L * 2 ^ h * c₁ + simScale Q * L * 2 ^ h * c₂ +
                      simScale Q * L * 2 ^ h * (e.size + 1) := by ring
                  rw [hhp₂_eq]
                  omega
                obtain ⟨o_H2, st₃, c_L2, hrL2, hcL2, hhp3_lo, hhp3_hi, hreg3, hin3_sub, hfr3, hout3⟩ :=
                  ih_loop (fun f hf => h_stmt f (Nat.lt_succ_of_lt hf)) e body depth ctrl framePtr retDst
                    st₂ gst₁ o₂ gst₂ c₂ v₁ hnext_exec he1 he_rb hbody_rb he_td hbody_td hinv₂ hrFlag₂ hheap₂
                have hr_body_ev : Runs w p ω
                    (compileStmt Q (base + 1) (base + 19) (base + 21) (depth + 1) body ;;
                     compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
                     .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5] ;;
                     .assign (16 + depth) (.bin .eq (.reg 8) (.const 0)))
                    st .normal st₂ (c_Hb + c_ev + 1) :=
                  runs_seq_iff.mpr (Or.inr ⟨st₁, c_Hb, c_ev, hrB, hr_ev, rfl⟩)
                have hr_all : Runs w p ω
                    (.loop (.reg (16 + depth))
                      (compileStmt Q (base + 1) (base + 19) (base + 21) (depth + 1) body ;;
                       compileExpr (base + 1) (base + 19) Q.regBound (Q.regBound + 1) e ;;
                       .call 8 (base + 1 + idxIsZero) [slotAddr 2 Q.regBound, .reg 5] ;;
                       .assign (16 + depth) (.bin .eq (.reg 8) (.const 0))))
                    st o_H2 st₃ (1 + (c_Hb + c_ev + 1) + c_L2 + 1) :=
                  runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st₂, c_Hb + c_ev + 1, c_L2, hr1_eval,
                    by omega, hr_body_ev, hrL2, rfl⟩))
                have hin_ev_eq : ∀ q, InTrie st₂.mem L h L (st₂.mem ctrl) q ↔
                    InTrie st₁.mem L h L (st₁.mem ctrl) q := by
                  rw [hctrl₂_eq]
                  exact inTrie_congr_mem L (st₁.mem ctrl) fun q hq => by
                    rcases (hinv₁.inTrie_disj q hq).2.2 with hlt | hge
                    · exact hmem_ev q (Or.inl (by omega))
                    · exact hmem_ev q (Or.inr hge)
                refine ⟨o_H2, st₃, _, hr_all, ?_, by omega, ?_, ?_, ?_, ?_, hout3⟩
                · have hS : 1000 ≤ simScale Q := by
                    dsimp only [simScale]; have := one_le_program_regBound Q; omega
                  have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
                  have h850 : 850 * L * w' * e.size ≤ simScale Q * L * w' * e.size :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
                  have h55 : 3 + 55 * L * w' ≤ simScale Q * L * w' := by
                    have h100 : 58 * (L * w') ≤ simScale Q * (L * w') := Nat.mul_le_mul_right _ (by omega)
                    have h3 : 3 ≤ 3 * (L * w') := Nat.le_mul_of_pos_right 3 h1w'
                    have hS' : simScale Q * (L * w') = simScale Q * L * w' := by ring
                    have h55' : 55 * (L * w') = 55 * L * w' := by ring
                    omega
                  have hdist : simScale Q * L * w' * (e.size + c₁ + c₂ + 1) =
                      simScale Q * L * w' * c₁ + simScale Q * L * w' * c₂ +
                      simScale Q * L * w' * e.size + simScale Q * L * w' := by ring
                  omega
                · have hdist : simScale Q * L * 2 ^ h * (e.size + c₁ + c₂ + 1) =
                      simScale Q * L * 2 ^ h * c₁ + simScale Q * L * 2 ^ h * c₂ +
                      simScale Q * L * 2 ^ h * (e.size + 1) := by ring
                  omega
                · intro r hr hd
                  rw [hreg3 r hr hd, hreg_ev r hr hd, hregB r (by omega) hd]
                · intro q hq
                  rcases hin3_sub q hq with hq2 | ⟨hlo, hhi⟩
                  · rw [hin_ev_eq] at hq2
                    rcases hinB_sub q hq2 with hq0 | ⟨hlo0, hhi0⟩
                    · exact Or.inl hq0
                    · exact Or.inr ⟨hlo0, by omega⟩
                  · exact Or.inr ⟨by omega, hhi⟩
                · intro q hq hqc0 hqc1 hqi hqr hqf
                  have hq1 : q < st₁.mem (ctrl + 1) := by omega
                  have hqi1 : ¬ InTrie st₁.mem L h L (st₁.mem ctrl) q := by
                    intro hqt
                    rcases hinB_sub q hqt with hqt0 | ⟨hlo, _⟩
                    · exact hqi hqt0
                    · omega
                  rw [hfr3 q (by omega) hqc0 hqc1 (by rwa [hin_ev_eq]) hqr hqf]
                  rw [hmem_ev q (by
                    rcases hqf with hlt | hge
                    · exact Or.inl (by omega)
                    · exact Or.inr hge)]
                  exact hfrB q hq hqc0 hqc1 hqi hqr hqf

end MinCostFlow.WideWord
