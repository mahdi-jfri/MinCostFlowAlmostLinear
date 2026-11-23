module

public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutPass2
public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutPass3

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-Edge Walk Shortcutting (`DynSpannerShortcutEdge`)

Composes Passes 1–3 (`DynSpannerShortcutPasses`, `DynSpannerShortcutPass2`,
`DynSpannerShortcutPass3`) into `dsShortcutEdge_triple` for `dsShortcutEdgeStmt`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

lemma dsVStampBase_le_fixed (b L vCap eCap : ℕ) :
    dsVStampBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]
  omega

lemma dsVStampBase_chain (b L vCap eCap : ℕ) :
    let d := dynGraphSize vCap eCap
    let m := b + dsHdrSize + 3 * d
    let dom := m + (3 * eCap + 2 * (L + 1))
    let rg := dom + ((L + 1) + 2 * ((L + 1) * eCap))
    let vs := rg + (3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap))
    vs = dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
  have hm := dsMinHBase_eq b vCap eCap
  have hdom := dsDomGenBase_eq b L vCap eCap
  have hrg := dsRevGenBase_eq b L vCap eCap
  have hrh := dsRevHeadBase_eq b L vCap eCap
  have hvs := dsVStampBase_eq b L vCap eCap
  have hle := dsVStampBase_le_fixed b L vCap eCap
  exact ⟨by omega, by omega⟩

private lemma mWalkAt_head_eq {mem : ℕ → ℕ} {ptr : ℕ} {P : List (ℕ × Bool)}
    (hMW : MWalkAt mem ptr P) : mem ptr = P.length := by
  have h0 := hMW 0 (by rw [mWalkEncode_length]; omega)
  simpa [mWalkEncode] using h0

private lemma isWalk_edges_lt_2pow {w gPtr vCapG eCapG u vEnd : ℕ}
    {mem : ℕ → ℕ} {G : MGraph} {P : List (ℕ × Bool)}
    (hg_w : gPtr + dynGraphSize vCapG eCapG < 2 ^ w)
    (hG : DynGraphAt mem gPtr vCapG eCapG G)
    (hG_val : G.IsValid) (hu : u ∈ G.V) (hW : G.IsWalk u vEnd P) :
    ∀ x ∈ P, x.1 < 2 ^ w := fun x hx => by
  have he : x.1 ∈ G.E := (isWalk_mem_V_tail_head hG_val hu hW x hx).1
  have he_cap : x.1 < eCapG := hG.2.2.1 x.1 he
  dsimp [dynGraphSize] at hg_w
  omega

/-- Single outer iteration verifying `dsShortcutEdgeStmt` on edge `e` (`args` in `r0..r8`). -/
theorem dsShortcutEdge_triple {w L vCap eCap b vCapG eCapG eCapEmb
    gPtr eListPtr mEmbPtr heapPtr permPtr heapMax gen0 stampVal k e : ℕ}
    {G : MGraph} {eL : List ℕ} {P : List (ℕ × Bool)} {p : Program} {bOps : ℕ}
    {mem0 regs0 : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hhp_perm : heapPtr ≤ permPtr)
    (hperm_hi : permPtr + 7 * (P.length + 1) ≤ heapMax)
    (hmax_w : heapMax < 2 ^ w)
    (hg_w : gPtr + dynGraphSize vCapG eCapG < 2 ^ w)
    (heL_w : eListPtr + eL.length < 2 ^ w)
    (hm_w : mEmbPtr + eCapEmb < 2 ^ w)
    (hk : k < eL.length)
    (hgen_lt : gen0 < stampVal)
    (hm_disj : ∀ e' < eCapEmb,
      (∀ v < vCap, mEmbPtr + e' ≠ dsVStampBase b L vCap eCap + v) ∧
      (mEmbPtr + e' < heapPtr ∨ heapMax ≤ mEmbPtr + e'))
    (hG_disj : ∀ i < dynGraphSize vCapG eCapG,
      dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr heapMax (gPtr + i))
    (he_mem_L : mem0 (eListPtr + k) = e)
    (heG : e ∈ G.E) (he_cap : e < eCapEmb)
    (hWalk : G.IsWalk (G.tail e) (G.head e) P)
    (hMW : MWalkAt mem0 (mem0 (mEmbPtr + e)) P)
    (hwPtr_w : mem0 (mEmbPtr + e) + 1 + 2 * P.length < 2 ^ w)
    (hW_disj : ∀ addr, mem0 (mEmbPtr + e) ≤ addr →
      addr < mem0 (mEmbPtr + e) + 1 + 2 * P.length →
      dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr heapMax addr)
    (hG : DynGraphAt mem0 gPtr vCapG eCapG G)
    (hG_val : G.IsValid)
    (hvG : ∀ v ∈ G.V, v < vCap)
    (hV_init : ∀ v < vCap, mem0 (dsVStampBase b L vCap eCap + v) ≤ gen0)
    (hregs : regs0 0 = b ∧ regs0 1 = gPtr ∧ regs0 2 = eListPtr ∧ regs0 3 = eL.length ∧
      regs0 4 = mEmbPtr ∧ regs0 5 = permPtr ∧
      regs0 6 = dsVStampBase b L vCap eCap ∧ regs0 7 = stampVal ∧ regs0 8 = k) :
    let vStampPtr := dsVStampBase b L vCap eCap
    let Q₀ := shortcutWalk G (G.tail e) P
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs = regs0)
      (dsShortcutEdgeStmt bOps)
      (normalPost fun st' => ∃ outWalkPtr,
        permPtr ≤ outWalkPtr ∧
        outWalkPtr + 1 + 2 * Q₀.length ≤ permPtr + 7 * (P.length + 1) ∧
        st'.regs 5 = outWalkPtr + 1 + 2 * Q₀.length ∧
        (∀ r, (r ≤ 4 ∨ (6 ≤ r ∧ r ≤ 8)) → st'.regs r = regs0 r) ∧
        st'.mem (mEmbPtr + e) = outWalkPtr ∧
        MWalkAt st'.mem outWalkPtr Q₀ ∧
        (∀ v < vCap, st'.mem (vStampPtr + v) ≤ gen0) ∧
        ∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) → addr ≠ mEmbPtr + e →
          (addr < permPtr ∨ outWalkPtr + 1 + 2 * Q₀.length ≤ addr) →
          st'.mem addr = mem0 addr)
      (fun _ => 390 * P.length + 291) := by
  intro vStampPtr Q₀ st ω ⟨hm0, hr0⟩
  subst hm0
  subst hr0
  rcases hregs with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩
  set wPtr := st.mem (mEmbPtr + e)
  set u := G.tail e
  set vEnd := G.head e
  have hu : u ∈ G.V := (hG_val e heG).1
  have hvEnd : vEnd ∈ G.V := (hG_val e heG).2
  have hvst_lt_heap : ∀ v < vCap, vStampPtr + v < heapPtr := fun v hv => by
    have hle := dsVStampBase_le_fixed b L vCap eCap; omega
  have hvst_perm : ∀ v < vCap, vStampPtr + v < permPtr := fun v hv =>
    lt_of_lt_of_le (hvst_lt_heap v hv) hhp_perm
  have hvst_w : vStampPtr + vCap < 2 ^ w := by
    have hle := dsVStampBase_le_fixed b L vCap eCap; omega
  have hQ_len_le : Q₀.length ≤ P.length := shortcutWalk_length_le G P u
  have heL_k_w : eListPtr + k < 2 ^ w := by omega
  have hm_e_w : mEmbPtr + e < 2 ^ w := by omega
  have hwPtr_w' : wPtr < 2 ^ w := by omega
  have hperm_w : permPtr + P.length + 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [dsShortcutEdgeStmt]
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (x := eListPtr + k)
      (by simp [Expr.eval, BinOp.eval, hr2, hr8, heL_k_w]) he_mem_L) ?_
  refine runs_seq_assign_le (v := wPtr)
    (Expr.eval_load_of_eq (x := mEmbPtr + e)
      (by simp [Expr.eval, BinOp.eval, hr4, hm_e_w]) rfl) ?_
  refine runs_seq_assign_le (v := P.length)
    (Expr.eval_load_of_eq (x := wPtr) (by simp [Expr.eval]) (mWalkAt_head_eq hMW)) ?_
  have hargs_ev : evalArgs w { st with regs := Function.update (Function.update
      (Function.update st.regs 9 e) 10 wPtr) 11 P.length } [.reg 1, .reg 9] =
      some [gPtr, e] := by
    simp [evalArgs, Expr.eval, hr1]
  have he_lt_w : e < 2 ^ w := by
    have he_capG : e < eCapG := hG.2.2.1 e heG
    dsimp [dynGraphSize] at hg_w; omega
  have hgPtr_w : gPtr < 2 ^ w := by dsimp [dynGraphSize] at hg_w; omega
  refine runs_seq_call_le (dgGetTail_meetsContract hpOps (w := w) (vCap := vCapG) (eCap := eCapG)
    (G := G)) hargs_ev
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> assumption)
    ⟨gPtr, e, rfl, hw16, hg_w, heG, hG⟩ ?_
  intro v_tail mem_c pos_c hpost_tail
  rcases hpost_tail with ⟨gPtr', e', hargs_eq, rfl, rfl⟩
  simp only [List.cons.injEq, and_true] at hargs_eq
  obtain ⟨_, he_eq⟩ := hargs_eq
  have htail : G.tail e' = u := by rw [← he_eq]
  refine runs_seq_store_le (x := permPtr) (v := u)
    (by simp [Expr.eval, hr5]) (Expr.eval_reg_of_eq (by simp [htail])) ?_
  let regs1 := Function.update (Function.update (Function.update
    (Function.update st.regs 9 e) 10 wPtr) 11 P.length) 12 u
  let mem1 := Function.update st.mem permPtr u
  have hG1 : DynGraphAt mem1 gPtr vCapG eCapG G :=
    hG.of_agree fun a ha1 ha2 => by
      have ha_diff : a - gPtr < dynGraphSize vCapG eCapG := by omega
      have hfc := hG_disj (a - gPtr) ha_diff
      rw [Nat.add_sub_of_le ha1] at hfc
      have hne : a ≠ permPtr := by rcases hfc.2.2 with h | h <;> omega
      dsimp only [mem1]; exact Function.update_of_ne hne _ _
  have hMW1 : MWalkAt mem1 wPtr P := hMW.of_agree fun a ha1 ha2 => by
    have hfc := hW_disj a ha1 ha2
    have hne : a ≠ permPtr := by rcases hfc.2.2 with h | h <;> omega
    dsimp only [mem1]; exact Function.update_of_ne hne _ _
  refine runs_seq_triple_le (Q₁ := Pass1Inv permPtr G u P mem1 regs1 P.length)
    (shortcut_pass1_triple (p := p) (bOps := bOps) (vCapG := vCapG) (eCapG := eCapG)
      hpOps hw16 hg_w hwPtr_w hperm_w (by simp [regs1, hr1]) (by simp [regs1, hr5])
      (by simp [regs1]) (by simp [regs1]) hG_val hu hWalk hG1 hMW1 (Function.update_self _ _ _)
      (fun a ha1 ha2 => by
        have hfc := hG_disj (a - gPtr) (by omega)
        rw [Nat.add_sub_of_le ha1] at hfc
        rcases hfc.2.2 with h | h <;> [left; right] <;> omega)
      (fun a ha1 ha2 => by
        have hfc := hW_disj a ha1 ha2
        rcases hfc.2.2 with h | h <;> [left; right] <;> omega))
    ⟨rfl, fun r _ => by dsimp only [regs1, u]; rw [← he_eq]⟩ ?_
  intro stP1 hP1
  rcases hP1 with ⟨hr13_P1, hr_P1, harr_P1, hfr_P1⟩
  have hr5_P1 : stP1.regs 5 = permPtr := (hr_P1 5 (by omega)).trans (by simp [regs1, hr5])
  have hr6_P1 : stP1.regs 6 = vStampPtr :=
    (hr_P1 6 (by omega)).trans (by simp [regs1, hr6, vStampPtr])
  have hr7_P1 : stP1.regs 7 = stampVal := (hr_P1 7 (by omega)).trans (by simp [regs1, hr7])
  have hr11_P1 : stP1.regs 11 = P.length := (hr_P1 11 (by omega)).trans (by simp [regs1])
  have hvEnd_eq : stP1.mem (permPtr + P.length) = vEnd := by
    rw [harr_P1 P.length le_rfl, vertAt_length_eq_of_isWalk hWalk]
  have hvEnd_lt : vEnd < vCap := hvG vEnd hvEnd
  have hvst_end_w : vStampPtr + vEnd < 2 ^ w := by omega
  refine runs_seq_assign_le (v := vEnd)
    (Expr.eval_load_of_eq (x := permPtr + P.length)
      (by simp [Expr.eval, BinOp.eval, hr5_P1, hr11_P1, show permPtr + P.length < 2 ^ w by omega])
      hvEnd_eq) ?_
  refine runs_seq_store_le (x := vStampPtr + vEnd) (v := stampVal)
    (by simp [Expr.eval, BinOp.eval, hr6_P1, hvst_end_w])
    (Expr.eval_reg_of_eq (by simp [hr7_P1])) ?_
  let nodeBase := permPtr + P.length + 1
  have hnb_w : nodeBase < 2 ^ w := hperm_w
  refine runs_seq_assign_le (v := nodeBase)
    (by simp [Expr.eval, BinOp.eval, hr5_P1, hr11_P1,
      show (1 : ℕ) < 2 ^ w by omega,
      show permPtr + P.length < 2 ^ w by omega, hperm_w, nodeBase]) ?_
  refine runs_seq_assign_le (v := nodeBase) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let mem2 := Function.update stP1.mem (vStampPtr + vEnd) stampVal
  let regs2 := Function.update (Function.update (Function.update
    (Function.update stP1.regs 19 vEnd) 16 nodeBase) 17 nodeBase) 18 0
  let st2 : State := { stP1 with mem := mem2, regs := regs2 }
  have hmem2_fr : ∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) →
      (addr < permPtr ∨ permPtr + P.length + 1 ≤ addr) → mem2 addr = st.mem addr := fun a hav har => by
    dsimp only [mem2]
    rw [Function.update_of_ne (hav vEnd hvEnd_lt)]
    rcases har with h | h
    · rw [hfr_P1 a (Or.inl (by omega))]; dsimp only [mem1]; rw [Function.update_of_ne (by omega)]
    · rw [hfr_P1 a (Or.inr h)]; dsimp only [mem1]; rw [Function.update_of_ne (by omega)]
  have hVarr2 : ∀ i ≤ P.length, mem2 (permPtr + i) = vertAt G u P i := fun i hi => by
    dsimp only [mem2]
    rw [Function.update_of_ne (by have := hvst_perm vEnd hvEnd_lt; omega)]
    exact harr_P1 i hi
  have hMW2 : MWalkAt mem2 wPtr P := hMW.of_agree fun a ha1 ha2 => by
    have hfc := hW_disj a ha1 ha2
    exact hmem2_fr a hfc.1 (by rcases hfc.2.2 with h | h <;> [left; right] <;> omega)
  have hvEnd_stamp2 : VStampInv mem2 vStampPtr vCap stampVal gen0 [vEnd] := fun v hv => by
    dsimp only [mem2]
    by_cases hve : v = vEnd
    · subst hve
      exact ⟨fun _ => Function.update_self _ _ _, fun hnot => by simp at hnot⟩
    · have hne : vStampPtr + v ≠ vStampPtr + vEnd := by omega
      constructor
      · intro hmemv; simp at hmemv; exact False.elim (hve hmemv)
      · intro _
        rw [Function.update_of_ne hne, hfr_P1 _ (Or.inl (lt_trans (hvst_perm v hv) (Nat.lt_succ_self _)))]
        dsimp only [mem1]
        rw [Function.update_of_ne (by have := hvst_perm v hv; omega)]
        exact hV_init v hv
  have hpass2_pre : st2.mem = mem2 ∧
      (∀ r, (r ≤ 11 ∨ r = 16 ∨ r = 19) → st2.regs r = regs2 r) ∧
      st2.regs 17 = nodeBase ∧ st2.regs 18 = 0 :=
    ⟨rfl, fun _ _ => rfl, by simp [st2, regs2], by simp [st2, regs2]⟩
  refine runs_seq_triple_le (Q₁ := Pass2Inv vCap vStampPtr stampVal gen0 nodeBase vEnd G u P
      mem2 regs2 P.length)
    (shortcut_pass2_triple (p := p) hw16 rfl (by omega) (by omega)
      (fun v hv => lt_trans (hvst_perm v hv) (by dsimp [nodeBase]; omega)) hvst_perm hvst_w
      hwPtr_w hgen_lt (isWalk_edges_lt_2pow hg_w hG hG_val hu hWalk) hG_val hvG hu hWalk
      hVarr2 hMW2
      (fun a ha1 ha2 => by
        have hfc := hW_disj a ha1 ha2
        exact ⟨hfc.1, by rcases hfc.2.2 with h | h <;> [left; right] <;> omega⟩)
      (by simp [regs2, hr5_P1]) (by simp [regs2, hr6_P1]) (by simp [regs2, hr7_P1])
      (by simp [regs2]; exact (hr_P1 10 (by omega)).trans (by simp [regs1]))
      (by simp [regs2, hr11_P1]) hvEnd_stamp2)
    hpass2_pre ?_
  intro stP2 hP2
  rcases hP2 with ⟨nodePtr, hr13_P2, hr17_P2, hnp_lo, hnp_hi, hr_P2, _, hW_P2, hNd_P2,
    hSt_P2, hV_P2, hm_P2⟩
  simp only [Nat.sub_self, List.drop_zero, vertAt_zero] at hW_P2 hNd_P2 hSt_P2 hV_P2
  have hr4_P2 : stP2.regs 4 = mEmbPtr := by
    rw [hr_P2 4 (Or.inl (by omega))]; simp [regs2, hr_P1 4 (by omega), regs1, hr4]
  have hr6_P2 : stP2.regs 6 = vStampPtr := by
    rw [hr_P2 6 (Or.inl (by omega))]; simp [regs2, hr6_P1]
  have hr9_P2 : stP2.regs 9 = e := by
    rw [hr_P2 9 (Or.inl (by omega))]; simp [regs2, hr_P1 9 (by omega), regs1]
  have hr19_P2 : stP2.regs 19 = vEnd := by
    rw [hr_P2 19 (Or.inr (Or.inr rfl))]; simp [regs2]
  have hout_ub : nodePtr + 1 + 2 * Q₀.length ≤ permPtr + 7 * (P.length + 1) := by
    dsimp only [nodeBase] at hnp_hi; omega
  have hout_w : nodePtr + 1 + 2 * Q₀.length < 2 ^ w := by omega
  have hm_out : mEmbPtr + e < nodePtr ∨ nodePtr + 1 + 2 * Q₀.length ≤ mEmbPtr + e := by
    rcases (hm_disj e he_cap).2 with h | h
    · left; dsimp only [nodeBase] at hnp_lo; omega
    · right; omega
  have hnb1 : 1 ≤ nodeBase := by dsimp [nodeBase]; omega
  obtain ⟨oF, stF, cF, hrunF, hqF, hcF⟩ :=
    shortcut_pass3_triple (p := p) (nodeBase := nodeBase) hw16 hnb1
      (fun v hv => lt_trans (hvst_perm v hv) (by dsimp [nodeBase]; omega))
      hvst_w hnp_lo hout_w hm_w he_cap
      (hm_disj e he_cap).1 hm_out hG_val hvG hu hvEnd hW_P2 hNd_P2 hSt_P2 hV_P2
      hr4_P2 hr6_P2 hr9_P2 hr17_P2 hr19_P2 stP2 ω ⟨rfl, rfl⟩
  cases oF with
  | returned _ => exact False.elim hqF
  | normal =>
    rcases hqF with ⟨hr5_F, hr_F, hm_e_F, hMW_F, hV_F, hfr_F⟩
    refine ⟨.normal, stF, cF, hrunF, ?_, ?_⟩
    · refine ⟨nodePtr, by dsimp only [nodeBase] at hnp_lo; omega, hout_ub, hr5_F, ?_,
        hm_e_F, hMW_F, hV_F, ?_⟩
      · intro r hrr
        have hrr3 : r ≤ 4 ∨ (6 ≤ r ∧ r ≤ 8) ∨ r = 16 := by
          rcases hrr with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        rw [hr_F r hrr3]
        have hrr2 : r ≤ 11 ∨ r = 16 ∨ r = 19 := by
          rcases hrr with h | h
          · exact Or.inl (by omega)
          · exact Or.inl (by omega)
        rw [hr_P2 r hrr2]
        have hrn19 : r ≠ 19 := by rcases hrr with h | h <;> omega
        have hrn16 : r ≠ 16 := by rcases hrr with h | h <;> omega
        have hrn17 : r ≠ 17 := by rcases hrr with h | h <;> omega
        have hrn18 : r ≠ 18 := by rcases hrr with h | h <;> omega
        dsimp only [regs2]
        rw [Function.update_of_ne hrn18, Function.update_of_ne hrn17,
          Function.update_of_ne hrn16, Function.update_of_ne hrn19,
          hr_P1 r (by rcases hrr with h | h <;> omega)]
        dsimp only [regs1]
        have hr12 : r ≠ 12 := by rcases hrr with h | h <;> omega
        have hr11 : r ≠ 11 := by rcases hrr with h | h <;> omega
        have hr10 : r ≠ 10 := by rcases hrr with h | h <;> omega
        have hr9 : r ≠ 9 := by rcases hrr with h | h <;> omega
        rw [Function.update_of_ne hr12, Function.update_of_ne hr11,
          Function.update_of_ne hr10, Function.update_of_ne hr9]
      · intro addr ha_vst ha_m ha_rng
        have ha_p3 : addr < nodePtr ∨ nodePtr + 1 + 2 * Q₀.length ≤ addr := by
          rcases ha_rng with h | h
          · left; dsimp only [nodeBase] at hnp_lo; omega
          · exact Or.inr h
        rw [hfr_F addr ha_vst ha_m ha_p3]
        by_cases ha_p2 : addr < nodeBase ∨ nodePtr ≤ addr
        · rw [hm_P2 addr ha_vst ha_p2]
          exact hmem2_fr addr ha_vst (by
            rcases ha_rng with h | h
            · exact Or.inl h
            · right; dsimp only [nodeBase] at hnp_lo; omega)
        · push Not at ha_p2
          exfalso
          rcases ha_rng with h | h
          · dsimp only [nodeBase] at ha_p2; omega
          · omega
    · dsimp only [argsSize, dgGetTailContract, Expr.size] at hcF ⊢
      omega

end

end MinCostFlow.DynSpanner.Program
