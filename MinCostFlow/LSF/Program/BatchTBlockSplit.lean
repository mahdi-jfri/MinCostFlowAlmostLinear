module

public import MinCostFlow.LSF.Program.BatchTBlockSplitPost
import Mathlib.Tactic.Linarith

/-!
# `T`-Block Vertex Split Verification (`BatchTBlockSplit`)

Proves `lsfTBlockSplit_meetsContract` (`Lemma 5.4`, Appendix A.1, `arXiv:2309.16629v1` page 48),
preserving `TBlockAt` in `O(kt + kh + 1)` time across canonical vertex splits.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Main verification of `lsfTBlockSplitProc`. -/
theorem lsfTBlockSplit_meetsContract {w idx idxDgAddV idxDgMoveLoop vCap eCap tM : ℕ}
    {p : Program} {G T_cur T₀ : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    {v v' : ℕ} {St Sh : Finset ℕ} {len : ℕ}
    (hp : p.procs[idx]? = some (lsfTBlockSplitProc idxDgAddV idxDgMoveLoop))
    (hDgAddV : ∀ H, MeetsContract w p idxDgAddV (dgAddVertexContract w vCap (2 * tM + 1) H))
    (hDgMoveLoop : ∀ E slotT slotH L isHead, MeetsContract w p idxDgMoveLoop
      (dgMoveSlotLoopContract w vCap (2 * tM + 1) E slotT slotH L isHead)) :
    MeetsContract w p idx
      (lsfTBlockSplitContract w vCap eCap tM G T_cur T₀ π tOrigList v v' St Sh len) := by
  classical
  intro args mem pos ω _ hpre
  rcases hpre with ⟨tPtr, updPtr, rfl, hw16, hbound, hupd_lt, hdisj_upd, hupd_word,
    hGval, heG_lt, hval_sp, hv'_lt, hcan_t, hcan_h, hUpdAt, hTval, hTV, hTE, hT⟩
  have hT_copy := hT
  rcases hT with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hLO, hLPi, hidx1, hidx2,
    dgT, hdgT, hdgTV, hdgTE, htrack⟩
  rcases hval_sp with ⟨hvG, hv'G, _, _⟩
  have hUpdAt_cases : ∃ tag Lt Lh,
      Lt.Nodup ∧ Lh.Nodup ∧ len = 5 + Lt.length + Lh.length ∧
      ListAt mem updPtr ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) ∧
      ((tag = 2 ∧ (∀ e, e ∈ Lt ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∈ St) ∧
          (∀ e, e ∈ Lh ↔ e ∈ G.E ∧ G.head e = v ∧ e ∈ Sh)) ∨
       (tag = 3 ∧ (∀ e, e ∈ Lt ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∉ St) ∧
          (∀ e, e ∈ Lh ↔ e ∈ G.E ∧ G.head e = v ∧ e ∉ Sh))) := by
    rcases hUpdAt with ⟨Lt, Lh, h1', h2', h3', h4', h5', h6'⟩ | ⟨Lt, Lh, h1', h2', h3', h4', h5', h6'⟩
    · exact ⟨2, Lt, Lh, h1', h2', h5', h6', Or.inl ⟨rfl, h3', h4'⟩⟩
    · exact ⟨3, Lt, Lh, h1', h2', h5', h6', Or.inr ⟨rfl, h3', h4'⟩⟩
  rcases hUpdAt_cases with ⟨tag, Lt, Lh, hLt_nd, hLh_nd, hlen_eq, hLA, htag_iff⟩
  set kt := Lt.length; set kh := Lh.length
  have hdgT_lt : tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) < 2 ^ w := by
    dsimp [tDgTPtr, tBlockSize] at hbound ⊢; omega
  have hidx_lt : tIdxOfEdgeBase tPtr vCap tM + eCap < 2 ^ w := by
    dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize] at hbound ⊢; omega
  have hscr_lt : tSplitScratchBase tPtr vCap eCap tM + (2 * tM + 4) < 2 ^ w := by
    dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase,
      tDgTPtr, tBlockSize] at hbound ⊢; omega
  have htPtr_ltw : tPtr + tHdrSize < 2 ^ w := by dsimp [tBlockSize] at hbound; omega
  have hmem_upd : ∀ i (hi : i < 5), mem (updPtr + i) = ([tag, v, v', kt, kh] : List ℕ)[i]'(by simp; omega) := by
    intro i hi
    have hi' : i < ([tag, v, v', kt, kh] ++ Lt ++ Lh).length := by simp [kt, kh]; omega
    have h := hLA i hi'
    simp only [List.append_assoc] at hi' h
    rw [List.getElem_append_left (by simp; omega)] at h
    exact h
  have htag_m : mem updPtr = tag := by simpa using hmem_upd 0 (by decide)
  have hv_m : mem (updPtr + 1) = v := hmem_upd 1 (by decide)
  have hv'_m : mem (updPtr + 2) = v' := hmem_upd 2 (by decide)
  have hkt_m : mem (updPtr + 3) = kt := hmem_upd 3 (by decide)
  have hkh_m : mem (updPtr + 4) = kh := hmem_upd 4 (by decide)
  have hLt_at : ListAt mem (updPtr + 5) Lt := fun i hi => by
    have hi' : 5 + i < ([tag, v, v', kt, kh] ++ Lt ++ Lh).length := by simp [kt, kh]; omega
    have h := hLA (5 + i) hi'
    rw [← Nat.add_assoc] at h
    simp only [List.append_assoc] at hi' h
    rw [List.getElem_append_right (by simp), List.getElem_append_left (by simp; omega)] at h
    simpa using h
  have hLh_at : ListAt mem (updPtr + 5 + kt) Lh := fun i hi => by
    have hi' : 5 + kt + i < ([tag, v, v', kt, kh] ++ Lt ++ Lh).length := by simp [kt, kh]; omega
    have h := hLA (5 + kt + i) hi'
    rw [← Nat.add_assoc, ← Nat.add_assoc] at h
    rw [List.getElem_append_right (by simp [kt]; omega)] at h
    have hsub : 5 + kt + i - ([tag, v, v', kt, kh] ++ Lt).length = i := by simp [kt]; omega
    exact h.trans (by congr 1)
  have hLt_word : ∀ x ∈ Lt, x < 2 ^ w := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have h := hupd_word (5 + i) (by omega)
    rw [← Nat.add_assoc] at h
    rwa [← hLt_at i hi]
  have hLh_word : ∀ x ∈ Lh, x < 2 ^ w := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have h := hupd_word (5 + kt + i) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at h
    rwa [← hLh_at i hi]
  have hidx_bd : ∀ e < eCap, mem (tIdxOfEdgeBase tPtr vCap tM + e) ≤ tM := by
    intro e he
    by_cases h0' : mem (tIdxOfEdgeBase tPtr vCap tM + e) = 0
    · omega
    · obtain ⟨i, hi, _, hm⟩ := hidx2 e he h0'; omega
  set L1 := scanTrackList mem (tIdxOfEdgeBase tPtr vCap tM) eCap false Lt
  set L2 := scanTrackList mem (tIdxOfEdgeBase tPtr vCap tM) eCap true Lh
  set L_tr := L1 ++ L2
  have hL1_p := scanTrackList_nodup_and_bounds hlen hLt_nd hidx2 (isHead := false)
  have hL2_p := scanTrackList_nodup_and_bounds hlen hLh_nd hidx2 (isHead := true)
  have hL1_len_kt : L1.length ≤ kt := scanTrackList_length_le _ _ _ _ _
  have hL2_len_kh : L2.length ≤ kh := scanTrackList_length_le _ _ _ _ _
  have hLtr_len : L_tr.length ≤ 2 * tM := by
    have h1 : L1.length ≤ tM := hL1_p.2.1
    have h2 : L2.length ≤ tM := hL2_p.2.1
    simp [L_tr]; omega
  have hLtr_word : ∀ x ∈ L_tr, x < 2 ^ w := by
    intro x hx; simp only [L_tr, List.mem_append] at hx
    rcases hx with h | h
    · have := (hL1_p.2.2.1 x h).1; omega
    · have := (hL2_p.2.2.1 x h).1; omega
  have hdisj_scr_upd : ∀ i < len, ∀ q < 2 * tM, updPtr + i ≠ tSplitScratchBase tPtr vCap eCap tM + q := by
    intro i hi q hq
    have hd := hdisj_upd i hi
    dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase,
      tDgTPtr, tBlockSize] at hd ⊢; omega
  have hdisj_scr_idx : ∀ e < eCap, ∀ q < 2 * tM, tIdxOfEdgeBase tPtr vCap tM + e ≠ tSplitScratchBase tPtr vCap eCap tM + q := by
    intro e he q hq; dsimp [tSplitScratchBase]; omega
  have hscr_disj_dgT : ∀ q < 2 * tM,
      tSplitScratchBase tPtr vCap eCap tM + q < tDgTPtr tPtr ∨
      tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) ≤ tSplitScratchBase tPtr vCap eCap tM + q := by
    intro q _; right
    dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase]; omega
  have hst0 : (startState [tPtr, updPtr, vCap, eCap, tM] mem pos).regs 0 = tPtr ∧
      (startState [tPtr, updPtr, vCap, eCap, tM] mem pos).regs 1 = updPtr ∧
      (startState [tPtr, updPtr, vCap, eCap, tM] mem pos).regs 2 = vCap ∧
      (startState [tPtr, updPtr, vCap, eCap, tM] mem pos).regs 3 = eCap := by
    simp [startState]
  rcases hst0 with ⟨hr0, hr1, hr2, hr3⟩
  have htag_ltw : tag < 2 ^ w := by rw [← htag_m]; exact hupd_word 0 (by omega)
  have hv_ltw : v < 2 ^ w := by rw [← hv_m]; exact hupd_word 1 (by omega)
  have hv'_ltw : v' < 2 ^ w := by rw [← hv'_m]; exact hupd_word 2 (by omega)
  have hkt_ltw : kt < 2 ^ w := by rw [← hkt_m]; exact hupd_word 3 (by omega)
  have hkh_ltw : kh < 2 ^ w := by rw [← hkh_m]; exact hupd_word 4 (by omega)
  have hgoal : ∃ o st' c,
      Runs w p ω (lsfTBlockSplitProc idxDgAddV idxDgMoveLoop)
        (startState [tPtr, updPtr, vCap, eCap, tM] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (lsfTBlockSplitContract w vCap eCap tM G T_cur T₀ π tOrigList v v' St Sh len).post
          [tPtr, updPtr, vCap, eCap, tM] mem 0 st'.mem) ∧
      0 + c ≤ 1400 * (kt + kh + 1) := by
    dsimp only [lsfTBlockSplitProc]
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tag) (by eval_expr) htag_m) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := v) (by eval_expr) hv_m) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := v') (by eval_expr) hv'_m) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := kt) (by eval_expr) hkt_m) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := kh) (by eval_expr) hkh_m) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tDgTPtr tPtr)
      (by dsimp [tOffDgTPtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h1) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tIdxOfEdgeBase tPtr vCap tM)
      (by dsimp [tOffIdxOfEdgePtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h6) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tSplitScratchBase tPtr vCap eCap tM)
      (by dsimp [tOffSplitScratchPtr, tHdrSize] at htPtr_ltw ⊢; eval_expr) h7) ?_
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    -- Scan loop 1 (Lt)
    dsimp only [lsfTBlockSplitScanLoopStmt]
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    let st_s0 : State :=
      { mem := mem
        regs := Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update (Function.update
            (startState [tPtr, updPtr, vCap, eCap, tM] mem pos).regs
            5 tag) 6 v) 7 v') 8 kt) 9 kh) 10 (tDgTPtr tPtr))
            11 (tIdxOfEdgeBase tPtr vCap tM)) 12 (tSplitScratchBase tPtr vCap eCap tM)) 13 0) 14 0
        pos := pos }
    obtain ⟨st_s1, c_s1, hrun_s1, hreg_s1, hr1_13, hacc1_at, hfr_s1, hc_s1⟩ :=
      scanLoop_runs (isHead := false) (L := Lt) (kt := kt) (kh := kh) (mem0 := mem) (p := p) (ω := ω)
        hw16 (by omega) hidx_lt hscr_lt rfl hLt_at
        (fun j hj q hq => hdisj_scr_upd (5 + j) (by omega) q hq |> fun h => by simpa [Nat.add_assoc] using h)
        hdisj_scr_idx hLt_word hidx_bd
        kt 0 0 [] st_s0 (by omega) rfl (by simp; omega)
        (by dsimp [st_s0]; simp [hr1]) (by dsimp [st_s0]; simp [hr3])
        (by dsimp [st_s0]; simp) (by dsimp [st_s0]; simp)
        (by dsimp [st_s0]; simp) (by dsimp [st_s0]; simp)
        (by dsimp [st_s0]; simp) (by dsimp [st_s0]; simp)
        (fun i hi => by simp at hi) (fun _ _ => rfl)
    refine runs_seq_of_runs_le hrun_s1 ?_
    -- Scan loop 2 (Lh)
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    let st_s1b : State := { mem := st_s1.mem, regs := Function.update st_s1.regs 14 0, pos := st_s1.pos }
    obtain ⟨st_s2, c_s2, hrun_s2, hreg_s2, hr2_13, hacc2_at, hfr_s2, hc_s2⟩ :=
      scanLoop_runs (isHead := true) (L := Lh) (kt := kt) (kh := kh) (mem0 := mem) (p := p) (ω := ω)
        hw16 (by omega) hidx_lt hscr_lt rfl hLh_at
        (fun j hj q hq => hdisj_scr_upd (5 + kt + j) (by omega) q hq |> fun h => by simpa [Nat.add_assoc] using h)
        hdisj_scr_idx hLh_word hidx_bd
        kh 0 L1.length L1 st_s1b (by omega) rfl (by simp [L1]; omega)
        (by dsimp [st_s1b]; rw [Function.update_of_ne (by decide), hreg_s1 1 (by decide)]; dsimp [st_s0]; simp [hr1])
        (by dsimp [st_s1b]; rw [Function.update_of_ne (by decide), hreg_s1 3 (by decide)]; dsimp [st_s0]; simp [hr3])
        (by dsimp [st_s1b]; rw [Function.update_of_ne (by decide), hreg_s1 8 (by decide)]; dsimp [st_s0]; simp)
        (by dsimp [st_s1b]; rw [Function.update_of_ne (by decide), hreg_s1 9 (by decide)]; dsimp [st_s0]; simp)
        (by dsimp [st_s1b]; rw [Function.update_of_ne (by decide), hreg_s1 11 (by decide)]; dsimp [st_s0]; simp)
        (by dsimp [st_s1b]; rw [Function.update_of_ne (by decide), hreg_s1 12 (by decide)]; dsimp [st_s0]; simp)
        (by dsimp [st_s1b]; rw [Function.update_of_ne (by decide), hr1_13]; simp [L1])
        (by dsimp [st_s1b]; simp)
        (by simpa [L1] using hacc1_at) hfr_s1
    refine runs_seq_of_runs_le hrun_s2 ?_
    have hreg_s2_lo : ∀ r ≤ 12, st_s2.regs r = st_s0.regs r := fun r hr =>
      (hreg_s2 r hr).trans ((Function.update_of_ne (by omega) _ _).trans (hreg_s1 r hr))
    have hr2_13_eq : st_s2.regs 13 = L_tr.length := by simpa [L_tr, L2] using hr2_13
    have hLtr_at2 : ListAt st_s2.mem (tSplitScratchBase tPtr vCap eCap tM) L_tr := by
      simpa [L_tr, L2] using hacc2_at
    have hdgT_s2 : DynGraphAt st_s2.mem (tDgTPtr tPtr) vCap (2 * tM + 1) dgT :=
      hdgT.of_agree fun a _ ha2 => hfr_s2 a (by
        dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase]; omega)
    -- Call dgAddVertex(dgTPtr, v')
    have hpre_av : (dgAddVertexContract w vCap (2 * tM + 1) dgT).pre [tDgTPtr tPtr, v'] st_s2.mem :=
      ⟨tDgTPtr tPtr, v', rfl, hw16, hdgT_lt, hv'_lt, hdgT_s2⟩
    have hargs_av : evalArgs w st_s2 [.reg 10, .reg 7] = some [tDgTPtr tPtr, v'] := by
      have h10 : st_s2.regs 10 = tDgTPtr tPtr := (hreg_s2_lo 10 (by decide)).trans (by dsimp [st_s0]; simp)
      have h7r : st_s2.regs 7 = v' := (hreg_s2_lo 7 (by decide)).trans (by dsimp [st_s0]; simp)
      eval_expr
    refine runs_seq_call_le (hDgAddV dgT) hargs_av
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> omega)
      hpre_av ?_
    intro ret_av mem1 pos1 hpost_av
    rcases hpost_av with ⟨_, _, hargs_av', _, hdgT1, hfr_av⟩
    simp only [List.cons.injEq, and_true] at hargs_av'
    rcases hargs_av' with ⟨rfl, rfl⟩
    let st_av : State := { mem := mem1, regs := Function.update st_s2.regs 14 ret_av, pos := pos1 }
    have hv_V1 : v ∈ ({ dgT with V := insert v' dgT.V } : MGraph).V := Finset.mem_insert_of_mem (hdgTV.symm ▸ hvG)
    have hv'_V1 : v' ∈ ({ dgT with V := insert v' dgT.V } : MGraph).V := Finset.mem_insert_self v' dgT.V
    set s_v := mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + v)
    set s_v' := mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + v')
    have hsv_lt : s_v < vCap := hdgT1.2.1 _ (hdgT1.2.2.2.2.2.2.2.2.2.1 v hv_V1).1
    have hsv'_lt : s_v' < vCap := hdgT1.2.1 _ (hdgT1.2.2.2.2.2.2.2.2.2.1 v' hv'_V1).1
    have hne_s : s_v ≠ s_v' := by
      intro hEq
      have h1' := (hdgT1.2.2.2.2.2.2.2.2.2.1 v hv_V1).2
      have h2' := (hdgT1.2.2.2.2.2.2.2.2.2.1 v' hv'_V1).2
      rw [show mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + v) = s_v from rfl, hEq] at h1'
      exact hv'G (h1'.symm.trans h2' ▸ hvG)
    have hv_lt : v < vCap := hdgT1.2.1 v hv_V1
    -- Run lsfTBlockSplitSetupStmt
    obtain ⟨st_set, c_set, hrun_set, hreg_set, hr_16, hr_17, hmem2_eq, hc_set⟩ :=
      tBlockSplitSetup_regs_lo (p := p) (ω := ω) (st := st_av) hdgT_lt rfl rfl hv_lt hv'_lt hsv_lt hsv'_lt htag_ltw
        (by dsimp [st_av]; rw [Function.update_of_ne (by decide), hreg_s2_lo 2 (by decide)]; dsimp [st_s0]; simp [hr2])
        (by dsimp [st_av]; rw [Function.update_of_ne (by decide), hreg_s2_lo 5 (by decide)]; dsimp [st_s0]; simp)
        (by dsimp [st_av]; rw [Function.update_of_ne (by decide), hreg_s2_lo 6 (by decide)]; dsimp [st_s0]; simp)
        (by dsimp [st_av]; rw [Function.update_of_ne (by decide), hreg_s2_lo 7 (by decide)]; dsimp [st_s0]; simp)
        (by dsimp [st_av]; rw [Function.update_of_ne (by decide), hreg_s2_lo 10 (by decide)]; dsimp [st_s0]; simp)
        rfl
    refine runs_seq_of_runs_le hrun_set ?_
    set mem2 := st_set.mem
    have hreg_set_10 : st_set.regs 10 = tDgTPtr tPtr := by
      rw [hreg_set 10 (by decide)]; dsimp [st_av]
      rw [Function.update_of_ne (by decide), hreg_s2_lo 10 (by decide)]; dsimp [st_s0]; simp
    have hreg_set_12 : st_set.regs 12 = tSplitScratchBase tPtr vCap eCap tM := by
      rw [hreg_set 12 (by decide)]; dsimp [st_av]
      rw [Function.update_of_ne (by decide), hreg_s2_lo 12 (by decide)]; dsimp [st_s0]; simp
    have hreg_set_13 : st_set.regs 13 = L_tr.length := by
      rw [hreg_set 13 (by decide)]; dsimp [st_av]
      rw [Function.update_of_ne (by decide), hr2_13_eq]
    have hmem2_out_dgT : ∀ a, a < tDgTPtr tPtr ∨ tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1) ≤ a → mem2 a = mem1 a := by
      intro a ha; rw [hmem2_eq]; split_ifs
      · rw [Function.update_of_ne (by dsimp [dgIntToExtBase, dynGraphSize] at *; omega),
          Function.update_of_ne (by dsimp [dgExtToIntBase, dynGraphSize] at *; omega),
          Function.update_of_ne (by dsimp [dgIntToExtBase, dynGraphSize] at *; omega),
          Function.update_of_ne (by dsimp [dgExtToIntBase, dynGraphSize] at *; omega)]
      · rfl
    have hLtr_at_m2 : ListAt mem2 (tSplitScratchBase tPtr vCap eCap tM) L_tr := fun q hq => by
      have hout := hscr_disj_dgT q (by omega)
      exact (hmem2_out_dgT _ hout).trans ((hfr_av _ hout).trans (hLtr_at2 q hq))
    have hInc2 : DgIncStateAt mem2 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT.E
        (fun x => mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x))
        (fun x => mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.head x)) := by
      rcases hdgT1 with ⟨hval1, hvCap1, heCap1, h0_1, h1_1, _, _, _, _, heti1, _, hep1, _, hets1, ⟨incL1, hincL1⟩⟩
      have hm2_ge : ∀ a, dgSlotDegBase (tDgTPtr tPtr) vCap ≤ a → mem2 a = mem1 a := by
        intro a ha; rw [hmem2_eq]; split_ifs
        · rw [Function.update_of_ne (by dsimp [dgSlotDegBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgSlotDegBase, dgExtToIntBase] at *; omega),
            Function.update_of_ne (by dsimp [dgSlotDegBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgSlotDegBase, dgExtToIntBase] at *; omega)]
        · rfl
      have hm2_lt : ∀ a, a < dgExtToIntBase (tDgTPtr tPtr) vCap → mem2 a = mem1 a := by
        intro a ha; rw [hmem2_eq]; split_ifs
        · rw [Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase, dgIntToExtBase] at *; omega),
            Function.update_of_ne (by dsimp [dgExtToIntBase] at *; omega)]
        · rfl
      refine ⟨(hm2_lt _ (by dsimp [dgVCapOff, dgExtToIntBase]; omega)).trans h0_1,
        (hm2_lt _ (by dsimp [dgECapOff, dgExtToIntBase]; omega)).trans h1_1,
        fun e he => ⟨heCap1 e he, hvCap1 _ (heti1 _ (hval1 e he).1).1, hvCap1 _ (heti1 _ (hval1 e he).2).1⟩,
        fun e he => (hm2_ge _ (by dsimp [dgEPresBase, dgSlotDegBase]; omega)).trans (hep1 e he),
        fun e he => ⟨(hm2_ge _ (by dsimp [dgETailSlotBase, dgSlotDegBase]; omega)).trans (hets1 e he).1,
          (hm2_ge _ (by dsimp [dgEHeadSlotBase, dgSlotDegBase]; omega)).trans (hets1 e he).2⟩,
        incL1, fun s hs => ?_⟩
      rcases hincL1 s hs with ⟨hdll, hdeg, hmem_i⟩
      refine ⟨hdll.of_agree (hm2_ge _ (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega))
          (fun _ _ => hm2_ge _ (by dsimp [dgHePrevBase, dgSlotDegBase]; omega))
          (fun _ _ => hm2_ge _ (by dsimp [dgHeNextBase, dgSlotDegBase]; omega)),
        (hm2_ge _ (by dsimp [dgSlotDegBase]; omega)).trans hdeg, fun h => ?_⟩
      rw [hmem_i h]; constructor <;> rintro ⟨hlt, h2E, hslot⟩ <;> refine ⟨hlt, h2E, ?_⟩
      · rcases hets1 (h / 2) h2E with ⟨ht, hh_⟩
        split_ifs at hslot ⊢ <;> [exact ht.symm.trans hslot; exact hh_.symm.trans hslot]
      · rcases hets1 (h / 2) h2E with ⟨ht, hh_⟩
        split_ifs at hslot ⊢ <;> [exact ht.trans hslot; exact hh_.trans hslot]
    -- Call 1: dgMoveSlotLoop(dgTPtr, s_v, s_v', scratchBase, L_tr.length, 0)
    have hLtr_ltw : L_tr.length < 2 ^ w := by omega
    have hvCap_ltw : vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgT_lt; omega
    have hdgT0_ltw : tDgTPtr tPtr < 2 ^ w := by omega
    have hscr0_ltw : tSplitScratchBase tPtr vCap eCap tM < 2 ^ w := by omega
    have hsv_ltw : s_v < 2 ^ w := by omega
    have hsv'_ltw : s_v' < 2 ^ w := by omega
    have hpre_ml0 : (dgMoveSlotLoopContract w vCap (2 * tM + 1) dgT.E
        (fun x => mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x))
        (fun x => mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.head x)) L_tr false).pre
        [tDgTPtr tPtr, s_v, s_v', tSplitScratchBase tPtr vCap eCap tM, L_tr.length, 0] mem2 :=
      ⟨tDgTPtr tPtr, s_v, s_v', tSplitScratchBase tPtr vCap eCap tM, L_tr.length,
        rfl, hw16, hdgT_lt, by omega, hsv_lt, hsv'_lt, hne_s, rfl, hLtr_at_m2, hLtr_word,
        fun q hq => hscr_disj_dgT q (by omega), hInc2⟩
    have hargs_ml0 : evalArgs w st_set [.reg 10, .reg 16, .reg 17, .reg 12, .reg 13, .const 0] =
        some [tDgTPtr tPtr, s_v, s_v', tSplitScratchBase tPtr vCap eCap tM, L_tr.length, 0] := by
      have h10 := hreg_set_10; have h12 := hreg_set_12; have h13 := hreg_set_13
      eval_expr
    refine runs_seq_call_le (hDgMoveLoop _ _ _ L_tr false) hargs_ml0
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hpre_ml0 ?_
    intro ret_ml0 mem3 pos3 hpost_ml0
    rcases hpost_ml0 with ⟨_, _, _, _, _, hEq_ml0, _, hInc3, hfr23⟩
    simp only [List.cons.injEq, and_true] at hEq_ml0
    rcases hEq_ml0 with ⟨rfl, rfl, rfl, rfl, rfl, _⟩
    have hLtr_at_m3 : ListAt mem3 (tSplitScratchBase tPtr vCap eCap tM) L_tr := fun q hq =>
      (hfr23.outside (hscr_disj_dgT q (by omega))).trans (hLtr_at_m2 q hq)
    -- Call 2: dgMoveSlotLoop(dgTPtr, s_v, s_v', scratchBase, L_tr.length, 1)
    have hpre_ml1 : (dgMoveSlotLoopContract w vCap (2 * tM + 1) dgT.E
        (fun x => if x ∈ L_tr.toFinset ∧ mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x) = s_v then s_v'
                  else mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x))
        (fun x => mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.head x)) L_tr true).pre
        [tDgTPtr tPtr, s_v, s_v', tSplitScratchBase tPtr vCap eCap tM, L_tr.length, 1] mem3 :=
      ⟨tDgTPtr tPtr, s_v, s_v', tSplitScratchBase tPtr vCap eCap tM, L_tr.length,
        rfl, hw16, hdgT_lt, by omega, hsv_lt, hsv'_lt, hne_s, rfl, hLtr_at_m3, hLtr_word,
        fun q hq => hscr_disj_dgT q (by omega), by simpa using hInc3⟩
    have hargs_ml1 : evalArgs w { mem := mem3, regs := Function.update st_set.regs 18 ret_ml0, pos := pos3 }
        [.reg 10, .reg 16, .reg 17, .reg 12, .reg 13, .const 1] =
        some [tDgTPtr tPtr, s_v, s_v', tSplitScratchBase tPtr vCap eCap tM, L_tr.length, 1] := by
      have h10 := hreg_set_10; have h12 := hreg_set_12; have h13 := hreg_set_13
      eval_expr
    refine runs_seq_call_le (hDgMoveLoop _ _ _ L_tr true) hargs_ml1
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hpre_ml1 ?_
    intro _ mem4 _ hpost_ml1
    rcases hpost_ml1 with ⟨_, _, _, _, _, hEq_ml1, _, hInc4, hfr34⟩
    simp only [List.cons.injEq, and_true] at hEq_ml1
    rcases hEq_ml1 with ⟨rfl, rfl, rfl, rfl, rfl, _⟩
    have hfr24 : DgSlotsOnlyModified mem2 mem4 (tDgTPtr tPtr) vCap (2 * tM + 1) := hfr23.trans hfr34
    have hInc4' : DgIncStateAt mem4 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT.E
        (fun x => if x ∈ L_tr.toFinset ∧ mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x) = s_v then s_v'
                  else mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x))
        (fun x => if x ∈ L_tr.toFinset ∧ mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.head x) = s_v then s_v'
                  else mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.head x)) := by
      simpa only [↓reduceIte] using hInc4
    -- Assemble target dgT' and TBlockAt
    let S_tr : Finset ℕ := dgT.E.filter fun k =>
      if k % 2 = 0 then tOrigList[k / 2]! ∈ St else tOrigList[k / 2]! ∈ Sh
    have hself_dgT : ∀ k ∈ dgT.E, dgT.tail k = dgT.head k := by
      intro k hk
      have hk_lt := hdgTE k hk
      have hi : k / 2 < tOrigList.length := by omega
      have htr := htrack (k / 2) hi
      by_cases heven : k % 2 = 0
      · have hk_eq : k = 2 * (k / 2) := by omega
        rw [hk_eq] at hk ⊢; have h := htr.2.1 hk; exact h.1.trans h.2.symm
      · have hk_eq : k = 2 * (k / 2) + 1 := by omega
        rw [hk_eq] at hk ⊢; have h := htr.2.2.2.2.1 hk; exact h.1.trans h.2.symm
    have htag_dgT : (tag = 2 ∧ ∀ k ∈ dgT.E, k ∈ L_tr ↔ dgT.tail k = v ∧ k ∈ S_tr) ∨
        (tag = 3 ∧ ∀ k ∈ dgT.E, k ∈ L_tr ↔ dgT.tail k = v ∧ k ∉ S_tr) := by
      have hmem_Ltr : ∀ k ∈ dgT.E,
          (k % 2 = 0 → (k ∈ L_tr ↔ tOrigList[k / 2]! ∈ Lt)) ∧
          (k % 2 = 1 → (k ∈ L_tr ↔ tOrigList[k / 2]! ∈ Lh)) := by
        intro k hk
        have hk_lt := hdgTE k hk
        have hi : k / 2 < tOrigList.length := by omega
        have hbang : tOrigList[k / 2]! = tOrigList[k / 2] := getElem!_pos tOrigList (k / 2) hi
        have htr := htrack (k / 2) hi
        refine ⟨fun heven => ?_, fun hodd => ?_⟩
        · have hk_eq : k = 2 * (k / 2) := by omega
          have hfG : tOrigList[k / 2] ∈ G.E := (htr.1.mp (hk_eq ▸ hk)).1
          have hf_lt : tOrigList[k / 2] < eCap := heG_lt _ hfG
          have hnot_L2 : k ∉ L2 := fun hm => by have := (hL2_p.2.2.1 k hm).2; simp at this; omega
          simp only [L_tr, List.mem_append, hnot_L2, or_false, hbang]
          have hiff := hL1_p.2.2.2 (k / 2) hi hf_lt
          simp only [Bool.false_eq_true, ↓reduceIte, ← hk_eq, hidx1 (k / 2) hi hf_lt, and_true] at hiff
          exact hiff
        · have hk_eq : k = 2 * (k / 2) + 1 := by omega
          have hfG : tOrigList[k / 2] ∈ G.E := (htr.2.2.2.1.mp (hk_eq ▸ hk)).1
          have hf_lt : tOrigList[k / 2] < eCap := heG_lt _ hfG
          have hnot_L1 : k ∉ L1 := fun hm => by have := (hL1_p.2.2.1 k hm).2; simp at this; omega
          simp only [L_tr, List.mem_append, hnot_L1, false_or, hbang]
          have hiff := hL2_p.2.2.2 (k / 2) hi hf_lt
          simp only [↓reduceIte, ← hk_eq, hidx1 (k / 2) hi hf_lt, and_true] at hiff
          exact hiff
      rcases htag_iff with ⟨rfl, hLt2, hLh2⟩ | ⟨rfl, hLt3, hLh3⟩
      · left; refine ⟨rfl, fun k hk => ?_⟩
        have hk_lt := hdgTE k hk; have hi : k / 2 < tOrigList.length := by omega
        have hbang : tOrigList[k / 2]! = tOrigList[k / 2] := getElem!_pos tOrigList (k / 2) hi
        have htr := htrack (k / 2) hi
        by_cases heven : k % 2 = 0
        · have hk_eq : k = 2 * (k / 2) := by omega
          have h1' := htr.1.mp (hk_eq ▸ hk)
          have h2' : dgT.tail k = G.tail tOrigList[k / 2] :=
            (congrArg dgT.tail hk_eq).trans ((htr.2.1 (hk_eq ▸ hk)).1.trans h1'.2.symm)
          rw [(hmem_Ltr k hk).1 heven, hbang, hLt2]
          simp only [S_tr, Finset.mem_filter, hk, true_and, heven, ↓reduceIte, hbang, h1'.1, h2']
        · have hodd : k % 2 = 1 := by omega
          have hk_eq : k = 2 * (k / 2) + 1 := by omega
          have h1' := htr.2.2.2.1.mp (hk_eq ▸ hk)
          have h2' : dgT.tail k = G.head tOrigList[k / 2] :=
            (congrArg dgT.tail hk_eq).trans ((htr.2.2.2.2.1 (hk_eq ▸ hk)).1.trans h1'.2.symm)
          rw [(hmem_Ltr k hk).2 hodd, hbang, hLh2]
          simp only [S_tr, Finset.mem_filter, hk, true_and, heven, ↓reduceIte, hbang, h1'.1, h2']
      · right; refine ⟨rfl, fun k hk => ?_⟩
        have hk_lt := hdgTE k hk; have hi : k / 2 < tOrigList.length := by omega
        have hbang : tOrigList[k / 2]! = tOrigList[k / 2] := getElem!_pos tOrigList (k / 2) hi
        have htr := htrack (k / 2) hi
        by_cases heven : k % 2 = 0
        · have hk_eq : k = 2 * (k / 2) := by omega
          have h1' := htr.1.mp (hk_eq ▸ hk)
          have h2' : dgT.tail k = G.tail tOrigList[k / 2] :=
            (congrArg dgT.tail hk_eq).trans ((htr.2.1 (hk_eq ▸ hk)).1.trans h1'.2.symm)
          rw [(hmem_Ltr k hk).1 heven, hbang, hLt3]
          simp only [S_tr, Finset.mem_filter, hk, true_and, heven, ↓reduceIte, hbang, h1'.1, h2']
        · have hodd : k % 2 = 1 := by omega
          have hk_eq : k = 2 * (k / 2) + 1 := by omega
          have h1' := htr.2.2.2.1.mp (hk_eq ▸ hk)
          have h2' : dgT.tail k = G.head tOrigList[k / 2] :=
            (congrArg dgT.tail hk_eq).trans ((htr.2.2.2.2.1 (hk_eq ▸ hk)).1.trans h1'.2.symm)
          rw [(hmem_Ltr k hk).2 hodd, hbang, hLh3]
          simp only [S_tr, Finset.mem_filter, hk, true_and, heven, ↓reduceIte, hbang, h1'.1, h2']
    let dgT' := dgT.applyUpdate (.split v v' (S_tr ∩ dgT.E) (S_tr ∩ dgT.E))
    have hdgT'_at : DynGraphAt mem4 (tDgTPtr tPtr) vCap (2 * tM + 1) dgT' :=
      dgT_post_dynGraphAt hdgT.1 (hdgTV.symm ▸ hvG) (hdgTV.symm ▸ hv'G) hv'_lt hdgT1 rfl rfl
        hmem2_eq hfr24 hInc4' hself_dgT htag_dgT
    have hfr_all : ∀ a, ¬ (tDgTPtr tPtr ≤ a ∧ a < tDgTPtr tPtr + dynGraphSize vCap (2 * tM + 1)) →
        ¬ (tSplitScratchBase tPtr vCap eCap tM ≤ a ∧ a < tSplitScratchBase tPtr vCap eCap tM + 2 * tM) →
        mem4 a = mem a := fun a hnotD hnotS =>
      (hfr24.outside (by omega)).trans ((hmem2_out_dgT a (by omega)).trans
        ((hfr_av a (by omega)).trans (hfr_s2 a hnotS)))
    have hT_post : TBlockAt mem4 tPtr vCap eCap tM
        (G.applyUpdate (.split v v' St Sh)) (T_cur.applyUpdate (.split v v' St Sh)) T₀ π tOrigList := by
      have hhd : ∀ off < tHdrSize, mem4 (tPtr + off) = mem (tPtr + off) := fun off hoff =>
        hfr_all _ (by dsimp [tDgTPtr]; omega)
          (by dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase,
            tPiBase, tOrigIdBase, tDgTPtr]; omega)
      have hmid : ∀ a, tOrigIdBase tPtr vCap tM ≤ a → a < tSplitScratchBase tPtr vCap eCap tM →
          mem4 a = mem a := fun a ha1 ha2 =>
        hfr_all a (by dsimp [tOrigIdBase] at ha1; omega) (by omega)
      refine ⟨(hhd _ (by decide)).trans h0, (hhd _ (by decide)).trans h1,
        (hhd _ (by decide)).trans h2, (hhd _ (by decide)).trans h3,
        (hhd _ (by decide)).trans h4, (hhd _ (by decide)).trans h5,
        (hhd _ (by decide)).trans h6, (hhd _ (by decide)).trans h7,
        hlen, hnd, hmemT,
        fun i hi => (hmid _ (Nat.le_add_right _ _) (by
          dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase]; omega)).trans (hLO i hi),
        fun i hi => (hmid _ (by dsimp [tPiBase]; omega) (by
          simp only [List.length_map] at hi
          dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase]; omega)).trans (hLPi i hi),
        fun i hi hlt => (hmid _ (by
          dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase]; omega)
          (by dsimp [tSplitScratchBase]; omega)).trans (hidx1 i hi hlt),
        fun e he hne => by
          have hm := hmid (tIdxOfEdgeBase tPtr vCap tM + e)
            (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase]; omega)
            (by dsimp [tSplitScratchBase]; omega)
          rw [hm] at hne ⊢; exact hidx2 e he hne,
        dgT', hdgT'_at, by simp [dgT', MGraph.applyUpdate, hdgTV], hdgTE, fun i hi => ?_⟩
      have htr := htrack i hi
      have hfT : tOrigList[i] ∈ T_cur.E := hTE.symm ▸ (hmemT _).mp (List.getElem_mem hi)
      have hTval_f := hTval _ hfT
      have hft_m : mem4 (tFrozenTailBase tPtr vCap tM + i) = mem (tFrozenTailBase tPtr vCap tM + i) :=
        hmid _ (by dsimp [tFrozenTailBase, tPiBase]; omega)
          (by dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase]; omega)
      have hfh_m : mem4 (tFrozenHeadBase tPtr vCap tM + i) = mem (tFrozenHeadBase tPtr vCap tM + i) :=
        hmid _ (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase]; omega)
          (by dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase]; omega)
      have h2i_div : 2 * i / 2 = i := by omega
      have h2i1_div : (2 * i + 1) / 2 = i := by omega
      have hbang : tOrigList[i]! = tOrigList[i] := getElem!_pos tOrigList i hi
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · constructor
        · intro h2i
          have h1' := htr.1.mp h2i
          simp only [MGraph.applyUpdate, h1'.1, h1'.2, true_and]
        · rintro ⟨hfG, heq'⟩
          by_contra hnot
          have hne_old : G.tail tOrigList[i] ≠ T_cur.tail tOrigList[i] := fun h => hnot (htr.1.mpr ⟨hfG, h⟩)
          have hnot_T : ¬ (tOrigList[i] ∈ St ∧ T_cur.tail tOrigList[i] = v) := by
            rintro ⟨hfSt, hTv⟩
            exact hne_old ((hcan_t _ hfSt).2.trans hTv.symm)
          dsimp only [MGraph.applyUpdate] at heq'
          rw [ite_eq_right hnot_T] at heq'
          split_ifs at heq' with hGt
          · exact hv'G (hTV ▸ heq'.symm ▸ hTval_f.1)
          · exact hne_old heq'
      · intro h2i
        have h1' := htr.1.mp h2i; have h2' := htr.2.1 h2i
        have hStr_iff : 2 * i ∈ S_tr ∩ dgT.E ↔ tOrigList[i] ∈ St := by
          simp only [S_tr, Finset.mem_inter, Finset.mem_filter, Nat.mul_mod_right, ↓reduceIte,
            h2i_div, hbang]
          exact ⟨fun h => h.1.2, fun h => ⟨⟨h2i, h⟩, h2i⟩⟩
        simp only [dgT', MGraph.applyUpdate, hStr_iff, h2'.1, h2'.2, and_self]
      · intro hnot
        have hnot_T : ¬ (tOrigList[i] ∈ St ∧ T_cur.tail tOrigList[i] = v) := by
          rintro ⟨hfSt, hTv⟩
          exact hnot (htr.1.mpr ⟨(hcan_t _ hfSt).1, (hcan_t _ hfSt).2.trans hTv.symm⟩)
        dsimp only [MGraph.applyUpdate]; rw [ite_eq_right hnot_T, hft_m]; exact htr.2.2.1 hnot
      · constructor
        · intro h2i1
          have h1' := htr.2.2.2.1.mp h2i1
          simp only [MGraph.applyUpdate, h1'.1, h1'.2, true_and]
        · rintro ⟨hfG, heq'⟩
          by_contra hnot
          have hne_old : G.head tOrigList[i] ≠ T_cur.head tOrigList[i] := fun h => hnot (htr.2.2.2.1.mpr ⟨hfG, h⟩)
          have hnot_T : ¬ (tOrigList[i] ∈ Sh ∧ T_cur.head tOrigList[i] = v) := by
            rintro ⟨hfSh, hTv⟩
            exact hne_old ((hcan_h _ hfSh).2.trans hTv.symm)
          dsimp only [MGraph.applyUpdate] at heq'
          rw [ite_eq_right hnot_T] at heq'
          split_ifs at heq' with hGh
          · exact hv'G (hTV ▸ heq'.symm ▸ hTval_f.2)
          · exact hne_old heq'
      · intro h2i1
        have h1' := htr.2.2.2.1.mp h2i1; have h2' := htr.2.2.2.2.1 h2i1
        have hStr_iff : 2 * i + 1 ∈ S_tr ∩ dgT.E ↔ tOrigList[i] ∈ Sh := by
          have hodd : (2 * i + 1) % 2 ≠ 0 := by omega
          simp only [S_tr, Finset.mem_inter, Finset.mem_filter, hodd, ↓reduceIte, h2i1_div, hbang]
          exact ⟨fun h => h.1.2, fun h => ⟨⟨h2i1, h⟩, h2i1⟩⟩
        simp only [dgT', MGraph.applyUpdate, hStr_iff, h2'.1, h2'.2, and_self]
      · intro hnot
        have hnot_T : ¬ (tOrigList[i] ∈ Sh ∧ T_cur.head tOrigList[i] = v) := by
          rintro ⟨hfSh, hTv⟩
          exact hnot (htr.2.2.2.1.mpr ⟨(hcan_h _ hfSh).1, (hcan_h _ hfSh).2.trans hTv.symm⟩)
        dsimp only [MGraph.applyUpdate]; rw [ite_eq_right hnot_T, hfh_m]; exact htr.2.2.2.2.2 hnot
    refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, tPtr, updPtr, rfl, rfl, hT_post, fun a ha => ?_⟩ ?_
    · exact hfr_all a (by dsimp [tDgTPtr, tBlockSize] at ha ⊢; omega)
        (by dsimp [tSplitScratchBase, tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase,
          tPiBase, tOrigIdBase, tDgTPtr, tBlockSize] at ha ⊢; omega)
    · have hml_cost : (dgMoveSlotLoopContract w vCap (2 * tM + 1) dgT.E
          (fun x => mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x))
          (fun x => mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.head x)) L_tr false).cost
          [tDgTPtr tPtr, s_v, s_v', tSplitScratchBase tPtr vCap eCap tM, L_tr.length, 0] mem2 =
          625 * L_tr.length + 25 := rfl
      have hml_cost1 : (dgMoveSlotLoopContract w vCap (2 * tM + 1) dgT.E
          (fun x => if x ∈ L_tr.toFinset ∧ mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x) = s_v then s_v'
                    else mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.tail x))
          (fun x => mem1 (dgExtToIntBase (tDgTPtr tPtr) vCap + dgT.head x)) L_tr true).cost
          [tDgTPtr tPtr, s_v, s_v', tSplitScratchBase tPtr vCap eCap tM, L_tr.length, 1] mem3 =
          625 * L_tr.length + 25 := rfl
      have hav_cost : (dgAddVertexContract w vCap (2 * tM + 1) dgT).cost [tDgTPtr tPtr, v'] st_s2.mem = 110 := rfl
      rw [hml_cost, hml_cost1, hav_cost]
      dsimp only [argsSize, Expr.size]
      have hLtr_le_k : L_tr.length ≤ kt + kh := by simp [L_tr]; omega
      clear * - hc_s1 hc_s2 hc_set hLtr_le_k
      omega
  obtain ⟨o, st', c, hrun, ⟨rfl, hpost⟩, hc⟩ := hgoal
  refine ⟨lsfTBlockSplitProc idxDgAddV idxDgMoveLoop, hp, .returned 0, st', c, hrun, hpost, ?_⟩
  dsimp only [lsfTBlockSplitContract]
  simp only [List.getD_cons_zero, List.getD_cons_succ, hkt_m, hkh_m]
  omega

end

end MinCostFlow.LSF.Program
