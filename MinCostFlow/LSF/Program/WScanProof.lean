module

public import MinCostFlow.LSF.Program.WScan

/-!
# The proof of `wScanProc`

`wScan_meetsContract`: the scan meets `wScanContract`. The loop invariant says that memory holds
the groups of the first `k` positions (`WMem`) and the first `k` edges.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 4000000 in
theorem wScan_meetsContract {w : ℕ} {p : Program} {b bAdd : ℕ}
    (hp : p.procs[b]? = some (wScanProc bAdd))
    (hAdd : MeetsContract w p bAdd (wAddVContract w)) :
    MeetsContract w p b (wScanContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨cnt, arrPtr, pePtr, parPtr, fidPtr, vListPtr, labYPtr, labBPtr, rtPtr, stPtr, wPtr, n0,
    n, tM, K, rfl, h16, hcn, hbw, hstw, hstD, hz, hA, hPe, hPa, hF, hV, hY, hB, hR, hlt, hK⟩ :=
    hpre
  set args := [cnt, arrPtr, pePtr, parPtr, fidPtr, vListPtr, labYPtr, labBPtr, rtPtr, stPtr, wPtr,
    n0, n] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hcw : cnt < 2 ^ w := hwords _ (by simp [hargs])
  obtain ⟨s, hs⟩ : ∃ f : ℕ → ℕ, f = fun j => mem (arrPtr + j) := ⟨_, rfl⟩
  obtain ⟨pa, hpa⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (parPtr + y) := ⟨_, rfl⟩
  obtain ⟨pe, hpe⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (pePtr + y) := ⟨_, rfl⟩
  obtain ⟨fid, hfid⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (fidPtr + y) := ⟨_, rfl⟩
  obtain ⟨vL, hvL⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (vListPtr + y) := ⟨_, rfl⟩
  obtain ⟨lY, hlY⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (labYPtr + y) := ⟨_, rfl⟩
  obtain ⟨lB, hlB⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (labBPtr + y) := ⟨_, rfl⟩
  obtain ⟨rtf, hrtf⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (rtPtr + y) := ⟨_, rfl⟩
  have hsx : ∀ j, mem (arrPtr + j) = s j := fun j => by rw [hs]
  have hpax : ∀ y, mem (parPtr + y) = pa y := fun y => by rw [hpa]
  have hpex : ∀ y, mem (pePtr + y) = pe y := fun y => by rw [hpe]
  have hfidx : ∀ y, mem (fidPtr + y) = fid y := fun y => by rw [hfid]
  have hvLx : ∀ y, mem (vListPtr + y) = vL y := fun y => by rw [hvL]
  have hlYx : ∀ y, mem (labYPtr + y) = lY y := fun y => by rw [hlY]
  have hlBx : ∀ y, mem (labBPtr + y) = lB y := fun y => by rw [hlB]
  have hrtx : ∀ y, mem (rtPtr + y) = rtf y := fun y => by rw [hrtf]
  simp only [hsx, hpax, hpex] at hlt
  rw [← hs, ← hlY, ← hlB, ← hrtf] at hK
  have hbs : wBlockSize n0 = 7 + (n0 + 1) + 2 * n0 + (n0 + 1) + n0 := by
    simp [wBlockSize, wHdrSize]
  set VO := wPtr + 7 with hVO
  set VS := VO + (n0 + 1) with hVS
  set EO := VS + 2 * n0 with hEO
  set ES := EO + (n0 + 1) with hES
  have hlay : WLay VO VS EO ES stPtr n n0 := by
    unfold WLay; rw [hbs] at hstD; omega
  let Fr : (ℕ → ℕ) → Prop := fun m =>
    ∀ a, (a < wPtr ∨ wPtr + wBlockSize n0 ≤ a) → (a < stPtr ∨ stPtr + n ≤ a) → m a = mem a
  have hRd : ∀ {a len : ℕ}, WAway w wPtr n0 stPtr n a len →
      ∀ m, Fr m → ∀ i < len, m (a + i) = mem (a + i) := fun hD m hm i hi => by
    obtain ⟨⟨hD1, -⟩, hD2⟩ := hD
    exact hm _ (by rcases hD1 with h | h <;> [left; right] <;> omega)
      (by rcases hD2 with h | h <;> [left; right] <;> omega)
  have haw : arrPtr + cnt < 2 ^ w := hA.1.2
  have hpew : pePtr + n < 2 ^ w := hPe.1.2
  have hpaw : parPtr + n < 2 ^ w := hPa.1.2
  have hfw : fidPtr + tM < 2 ^ w := hF.1.2
  have hvw : vListPtr + n < 2 ^ w := hV.1.2
  have hyw : labYPtr + n < 2 ^ w := hY.1.2
  have hbw' : labBPtr + n < 2 ^ w := hB.1.2
  have hrw : rtPtr + n < 2 ^ w := hR.1.2
  have hESw : ES + n0 < 2 ^ w := by rw [hbs] at hbw; omega
  let Inv : ℕ → State → Prop := fun k st =>
    (∀ i < 12, st.regs i = args.getD i 0) ∧ st.regs 12 = VO ∧ st.regs 13 = VS ∧
    st.regs 14 = EO ∧ st.regs 15 = ES ∧ st.regs 16 = (wGroups K s pa k).length ∧
    st.regs 17 = vTotal (wGroups K s pa k) ∧ st.regs 18 = k ∧ Fr st.mem ∧
    WMem st.mem VO VS EO stPtr n vL (wGroups K s pa k) ∧
    (∀ j < k, st.mem (ES + j) = fid (pe (s j)))
  have hbody : ∀ k, 0 ≤ k → k < cnt → Triple w p (Inv k) (wScanBody bAdd)
      (normalPost fun st₁ => Inv (k + 1) { st₁ with regs := Function.update st₁.regs 18 (k + 1) } ∧
        st₁.regs 18 = k) (fun _ => 300) := by
    intro k _ hk st ω' hI
    obtain ⟨hRg, r12, r13, r14, r15, r16, r17, r18, hfr, hW, hE⟩ := hI
    have r1 : st.regs 1 = arrPtr := hRg 1 (by omega)
    have r2 : st.regs 2 = pePtr := hRg 2 (by omega)
    have r3 : st.regs 3 = parPtr := hRg 3 (by omega)
    have r4 : st.regs 4 = fidPtr := hRg 4 (by omega)
    have r5 : st.regs 5 = vListPtr := hRg 5 (by omega)
    have r6 : st.regs 6 = labYPtr := hRg 6 (by omega)
    have r7 : st.regs 7 = labBPtr := hRg 7 (by omega)
    have r8 : st.regs 8 = rtPtr := hRg 8 (by omega)
    have r9 : st.regs 9 = stPtr := hRg 9 (by omega)
    have GI := groupsInv_of_le (pa := pa) hK.1 k hk.le
    obtain ⟨G, hG⟩ : ∃ G, wGroups K s pa k = G := ⟨_, rfl⟩
    rw [hG] at GI r16 r17 hW
    have hGl : G.length ≤ k := length_le GI
    have hGv : vTotal G ≤ 2 * k := vTotal_le GI
    obtain ⟨hsk, hpak, hpek⟩ := hlt k hk
    obtain ⟨hsk1, -, -⟩ := hlt (k - 1) (by omega)
    have m_sk : st.mem (arrPtr + k) = s k := (hRd hA _ hfr k hk).trans (hsx k)
    have m_sk1 : st.mem (arrPtr + (k - 1)) = s (k - 1) :=
      (hRd hA _ hfr (k - 1) (by omega)).trans (hsx _)
    have m_y0 : st.mem (labYPtr + s k) = lY (s k) := (hRd hY _ hfr _ hsk).trans (hlYx _)
    have m_y1 : st.mem (labYPtr + s (k - 1)) = lY (s (k - 1)) :=
      (hRd hY _ hfr _ hsk1).trans (hlYx _)
    have m_b0 : st.mem (labBPtr + s k) = lB (s k) := (hRd hB _ hfr _ hsk).trans (hlBx _)
    have m_b1 : st.mem (labBPtr + s (k - 1)) = lB (s (k - 1)) :=
      (hRd hB _ hfr _ hsk1).trans (hlBx _)
    have m_r0 : st.mem (rtPtr + s k) = rtf (s k) := (hRd hR _ hfr _ hsk).trans (hrtx _)
    have m_r1 : st.mem (rtPtr + s (k - 1)) = rtf (s (k - 1)) :=
      (hRd hR _ hfr _ hsk1).trans (hrtx _)
    have hcont : ∀ (G1 : List (List ℕ × List ℕ)) (st1 : State) (c0 : ℕ),
        G1 = (if IsBoundary K s k then G ++ [([], [])] else G) →
        (∀ i < 12, st1.regs i = args.getD i 0) → st1.regs 12 = VO → st1.regs 13 = VS →
        st1.regs 14 = EO → st1.regs 15 = ES → st1.regs 16 = G1.length →
        st1.regs 17 = vTotal G1 → st1.regs 18 = k → st1.regs 19 = s k → Fr st1.mem →
        WMem st1.mem VO VS EO stPtr n vL G1 → (∀ j < k, st1.mem (ES + j) = fid (pe (s j))) →
        c0 + 140 ≤ 300 →
        ∃ o st' c, Runs w p ω' (wScanRest bAdd) st1 o st' c ∧
          normalPost (fun st₁ => Inv (k + 1)
            { st₁ with regs := Function.update st₁.regs 18 (k + 1) } ∧ st₁.regs 18 = k) o st' ∧
          c0 + c ≤ 300 := by
      intro G1 st1 c0 hG1 q0 q12 q13 q14 q15 q16 q17 q18 q19 hfr1 hW1 hE1 hc0
      have hk0 : ¬ IsBoundary K s k → k ≠ 0 := fun h he => h (Or.inl he)
      have hG1ne : G1 ≠ [] := by
        rw [hG1]; split_ifs with hb
        · simp
        · intro he; exact hk0 hb (GI.hnil.mp he)
      have hG1l : G1.length ≤ k + 1 := by
        rw [hG1]; split_ifs
        · simp only [List.length_append, List.length_singleton]; omega
        · omega
      have hG1v : vTotal G1 = vTotal G := by
        rw [hG1]; split_ifs
        · rw [vTotal_eq, vTotal_eq, flatV_append_nil]
        · rfl
      have p2 : st1.regs 2 = pePtr := q0 2 (by omega)
      have p3 : st1.regs 3 = parPtr := q0 3 (by omega)
      have p4 : st1.regs 4 = fidPtr := q0 4 (by omega)
      have p5 : st1.regs 5 = vListPtr := q0 5 (by omega)
      have p9 : st1.regs 9 = stPtr := q0 9 (by omega)
      have n_pe : st1.mem (pePtr + s k) = pe (s k) := (hRd hPe _ hfr1 _ hsk).trans (hpex _)
      have n_fid : st1.mem (fidPtr + pe (s k)) = fid (pe (s k)) :=
        (hRd hF _ hfr1 _ hpek).trans (hfidx _)
      unfold wScanRest
      refine runs_seq_store_le (x := ES + k) (v := fid (pe (s k))) (by eval_expr)
        (by rw [← n_fid, ← n_pe]; eval_expr) ?_
      obtain ⟨m2, hm2⟩ : ∃ m, m = Function.update st1.mem (ES + k) (fid (pe (s k))) := ⟨_, rfl⟩
      rw [← hm2]
      have hfr2 : Fr m2 := fun a ha1 ha2 => by
        rw [hm2, Function.update_of_ne (by rw [hbs] at ha1; omega)]; exact hfr1 a ha1 ha2
      have hW2 : WMem m2 VO VS EO stPtr n vL G1 := by
        refine hW1.congr (N := n0) (by omega) (by omega) fun a ha => ?_
        rw [hm2, Function.update_of_ne]
        obtain ⟨l1, l2, l3, l4⟩ := hlay
        omega
      have hE2 : ∀ j < k + 1, m2 (ES + j) = fid (pe (s j)) := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [hm2, Function.update_of_ne (by omega)]; exact hE1 j hj
        · rw [hm2, Function.update_self]
      obtain ⟨G2, hG2⟩ : ∃ G', G' = pushLast (eAdd (s k)) G1 := ⟨_, rfl⟩
      have hW2' : WMem m2 VO VS EO stPtr n vL G2 := hG2 ▸ hW2.addElem hG1ne (s k)
      have hl2 : G2.length = G1.length := hG2 ▸ pushLast_length _ hG1ne
      have hv2 : vTotal G2 = vTotal G1 := by
        rw [hG2, vTotal_eq, vTotal_eq, flatV_pushLast_eAdd _ hG1ne]
      have hG2ne : G2 ≠ [] := hG2 ▸ pushLast_ne_nil _ _
      have n_vL : m2 (vListPtr + s k) = vL (s k) := (hRd hV _ hfr2 _ hsk).trans (hvLx _)
      obtain ⟨hW3, hret3⟩ := hW2'.addVert hG2ne hlay (by omega) hsk n_vL (fun _ => by omega)
      rw [hl2, hv2] at hW3 hret3
      refine runs_seq_call_le (vs := [stPtr, vListPtr, VS, s k, G1.length, vTotal G1]) hAdd
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
            (evalArgs_nil _ _)))))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        ⟨stPtr, vListPtr, VS, s k, G1.length, vTotal G1, rfl, by omega, by omega, by omega,
          by omega, by omega⟩ ?_
      rintro v mem3 pos3 ⟨a0, a1, a2, a3, a4, a5, heq, hret, hmem⟩
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
      obtain ⟨G3, hG3⟩ : ∃ G', G' = pushLast (vAdd (s k)) G2 := ⟨_, rfl⟩
      rw [← hG3] at hW3 hret3
      rw [← hmem] at hW3
      have hv3 : v = vTotal G3 := by rw [hret, hret3]
      have hl3 : G3.length = G1.length := by rw [hG3, pushLast_length _ hG2ne, hl2]
      have hG3ne : G3 ≠ [] := hG3 ▸ pushLast_ne_nil _ _
      have hv3le : vTotal G3 ≤ vTotal G1 + 1 := by
        rw [hG3, vTotal_eq, flatV_pushLast_vAdd _ hG2ne]
        have := vTotal_eq G2
        rw [hv2] at this
        split_ifs
        · omega
        · simp only [List.length_append, List.length_singleton]; omega
      have hm3o : ∀ a, a ≠ stPtr + s k → a ≠ VS + vTotal G1 → mem3 a = m2 a := fun a h1 h2 => by
        rw [hmem]; exact wAddVMem_other h1 h2
      have hfr3 : Fr mem3 := fun a ha1 ha2 => by
        rw [hm3o a (by omega) (by rw [hbs] at ha1; omega)]; exact hfr2 a ha1 ha2
      have hE3 : ∀ j < k + 1, mem3 (ES + j) = fid (pe (s j)) := fun j hj => by
        obtain ⟨l1, l2, l3, l4⟩ := hlay
        rw [hm3o _ (by omega) (by omega)]; exact hE2 j hj
      have n_pa : mem3 (parPtr + s k) = pa (s k) := (hRd hPa _ hfr3 _ hsk).trans (hpax _)
      have n_vL3 : mem3 (vListPtr + pa (s k)) = vL (pa (s k)) :=
        (hRd hV _ hfr3 _ hpak).trans (hvLx _)
      obtain ⟨hW4, hret4⟩ := hW3.addVert hG3ne hlay (by omega) hpak n_vL3 (fun _ => by omega)
      rw [hl3] at hW4 hret4
      obtain ⟨G4, hG4⟩ : ∃ G', G' = pushLast (vAdd (pa (s k))) G3 := ⟨_, rfl⟩
      rw [← hG4] at hW4 hret4
      have hsplit : wGroups K s pa (k + 1) = G4 := by
        rw [wGroups_succ_split, hG, ← hG1, ← hG2, ← hG3, ← hG4]
      have hl4 : G4.length = G1.length := by rw [hG4, pushLast_length _ hG3ne, hl3]
      refine runs_call_le (vs := [stPtr, vListPtr, VS, pa (s k), G1.length, vTotal G3]) hAdd
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by rw [← n_pa]; eval_expr) (evalArgs_cons (by eval_expr)
            (evalArgs_cons (by rw [← hv3]; eval_expr) (evalArgs_nil _ _)))))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        ⟨stPtr, vListPtr, VS, pa (s k), G1.length, vTotal G3, rfl, by omega, by omega, by omega,
          by omega, by omega⟩ ?_
      rintro v' mem4 pos4 ⟨b0, b1, b2, b3, b4, b5, heq', hret', hmem'⟩
      simp only [List.cons.injEq, and_true] at heq'
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq'
      rw [← hmem'] at hW4
      have hv4 : v' = vTotal G4 := by rw [hret', hret4]
      have hm4o : ∀ a, a ≠ stPtr + pa (s k) → a ≠ VS + vTotal G3 → mem4 a = mem3 a :=
        fun a h1 h2 => by rw [hmem']; exact wAddVMem_other h1 h2
      refine ⟨⟨⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha1 ha2 => ?_, ?_,
        fun j hj => ?_⟩, ?_⟩, ?_⟩
      · simp only [Function.update_of_ne (show i ≠ 18 by omega),
          Function.update_of_ne (show i ≠ 17 by omega)]
        exact q0 i hi
      · simpa using q12
      · simpa using q13
      · simpa using q14
      · simpa using q15
      · simp only [Function.update_of_ne (show (16 : ℕ) ≠ 18 by omega),
          Function.update_of_ne (show (16 : ℕ) ≠ 17 by omega), hsplit, hl4]
        exact q16
      · simp only [Function.update_of_ne (show (17 : ℕ) ≠ 18 by omega), Function.update_self,
          hsplit, hv4]
      · simp
      · dsimp only
        rw [hm4o a (by omega) (by rw [hbs] at ha1; omega)]; exact hfr3 a ha1 ha2
      · dsimp only; rw [hsplit]; exact hW4
      · dsimp only
        obtain ⟨l1, l2, l3, l4⟩ := hlay
        rw [hm4o _ (by omega) (by omega)]; exact hE3 j hj
      · simp only [Function.update_of_ne (show (18 : ℕ) ≠ 17 by omega)]
        exact q18
      · simp only [argsSize, Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const,
          wAddVContract]
        omega
    have hbnd : ((if lY (s k) = lY (s (k - 1)) then 1 else 0) +
        ((if lB (s k) = lB (s (k - 1)) then 1 else 0) +
          (if rtf (s k) = rtf (s (k - 1)) then 1 else 0)) < 3 + (if k = 0 then 1 else 0)) ↔
        IsBoundary K s k := by
      rw [wBnd_iff]
      unfold IsBoundary
      by_cases hk0 : k = 0
      · simp [hk0]
      · have := hK.2 (k - 1) (by omega) k hk
        simp only [hk0, false_or, ne_eq, this]
        constructor
        · rintro h ⟨a, b, c⟩; exact h ⟨a.symm, b.symm, c.symm⟩
        · rintro h ⟨a, b, c⟩; exact h ⟨a.symm, b.symm, c.symm⟩
    have hEG := eStart_length GI
    refine runs_start_le ?_
    unfold wScanBody
    refine runs_seq_assign_le (v := s k) (by rw [← m_sk]; eval_expr) ?_
    refine runs_seq_assign_le (v := s (k - 1)) (by rw [← m_sk1]; eval_expr) ?_
    refine runs_seq_assign_le (v := if k = 0 then 1 else 0) (by eval_expr) ?_
    refine runs_seq_assign_le (v := if lY (s k) = lY (s (k - 1)) then 1 else 0)
      (by rw [← m_y0, ← m_y1]; eval_expr) ?_
    refine runs_seq_assign_le (v := if lB (s k) = lB (s (k - 1)) then 1 else 0)
      (by rw [← m_b0, ← m_b1]; eval_expr) ?_
    refine runs_seq_assign_le (v := if rtf (s k) = rtf (s (k - 1)) then 1 else 0)
      (by rw [← m_r0, ← m_r1]; eval_expr) ?_
    refine runs_seq_cond_le (v := if ((if lY (s k) = lY (s (k - 1)) then 1 else 0) +
        ((if lB (s k) = lB (s (k - 1)) then 1 else 0) +
          (if rtf (s k) = rtf (s (k - 1)) then 1 else 0)) < 3 + (if k = 0 then 1 else 0))
        then 1 else 0) (by eval_expr <;> (split_ifs <;> omega)) (fun hb => ?_) (fun hb => ?_)
    · have hIB : IsBoundary K s k := hbnd.mp (by by_contra hc; simp [hc] at hb)
      unfold wScanNew
      refine runs_seq_assoc_le ?_
      refine runs_seq_store_le (x := VO + G.length) (v := vTotal G) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_store_le (x := EO + G.length) (v := k) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_assign_le (v := G.length + 1) (by eval_expr) ?_
      have hWn := hW.newGroup hlay (by omega) (by omega)
      rw [hEG] at hWn
      refine hcont (G ++ [([], [])]) _ _ (by rw [if_pos hIB]) (fun i hi => ?_) (by simp [r12])
        (by simp [r13]) (by simp [r14]) (by simp [r15]) (by simp [r16]) (by simp [r17, vTotal_eq, flatV_append_nil])
        (by simp [r18]) (by simp) (fun a ha1 ha2 => ?_) hWn (fun j hj => ?_) ?_
      · simp only [Function.update_apply]
        split_ifs <;> first | omega | exact hRg i hi
      · dsimp only
        rw [Function.update_of_ne (by rw [hbs] at ha1; omega),
          Function.update_of_ne (by rw [hbs] at ha1; omega)]
        exact hfr a ha1 ha2
      · dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hE j hj
      · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const]
        omega
    · have hIB : ¬ IsBoundary K s k := fun h => by
        rw [if_pos (hbnd.mpr h)] at hb; exact one_ne_zero hb
      refine runs_seq_nop_le ?_
      refine hcont G _ _ (by rw [if_neg hIB]) (fun i hi => ?_) (by simp [r12])
        (by simp [r13]) (by simp [r14]) (by simp [r15]) (by simp [r16]) (by simp [r17])
        (by simp [r18]) (by simp) hfr hW hE ?_
      · simp only [Function.update_apply]
        split_ifs <;> first | omega | exact hRg i hi
      · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const]
        omega
  have hloop : Triple w p (Inv 0) (forRange 18 (.const 0) (.reg 0) (wScanBody bAdd))
      (normalPost (Inv cnt))
      (fun _ => (cnt - 0) * (300 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 300 0 cnt (by omega) hw1 (fun _ => hcw) ?_ ?_ ?_ hbody
    · intro st hI
      refine ⟨by eval_expr, ?_⟩
      have h18 : Function.update st.regs 18 0 = st.regs :=
        Function.update_eq_self_iff.mpr hI.2.2.2.2.2.2.2.1.symm
      rw [h18]
      exact hI
    · intro i st _ _ hI; exact hI.2.2.2.2.2.2.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = cnt := hI.1 0 (by omega)
      eval_expr
  have hst : ∀ i < 12, (startState args mem pos).regs i = args.getD i 0 := fun i _ => rfl
  have s0 := hst 0 (by omega)
  have s10 := hst 10 (by omega)
  have s11 := hst 11 (by omega)
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at s0 s10 s11
  have hn0w : n0 < 2 ^ w := by rw [hbs] at hbw; omega
  refine runs_start_le ?_
  unfold wScanProc
  refine runs_seq_assign_le (v := VO) (by eval_expr) ?_
  refine runs_seq_assign_le (v := VS) (by eval_expr) ?_
  refine runs_seq_assign_le (v := EO) (by eval_expr) ?_
  refine runs_seq_assign_le (v := ES) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨fun i hi => ?_, by simp, by simp, by simp, by simp,
    by simp [wGroups], by simp [wGroups, vTotal, vStart], by simp [startState, hargs],
    fun a _ _ => rfl, wMem_nil _ _ _ _ _ _ _ hz, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ ?_
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | exact hst i hi
  rintro st ⟨hRg, r12, r13, r14, r15, r16, r17, -, hfr, hW, hE⟩
  have GI := groupsInv_of_le (pa := pa) hK.1 cnt le_rfl
  obtain ⟨G, hG⟩ : ∃ G, wGroups K s pa cnt = G := ⟨_, rfl⟩
  rw [hG] at GI r16 r17 hW
  have hGl : G.length ≤ cnt := length_le GI
  have hGv : vTotal G ≤ 2 * cnt := vTotal_le GI
  have hEG := eStart_length GI
  have r0 : st.regs 0 = cnt := hRg 0 (by omega)
  have r10 : st.regs 10 = wPtr := hRg 10 (by omega)
  obtain ⟨hVOm, hEOm, hVSm, -⟩ := hW
  refine runs_seq_store_le (x := VO + G.length) (v := vTotal G) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := EO + G.length) (v := cnt) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr) (v := G.length) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr + 1) (v := VO) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr + 2) (v := VS) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr + 3) (v := EO) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr + 4) (v := ES) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr + 5) (v := vTotal G) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := wPtr + 6) (v := cnt) (by eval_expr) (by eval_expr) ?_
  rw [← hG] at hVOm hEOm hVSm hGl hGv hEG ⊢
  subst hs hpa hpe hfid hvL hlY hlB hrtf
  refine runs_ret_le (v := 0) (by eval_expr) ⟨cnt, arrPtr, pePtr, parPtr, fidPtr, vListPtr,
    labYPtr, labBPtr, rtPtr, stPtr, wPtr, n0, n, K, rfl, rfl, hK, fun a ha1 ha2 => ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, fun j hj => ?_⟩ ?_
  all_goals try dsimp only
  · rw [hbs] at ha1
    simp only [Function.update_apply]
    split_ifs <;> first | omega | exact hfr a (by rw [hbs]; omega) ha2
  all_goals try (simp only [wOffNumPieces, wOffVertOffPtr, wOffVertsPtr, wOffEdgeOffPtr,
    wOffEdgesPtr, wOffTotalVerts, wOffTotalEdges, wVertOffBase, wVertsBase, wEdgeOffBase,
    wEdgesBase, wHdrSize, Function.update_apply] <;> split_ifs <;> first | omega | rfl | skip)
  all_goals first
    | (exact hVOm _ (by omega))
    | (exact hEOm _ (by omega))
    | (exact hVSm _ (by simpa using hj))
    | (simpa using hE _ hj)
    | (obtain rfl : i = (wGroups K (fun j => mem (arrPtr + j)) (fun y => mem (parPtr + y))
        cnt).length := by omega
       first | rfl | exact hEG.symm)
    | (simp only [List.length_map, ← vTotal_eq] at hj; omega)
    | skip
  simp only [wScanContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
    Expr.size_bin, Expr.size_load, Nat.sub_zero]
  omega
