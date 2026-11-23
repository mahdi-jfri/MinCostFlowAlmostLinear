module

public import MinCostFlow.LSF.Program.WBlock
public import MinCostFlow.LSF.Program.WKeysProof

/-!
# The proof of `wBlockProc`

`wBlock_meetsContract`: the three passes meet `wBlockContract`. The sort keeps the keys, and
the list it returns is a permutation of the kept indices. So the sorted list lists the kept
indices once each, in order of key, which is what the scan needs.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 4000000 in
theorem wBlock_meetsContract {w h : ℕ} {p : Program} {b bKeys bSort bScan : ℕ}
    (hp : p.procs[b]? = some (wBlockProc bKeys bSort bScan))
    (hKeys : MeetsContract w p bKeys (wKeysContract w h))
    (hSort : MeetsContract w p bSort (keyedMergeSortContract w h))
    (hScan : MeetsContract w p bScan (wScanContract w)) :
    MeetsContract w p b (wBlockContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, base, parPtr, fidPtr, vListPtr, wPtr,
    n0, tM, rfl, h16, hL, h3L, hnC, hnn0, hbase, hwP, hWD, hz, hPe, hOw, hY, hB, hR, hPa, hF,
    hV, hpe, hpar, hval⟩ := hpre
  set args := [n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, base, parPtr, fidPtr, vListPtr,
    wPtr, n0] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hws : wWorkSize n L = n * (3 * L) + 3 * n := rfl
  rw [hws] at hbase hWD hPe hOw hY hB hR hPa hF hV
  set kL := n * (3 * L) with hkL
  set A := base + kL with hA
  set Sc := A + n with hSc
  set St := Sc + n with hSt
  have hst : ∀ i < 14, (startState args mem pos).regs i = args.getD i 0 := fun i _ => rfl
  have s0 := hst 0 (by omega)
  have s1 := hst 1 (by omega)
  have s2 := hst 2 (by omega)
  have s3 := hst 3 (by omega)
  have s4 := hst 4 (by omega)
  have s5 := hst 5 (by omega)
  have s6 := hst 6 (by omega)
  have s7 := hst 7 (by omega)
  have s8 := hst 8 (by omega)
  have s9 := hst 9 (by omega)
  have s10 := hst 10 (by omega)
  have s11 := hst 11 (by omega)
  have s12 := hst 12 (by omega)
  have s13 := hst 13 (by omega)
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at s0 s1 s2 s3 s4 s5 s6 s7
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at s8 s9 s10 s11 s12 s13
  have hargw : ∀ a ∈ args, a < 2 ^ w := hwords
  have hkLw : kL < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold wBlockProc
  refine runs_seq_assign_le (v := A) (by eval_expr <;> omega) ?_
  refine runs_seq_assign_le (v := Sc) (by eval_expr <;> omega) ?_
  refine runs_seq_assign_le (v := St) (by eval_expr <;> omega) ?_
  -- pass 1: keys and the kept list
  refine runs_seq_call_le (vs := [n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, base, A]) hKeys
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | omega | exact hwords _ (by simp [hargs]))
    ⟨n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, base, A, tM, rfl, by omega, hL, h3L, hnC,
      by omega, by omega, Or.inr le_rfl,
      ⟨by rcases hPe.1 with h | h <;> [left; right] <;> omega,
        by rcases hPe.1 with h | h <;> [left; right] <;> omega, hPe.2.2⟩,
      ⟨by rcases hOw.1 with h | h <;> [left; right] <;> omega,
        by rcases hOw.1 with h | h <;> [left; right] <;> omega, hOw.2.2⟩,
      ⟨by rcases hY.1 with h | h <;> [left; right] <;> omega,
        by rcases hY.1 with h | h <;> [left; right] <;> omega, hY.2.2⟩,
      ⟨by rcases hB.1 with h | h <;> [left; right] <;> omega,
        by rcases hB.1 with h | h <;> [left; right] <;> omega, hB.2.2⟩,
      ⟨by rcases hR.1 with h | h <;> [left; right] <;> omega,
        by rcases hR.1 with h | h <;> [left; right] <;> omega, hR.2.2⟩, hpe, hval⟩ ?_
  rintro cnt mem1 pos1 ⟨n', r', pe', own', lY', lB', rt', L', base', A', heq1, hfr1, hcnt, hLA1,
    hkeys⟩
  simp only [List.cons.injEq, and_true] at heq1
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq1
  dsimp only [startState] at hfr1 hcnt hLA1 hkeys
  obtain ⟨kl, hkl⟩ : ∃ l, keptList r (fun i => mem (ownPtr + i)) (fun x => mem (pePtr + x)) n = l :=
    ⟨_, rfl⟩
  rw [hkl] at hcnt hLA1
  have hkln : kl.length ≤ n := hkl ▸ keptList_length_le _ _ _ n
  have hklm : ∀ y, y ∈ kl ↔ y < n ∧ y ≠ r ∧ mem (ownPtr + mem (pePtr + y)) = 0 := fun y => by
    rw [← hkl, mem_keptList]
  have hklnd : kl.Nodup := hkl ▸ keptList_nodup _ _ _ n
  subst hcnt
  -- pass 2: the sort
  have hidx : ∀ i < kl.length, mem1 (A + i) < n := fun i hi => by
    rw [hLA1 i hi]; exact ((hklm _).mp (List.getElem_mem hi)).1
  refine runs_seq_call_le (vs := [A, Sc, base, 3 * L, 0, kl.length]) hSort
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_nil _ _)))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨A, Sc, base, 3 * L, 0, kl.length, rfl, by omega, by omega, by omega, by omega, by omega,
      Or.inl (by omega), fun i _ hi => ?_⟩ ?_
  · have hi' := hidx i hi
    have hb := kblock_lt (keysPtr := base) (L := L) hi'
    dsimp only
    refine ⟨by omega, (hkeys _ hi').1, Or.inl (by omega), Or.inl (by omega)⟩
  rintro v2 mem2 pos2 ⟨A', Sc', base', L3, lo, hi, heq2, -, hsorted, hperm, hfr2⟩
  simp only [List.cons.injEq, and_true] at heq2
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq2
  dsimp only at hsorted hperm hfr2
  simp only [Nat.add_zero, Nat.sub_zero] at hsorted hperm hfr2
  set cnt := kl.length with hcntd
  have hsl1 : memSlice mem1 A cnt = kl :=
    List.ext_getElem (by simp [memSlice_length, hcntd]) fun i h1 h2 => by
      rw [memSlice_getElem]; exact hLA1 i h2
  rw [hsl1] at hperm
  obtain ⟨s, hs⟩ : ∃ f : ℕ → ℕ, f = fun j => mem2 (A + j) := ⟨_, rfl⟩
  have hSl : (List.range cnt).map s = memSlice mem2 A cnt := by rw [hs]; rfl
  have hSnd : ((List.range cnt).map s).Nodup := by rw [hSl]; exact hperm.nodup_iff.mpr hklnd
  have hSmem : ∀ y, y ∈ (List.range cnt).map s ↔
      y < n ∧ y ≠ r ∧ mem (ownPtr + mem (pePtr + y)) = 0 := fun y => by
    rw [hSl, hperm.mem_iff, hklm]
  have hslt : ∀ j < cnt, s j < n ∧ s j ≠ r := fun j hj => by
    have : s j ∈ (List.range cnt).map s := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    exact ⟨((hSmem _).mp this).1, ((hSmem _).mp this).2.1⟩
  obtain ⟨K, hK⟩ : ∃ f : ℕ → ℕ, f = fun x => unsignedVal mem1 (base + x * (3 * L)) h (3 * L) :=
    ⟨_, rfl⟩
  have hKv : ∀ x < n, K x = key3 (capacity h L) (mem (labYPtr + x)) (mem (labBPtr + x))
      (mem (rtPtr + x)) := fun x hx => by rw [hK]; exact (hkeys x hx).2
  -- the reads of the scan see the original memory
  have hag2 : ∀ a, (a < base ∨ base + (kL + 3 * n) ≤ a) → mem2 a = mem a := fun a ha => by
    rw [hfr2 a (by omega) (by omega), hfr1 a (by omega) (by omega)]
  have hRd : ∀ {a len : ℕ}, BAway w base (kL + 3 * n) wPtr n0 a len → ∀ i < len,
      mem2 (a + i) = mem (a + i) := fun hD i hi => hag2 _ (by rcases hD.1 with h | h <;> omega)
  have hKok : ∀ (lY lB rt : ℕ → ℕ), (∀ x < n, lY x = mem (labYPtr + x)) →
      (∀ x < n, lB x = mem (labBPtr + x)) → (∀ x < n, rt x = mem (rtPtr + x)) →
      WKeyOK K s lY lB rt cnt := by
    intro lY lB rt h1 h2 h3
    refine ⟨fun i j hij hj => ?_, fun j hj j' hj' => ?_⟩
    · rcases Nat.lt_or_eq_of_le hij with hij | rfl
      · have := List.pairwise_iff_getElem.mp hsorted i j (by simp [memSlice_length]; omega)
          (by simp [memSlice_length]; omega) hij
        simp only [memSlice_getElem] at this
        rw [hK, hs]; exact this
      · exact le_rfl
    · obtain ⟨a, -⟩ := hslt j hj
      obtain ⟨a', -⟩ := hslt j' hj'
      obtain ⟨y1, b1, r1⟩ := hval _ a
      obtain ⟨y2, b2, r2⟩ := hval _ a'
      rw [hKv _ a, hKv _ a', key3_iff (by omega) (by omega) (by omega) (by omega), h1 _ a, h1 _ a',
        h2 _ a, h2 _ a', h3 _ a, h3 _ a']
  have hsx : ∀ j, mem2 (A + j) = s j := fun j => by rw [hs]
  have hWDa := hWD
  -- pass 3: the scan
  refine runs_seq_call_le (vs := [cnt, A, pePtr, parPtr, fidPtr, vListPtr, labYPtr, labBPtr,
      rtPtr, St, wPtr, n0, n]) hScan
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | omega | exact hwords _ (by simp [hargs]))
    ⟨cnt, A, pePtr, parPtr, fidPtr, vListPtr, labYPtr, labBPtr, rtPtr, St, wPtr, n0, n, tM, K, rfl,
      h16, by omega, hwP, by omega, by rcases hWDa with h | h <;> [left; right] <;> omega,
      fun y hy => ?_,
      ⟨⟨by rcases hWDa with h | h <;> [left; right] <;> omega, by omega⟩, Or.inl (by omega)⟩,
      ⟨⟨hPe.2.1, hPe.2.2⟩, by rcases hPe.1 with h | h <;> [left; right] <;> omega⟩,
      ⟨⟨hPa.2.1, hPa.2.2⟩, by rcases hPa.1 with h | h <;> [left; right] <;> omega⟩,
      ⟨⟨hF.2.1, hF.2.2⟩, by rcases hF.1 with h | h <;> [left; right] <;> omega⟩,
      ⟨⟨hV.2.1, hV.2.2⟩, by rcases hV.1 with h | h <;> [left; right] <;> omega⟩,
      ⟨⟨hY.2.1, hY.2.2⟩, by rcases hY.1 with h | h <;> [left; right] <;> omega⟩,
      ⟨⟨hB.2.1, hB.2.2⟩, by rcases hB.1 with h | h <;> [left; right] <;> omega⟩,
      ⟨⟨hR.2.1, hR.2.2⟩, by rcases hR.1 with h | h <;> [left; right] <;> omega⟩,
      fun j hj => ?_, ?_⟩ ?_
  · dsimp only
    rw [hfr2 _ (by omega) (by omega), hfr1 _ (by omega) (by omega)]
    have := hz y hy
    rwa [show base + kL + 2 * n + y = St + y by omega] at this
  · dsimp only
    rw [hsx j]
    obtain ⟨hj1, hj2⟩ := hslt j hj
    rw [hRd hPa _ hj1, hRd hPe _ hj1]
    exact ⟨hj1, hpar _ hj1, hpe _ hj1 hj2⟩
  · dsimp only
    have : (fun j => mem2 (A + j)) = s := hs.symm
    rw [this]
    exact hKok _ _ _ (fun x hx => hRd hY x hx) (fun x hx => hRd hB x hx) (fun x hx => hRd hR x hx)
  rintro v3 mem3 pos3 ⟨cnt', A', pe', par', fid', vL', lY', lB', rt', St', w', n0', nst, K',
    heq3, -, hK', hfr3, g0, g1, g2, g3, g4, g5, g6, gVO, gEO, gVS, gES⟩
  simp only [List.cons.injEq, and_true] at heq3
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq3
  dsimp only at hK' hfr3 g0 g1 g2 g3 g4 g5 g6 gVO gEO gVS gES
  have hsfun : (fun j => mem2 (A + j)) = s := hs.symm
  rw [hsfun] at hK' g0 g5 gVO gEO gVS
  have hGeq : wGroups K' s (fun y => mem2 (parPtr + y)) cnt =
      wGroups K' s (fun y => mem (parPtr + y)) cnt :=
    wGroups_congr_pa cnt fun j hj => hRd hPa _ (hslt j hj).1
  rw [hGeq] at g0 g5 gVO gEO gVS
  have GI := groupsInv_of_le (pa := fun y => mem (parPtr + y)) hK'.1 cnt le_rfl
  have hflt : ∀ y ∈ flatV (wGroups K' s (fun y => mem (parPtr + y)) cnt), y < n := by
    intro y hy
    obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
    obtain ⟨z, hz, hyz⟩ := ((GI.hvert q hq).2 y).mp hyl
    have hzS : z ∈ (List.range cnt).map s := by
      rw [← GI.hflat]; exact List.mem_flatten.mpr ⟨q.1, List.mem_map_of_mem hq, hz⟩
    have hzn := ((hSmem z).mp hzS).1
    rcases hyz with rfl | rfl
    · exact hzn
    · exact hpar _ hzn
  have hVmap : (flatV (wGroups K' s (fun y => mem (parPtr + y)) cnt)).map
      (fun y => mem2 (vListPtr + y)) =
      (flatV (wGroups K' s (fun y => mem (parPtr + y)) cnt)).map (fun y => mem (vListPtr + y)) :=
    List.map_congr_left fun y hy => hRd hV _ (hflt y hy)
  rw [hVmap] at gVS
  refine runs_ret_le (v := cnt) (by eval_expr) ⟨n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L,
    base, parPtr, fidPtr, vListPtr, wPtr, n0, cnt, K', s, rfl, rfl, hkln, fun a ha1 ha2 => ?_,
    hSnd, hSmem, ?_, g0, g1, g2, g3, g4, g5, g6, gVO, gEO, gVS, fun j hj => ?_⟩ ?_
  · dsimp only
    rw [hws] at ha1
    rw [hfr3 a (by rcases ha2 with h | h <;> [left; right] <;> omega)
      (by rcases ha1 with h | h <;> [left; right] <;> omega)]
    rcases ha1 with h | h
    · exact hag2 a (Or.inl h)
    · exact hag2 a (Or.inr h)
  · refine ⟨hK'.1, fun j hj j' hj' => ?_⟩
    rw [hK'.2 j hj j' hj']
    dsimp only
    obtain ⟨a, -⟩ := hslt j hj
    obtain ⟨a', -⟩ := hslt j' hj'
    rw [hRd hY _ a, hRd hY _ a', hRd hB _ a, hRd hB _ a', hRd hR _ a, hRd hR _ a']
  · dsimp only
    rw [gES j hj, hsx j]
    obtain ⟨a, a2⟩ := hslt j hj
    rw [hRd hPe _ a, hRd hF _ (hpe _ a a2)]
  · have hc1 : Nat.clog 2 cnt ≤ Nat.clog 2 n := Nat.clog_mono_right 2 hkln
    have hc2 : (90 * (3 * L) + 180) * cnt * (Nat.clog 2 cnt + 1) ≤
        (270 * L + 180) * n * (Nat.clog 2 n + 1) := by
      rw [show 90 * (3 * L) + 180 = 270 * L + 180 by ring]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hkln) (by omega)
    simp only [wBlockContract, wKeysContract, keyedMergeSortContract, wScanContract, hargs,
      List.getD_cons_zero, List.getD_cons_succ, Expr.size_const, Expr.size_reg, Expr.size_bin,
      argsSize, Nat.sub_zero] at hc2 ⊢
    omega
