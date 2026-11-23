module

public import MinCostFlow.MinRatio.GraphLiveCopyLoops
public import WordRAM.DataStructure
import WordRAM.Logic
import WordRAM.Tactic

/-!
# Live-list copy of a dynamic named graph (`GraphLiveCopy`)

Assembles the five stages of `copyGraphLiveFromHeader` (`GraphLiveCopyLoops.lean`) into:
* `copyGraphLiveFromHeader_runs`: full correctness, frame, zero-tail, and `O(G.n + G.m + 1)` cost.
* `copyGraphLive_preserves_tool_runs`: caller-owned live copy preserving a local `DSRep`.
* `copyGraphLiveCost_le_17_dynGraphSize`: compatibility bound against the array-copy cost.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

private theorem copyGraphLiveHeader_runs {w src heap vc ec : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hsrc : st.regs 6 = src) (hheap : st.regs 5 = heap)
    (hG : DynGraphAt st.mem src vc ec G)
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out c, Runs w p ω copyGraphLiveHeader st .normal out c ∧ c ≤ 56 ∧
      out.regs 5 = heap ∧ out.regs 6 = src ∧ out.regs 10 = vc ∧ out.regs 11 = ec ∧
      out.regs 8 = G.n ∧ out.regs 63 = src + 4 ∧ out.regs 64 = heap + 4 ∧ out.regs 12 = 0 ∧
      out.pos = st.pos ∧
      out.mem (heap + dgVCapOff) = vc ∧ out.mem (heap + dgECapOff) = ec ∧
      out.mem (heap + dgNOff) = G.n ∧ out.mem (heap + dgMOff) = G.m ∧
      ZeroFrom out.mem (heap + 4) ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 63 → r ≠ 64 →
        out.regs r = st.regs r) := by
  have hsz : dynGraphSize vc ec = 4 + 7 * vc + 9 * ec := rfl
  have hm0 : st.mem src = vc := by simpa [dgVCapOff] using hG.2.2.2.1
  have hm1 : st.mem (src + 1) = ec := by simpa [dgECapOff] using hG.2.2.2.2.1
  have hm2 : st.mem (src + 2) = G.n := by simpa [dgNOff] using hG.2.2.2.2.2.1
  have hm3 : st.mem (src + 3) = G.m := by simpa [dgMOff] using hG.2.2.2.2.2.2.1
  suffices h : ∃ o out c, Runs w p ω copyGraphLiveHeader st o out c ∧
      (o = .normal ∧
        out.regs 5 = heap ∧ out.regs 6 = src ∧ out.regs 10 = vc ∧ out.regs 11 = ec ∧
        out.regs 8 = G.n ∧ out.regs 63 = src + 4 ∧ out.regs 64 = heap + 4 ∧ out.regs 12 = 0 ∧
        out.pos = st.pos ∧
        out.mem (heap + dgVCapOff) = vc ∧ out.mem (heap + dgECapOff) = ec ∧
        out.mem (heap + dgNOff) = G.n ∧ out.mem (heap + dgMOff) = G.m ∧
        ZeroFrom out.mem (heap + 4) ∧ (∀ a < heap, out.mem a = st.mem a) ∧
        (∀ r, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 63 → r ≠ 64 →
          out.regs r = st.regs r)) ∧ c ≤ 56 by
    rcases h with ⟨o, out, c, hr, ⟨rfl, hpost⟩, hc⟩
    exact ⟨out, c, hr, hc, hpost⟩
  refine runs_start_le ?_
  dsimp only [copyGraphLiveHeader]
  refine runs_seq_assign_le (v := vc) (by eval_expr) ?_
  refine runs_seq_assign_le (v := ec) (by eval_expr) ?_
  refine runs_seq_assign_le (v := G.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := G.m) (by eval_expr) ?_
  refine runs_seq_store_le (x := heap) (v := vc) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := heap + 1) (v := ec) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := heap + 2) (v := G.n) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := heap + 3) (v := G.m) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := src + 4) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 4) (by eval_expr) ?_
  refine runs_assign_le (v := 0) (by eval_expr) ?_ (by simp)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne, hheap]
  · simp [Function.update_of_ne, hsrc]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp
  · simp [dgVCapOff]
  · simp [dgECapOff]
  · simp [dgNOff]
  · simp [dgMOff]
  · intro a ha
    simp only [Function.update_of_ne (by omega : a ≠ heap + 3),
      Function.update_of_ne (by omega : a ≠ heap + 2),
      Function.update_of_ne (by omega : a ≠ heap + 1),
      Function.update_of_ne (by omega : a ≠ heap)]
    exact hz a (by omega)
  · intro a ha
    simp only [Function.update_of_ne (by omega : a ≠ heap + 3),
      Function.update_of_ne (by omega : a ≠ heap + 2),
      Function.update_of_ne (by omega : a ≠ heap + 1),
      Function.update_of_ne (by omega : a ≠ heap)]
  · intro r h8 h9 h10 h11 h12 h63 h64
    simp [Function.update_of_ne h12, Function.update_of_ne h64, Function.update_of_ne h63,
      Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h11,
      Function.update_of_ne h10]

private theorem copyGraphLiveMid_runs {w src heap vc ec : ℕ} {G : MGraph}
    {p : Program} {st1 : State} {ω : ℕ → Bool}
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w)
    (hr5 : st1.regs 5 = heap) (hr6 : st1.regs 6 = src) (hr10 : st1.regs 10 = vc)
    (hr11 : st1.regs 11 = ec) (hr63 : st1.regs 63 = src + 4) (hr64 : st1.regs 64 = heap + 4)
    (hmem_m : st1.mem (src + 3) = G.m) :
    ∃ out c, Runs w p ω copyGraphLiveMid st1 .normal out c ∧ c ≤ 25 ∧
      out.regs 5 = heap ∧ out.regs 6 = src ∧ out.regs 10 = ec ∧ out.regs 11 = ec ∧
      out.regs 8 = G.m ∧ out.regs 63 = src + 4 + 7 * vc ∧ out.regs 64 = heap + 4 + 7 * vc ∧
      out.regs 12 = 0 ∧ out.mem = st1.mem ∧ out.pos = st1.pos ∧
      (∀ r, r ≠ 8 → r ≠ 10 → r ≠ 12 → r ≠ 63 → r ≠ 64 → out.regs r = st1.regs r) := by
  have hsz : dynGraphSize vc ec = 4 + 7 * vc + 9 * ec := rfl
  suffices h : ∃ o out c, Runs w p ω copyGraphLiveMid st1 o out c ∧
      (o = .normal ∧
        out.regs 5 = heap ∧ out.regs 6 = src ∧ out.regs 10 = ec ∧ out.regs 11 = ec ∧
        out.regs 8 = G.m ∧ out.regs 63 = src + 4 + 7 * vc ∧ out.regs 64 = heap + 4 + 7 * vc ∧
        out.regs 12 = 0 ∧ out.mem = st1.mem ∧ out.pos = st1.pos ∧
        (∀ r, r ≠ 8 → r ≠ 10 → r ≠ 12 → r ≠ 63 → r ≠ 64 → out.regs r = st1.regs r)) ∧ c ≤ 25 by
    rcases h with ⟨o, out, c, hr, ⟨rfl, hpost⟩, hc⟩
    exact ⟨out, c, hr, hc, hpost⟩
  refine runs_start_le ?_
  dsimp only [copyGraphLiveMid]
  refine runs_seq_assign_le (v := src + 4 + 7 * vc) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 4 + 7 * vc) (by eval_expr) ?_
  refine runs_seq_assign_le (v := ec) (by eval_expr) ?_
  refine runs_seq_assign_le (v := G.m) (by eval_expr) ?_
  refine runs_assign_le (v := 0) (by eval_expr) ?_ (by simp)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp [Function.update_of_ne, hr5]
  · simp [Function.update_of_ne, hr6]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne, hr11]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · simp
  · intro r h8 h10 h12 h63 h64
    simp [Function.update_of_ne h12, Function.update_of_ne h8, Function.update_of_ne h10,
      Function.update_of_ne h64, Function.update_of_ne h63]

private theorem copyGraphLiveEnd_runs {w heap vc ec : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hword : heap + dynGraphSize vc ec < 2 ^ w) (hw : 9 < 2 ^ w)
    (hr5 : st.regs 5 = heap) (hr10 : st.regs 10 = ec) (hr64 : st.regs 64 = heap + 4 + 7 * vc) :
    ∃ out c, Runs w p ω copyGraphLiveEnd st .normal out c ∧ c ≤ 9 ∧
      out.regs 6 = heap ∧ out.regs 5 = heap + dynGraphSize vc ec ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r, r ≠ 5 → r ≠ 6 → out.regs r = st.regs r) := by
  have hsz : heap + dynGraphSize vc ec = heap + 4 + 7 * vc + 9 * ec := by
    unfold dynGraphSize; omega
  suffices h : ∃ o out c, Runs w p ω copyGraphLiveEnd st o out c ∧
      (o = .normal ∧
        out.regs 6 = heap ∧ out.regs 5 = heap + dynGraphSize vc ec ∧
        out.mem = st.mem ∧ out.pos = st.pos ∧
        (∀ r, r ≠ 5 → r ≠ 6 → out.regs r = st.regs r)) ∧ c ≤ 9 by
    rcases h with ⟨o, out, c, hr, ⟨rfl, hpost⟩, hc⟩
    exact ⟨out, c, hr, hc, hpost⟩
  refine runs_start_le ?_
  dsimp only [copyGraphLiveEnd]
  refine runs_seq_assign_le (v := heap) (by eval_expr) ?_
  refine runs_assign_le (v := heap + 4 + 7 * vc + 9 * ec) (by eval_expr) ?_ (by simp)
  refine ⟨rfl, ?_, ?_, rfl, rfl, ?_⟩
  · simp [Function.update_of_ne]
  · simp [hsz]
  · intro r h5 h6
    simp [Function.update_of_ne h5, Function.update_of_ne h6]

/-- **Live-list copy of a dynamic graph.** Walks only the `G.n` live vertices and `G.m` live edges
into fresh zero memory starting at `heap`, taking at most `copyGraphLiveCost G.n G.m` steps and
preserving memory below `heap` and registers outside `{5, 6, 8, 9, 10, 11, 12, 63, 64}`. -/
theorem copyGraphLiveFromHeader_runs {w src heap vc ec : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hsrc : st.regs 6 = src) (hheap : st.regs 5 = heap)
    (hG : DynGraphAt st.mem src vc ec G)
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out cost, Runs w p ω copyGraphLiveFromHeader st .normal out cost ∧
      DynGraphAt out.mem heap vc ec G ∧
      out.regs 6 = heap ∧ out.regs 5 = heap + dynGraphSize vc ec ∧
      ZeroFrom out.mem (heap + dynGraphSize vc ec) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ out.pos = st.pos ∧
      cost ≤ copyGraphLiveCost G.n G.m ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 63 → r ≠ 64 →
        out.regs r = st.regs r) := by
  have hsz : dynGraphSize vc ec = 4 + 7 * vc + 9 * ec := rfl
  have hG0 : DynGraphAt st.mem src vc ec G := hG
  obtain ⟨hvalid, hvCap, heCap, _, _, _, hGm, _, ⟨vL, hvLen, hvNodup, hvMem, hvList, _⟩,
    he2i, hi2e, _, ⟨eL, heLen, heNodup, heMem, heList, _⟩, hends, ⟨incL, hinc⟩⟩ := hG
  -- 1. Header
  obtain ⟨s1, c1, r1, hc1, hs1_5, hs1_6, hs1_10, hs1_11, hs1_8, hs1_63, hs1_64, hs1_12, hs1_pos,
    hs1_m0, hs1_m1, hs1_m2, hs1_m3, hs1_hz, hs1_fr, hs1_regs⟩ :=
    copyGraphLiveHeader_runs (ω := ω) hsrc hheap hG0 hdisj hword hw hz
  -- 2. Vertex loop
  have hVInit : vLoopInv src heap vc ec G vL st s1.mem 0 s1 := by
    refine ⟨hs1_5, hs1_6, hs1_10, hs1_11, hs1_8, hs1_63, hs1_64, hs1_12, hs1_pos, hs1_regs,
      fun _ _ => rfl, fun _ hj => by omega, ?_, fun _ hj => by omega,
      fun _ hj => by omega, fun _ hj => by omega, ?_, ?_⟩
    · intro v hv
      simp only [Nat.not_lt_zero, false_and, exists_false, ↓reduceIte]
      exact hs1_hz _ (by unfold dgVPresBase; omega)
    · intro v hv
      simp only [Nat.not_lt_zero, false_and, exists_false, ↓reduceIte]
      exact hs1_hz _ (by unfold dgSlotDegBase; omega)
    · intro v hv
      simp only [Nat.not_lt_zero, false_and, exists_false, ↓reduceIte]
      exact hs1_hz _ (by unfold dgIncHeadBase; omega)
  obtain ⟨s2, c2, r2, hs2_inv, hc2⟩ :=
    copyGraphLiveVLoop_runs (ω := ω) hG0 hvLen hvNodup hvMem hvList hdisj hword hw hs1_fr hVInit
  rcases hs2_inv with ⟨hs2_5, hs2_6, hs2_10, hs2_11, _, hs2_63, hs2_64, _, hs2_pos, hs2_regs,
    hs2_fr, hs2_VL, hs2_VP, hs2_VPos, hs2_E2I, hs2_I2E, hs2_Deg, hs2_Head⟩
  -- 3. Transition
  have hs2_m_src : s2.mem (src + 3) = G.m := by
    rw [hs2_fr _ (by omega), hs1_fr _ (by omega)]; exact hGm
  obtain ⟨s3, c3, r3, hc3, hs3_5, hs3_6, hs3_10, hs3_11, hs3_8, hs3_63, hs3_64, hs3_12, hs3_mem,
    hs3_pos, hs3_regs⟩ :=
    copyGraphLiveMid_runs (ω := ω) (G := G) hdisj hword hw
      hs2_5 hs2_6 hs2_10 hs2_11 hs2_63 hs2_64 hs2_m_src
  -- 4. Edge loop
  have hs3_fr_lt : ∀ a < heap, s3.mem a = st.mem a := fun a ha => by
    rw [hs3_mem, hs2_fr a (by omega), hs1_fr a ha]
  have hEInit : eLoopInv src heap vc ec G eL st s3.mem 0 s3 := by
    refine ⟨hs3_5, hs3_6, hs3_10, hs3_11, hs3_8, hs3_63, hs3_64, hs3_12, hs3_pos.trans hs2_pos,
      fun r h8 h9 h10 h11 h12 h63 h64 =>
        (hs3_regs r h8 h10 h12 h63 h64).trans (hs2_regs r h8 h9 h10 h11 h12 h63 h64),
      fun _ _ => rfl, fun _ hj => by omega, ?_, fun _ hj => by omega,
      fun _ hj => by omega, fun _ hj => by omega, fun _ hj => by omega, fun _ hj => by omega⟩
    intro e he
    simp only [Nat.not_lt_zero, false_and, exists_false, ↓reduceIte]
    rw [hs3_mem, hs2_fr _ (by unfold dgEPresBase; omega)]
    exact hs1_hz _ (by unfold dgEPresBase; omega)
  obtain ⟨s4, c4, r4, hs4_inv, hc4⟩ :=
    copyGraphLiveELoop_runs (ω := ω) hG0 heLen heNodup heMem heList hdisj hword hw hs3_fr_lt hEInit
  rcases hs4_inv with ⟨hs4_5, _, hs4_10, _, _, _, hs4_64, _, hs4_pos, hs4_regs,
    hs4_fr, hs4_EL, hs4_EP, hs4_EPos, hs4_Tail, hs4_Head, hs4_Prev, hs4_Next⟩
  -- 5. End
  obtain ⟨s5, c5, r5, hc5, hs5_6, hs5_5, hs5_mem, hs5_pos, hs5_regs⟩ :=
    copyGraphLiveEnd_runs (ω := ω) hword hw hs4_5 hs4_10 hs4_64
  -- Assemble DynGraphAt
  have hv_iff (v : ℕ) : (∃ j < G.n, ∃ hjl : j < vL.length, vL[j]'hjl = v) ↔ v ∈ G.V := by
    rw [← hvMem v, List.mem_iff_getElem]
    exact ⟨fun ⟨j, _, hjl, eq⟩ => ⟨j, hjl, eq⟩, fun ⟨j, hjl, eq⟩ => ⟨j, by omega, hjl, eq⟩⟩
  have he_iff (e : ℕ) : (∃ j < G.m, ∃ hjl : j < eL.length, eL[j]'hjl = e) ↔ e ∈ G.E := by
    rw [← heMem e, List.mem_iff_getElem]
    exact ⟨fun ⟨j, _, hjl, eq⟩ => ⟨j, hjl, eq⟩, fun ⟨j, hjl, eq⟩ => ⟨j, by omega, hjl, eq⟩⟩
  have hmem_v (a : ℕ) (ha : a < heap + 4 + 7 * vc) : s5.mem a = s2.mem a := by
    rw [hs5_mem, hs4_fr a (Or.inl ha), hs3_mem]
  have hmem_e2i (v : ℕ) (hv : v ∈ G.V) :
      s5.mem (dgExtToIntBase heap vc + v) = st.mem (dgExtToIntBase src vc + v) := by
    have hvlt := hvCap v hv
    obtain ⟨j, hj, hjl, rfl⟩ := (hv_iff v).mpr hv
    rw [hmem_v _ (by unfold dgExtToIntBase; omega)]
    exact hs2_E2I j hj hjl
  have hmem_i2e (v : ℕ) (hv : v ∈ G.V) :
      s5.mem (dgIntToExtBase heap vc + v) = st.mem (dgIntToExtBase src vc + v) := by
    have hvlt := hvCap v hv
    obtain ⟨j, hj, hjl, rfl⟩ := (hv_iff v).mpr hv
    rw [hmem_v _ (by unfold dgIntToExtBase; omega)]
    exact hs2_I2E j hj hjl
  have hmem_tail (e : ℕ) (he : e ∈ G.E) :
      s5.mem (dgETailSlotBase heap vc ec + e) = st.mem (dgETailSlotBase src vc ec + e) := by
    obtain ⟨j, hj, hjl, rfl⟩ := (he_iff e).mpr he
    rw [hs5_mem]; exact hs4_Tail j hj hjl
  have hmem_head (e : ℕ) (he : e ∈ G.E) :
      s5.mem (dgEHeadSlotBase heap vc ec + e) = st.mem (dgEHeadSlotBase src vc ec + e) := by
    obtain ⟨j, hj, hjl, rfl⟩ := (he_iff e).mpr he
    rw [hs5_mem]; exact hs4_Head j hj hjl
  have hmem_he (h : ℕ) (he : h / 2 ∈ G.E) :
      s5.mem (dgHePrevBase heap vc ec + h) = st.mem (dgHePrevBase src vc ec + h) ∧
      s5.mem (dgHeNextBase heap vc ec + h) = st.mem (dgHeNextBase src vc ec + h) := by
    obtain ⟨j, hj, hjl, hjeq⟩ := (he_iff (h / 2)).mpr he
    have hcases : h = 2 * (eL[j]'hjl) ∨ h = 2 * (eL[j]'hjl) + 1 := by omega
    rcases hcases with rfl | rfl
    · rw [hs5_mem]; exact ⟨(hs4_Prev j hj hjl).1, (hs4_Next j hj hjl).1⟩
    · rw [hs5_mem]; exact ⟨(hs4_Prev j hj hjl).2, (hs4_Next j hj hjl).2⟩
  have hDG : DynGraphAt s5.mem heap vc ec G := by
    refine ⟨hvalid, hvCap, heCap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmem_v _ (by unfold dgVCapOff; omega), hs2_fr _ (by unfold dgVCapOff; omega)]; exact hs1_m0
    · rw [hmem_v _ (by unfold dgECapOff; omega), hs2_fr _ (by unfold dgECapOff; omega)]; exact hs1_m1
    · rw [hmem_v _ (by unfold dgNOff; omega), hs2_fr _ (by unfold dgNOff; omega)]; exact hs1_m2
    · rw [hmem_v _ (by unfold dgMOff; omega), hs2_fr _ (by unfold dgMOff; omega)]; exact hs1_m3
    · intro v hv
      rw [hmem_v _ (by unfold dgVPresBase; omega), hs2_VP v hv]
      simp [hv_iff v]
    · refine ⟨vL, hvLen, hvNodup, hvMem, ?_, ?_⟩
      · intro i hi
        have hlt : i < vc := lt_of_lt_of_le (by omega) (graph_n_le_vCap hG0)
        rw [hmem_v _ (by unfold dgVListBase; omega)]
        exact hs2_VL i (by omega) hi
      · intro i hi
        have hvlt := hvCap _ ((hvMem _).mp (List.getElem_mem hi))
        rw [hmem_v _ (by unfold dgVPosBase; omega)]
        exact hs2_VPos i (by omega) hi
    · intro v hv
      rw [hmem_e2i v hv]
      have hslot := (he2i v hv).1
      rw [hmem_i2e _ hslot]
      exact he2i v hv
    · intro s hs
      rw [hmem_i2e s hs]
      have hvet := (hi2e s hs).1
      rw [hmem_e2i _ hvet]
      exact hi2e s hs
    · intro e he
      rw [hs5_mem, hs4_EP e he]; simp [he_iff e]
    · refine ⟨eL, heLen, heNodup, heMem, ?_, ?_⟩
      · intro i hi; rw [hs5_mem]; exact hs4_EL i (by omega) hi
      · intro i hi; rw [hs5_mem]; exact hs4_EPos i (by omega) hi
    · intro e he
      rw [hmem_tail e he, hmem_head e he, hmem_e2i _ (hvalid e he).1, hmem_e2i _ (hvalid e he).2]
      exact hends e he
    · refine ⟨incL, fun s hs => ?_⟩
      obtain ⟨hdll, hdeg, hmem⟩ := hinc s hs
      have hmem_s : ∀ h, h ∈ incL s ↔ h < 2 * ec ∧ h / 2 ∈ G.E ∧
          (if h % 2 = 0 then s5.mem (dgETailSlotBase heap vc ec + h / 2)
           else s5.mem (dgEHeadSlotBase heap vc ec + h / 2)) = s := by
        intro h
        rw [hmem h]
        refine and_congr_right fun _ => and_congr_right fun he => ?_
        rw [hmem_tail _ he, hmem_head _ he]
      by_cases hsV : s ∈ G.V
      · have hhd_eq : s5.mem (dgIncHeadBase heap vc + s) = st.mem (dgIncHeadBase src vc + s) := by
          rw [hmem_v _ (by unfold dgIncHeadBase; omega), hs2_Head s hs]
          simp [hv_iff s, hsV]
        have hdeg_eq : s5.mem (dgSlotDegBase heap vc + s) = st.mem (dgSlotDegBase src vc + s) := by
          rw [hmem_v _ (by unfold dgSlotDegBase; omega), hs2_Deg s hs]
          simp [hv_iff s, hsV]
        refine ⟨⟨hdll.1, hdll.2.1, hhd_eq.trans hdll.2.2.1, fun i hi => ?_⟩,
          hdeg_eq.trans hdeg, hmem_s⟩
        have hhe : (incL s)[i] / 2 ∈ G.E := ((hmem _).mp (List.getElem_mem hi)).2.1
        rw [(hmem_he _ hhe).1, (hmem_he _ hhe).2]
        exact hdll.2.2.2 i hi
      · have hnil : incL s = [] := by
          cases hL : incL s with
          | nil => rfl
          | cons h rest =>
            have hin : h ∈ incL s := by rw [hL]; exact List.mem_cons_self
            obtain ⟨_, he, heq⟩ := (hmem h).mp hin
            exfalso; apply hsV
            by_cases hmod : h % 2 = 0
            · simp only [hmod, ↓reduceIte] at heq
              rw [← heq, (hends _ he).1]; exact (he2i _ (hvalid _ he).1).1
            · simp only [hmod, ↓reduceIte] at heq
              rw [← heq, (hends _ he).2]; exact (he2i _ (hvalid _ he).2).1
        have hhd0 : s5.mem (dgIncHeadBase heap vc + s) = 0 := by
          rw [hmem_v _ (by unfold dgIncHeadBase; omega), hs2_Head s hs]
          simp [hv_iff s, hsV]
        have hdeg0 : s5.mem (dgSlotDegBase heap vc + s) = 0 := by
          rw [hmem_v _ (by unfold dgSlotDegBase; omega), hs2_Deg s hs]
          simp [hv_iff s, hsV]
        refine ⟨⟨by simp [hnil], by simp [hnil], by simp [hnil, hhd0], fun i hi => by simp [hnil] at hi⟩,
          by simp [hnil, hdeg0], hmem_s⟩
  refine ⟨s5, c1 + (c2 + (c3 + (c4 + c5 + 1) + 1) + 1) + 1, ?_, hDG, hs5_6, hs5_5, ?_, ?_,
    hs5_pos.trans hs4_pos, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, c3, _, r3,
          runs_seq_iff.mpr (Or.inr ⟨s4, c4, c5, r4, r5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  · intro a ha
    rw [hs5_mem, hs4_fr a (Or.inr ha), hs3_mem, hs2_fr a (Or.inr (by omega))]
    exact hs1_hz a (by omega)
  · intro a ha
    rw [hs5_mem, hs4_fr a (Or.inl (by omega)), hs3_mem, hs2_fr a (Or.inl (by omega))]
    exact hs1_fr a ha
  · unfold copyGraphLiveCost; omega
  · intro r h5 h6 h8 h9 h10 h11 h12 h63 h64
    exact (hs5_regs r h5 h6).trans (hs4_regs r h8 h9 h10 h11 h12 h63 h64)

/-- The live-list caller-owned copy preserves a local `DSRep` and its potential, and places the
copied graph block outside the tool's footprint in `O(G.n + G.m + 1)` time. -/
theorem copyGraphLive_preserves_tool_runs {w src heap vc ec handle : ℕ} {G : MGraph}
    {σ : Type} {R : DSRep σ} {s : σ} {x : R.τ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hLocal : R.Local) (hrep : R.rep handle s x st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hsrc : st.regs 6 = src) (hheap : st.regs 5 = heap)
    (hG : DynGraphAt st.mem src vc ec G)
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out cost, Runs w p ω copyGraphLiveFromHeader st .normal out cost ∧
      DynGraphAt out.mem (out.regs 6) vc ec G ∧ out.regs 6 = heap ∧
      out.regs 5 = heap + dynGraphSize vc ec ∧ ZeroFrom out.mem (out.regs 5) ∧
      R.rep handle s x out.mem ∧ R.phi handle x out.mem = R.phi handle x st.mem ∧
      (∀ a, heap ≤ a → ¬ R.foot handle x a) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      out.pos = st.pos ∧ cost ≤ copyGraphLiveCost G.n G.m ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 63 → r ≠ 64 →
        out.regs r = st.regs r) := by
  obtain ⟨out, c, hr, hg, hgraph, hnew, hz', hmem, hp, hc, hregs⟩ :=
    copyGraphLiveFromHeader_runs (ω := ω) hsrc hheap hG hdisj hword hw hz
  have hstate := hLocal handle s x st.mem out.mem (fun a ha => (hmem a (hfoot a ha)).symm)
  exact ⟨out, c, hr, hgraph.symm ▸ hg, hgraph, hnew, hnew.symm ▸ hz', hstate.1 hrep,
    hstate.2.symm, fun a ha hf => Nat.not_lt_of_ge ha (hfoot a hf), hmem, hp, hc, hregs⟩

/-- Compatibility bound: for any graph represented with `vc + ec + 2 ≤ capLimit`, the live-list
copy cost is bounded by the array-copy cost `17 * dynGraphSize capLimit capLimit`. -/
theorem copyGraphLiveCost_le_17_dynGraphSize {mem : ℕ → ℕ} {a vc ec capLimit : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vc ec G) (hcap : vc + ec + 2 ≤ capLimit) :
    copyGraphLiveCost G.n G.m ≤ 17 * dynGraphSize capLimit capLimit := by
  have hn : G.n ≤ vc := graph_n_le_vCap hG
  have hm : G.m ≤ ec := graph_m_le_eCap hG
  unfold copyGraphLiveCost dynGraphSize
  omega

end MinCostFlow.MinRatio
