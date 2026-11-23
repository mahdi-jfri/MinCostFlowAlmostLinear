module

public import MinCostFlow.LinkCut.PathProg.WrapQuery

/-!
# The runs of the point write and path update wrappers

The point write wrapper copies the new value to the heap pointer first, since the caller's value
may lie anywhere below the heap pointer, and point write reads it from above the arena. The path
update wrapper widens the two numbers of the tag from `L` to `K` limbs at the heap pointer and
calls the path update with that block.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

/-- An arena below the heap pointer survives a call that changes only cells from the heap pointer
on. -/
theorem arena_above {h L b heap : ℕ} {s : PathTreeState} {S : List ℕ} {mem mem' : ℕ → ℕ}
    (hA : ArenaAt h L b s S mem) (hend : arenaEnd b s.n L ≤ heap)
    (hfr : ∀ a < heap, mem' a = mem a) : ArenaAt h L b s S mem' :=
  hA.congr fun a _ h2 => hfr a (by omega)

section Width

variable {w h b0 : ℕ} {p : Program} (L : ℕ) (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
  (hp : p.HasAt b0 (pathTreeBodies h b0))

include hh hw hp in
theorem widen_ok (K : ℕ) : MeetsContract w p (b0 + Ix.widen) (widenContract w h L K) :=
  widen_meetsContract (core_at hp 25 (by decide)) (ext_ok hh hw hp) (copy_ok hp)

include hh hw hp in
theorem writeV_ok (K : ℕ) : MeetsContract w p (b0 + Ix.writeV) (writeValContract w h L K) :=
  writeVal_meetsContract (core_at hp 26 (by decide)) (widen_ok L hh hw hp K) (copy_ok hp)

/-- The run of the point write wrapper. -/
theorem writeWrap_runs (ω : ℕ → Bool) {b x va heap pos : ℕ} {mem : ℕ → ℕ} {s : PathTreeState}
    {S : List ℕ} {e : PathEdgeValue} (hA : ArenaAt h L b s S mem) (hP : PtrOk (2 * s.n) s.splay)
    (hend : arenaEnd b s.n L ≤ heap) (hroom : heap + (2 + 4 * L) + treeSpace L < 2 ^ w)
    (hz : ZeroFrom mem heap) (hn : 2 * s.n + 1 < 2 ^ w) (hx : x ≤ 2 * s.n)
    (hok : ExposeOk (pathOk h (treeLimbs L)) pathPayload s x)
    (hva : va + (2 + 4 * L) ≤ heap) (hval : PathEdgeAt mem va h L (some e))
    (hokp : x ≠ 0 → (pathOk h (treeLimbs L)).sumOk (pullSum pathPayload
      ((lctExpose pathPayload s x).splay.updateNode x fun nd => { nd with val := some e }) x)) :
    ∃ o st' c, Runs w p ω (writeWrap b0) (startState [b, x, va, heap] mem pos) o st' c ∧
      (o.value = heap + (2 + 4 * L) ∧
        ArenaAt h L b (pathTreeWrite s x (some e)) (exposeNotes pathPayload s x S) st'.mem ∧
        OpFrame b s.n L heap (heap + (2 + 4 * L)) mem st'.mem) ∧
      c ≤ exposeCost (stepsAt (treeLimbs L) hh hw hp) s x + 300 * treeLimbs L +
        (stepsAt (treeLimbs L) hh hw hp).cost + 68 * L + 1200 := by
  set K := treeLimbs L with hKdef
  have h16 := sixteen_le hh hw
  have hnb := nb_lt_end b s.n L
  have hb4 : b + 4 < 2 ^ w := by unfold arenaNb at hnb; omega
  have hbh : b < heap := by unfold arenaNb at hnb; omega
  have hLK : L ≤ K := by rw [hKdef]; unfold treeLimbs; omega
  have hroomK : heap + (2 + 4 * L) + (12 * K + 8) < 2 ^ w := hroom
  have hn2 := hA.hL
  have hproc : p.procs[b0 + Ix.pWrite]? =
      some (pointWriteBody (b0 + Ix.expose) (b0 + Ix.writeV) (b0 + Ix.pull)) :=
    core_at hp 52 (by decide)
  apply runs_start_le
  unfold writeWrap
  rw [startState]
  refine runs_seq_assign_le (v := L) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 2 + 4 * L) (by eval_expr) ?_
  refine runs_seq_call_le (copy_ok hp) (vs := [va, heap, 2 + 4 * L]) (by eval_expr)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, by omega, by omega, by omega, Or.inr hva⟩ ?_
  rintro v₁ m₁ pos₁ ⟨src, dst, len, heq, -, hcp, hfr₁⟩
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hA1 := arena_above hA hend fun a ha => hfr₁ a (Or.inl ha)
  have hn1 := hA1.hn
  have hn4 := hA1.hnb
  have hval1 : PathEdgeAt m₁ heap h L (some e) := pathEdgeAt_move hval hcp
  have hz1 : ZeroFrom m₁ (heap + (2 + 4 * L)) := fun a ha => by
    rw [hfr₁ a (Or.inr ha)]; exact hz a (by omega)
  have hheap := heapOk_arena (h := h) (b := b) (n := s.n) (L := L) (by omega) (by omega) hz1 h16
  refine runs_seq_callBody_le
    (vs := [arenaNb b s.n, x, heap, 2 * s.n + 1, L, heap + (2 + 4 * L)]) hproc (by eval_expr)
    (R := fun v' m₂ c₂ => (v' = heap + (2 + 4 * L) ∧
        ArenaAt h L b (pathTreeWrite s x (some e)) (exposeNotes pathPayload s x S) m₂.mem ∧
        OpFrame b s.n L heap (heap + (2 + 4 * L)) mem m₂.mem) ∧
      c₂ ≤ exposeCost (stepsAt K hh hw hp) s x + (300 * K + 600) +
        (stepsAt K hh hw hp).cost + 400) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hnd, hfr, hov⟩, hc⟩ :=
      pointWriteBody_runs (exposeAt K hh hw hp) (writeV_ok L hh hw hp K) ω (pos := pos₁)
        hA1.nodes hP hx hheap hn hok hLK
        (by unfold NodeLayout.nodeAddr; rw [recW_stride]; exact hend) le_rfl hval1 hokp
        (nb_room b s.n) hA1.idx
    have hfh : st'.mem b = (pathTreeWrite s x (some e)).freeHead := by
      rw [fh_frame (by omega) hfr.1.2, hA1.fh, pathTreeWrite_freeHead, lctExpose_freeHead]
    obtain ⟨hA', hout⟩ := arena_of_frame hA1 (by omega)
      (by rw [pathTreeWrite_n, lctExpose_n]) (by rw [pathTreeWrite_splay]; exact hnd) hfr.2 hfh
      fun a ha hr hi _ => hfr.1.2 a ha hr hi
    refine ⟨o, st', c, hr, ⟨hov, hA', hfr.1.1, fun a ha hout' => ?_⟩, by omega⟩
    rw [hout a (by omega) hout', hfr₁ a (Or.inl ha)]
  rintro v' m₂ c₂ ⟨⟨hv', hres⟩, hc₂⟩
  wram_step
  · exact ⟨rfl, hres⟩
  · simp only [hdr, fuelExpr, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil, copyWordsContract] at *
    omega

/-- The run of the path update wrapper. -/
theorem applyWrap_runs (ω : ℕ → Bool) {b u v ta heap pos : ℕ} {mem : ℕ → ℕ} {s : PathTreeState}
    {S : List ℕ} {t : PathTag} (hA : ArenaAt h L b s S mem) (hP : PtrOk (2 * s.n) s.splay)
    (hend : arenaEnd b s.n L ≤ heap)
    (hroom : heap + 2 * treeLimbs L + treeSpace L < 2 ^ w)
    (hz : ZeroFrom mem heap) (hn : 2 * s.n + 1 < 2 ^ w) (hu : u ≤ 2 * s.n) (hv : v ≤ 2 * s.n)
    (hta : ta + 2 * L ≤ heap) (ht : PathTagAt mem ta h L t)
    (hok : PathApplyOk (pathOk h (treeLimbs L)) pathPayload s u v t) :
    ∃ o st' c, Runs w p ω (applyWrap b0) (startState [b, u, v, ta, heap] mem pos) o st' c ∧
      (o.value = heap + 2 * treeLimbs L ∧
        ArenaAt h L b (lctPathApply pathPayload s u v t) (rerootExposeNotes pathPayload s u v S)
          st'.mem ∧
        OpFrame b s.n L heap (heap + 2 * treeLimbs L) mem st'.mem) ∧
      c ≤ rerootExposeCost (stepsAt (treeLimbs L) hh hw hp) s u v +
        (stepsAt (treeLimbs L) hh hw hp).cost + 140 * treeLimbs L + 500 := by
  set K := treeLimbs L with hKdef
  have h16 := sixteen_le hh hw
  have hnb := nb_lt_end b s.n L
  have hb4 : b + 4 < 2 ^ w := by unfold arenaNb at hnb; omega
  have hbh : b < heap := by unfold arenaNb at hnb; omega
  have hLK : L ≤ K := by rw [hKdef]; unfold treeLimbs; omega
  have hroomK : heap + 2 * K + (12 * K + 8) < 2 ^ w := hroom
  have hn2 := hA.hL
  have hn3 := hA.hK
  have hproc : p.procs[b0 + Ix.pathApply]? =
      some (pathApplyBody (b0 + Ix.rerootE) (b0 + Ix.applyTag)) := core_at hp 44 (by decide)
  apply runs_start_le
  unfold applyWrap
  rw [startState]
  refine runs_seq_assign_le (v := K) (by eval_expr) ?_
  refine runs_seq_assign_le (v := L) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 2 * K) (by eval_expr) ?_
  -- Widen the flow.
  have hha1 : heapArg [ta, heap, L, K, heap + 2 * K] = heap + 2 * K := rfl
  have hha2 : heapArg [ta + L, heap + K, L, K, heap + 2 * K] = heap + 2 * K := rfl
  refine runs_seq_call_le (widen_ok L hh hw hp K) (vs := [ta, heap, L, K, heap + 2 * K])
    (by eval_expr)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨⟨_, _, _, rfl, by omega, hLK, by omega, by omega, ht.1.1⟩,
      fun a ha => hz a (by rw [hha1] at ha; omega), by rw [hha1]; omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨hz₁, hfr₁, hval₁, heq₁⟩
  rw [hha1] at hz₁ hfr₁
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hfr₁ hval₁ heq₁
  have hA1 := arena_above hA hend fun a ha => hfr₁ a (by omega) (by omega)
  have hn1 := hA1.hn
  have hn4 := hA1.hnb
  have hdet₁ : PathIntAt m₁ (ta + L) h L t.detector :=
    ht.2.congr fun i hi => hfr₁ _ (by omega) (by omega)
  -- Widen the detector.
  refine runs_seq_call_le (widen_ok L hh hw hp K) (vs := [ta + L, heap + K, L, K, heap + 2 * K])
    (by eval_expr)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨⟨_, _, _, rfl, by omega, hLK, by omega, by omega, hdet₁.1⟩,
      by rw [hha2]; exact hz₁, by rw [hha2]; omega⟩ ?_
  rintro v₂ m₂ pos₂ ⟨hz₂, hfr₂, hval₂, heq₂⟩
  rw [hha2] at hz₂ hfr₂
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hfr₂ hval₂ heq₂
  have hA2 := arena_above hA1 hend fun a ha => hfr₂ a (by omega) (by omega)
  have hn1' := hA2.hn
  have hn4' := hA2.hnb
  have htag : PathTagAt m₂ heap h K t := by
    refine ⟨⟨fun i hi => ?_, ?_⟩, ⟨hval₂, heq₂.trans hdet₁.2⟩⟩
    · rw [hfr₂ _ (by omega) (by omega)]; exact hval₁ i hi
    · rw [Num.intVal_congr (fun i hi => hfr₂ (heap + i) (by omega) (by omega)), heq₁]
      exact ht.1.2
  have hz2 : ZeroFrom m₂ (heap + 2 * K) := hz₂
  have hheap := heapOk_arena (h := h) (b := b) (n := s.n) (L := L) (by omega) (by omega) hz2 h16
  refine runs_seq_callBody_le
    (vs := [arenaNb b s.n, u, v, heap, 2 * s.n + 1, heap + 2 * K]) hproc (by eval_expr)
    (R := fun _ m₃ c₃ => (ArenaAt h L b (lctPathApply pathPayload s u v t)
        (rerootExposeNotes pathPayload s u v S) m₃.mem ∧
        OpFrame b s.n L heap (heap + 2 * K) mem m₃.mem) ∧
      c₃ ≤ rerootExposeCost (stepsAt K hh hw hp) s u v + (stepsAt K hh hw hp).cost + 100) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hnd, hfr⟩, hc⟩ :=
      pathApplyBody_runs (pathAt K hh hw hp) ω (pos := pos₂) hA2.nodes hP hu hv hheap
        (by unfold NodeLayout.nodeAddr; rw [recW_stride]; exact hend) (by simp [pathLayout])
        htag hn hok (nb_room b s.n) hA2.idx
    have hfh : st'.mem b = (lctPathApply pathPayload s u v t).freeHead := by
      rw [fh_frame (by omega) hfr.1.2, hA2.fh, lctPathApply_freeHead]
    obtain ⟨hA', hout⟩ := arena_of_frame hA2 (by omega) (lctPathApply_n _ _ _ _ _) hnd hfr.2 hfh
      fun a ha hr hi _ => hfr.1.2 a ha hr hi
    refine ⟨o, st', c, hr, ⟨hA', hfr.1.1, fun a ha hout' => ?_⟩, by omega⟩
    rw [hout a (by omega) hout', hfr₂ a (by omega) (by omega), hfr₁ a (by omega) (by omega)]
  rintro - m₃ c₃ ⟨hres, hc₃⟩
  wram_step
  · exact ⟨rfl, hres⟩
  · simp only [hdr, fuelExpr, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil, widenContract, payloadContract] at *
    omega

/-- The run of the link wrapper. -/
theorem linkWrap_runs (ω : ℕ → Bool) {b u v va heap pos : ℕ} {mem : ℕ → ℕ} {s : PathTreeState}
    {S : List ℕ} {e : PathEdgeValue} (hA : ArenaAt h L b s S mem) (hP : PtrOk (2 * s.n) s.splay)
    (hend : arenaEnd b s.n L ≤ heap)
    (hroom : heap + (7 + 4 * treeLimbs L) + treeSpace L < 2 ^ w)
    (hz : ZeroFrom mem heap) (hn : 2 * s.n + 1 < 2 ^ w) (hu : u ≤ 2 * s.n) (hv : v ≤ 2 * s.n)
    (hfc : s.freeHead ≤ 2 * s.n) (hva : va + (2 + 4 * L) ≤ heap)
    (hval : PathEdgeAt mem va h L (some e))
    (hok : LinkOk (pathOk h (treeLimbs L)) pathPayload s u v (some e)) :
    ∃ o st' c, Runs w p ω (linkWrap b0) (startState [b, u, v, va, heap] mem pos) o st' c ∧
      (o.value = heap + (7 + 4 * treeLimbs L) ∧
        ArenaAt h L b (lctLink pathPayload s u v (some e)) (linkNotes pathPayload s u v S)
          st'.mem ∧
        OpFrame b s.n L heap (heap + (7 + 4 * treeLimbs L)) mem st'.mem ∧
        st'.mem heap = s.freeHead) ∧
      c ≤ linkCost (stepsAt (treeLimbs L) hh hw hp) s u v + 300 * treeLimbs L + 1000 := by
  set K := treeLimbs L with hKdef
  have h16 := sixteen_le hh hw
  have hnb := nb_lt_end b s.n L
  have hb4 : b + 4 < 2 ^ w := by unfold arenaNb at hnb; omega
  have hbh : b + 8 ≤ heap := by unfold arenaNb at hnb; omega
  have hLK : L ≤ K := by rw [hKdef]; unfold treeLimbs; omega
  have hroomK : heap + (7 + 4 * K) + (12 * K + 8) < 2 ^ w := hroom
  have hn2 := hA.hL
  have hn3 := hA.hK
  have hproc : p.procs[b0 + Ix.glink]? =
      some (linkBody (b0 + Ix.reroot) (b0 + Ix.mkSingle) (b0 + Ix.note)) :=
    core_at hp 46 (by decide)
  apply runs_start_le
  unfold linkWrap
  rw [startState]
  refine runs_seq_assign_le (v := K) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 1 + (6 + 4 * K)) (by eval_expr) ?_
  refine runs_seq_store_named_le (x := heap + 1) (v := 13 + 9 * K) (by eval_expr) (by eval_expr)
    fun M₁ hM₁ => ?_
  refine runs_seq_store_named_le (x := heap + 1 + 1) (v := 6 + 4 * K) (by eval_expr)
    (by eval_expr) fun M₂ hM₂ => ?_
  refine runs_seq_store_named_le (x := heap + 1 + 2) (v := 2 * K) (by eval_expr)
    (by eval_expr) fun M₃ hM₃ => ?_
  refine runs_seq_store_named_le (x := heap + 1 + 3) (v := K) (by eval_expr)
    (by eval_expr) fun M₄ hM₄ => ?_
  simp only at hM₁ hM₂ hM₃ hM₄
  have hM : ∀ a, a < heap + 1 ∨ heap + 5 ≤ a → M₄ a = mem a := by
    intro a ha
    rw [hM₄, hM₃, hM₂, hM₁]
    simp only [Function.update_apply]
    split_ifs <;> first | omega | rfl
  have hhdr : M₄ (heap + 1) = 13 + 9 * K ∧ M₄ (heap + 1 + 1) = 6 + 4 * K ∧
      M₄ (heap + 1 + 2) = 2 * K ∧ M₄ (heap + 1 + 3) = K := by
    rw [hM₄, hM₃, hM₂, hM₁]
    simp only [Function.update_apply]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> first | omega | rfl
  have hval4 : PathEdgeAt M₄ va h L (some e) :=
    hval.congr fun a _ ha => hM a (Or.inl (by omega))
  have hha : heapArg [va, heap + 1 + 4, L, K, heap + 1 + (6 + 4 * K)] =
      heap + 1 + (6 + 4 * K) := rfl
  have hn2' : M₄ (b + 2) = L := by rw [hM (b + 2) (Or.inl (by omega))]; exact hn2
  refine runs_seq_call_le (writeV_ok L hh hw hp K)
    (vs := [va, heap + 1 + 4, L, K, heap + 1 + (6 + 4 * K)]) (by eval_expr)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨⟨_, _, _, rfl, by omega, hLK, by omega, by omega, Or.inl (by omega), e, hval4⟩,
      fun a ha => by
        rw [hha] at ha; show M₄ a = 0; rw [hM a (Or.inr (by omega))]; exact hz a (by omega),
      by rw [hha]; omega⟩ ?_
  rintro v₅ m₅ pos₅ ⟨hz₅, hfr₅, hval₅⟩
  rw [hha] at hz₅ hfr₅
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hfr₅ hval₅
  have hm5 : ∀ a < heap + 1 + 4, m₅ a = M₄ a := fun a ha => hfr₅ a (by omega) (by omega)
  have hA5 := arena_above (mem' := m₅) hA hend fun a ha => by rw [hm5 a (by omega), hM a (Or.inl (by omega))]
  have hn1 := hA5.hn
  have hn4 := hA5.hnb
  have hfh5 := hA5.fh
  have hvalK : PathValAt m₅ (heap + 1) h K (some e) := by
    obtain ⟨g1, g2, g3, g4⟩ := hhdr
    refine ⟨?_, ?_, ?_, ?_, hval₅ e hval4⟩
    · rw [hm5 _ (by omega)]; exact g1
    · rw [hm5 _ (by omega)]; exact g2
    · rw [hm5 _ (by omega)]; exact g3
    · rw [hm5 _ (by omega)]; exact g4
  refine runs_seq_assign_le (v := s.freeHead) (by eval_expr) ?_
  have hheap := heapOk_arena (h := h) (b := b) (n := s.n) (L := L) (by omega) (by omega) hz₅ h16
  refine runs_seq_callBody_le
    (vs := [arenaNb b s.n, b, u, v, heap + 1, 2 * s.n + 1, heap + 1 + (6 + 4 * K)]) hproc
    (by eval_expr)
    (R := fun _ m₆ c₆ => (ArenaAt h L b (lctLink pathPayload s u v (some e))
        (linkNotes pathPayload s u v S) m₆.mem ∧
        OpFrame b s.n L heap (heap + 1 + (6 + 4 * K)) mem m₆.mem) ∧
      c₆ ≤ linkCost (stepsAt K hh hw hp) s u v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hnd, hfh, hfr, hI⟩, hc⟩ :=
      linkBody_runs pathPayload_laws (pathAt K hh hw hp) (core_at hp 45 (by decide)) ω
        (pos := pos₅) (fh := b) (va := heap + 1) hA5.nodes hA5.fh hP hu hv hfc hheap
        (not_inRecords_of_lt (by unfold arenaNb at hnb ⊢; omega)) (not_inIndex_hdr (by omega))
        (by omega) (by unfold NodeLayout.nodeAddr; rw [recW_stride]; exact le_trans hend (by omega))
        (by simp only [pathLayout]; omega) (Or.inl (by omega)) hvalK hn hok (nb_room b s.n)
        hA5.idx
    obtain ⟨hA', hout⟩ := arena_of_frame hA5 (by omega) (lctLink_n s u v (some e)) hnd hI hfh
      fun a ha hr hi hb => hfr.2 a ha hr hi hb
    refine ⟨o, st', c, hr, ⟨hA', hfr.1, fun a ha hout' => ?_⟩, by omega⟩
    rw [hout a (by omega) hout', hm5 a (by omega), hM a (Or.inl (by omega))]
  rintro - m₆ c₆ ⟨⟨hA6, hF6⟩, hc₆⟩
  refine runs_seq_store_named_le (x := heap) (v := s.freeHead) (by eval_expr) (by eval_expr)
    fun M₇ hM₇ => ?_
  simp only at hM₇
  wram_step
  · refine ⟨by show heap + 1 + (6 + 4 * K) = _; omega, ?_,
      ⟨fun a ha => ?_, fun a ha hout => ?_⟩, ?_⟩
    · refine hA6.congr fun a h1 h2 => ?_
      rw [lctLink_n] at h2
      dsimp only; simp only [hM₇, Function.update_apply]; rw [ite_eq_right (by omega)]
    · dsimp only; simp only [hM₇, Function.update_apply]; rw [ite_eq_right (by omega)]
      exact hF6.1 a (by omega)
    · dsimp only; simp only [hM₇, Function.update_apply]; rw [ite_eq_right (by omega)]
      exact hF6.2 a ha hout
    · simp [hM₇]
  · simp only [hdr, fuelExpr, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil, writeValContract, payloadContract] at *
    omega

end Width

end MinCostFlow.LinkCut.PathProg
