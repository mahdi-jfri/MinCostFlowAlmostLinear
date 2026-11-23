module

public import MinCostFlow.LinkCut.PathProg.Wrap

/-!
# The runs of the point read and path summary wrappers

The point read wrapper calls point read, which exposes the node and copies its value to the
heap pointer in `L` limbs. The path summary wrapper calls the reroot and expose, then copies the
summary of the exposed node to the heap pointer in `L` limbs (`readSumBody`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

section Width

variable {w h b0 : ℕ} {p : Program} (L : ℕ) (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
  (hp : p.HasAt b0 (pathTreeBodies h b0))

/-- The run of the point read wrapper. -/
theorem readWrap_runs (ω : ℕ → Bool) {b x heap pos : ℕ} {mem : ℕ → ℕ} {s : PathTreeState}
    {S : List ℕ} (hA : ArenaAt h L b s S mem) (hP : PtrOk (2 * s.n) s.splay)
    (hend : arenaEnd b s.n L ≤ heap) (hroom : heap + treeSpace L < 2 ^ w)
    (hz : ZeroFrom mem heap) (hn : 2 * s.n + 1 < 2 ^ w) (hx : x ≤ 2 * s.n)
    (hok : ExposeOk (pathOk h (treeLimbs L)) pathPayload s x)
    (hfit : PathEdgeFits h L ((lctExpose pathPayload s x).splay.nodes x).val) :
    ∃ o st' c, Runs w p ω (readWrap b0) (startState [b, x, heap] mem pos) o st' c ∧
      (o.value = heap + (2 + 4 * L) ∧
        ArenaAt h L b (lctExpose pathPayload s x) (exposeNotes pathPayload s x S) st'.mem ∧
        OpFrame b s.n L heap (heap + (2 + 4 * L)) mem st'.mem ∧
        PathEdgeAt st'.mem heap h L ((lctExpose pathPayload s x).splay.nodes x).val) ∧
      c ≤ exposeCost (stepsAt (treeLimbs L) hh hw hp) s x + 68 * L + 380 := by
  have h16 := sixteen_le hh hw
  have hnb := nb_lt_end b s.n L
  have hheap := heapOk_arena (h := h) hend hroom hz h16
  have hb4 : b + 4 < 2 ^ w := by unfold arenaNb at hnb; omega
  have hbh : b < heap := by unfold arenaNb at hnb; omega
  have hn1 := hA.hn
  have hn2 := hA.hL
  have hn4 := hA.hnb
  have hLw : L < 2 ^ w := by unfold treeSpace treeLimbs at hroom; omega
  have hproc : p.procs[b0 + Ix.pRead]? =
      some (pointReadBody (b0 + Ix.expose) (b0 + Ix.readV)) := core_at hp 51 (by decide)
  have hrv : MeetsContract w p (b0 + Ix.readV) (readValContract w h (treeLimbs L) L) :=
    readVal_meetsContract (core_at hp 23 (by decide)) (copy_ok hp)
  apply runs_start_le
  unfold readWrap
  rw [startState]
  refine runs_seq_callBody_le (vs := [arenaNb b s.n, x, 2 * s.n + 1, L, heap]) hproc
    (by eval_expr)
    (R := fun v' m₁ c₁ => (v' = heap + (2 + 4 * L) ∧
        ArenaAt h L b (lctExpose pathPayload s x) (exposeNotes pathPayload s x S) m₁.mem ∧
        OpFrame b s.n L heap (heap + (2 + 4 * L)) mem m₁.mem ∧
        PathEdgeAt m₁.mem heap h L ((lctExpose pathPayload s x).splay.nodes x).val) ∧
      c₁ ≤ exposeCost (stepsAt (treeLimbs L) hh hw hp) s x + 68 * L + 350) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hnd, hfr, hI, hzero, hval, hov⟩, hc⟩ :=
      pointReadBody_runs (exposeAt (treeLimbs L) hh hw hp) hrv ω (pos := pos) hA.nodes hP hx
        hheap hn hok (by unfold treeLimbs; omega) (by unfold treeSpace treeLimbs at hroom; omega)
        hfit (nb_room b s.n) hA.idx
    have hfh : st'.mem b = (lctExpose pathPayload s x).freeHead := by
      rw [fh_frame hbh hfr, hA.fh, lctExpose_freeHead]
    obtain ⟨hA', hout⟩ := arena_of_frame hA hend (lctExpose_n _ _ _) hnd hI hfh
      fun a ha hr hi _ => hfr a ha hr hi
    exact ⟨o, st', c, hr, ⟨hov, hA', ⟨hzero, hout⟩, hval⟩, by omega⟩
  rintro v' m₁ c₁ ⟨⟨hv', hres⟩, hc₁⟩
  wram_step
  · exact ⟨hv', hres⟩
  · simp only [hdr, fuelExpr, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil] at *
    omega

theorem lctPathSummary_n (s : PathTreeState) (u v : ℕ) :
    (lctPathSummary pathPayload s u v).1.n = s.n := by
  rw [lctPathSummary_fst, lctExpose_n, lctReroot_n]

theorem lctPathSummary_freeHead (s : PathTreeState) (u v : ℕ) :
    (lctPathSummary pathPayload s u v).1.freeHead = s.freeHead := by
  rw [lctPathSummary_fst, lctExpose_freeHead, lctReroot_freeHead]

/-- The address of the summary of node `v` in the arena. -/
theorem sumAddr_eq (h K nb v : ℕ) :
    (pathLayout h K).nodeAddr nb v + (pathLayout h K).offSum = nb + (13 + 9 * K) * v + (12 + 4 * K) := by
  unfold NodeLayout.nodeAddr NodeLayout.offSum
  rw [pathLayout_stride]
  simp only [pathLayout]
  omega

/-- The run of the path summary wrapper. -/
theorem summaryWrap_runs (ω : ℕ → Bool) {b u v heap pos : ℕ} {mem : ℕ → ℕ} {s : PathTreeState}
    {S : List ℕ} (hA : ArenaAt h L b s S mem) (hP : PtrOk (2 * s.n) s.splay)
    (hend : arenaEnd b s.n L ≤ heap) (hroom : heap + treeSpace L < 2 ^ w)
    (hz : ZeroFrom mem heap) (hn : 2 * s.n + 1 < 2 ^ w) (hu : u ≤ 2 * s.n) (hv : v ≤ 2 * s.n)
    (hok : RerootExposeOk (pathOk h (treeLimbs L)) pathPayload s u v)
    (hfit : PathSummaryFits h L (lctPathSummary pathPayload s u v).2) :
    ∃ o st' c, Runs w p ω (summaryWrap b0) (startState [b, u, v, heap] mem pos) o st' c ∧
      (o.value = heap + (3 * L + 1) ∧
        ArenaAt h L b (lctPathSummary pathPayload s u v).1 (rerootExposeNotes pathPayload s u v S)
          st'.mem ∧
        OpFrame b s.n L heap (heap + (3 * L + 1)) mem st'.mem ∧
        PathSummaryAt st'.mem heap h L (lctPathSummary pathPayload s u v).2) ∧
      c ≤ rerootExposeCost (stepsAt (treeLimbs L) hh hw hp) s u v + 60 * L + 400 := by
  set K := treeLimbs L with hKdef
  have h16 := sixteen_le hh hw
  have hnb := nb_lt_end b s.n L
  have hheap := heapOk_arena (h := h) hend hroom hz h16
  have hb4 : b + 4 < 2 ^ w := by unfold arenaNb at hnb; omega
  have hbh : b < heap := by unfold arenaNb at hnb; omega
  have hn1 := hA.hn
  have hn4 := hA.hnb
  have hroomK : heap + (12 * K + 8) < 2 ^ w := hroom
  have hLK : L ≤ K := by rw [hKdef]; unfold treeLimbs; omega
  -- The summary of `v` lies in the arena.
  have hsv : (13 + 9 * K) * v + (13 + 9 * K) ≤ (13 + 9 * K) * (2 * s.n + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have hendK : arenaNb b s.n + (13 + 9 * K) * (2 * s.n + 1) ≤ heap := hend
  have hsrc : arenaNb b s.n + (13 + 9 * K) * v + (12 + 4 * K) + (3 * K + 1) ≤ heap := by omega
  have hproc : p.procs[b0 + Ix.rerootE]? =
      some (rerootExposeBody (b0 + Ix.reroot) (b0 + Ix.expose)) := core_at hp 43 (by decide)
  have hrs : MeetsContract w p (b0 + Ix.readS) (readSumContract w h K L) :=
    readSum_meetsContract (core_at hp 24 (by decide)) (copy_ok hp)
  apply runs_start_le
  unfold summaryWrap
  rw [startState]
  refine runs_seq_callBody_le (vs := [arenaNb b s.n, u, v, 2 * s.n + 1, heap]) hproc
    (by eval_expr)
    (R := fun _ m₁ c₁ => (ArenaAt h L b (lctPathSummary pathPayload s u v).1
        (rerootExposeNotes pathPayload s u v S) m₁.mem ∧
        OpFrame b s.n L heap heap mem m₁.mem) ∧
      c₁ ≤ rerootExposeCost (stepsAt K hh hw hp) s u v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hnd, hfr, hI⟩, hc⟩ :=
      rerootExposeBody_runs (pathAt K hh hw hp) ω (pos := pos) hA.nodes hP hu hv hheap hn hok
        (nb_room b s.n) hA.idx
    have hfh : st'.mem b = (lctPathSummary pathPayload s u v).1.freeHead := by
      rw [fh_frame hbh hfr.2, hA.fh, lctPathSummary_freeHead]
    obtain ⟨hA', hout⟩ := arena_of_frame hA hend (lctPathSummary_n s u v) hnd hI hfh
      fun a ha hr hi _ => hfr.2 a ha hr hi
    exact ⟨o, st', c, hr, ⟨hA', hfr.1, hout⟩, by omega⟩
  rintro - m₁ c₁ ⟨⟨hA1, hF1⟩, hc₁⟩
  have hK1 := hA1.hK
  have hL1 := hA1.hL
  have hnb1 := hA1.hnb
  rw [lctPathSummary_n] at hnb1
  refine runs_seq_assign_le (v := K) (by eval_expr) ?_
  refine runs_seq_assign_le (v := L) (by eval_expr) ?_
  refine runs_seq_assign_le (v := arenaNb b s.n + (13 + 9 * K) * v + (12 + 4 * K))
    (by eval_expr) ?_
  -- The summary of `v` after the reroot and expose.
  have hnode := hA1.nodes v (by rw [lctPathSummary_n]; exact hv)
  have hsum : PathSummaryAt m₁.mem (arenaNb b s.n + (13 + 9 * K) * v + (12 + 4 * K)) h K
      (lctPathSummary pathPayload s u v).2 := by
    have := hnode.2.2.2.2.2.2.2.1
    rw [lctPathSummary_n, sumAddr_eq] at this
    rw [lctPathSummary_snd]
    rw [lctPathSummary_fst] at this
    exact this
  refine runs_seq_call_le hrs
    (vs := [arenaNb b s.n + (13 + 9 * K) * v + (12 + 4 * K), heap, K, L]) (by eval_expr)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, rfl, by omega, hLK, by omega, by omega, Or.inl (by omega), _, hsum, hfit⟩ ?_
  rintro v₂ m₂ pos₂ ⟨hfr₂, hsum₂⟩
  have hsum' := hsum₂ _ hsum hfit
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hfr₂ hsum'
  wram_step
  · refine ⟨rfl, ?_, ⟨fun a ha => ?_, fun a ha hout => ?_⟩, hsum'⟩
    · refine hA1.congr fun a h1 h2 => ?_
      rw [lctPathSummary_n] at h2
      exact hfr₂ a (by omega)
    · dsimp only; rw [hfr₂ a (by omega)]; exact hF1.1 a (by omega)
    · dsimp only; rw [hfr₂ a (by omega)]; exact hF1.2 a ha hout
  · simp only [hdr, fuelExpr, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil, readSumContract] at *
    omega

end Width

end MinCostFlow.LinkCut.PathProg
