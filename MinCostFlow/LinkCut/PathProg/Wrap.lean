module

public import MinCostFlow.LinkCut.PathProg.Procs
public import MinCostFlow.LinkCut.PathProg.KeepCut

/-!
# The runs of the operation wrappers: shared facts, and cut

Each wrapper reads the arena header and calls one tree procedure. The tree procedures change
only the records, the index and the free list word `b`, and they need the records to end below
the heap pointer (`HeapOk`). This file shows that an arena below the heap pointer gives
`HeapOk` (`heapOk_arena`), and that the arena of the new state is in memory after such a call
(`arena_of_frame`). It ends with the run of the cut wrapper (`cutWrap_runs`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

/-- What an operation leaves outside the arena at `b`: memory from `heap'` on is zero, and
memory below `heap` outside the arena is unchanged. -/
def OpFrame (b n L heap heap' : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ZeroFrom mem' heap' ∧ ∀ a < heap, ¬ (b ≤ a ∧ a < arenaEnd b n L) → mem' a = mem a

/-- The scratch space that the tree procedures need above their heap pointer. -/
def treeSpace (L : ℕ) : ℕ := 12 * treeLimbs L + 8

theorem treeSpace_eq (h L : ℕ) :
    2 * (pathLayout h (treeLimbs L)).tagW + pathSpace (treeLimbs L) = treeSpace L := by
  simp only [pathLayout, pathSpace, treeSpace]; omega

theorem nb_lt_end (b n L : ℕ) : arenaNb b n < arenaEnd b n L := by
  unfold arenaEnd recW; have := Nat.le_mul_of_pos_right (13 + 9 * treeLimbs L)
    (show 0 < 2 * n + 1 by omega)
  omega

/-- The records of an arena below the heap pointer end below the heap pointer. -/
theorem heapOk_arena {w h b n L heap : ℕ} {mem : ℕ → ℕ} (hend : arenaEnd b n L ≤ heap)
    (hroom : heap + treeSpace L < 2 ^ w) (hz : ZeroFrom mem heap) (hw : 16 ≤ 2 ^ w) :
    HeapOk (pathLayout h (treeLimbs L)) w (arenaNb b n) (2 * n) heap
      (2 * (pathLayout h (treeLimbs L)).tagW + pathSpace (treeLimbs L)) mem := by
  refine ⟨?_, by rw [treeSpace_eq]; exact hroom, hz, hw⟩
  unfold NodeLayout.nodeAddr
  rw [recW_stride]
  exact hend

theorem not_inRecords_of_lt {h L b n a : ℕ} (ha : a < arenaNb b n) :
    ¬ (pathLayout h (treeLimbs L)).InRecords (arenaNb b n) (2 * n) a := fun h => by
  have := h.1; omega

theorem not_inIndex_hdr {b n a : ℕ} (ha : a < b + 5) : ¬ InIndex (arenaNb b n) (2 * n) a := by
  rintro ⟨h1, -⟩; unfold arenaNb at h1; omega

/-- After a tree call that changes only the records, the index and the word `b`, memory holds
the arena of the new state, and memory below the heap pointer outside the arena is unchanged. -/
theorem arena_of_frame {h L b heap : ℕ} {s s' : PathTreeState} {S S' : List ℕ}
    {mem mem' : ℕ → ℕ} (hA : ArenaAt h L b s S mem) (hend : arenaEnd b s.n L ≤ heap)
    (hn : s'.n = s.n)
    (hnodes : (pathLayout h (treeLimbs L)).NodesAt mem' (arenaNb b s.n) (2 * s.n) s'.splay)
    (hI : IdxAt mem' (arenaNb b s.n) (2 * s.n) S') (hfh : mem' b = s'.freeHead)
    (hfr : ∀ a < heap, ¬ (pathLayout h (treeLimbs L)).InRecords (arenaNb b s.n) (2 * s.n) a →
      ¬ InIndex (arenaNb b s.n) (2 * s.n) a → a ≠ b → mem' a = mem a) :
    ArenaAt h L b s' S' mem' ∧
      ∀ a < heap, ¬ (b ≤ a ∧ a < arenaEnd b s.n L) → mem' a = mem a := by
  have hnb := nb_lt_end b s.n L
  have hkeep : ∀ a, b < a → a < b + 5 → mem' a = mem a := fun a h1 h2 =>
    hfr a (by unfold arenaNb at hnb; omega)
      (not_inRecords_of_lt (by unfold arenaNb; omega)) (not_inIndex_hdr h2) (by omega)
  refine ⟨⟨hfh, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun a ha hout => ?_⟩
  · rw [hkeep _ (by omega) (by omega), hA.hn, hn]
  · rw [hkeep _ (by omega) (by omega), hA.hL]
  · rw [hkeep _ (by omega) (by omega), hA.hK]
  · rw [hkeep _ (by omega) (by omega), hA.hnb, hn]
  · rw [hn]; exact hnodes
  · rw [hn]; exact hI
  · refine hfr a ha (fun hr => hout (inRecords_foot hr)) (fun hi => hout (inIndex_foot hi)) ?_
    rintro rfl
    exact hout ⟨le_refl _, by unfold arenaNb at hnb; omega⟩

/-- The free list word is not in the records or the index. -/
theorem fh_frame {h L b heap : ℕ} {n : ℕ} {mem mem' : ℕ → ℕ} (hbh : b < heap)
    (hfr : ∀ a < heap, ¬ (pathLayout h (treeLimbs L)).InRecords (arenaNb b n) (2 * n) a →
      ¬ InIndex (arenaNb b n) (2 * n) a → mem' a = mem a) : mem' b = mem b :=
  hfr b hbh (not_inRecords_of_lt (by unfold arenaNb; omega)) (not_inIndex_hdr (by omega))

section Width

variable {w h b0 : ℕ} {p : Program} (L : ℕ) (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
  (hp : p.HasAt b0 (pathTreeBodies h b0))

include hh hw in
theorem sixteen_le : 16 ≤ 2 ^ w := by
  have : 2 ^ 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa using this

/-- The run of the cut wrapper. -/
theorem cutWrap_runs (ω : ℕ → Bool) {b u v heap pos : ℕ} {mem : ℕ → ℕ} {s : PathTreeState}
    {S : List ℕ} (hA : ArenaAt h L b s S mem) (hP : PtrOk (2 * s.n) s.splay)
    (hend : arenaEnd b s.n L ≤ heap) (hroom : heap + treeSpace L < 2 ^ w)
    (hz : ZeroFrom mem heap) (hn : 2 * s.n + 1 < 2 ^ w)
    (hok : CutOk (pathOk h (treeLimbs L)) pathPayload s u v) :
    ∃ o st' c, Runs w p ω (cutWrap b0) (startState [b, u, v, heap] mem pos) o st' c ∧
      (o.value = heap ∧ ArenaAt h L b (lctCut pathPayload s u v) (cutNotes pathPayload s u v S)
        st'.mem ∧ OpFrame b s.n L heap heap mem st'.mem) ∧
      c ≤ cutCost (stepsAt (treeLimbs L) hh hw hp) s u v + 20 := by
  have h16 := sixteen_le hh hw
  have hnb := nb_lt_end b s.n L
  have hheap := heapOk_arena (h := h) hend hroom hz h16
  have hb4 : b + 4 < 2 ^ w := by unfold arenaNb at hnb; omega
  have hbh : b < heap := by unfold arenaNb at hnb; omega
  have hn1 := hA.hn
  have hn4 := hA.hnb
  have hproc : p.procs[b0 + Ix.gcut]? = some (cutBody (b0 + Ix.rerootE) (b0 + Ix.pushDown)
      (b0 + Ix.splay) (b0 + Ix.detachC) (b0 + Ix.pick)) := core_at hp 48 (by decide)
  apply runs_start_le
  unfold cutWrap
  rw [startState]
  refine runs_seq_callBody_le (vs := [arenaNb b s.n, b, u, v, s.n, heap]) hproc (by eval_expr)
    (R := fun v' m₁ c₁ => (ArenaAt h L b (lctCut pathPayload s u v)
        (cutNotes pathPayload s u v S) m₁.mem ∧ OpFrame b s.n L heap heap mem m₁.mem) ∧
      c₁ ≤ cutCost (stepsAt (treeLimbs L) hh hw hp) s u v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hnd, hfh, hfr, hI⟩, hc⟩ :=
      cutBody_runs (pathAt (treeLimbs L) hh hw hp) (core_at hp 47 (by decide))
        (core_at hp 11 (by decide)) ω (fh := b) (pos := pos) hA.nodes hA.fh hP (by omega) hheap
        (not_inRecords_of_lt (by unfold arenaNb at hnb ⊢; omega)) (not_inIndex_hdr (by omega))
        hbh hn hok (nb_room b s.n) hA.idx
    obtain ⟨hA', hout⟩ := arena_of_frame hA hend (lctCut_n s u v) hnd hI hfh
      fun a ha hr hi hb => hfr.2 a ha hr hi hb
    exact ⟨o, st', c, hr, ⟨hA', hfr.1, hout⟩, by omega⟩
  rintro - m₁ c₁ ⟨hres, hc₁⟩
  wram_step
  · exact ⟨rfl, hres⟩
  · simp only [hdr, fuelExpr, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load, argsSize_cons,
      argsSize_nil] at *
    omega

end Width

end MinCostFlow.LinkCut.PathProg
