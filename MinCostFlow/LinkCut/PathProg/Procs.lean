module

public import MinCostFlow.LinkCut.PathProg.Bodies

/-!
# The procedures of the fixed program, for every width

A program that holds `pathTreeBodies h b0` from index `b0` on holds every tree and payload
procedure at a fixed index. This file reads them off (`core_at`) and packs them, for every tree
width `K`, into the structures that the run theorems of `LinkCut/Gen` take: the payload steps
(`stepsAt`), the lazy procedures (`lazyAt`), the splay, expose and path procedures, the ready
tests and the find-ready procedures. The bodies do not depend on `K`; only the contracts do.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.Path
  MinCostFlow.LinkCut.PathTree MinCostFlow.MinRatio

variable {h b0 : ℕ} {p : Program}

theorem core_at (hp : p.HasAt b0 (pathTreeBodies h b0)) (k : ℕ) (hk : k < 53) :
    p.procs[b0 + k]? = some ((pathCoreBodies h b0)[k]'(by rw [pathCoreBodies_length]; exact hk)) := by
  have hc := hasAt_append_left hp
  have := hc k (by rw [pathCoreBodies_length]; exact hk)
  exact this

/-- The number modules of the program. -/
theorem num_at (hp : p.HasAt b0 (pathTreeBodies h b0)) :
    p.HasAt (b0 + Ix.neg) (negateModule (b0 + Ix.neg) h) ∧
    p.HasAt (b0 + Ix.add) (addModule (b0 + Ix.add) h) ∧
    p.HasAt (b0 + Ix.isZ) (isZeroModule (b0 + Ix.isZ)) ∧
    p.HasAt (b0 + Ix.less) (lessModule (b0 + Ix.less) h) ∧
    p.HasAt (b0 + Ix.ext) (signExtendModule (b0 + Ix.ext) h) := by
  have h1 := hasAt_append_right hp
  rw [pathCoreBodies_length] at h1
  have h2 := hasAt_append_right h1
  have h3 := hasAt_append_right h2
  have h4 := hasAt_append_right h3
  have h5 := hasAt_append_right h4
  refine ⟨hasAt_append_left h1, ?_, ?_, ?_, ?_⟩
  · have := hasAt_append_left h2
    simp only [negateModule, List.length_cons, List.length_nil] at this
    exact this
  · have := hasAt_append_left h3
    simp only [negateModule, addModule, List.length_cons, List.length_nil] at this
    exact this
  · have := hasAt_append_left h4
    simp only [negateModule, addModule, isZeroModule, List.length_cons, List.length_nil] at this
    exact this
  · simp only [negateModule, addModule, isZeroModule, lessModule, List.length_cons,
      List.length_nil] at h5
    exact h5

theorem copy_at (hp : p.HasAt b0 (pathTreeBodies h b0)) :
    p.HasAt (b0 + Ix.copy) [copyWords] := by
  intro i hi
  obtain rfl : i = 0 := by simpa using hi
  exact core_at hp 8 (by decide)

section Width

variable {w : ℕ} (K : ℕ) (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
  (hp : p.HasAt b0 (pathTreeBodies h b0))

include hh hw in
theorem one_lt_w : 1 < 2 ^ w := by
  have : 2 ^ 1 < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [pow_one] at this; omega

include hh hw in
theorem base_lt_w : base h < 2 ^ w := by
  unfold base
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

include hp in
theorem copy_ok : MeetsContract w p (b0 + Ix.copy) (copyWordsContract w) :=
  copyWords_meetsContract (copy_at hp)

include hh hw hp in
theorem negB_ok : MeetsContract w p (b0 + Ix.negB) (negBlockContract w h K) :=
  negBlock_meetsContract (one_lt_w hh hw) (core_at hp 17 (by decide))
    (negate_meetsContract (one_lt_w hh hw) (base_lt_w hh hw) (num_at hp).1)
    (copy_ok hp)

include hh hw hp in
theorem addB_ok : MeetsContract w p (b0 + Ix.addB) (addBlockContract w h K) :=
  addBlock_meetsContract (one_lt_w hh hw) (core_at hp 18 (by decide))
    (add_meetsContract hh hw (num_at hp).2.1) (copy_ok hp)

include hh hw hp in
theorem maxI_ok : MeetsContract w p (b0 + Ix.maxI) (maxIntoContract w h K) :=
  maxInto_meetsContract (core_at hp 19 (by decide))
    (less_meetsContract hh (one_lt_w hh hw) (base_lt_w hh hw) (num_at hp).2.2.2.1)
    (copy_ok hp)

include hh hw hp in
theorem seg_ok : MeetsContract w p (b0 + Ix.seg) (segContract w h K) :=
  seg_meetsContract (core_at hp 20 (by decide)) (addB_ok K hh hw hp) (maxI_ok K hh hw hp)

include hh hw hp in
theorem isZ_ok : MeetsContract w p (b0 + Ix.isZ) (isZeroContract w h) :=
  isZero_meetsContract (one_lt_w hh hw) (num_at hp).2.2.1

include hh hw hp in
theorem ext_ok : MeetsContract w p (b0 + Ix.ext) (signExtendContract w h) :=
  signExtend_meetsContract hh (one_lt_w hh hw) (base_lt_w hh hw) (num_at hp).2.2.2.2

/-- The payload steps of the path payload in `K` limbs. -/
def stepsAt : PayloadSteps w p pathPayload (pathLayout h K) (pathOk h K) :=
  pathSteps (b0 + Ix.rev) (b0 + Ix.act) (b0 + Ix.pullP) (b0 + Ix.isId) (b0 + Ix.setId)
    (b0 + Ix.negB) (b0 + Ix.addB) (b0 + Ix.seg) (b0 + Ix.isZ) (b0 + Ix.copy)
    (core_at hp 12 (by decide)) (core_at hp 13 (by decide)) (core_at hp 14 (by decide))
    (core_at hp 15 (by decide)) (core_at hp 16 (by decide))
    (negB_ok K hh hw hp) (addB_ok K hh hw hp) (seg_ok K hh hw hp) (isZ_ok hh hw hp)
    (copy_ok hp)

/-- The lazy procedures. -/
def lazyAt : LazyProcs w p pathPayload (pathLayout h K) (pathOk h K) (stepsAt K hh hw hp) where
  copy := b0 + Ix.copy
  revNode := b0 + Ix.revNode
  applyTag := b0 + Ix.applyTag
  pushDownRev := b0 + Ix.pdRev
  pushDownTag := b0 + Ix.pdTag
  pushDown := b0 + Ix.pushDown
  copy_ok := copy_ok hp
  revNode_body := core_at hp 27 (by decide)
  applyTag_body := core_at hp 28 (by decide)
  pushDownRev_body := core_at hp 29 (by decide)
  pushDownTag_body := core_at hp 30 (by decide)
  pushDown_body := core_at hp 31 (by decide)

/-- The splay procedures. -/
def splayAt : SplayProcs (lazyAt K hh hw hp) where
  pull := b0 + Ix.pull
  rotate := b0 + Ix.rotate
  step := b0 + Ix.step
  loop := b0 + Ix.sLoop
  pushPath := b0 + Ix.pushPath
  splay := b0 + Ix.splay
  pull_body := core_at hp 32 (by decide)
  rotate_body := core_at hp 33 (by decide)
  step_body := core_at hp 34 (by decide)
  loop_body := core_at hp 35 (by decide)
  pushPath_body := core_at hp 36 (by decide)
  splay_body := core_at hp 37 (by decide)

/-- The expose procedures. -/
def exposeAt : ExposeProcs (splayAt K hh hw hp) where
  detachRight := b0 + Ix.detachR
  attachRight := b0 + Ix.attachR
  loop := b0 + Ix.eLoop
  expose := b0 + Ix.expose
  note := b0 + Ix.note
  note_body := core_at hp 9 (by decide)
  detachRight_body := core_at hp 38 (by decide)
  attachRight_body := core_at hp 39 (by decide)
  loop_body := core_at hp 40 (by decide)
  expose_body := core_at hp 41 (by decide)

/-- The reroot and path procedures. -/
def pathAt : PathProcs (exposeAt K hh hw hp) where
  reroot := b0 + Ix.reroot
  rerootExpose := b0 + Ix.rerootE
  pathApply := b0 + Ix.pathApply
  reroot_body := core_at hp 42 (by decide)
  rerootExpose_body := core_at hp 43 (by decide)
  pathApply_body := core_at hp 44 (by decide)

/-- The two ready tests. -/
def testsAt (hK : 0 < K) : ReadyTests w p (pathLayout h K) pathRs pathRv where
  sumTest := b0 + Ix.sumT
  valTest := b0 + Ix.valT
  cost := 40
  sum_ok := pathSumTest_meetsContract hh hK (base_lt_w hh hw) (core_at hp 21 (by decide))
  val_ok := pathValTest_meetsContract hh hK (base_lt_w hh hw) (core_at hp 22 (by decide))

/-- The find-ready procedures. -/
def findAt (hK : 0 < K) : FindProcs (exposeAt K hh hw hp) (testsAt K hh hw hp hK) where
  desc := b0 + Ix.desc
  pop := b0 + Ix.pop
  find := b0 + Ix.gfind
  desc_body := core_at hp 49 (by decide)
  pop_body := core_at hp 10 (by decide)
  find_body := core_at hp 50 (by decide)

end Width

end MinCostFlow.LinkCut.PathProg
