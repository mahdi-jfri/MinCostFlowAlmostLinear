module

public import MinCostFlow.HierPaths.BuildTopPlayerSetup

/-! # Depth inputs determined by the schedule and the current graphs -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The schedule fixes the player and geometry words. The parent graphs
and their addresses come from the preceding advance. -/
def buildTopScheduledDepth (table n term x b m d j dir : ℕ) (addr : ℕ → ℕ)
    (graphs : ℕ → Cited.Graph) : BuildTopDepthInput :=
  { buildTopDepthPlayer term (2 ^ x) (depthOf m) (49 * (x + 1) + 2) (x + 1)
      (100 * d) (4 * PParam ParamConfig.default (2 ^ x) (depthOf m)) j with
    graphDir := dir
    replyDir := buildTopScheduleReplies table n x j
    childSize := groupSize x b (j + 1)
    branch := branching x b j
    count := numGroups x b j
    graphAddr := addr
    graph := graphs }

/-- Player words computed before the recursion can be used for any later reply. -/
theorem buildTopScheduledDepth_playerWords (table n term x b m d j dir : ℕ)
    (addr : ℕ → ℕ) (graphs : ℕ → Cited.Graph) :
    (buildTopScheduledDepth table n term x b m d j dir addr graphs).playerWords =
      buildTopPlayerWords term x m d j := by
  simp only [buildTopScheduledDepth, buildTopDepthPlayer, BuildTopDepthInput.playerWords,
    buildTopPlayerWords]

/-- The complete schedule row depends only on public shape and player parameters. -/
theorem buildTopScheduledDepth_scheduleWords (table n term x b m d j dir dir' : ℕ)
    (addr addr' : ℕ → ℕ) (graphs graphs' : ℕ → Cited.Graph) :
    let inCell := buildTopSchedulePointer table n j
    let outCell := buildTopSchedulePointer table n (j + 1)
    (buildTopScheduledDepth table n term x b m d j dir addr graphs).scheduleWords inCell outCell =
      (buildTopScheduledDepth table n term x b m d j dir' addr' graphs').scheduleWords inCell outCell :=
  rfl

/-- Prepare the schedule for every possible succession of certified replies
from one table of computed player words. -/
theorem buildTopScheduleRun_forDepths {w write players geometry addresses x b table n src pos : ℕ}
    {term m d : ℕ} {p : Program} {mem : ℕ → ℕ} (ω : ℕ → Bool)
    (hf : p.procs[write]? = some (buildTopScheduleRow players geometry addresses))
    (hp : p.procs[players]? = some buildTopSchedulePlayers)
    (hg : p.procs[geometry]? = some buildTopScheduleGeometry)
    (ha : p.procs[addresses]? = some buildTopScheduleAddresses)
    (hdepth : n ≤ leafDepth x b) (hb : 0 < b) (hbx : b ≤ x)
    (hP : 2 ^ x < 2 ^ w) (hend : buildTopScheduleEnd table n x < 2 ^ w)
    (hsrc : src + 7 * n < 2 ^ w) (hsep : src + 7 * n ≤ table ∨ table + 13 * n ≤ src)
    (hwords : ∀ j < n, ∀ v ∈ buildTopPlayerWords term x m d j, v < 2 ^ w)
    (hinput : ∀ j < n, ListAt mem (src + 7 * j) (buildTopPlayerWords term x m d j)) :
    ∃ t c, Runs w p ω (buildTopScheduleRun write)
      (startState [x,b,table,n,src] mem pos) (.returned table) t c ∧
      (∀ j < n, ∀ dir addr graphs, ListAt t.mem (table + 13 * j)
        ((buildTopScheduledDepth table n term x b m d j dir addr graphs).scheduleWords
          (buildTopSchedulePointer table n j) (buildTopSchedulePointer table n (j + 1)))) ∧
      (∀ y, y < table ∨ table + 13 * n ≤ y → t.mem y = mem y) ∧ c ≤ 389 * n + 12 := by
  let D := fun j => buildTopScheduledDepth table n term x b m d j 0
    (fun _ => 0) (fun _ => ⟨0, []⟩)
  obtain ⟨t,c,hr,hrows,hframe,hcost⟩ :=
    buildTopScheduleRun_runs (D := D) ω hf hp hg ha (fun _ _ => ⟨rfl,rfl,rfl,rfl⟩)
      hdepth hb hbx hP hend hsrc hsep
      (fun j hj => by simpa only [D, buildTopScheduledDepth_playerWords] using hwords j hj)
      (fun j hj => by simpa only [D, buildTopScheduledDepth_playerWords] using hinput j hj)
  exact ⟨t,c,hr,fun j hj _ _ _ => hrows j hj,hframe,hcost⟩

def buildTopScheduleRunContract (w x b table n src term m d : ℕ) : Contract :=
  {
      pre := fun args mem => args = [x,b,table,n,src] ∧ n ≤ leafDepth x b ∧
        0 < b ∧ b ≤ x ∧ 2 ^ x < 2 ^ w ∧ buildTopScheduleEnd table n x < 2 ^ w ∧
        src + 7 * n < 2 ^ w ∧ (src + 7 * n ≤ table ∨ table + 13 * n ≤ src) ∧
        (∀ j < n, ∀ v ∈ buildTopPlayerWords term x m d j, v < 2 ^ w) ∧
        ∀ j < n, ListAt mem (src + 7 * j) (buildTopPlayerWords term x m d j)
      post := fun _ mem v mem' => v = table ∧
        (∀ j < n, ∀ dir addr graphs, ListAt mem' (table + 13 * j)
          ((buildTopScheduledDepth table n term x b m d j dir addr graphs).scheduleWords
            (buildTopSchedulePointer table n j) (buildTopSchedulePointer table n (j + 1)))) ∧
        ∀ y, y < table ∨ table + 13 * n ≤ y → mem' y = mem y
      cost := fun _ _ => 389 * n + 12 }

/-- The schedule pass is callable with the player table written by setup. -/
theorem buildTopScheduleRun_meetsContract
    {w f write players geometry addresses x b table n src term m d : ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildTopScheduleRun write))
    (hw : p.procs[write]? = some (buildTopScheduleRow players geometry addresses))
    (hp : p.procs[players]? = some buildTopSchedulePlayers)
    (hg : p.procs[geometry]? = some buildTopScheduleGeometry)
    (ha : p.procs[addresses]? = some buildTopScheduleAddresses) :
    MeetsContract w p f (buildTopScheduleRunContract w x b table n src term m d) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl,hd,hb,hbx,hP,hend,hsrc,hsep,hwords,hrows⟩ := hpre
  obtain ⟨t,c,hr,hout,hframe,hcost⟩ :=
    buildTopScheduleRun_forDepths (pos := pos) ω hw hp hg ha hd hb hbx
      hP hend hsrc hsep hwords hrows
  exact ⟨.returned table,t,c,hr,⟨rfl,hout,hframe⟩,hcost⟩

end MinCostFlow.HierPaths

end
