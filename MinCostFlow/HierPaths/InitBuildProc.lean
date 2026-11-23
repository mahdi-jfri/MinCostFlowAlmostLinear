module

public import MinCostFlow.HierPaths.InitBuild
public import MinCostFlow.HierPaths.Impl

/-!
# The builder as a `HierProc`

A relocatable writer (`SecW`) is a body that takes the index of its helpers, a fixed list of
helpers, the section and cost it writes for each static output and graph, and a proof that it
meets `SecContract` wherever it is placed. `buildProc Ws` places `secsEntry` as the entry, the
writers' bodies at `k, k + 1, …` and their helpers after them. `buildProc_spec` proves
`BuildProcSpec` from 24 writers whose sections are those of the initial block.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- A relocatable writer of one section. -/
structure SecW (a : ℕ) where
  body : ℕ → Stmt
  helpers : ℕ → List Stmt
  l : StaticData → Graph → List ℕ → List ℕ
  cost : StaticData → Graph → List ℕ → ℕ
  scratch : StaticData → Graph → List ℕ → ℕ := fun _ _ _ => 0
  noRand : ∀ k, (body k).NoRand ∧ ∀ s ∈ helpers k, s.NoRand
  spec : ∀ w p f k, p.procs[f]? = some (body k) → p.HasAt k (helpers k) → ∀ S G,
    MeetsContract w p f (SecContract w (buildInv w S a G) ⟨f, l S G, cost S G, scratch S G⟩)

/-- `writeSecs` only uses the procedure numbers. -/
theorem writeSecs_congr : ∀ (ss ss' : List SecProc) (i : ℕ), ss.map SecProc.f = ss'.map SecProc.f →
    writeSecs ss i = writeSecs ss' i
  | [], [], _, _ => rfl
  | s :: ss, s' :: ss', i, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [writeSecs, h.1, writeSecs_congr ss ss' (i + 1) h.2]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- The writers placed at `k, k + 1, …`, for a static output and graph. -/
def placedSecs {a : ℕ} (S : StaticData) (G : Graph) : List (SecW a) → ℕ → List SecProc
  | [], _ => []
  | W :: Ws, k => ⟨k, W.l S G, W.cost S G, W.scratch S G⟩ :: placedSecs S G Ws (k + 1)

/-- The procedure numbers `k, k + 1, …` of the writers, with no sections. -/
def placedNums {a : ℕ} : List (SecW a) → ℕ → List SecProc
  | [], _ => []
  | _ :: Ws, k => ⟨k, fun _ => [], fun _ => 0, fun _ => 0⟩ :: placedNums Ws (k + 1)

/-- The bodies of the writers, with their helpers from `h` on, one writer after the other. -/
def placedBodies {a : ℕ} : List (SecW a) → ℕ → List Stmt
  | [], _ => []
  | W :: Ws, h => W.body h :: placedBodies Ws (h + (W.helpers h).length)

/-- Place each helper at its final procedure index. -/
def placedHelpers {a : ℕ} : List (SecW a) → ℕ → List Stmt
  | [], _ => []
  | W :: Ws, h => W.helpers h ++ placedHelpers Ws (h + (W.helpers h).length)

/-- The builder: entry `secsEntry`, the writers' bodies at `k, …`, then their helpers. -/
def buildProc {a : ℕ} (Ws : List (SecW a)) : HierProc where
  entry k := secsEntry (placedNums Ws k)
  helpers k := placedBodies Ws (k + Ws.length) ++ placedHelpers Ws (k + Ws.length)

theorem placedSecs_map_f {a : ℕ} (S : StaticData) (G : Graph) :
    ∀ (Ws : List (SecW a)) (k : ℕ),
      (placedSecs S G Ws k).map SecProc.f = (placedNums Ws k).map SecProc.f
  | [], _ => rfl
  | _ :: Ws, k => by simp [placedSecs, placedNums, placedSecs_map_f S G Ws (k + 1)]

theorem placedSecs_map_l {a : ℕ} (S : StaticData) (G : Graph) (base : List ℕ) :
    ∀ (Ws : List (SecW a)) (k : ℕ),
      (placedSecs S G Ws k).map (fun s => s.l base) = Ws.map fun W => W.l S G base
  | [], _ => rfl
  | _ :: Ws, k => by simp [placedSecs, placedSecs_map_l S G base Ws (k + 1)]

theorem placedSecs_map_cost {a : ℕ} (S : StaticData) (G : Graph) (base : List ℕ) :
    ∀ (Ws : List (SecW a)) (k : ℕ),
      (placedSecs S G Ws k).map (fun s => s.cost base + 40) =
        Ws.map fun W => W.cost S G base + 40
  | [], _ => rfl
  | _ :: Ws, k => by simp [placedSecs, placedSecs_map_cost S G base Ws (k + 1)]

theorem placedSecs_scratch {a : ℕ} (S : StaticData) (G : Graph) (base : List ℕ) :
    ∀ (Ws : List (SecW a)) (k : ℕ),
      secScratch base (placedSecs S G Ws k) = (Ws.map fun W => W.scratch S G base).sum
  | [], _ => rfl
  | _ :: Ws, k => by
    have ih := placedSecs_scratch S G base Ws (k + 1)
    simpa [placedSecs, secScratch] using ih

theorem length_placedSecs {a : ℕ} (S : StaticData) (G : Graph) :
    ∀ (Ws : List (SecW a)) (k : ℕ), (placedSecs S G Ws k).length = Ws.length
  | [], _ => rfl
  | _ :: Ws, k => by simp [placedSecs, length_placedSecs S G Ws (k + 1)]

theorem hasAt_tail {p : Program} {k : ℕ} {s : Stmt} {l : List Stmt}
    (h : p.HasAt k (s :: l)) : p.HasAt (k + 1) l :=
  hasAt_append_right (l₁ := [s]) h

/-- **The placed writers meet their contracts.** -/
theorem placedSecs_spec {a w : ℕ} {p : Program} (S : StaticData) (G : Graph) :
    ∀ (Ws : List (SecW a)) (k h : ℕ), p.HasAt k (placedBodies Ws h) →
      p.HasAt h (placedHelpers Ws h) →
      ∀ s ∈ placedSecs S G Ws k, MeetsContract w p s.f (SecContract w (buildInv w S a G) s)
  | [], _, _, _, _ => by simp [placedSecs]
  | W :: Ws, k, h, hb, hh => by
    intro s hs
    simp only [placedSecs, List.mem_cons] at hs
    simp only [placedHelpers] at hh
    rcases hs with rfl | hs
    · have h0 := hb 0 (by simp [placedBodies])
      simp only [Nat.add_zero, placedBodies, List.getElem_cons_zero] at h0
      exact W.spec w p k h h0 (hasAt_append_left hh) S G
    · exact placedSecs_spec S G Ws (k + 1) (h + (W.helpers h).length)
        (hasAt_tail (by simpa [placedBodies] using hb)) (hasAt_append_right hh) s hs

theorem placedBodies_noRand {a : ℕ} :
    ∀ (Ws : List (SecW a)) (h : ℕ), ∀ s ∈ placedBodies Ws h, s.NoRand
  | [], _ => by simp [placedBodies]
  | W :: Ws, h => by
    intro s hs
    simp only [placedBodies, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact (W.noRand h).1
    · exact placedBodies_noRand Ws _ s hs

theorem placedHelpers_noRand {a : ℕ} :
    ∀ (Ws : List (SecW a)) (h : ℕ), ∀ s ∈ placedHelpers Ws h, s.NoRand
  | [], _ => by simp [placedHelpers]
  | W :: Ws, h => by
    intro s hs
    simp only [placedHelpers, List.mem_append] at hs
    rcases hs with hs | hs
    · exact (W.noRand h).2 s hs
    · exact placedHelpers_noRand Ws _ s hs

theorem length_placedBodies {a : ℕ} :
    ∀ (Ws : List (SecW a)) (h : ℕ), (placedBodies Ws h).length = Ws.length
  | [], _ => rfl
  | _ :: Ws, h => by simp [placedBodies, length_placedBodies Ws]

theorem writeSecs_noRand : ∀ (ss : List SecProc) (i : ℕ), (writeSecs ss i).NoRand
  | [], _ => by simp [writeSecs, Stmt.NoRand]
  | _ :: ss, i => by simp [writeSecs, Stmt.NoRand, writeSecs_noRand ss (i + 1)]

/-- **The builder from 24 relocatable writers meets `BuildProcSpec`**, when writer `i` writes
section `i` of the initial block, the writers cost at most `K` per step and per word, and the
block fits in `sR`. -/
theorem buildProc_spec {a K : ℕ} {sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {C c : ℕ} (Ws : List (SecW a))
    (hlen : Ws.length = 24)
    (hsecs : ∀ S G gAddr phiNum phiDen M h h₁,
      S.Good a (dOf phiNum phiDen) M G →
      Ws.map (fun W => W.l S G [gAddr, phiNum, phiDen, M, h, h₁]) =
        (initConcrete S a (initAbs phiNum phiDen M G)).sections)
    (hsp : ∀ S G gAddr phiNum phiDen M h h₁, 1 ≤ phiNum → phiNum ≤ phiDen →
      S.Good a (dOf phiNum phiDen) M G →
      (initBlock S a G phiNum phiDen M).length +
        (Ws.map fun W => W.scratch S G [gAddr, phiNum, phiDen, M, h, h₁]).sum ≤ sR phiNum phiDen G.n G.m M)
    (hcost : ∀ S G gAddr phiNum phiDen M h h₁,
      S.Good a (dOf phiNum phiDen) M G →
      (Ws.map fun W => W.cost S G [gAddr, phiNum, phiDen, M, h, h₁] + 40).sum + 30 ≤
        K * (initRestSteps S.H S.x S.b S.owner S.label G.n G.m +
          (initBlock S a G phiNum phiDen M).length))
    (hform : SpaceForm a sR C c) :
    BuildProcSpec a (buildProc Ws) K sR C c := by
  refine ⟨fun k => ⟨?_, ?_⟩, hform, ?_⟩
  · exact (by simp [buildProc, secsEntry, Stmt.NoRand, writeSecs_noRand])
  · intro s hs
    simp only [buildProc, List.mem_append] at hs
    rcases hs with hs | hs
    · exact placedBodies_noRand Ws _ s hs
    · exact placedHelpers_noRand Ws _ s hs
  intro w p j k hat S G
  obtain ⟨hj, hk⟩ := hat
  have hB := hasAt_append_left hk
  have hH := hasAt_append_right hk
  rw [length_placedBodies, hlen] at hH
  have hspec := placedSecs_spec (w := w) S G Ws k (k + Ws.length) hB (by rw [hlen]; exact hH)
  have hentry : p.procs[j]? = some (secsEntry (placedSecs S G Ws k)) := by
    rw [hj]
    simp only [buildProc, secsEntry]
    rw [writeSecs_congr _ _ 0 (placedSecs_map_f S G Ws k).symm]
  have hE := secsEntry_meetsContract (buildInv_stable w S a G)
    (by rw [length_placedSecs, hlen]) hspec hentry
  refine buildContract_of_secs hE (fun gAddr phiNum phiDen M h h₁ hgood => ?_) ?_ ?_
  · rw [placedSecs_map_l]; exact hsecs S G gAddr phiNum phiDen M h h₁ hgood
  · intro gAddr phiNum phiDen M h h₁ h1 h2 hgood
    rw [placedSecs_scratch]; exact hsp S G gAddr phiNum phiDen M h h₁ h1 h2 hgood
  · intro gAddr phiNum phiDen M h h₁ hgood
    rw [placedSecs_map_cost]; exact hcost S G gAddr phiNum phiDen M h h₁ hgood

end MinCostFlow.HierPaths

end
