module

public import MinCostFlow.HierPaths.BuildTopRootLayout
public import MinCostFlow.HierPaths.Impl

/-!
# Relocatable padded-root procedure

The root entry supplies the addresses of its consecutive buffers.
Its helpers include the port graph and explicit cloud construction.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.LowStretch

def buildTopRootHelpers (k : ℕ) : List Stmt :=
  [buildTopRootProc (k + 1) (k + 2) (k + 3),
    buildTopPort (k + 6) (k + 7), buildTopSize, buildTopRootPad (k + 4) (k + 5),
    buildCopyProc, buildTopPadProc, iotaP] ++ portGraphProcs (k + 7)

def buildTopRootModule : HierProc where
  entry := buildTopRootLayout
  helpers := buildTopRootHelpers

theorem buildTopRootModule_noRand : buildTopRootModule.NoRand := by
  intro k
  refine ⟨buildTopRootLayout_noRand k, ?_⟩
  intro s hs
  change s ∈ buildTopRootHelpers k at hs
  rw [buildTopRootHelpers, List.mem_append] at hs
  rcases hs with hs | hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact buildTopRootProc_noRand _ _ _
    · exact buildTopPort_noRand _ _
    · exact buildTopSize_noRand
    · exact buildTopRootPad_noRand _ _
    · simp [buildCopyProc, forRange, forUp, Stmt.NoRand]
    · exact buildTopPadProc_noRand
    · exact iotaP_noRand
  · exact portGraphProcs_noRand _ _ hs

theorem buildTopRootModule_meetsContract {w f k : ℕ} {G : Graph} {p : Program}
    (hp : buildTopRootModule.At p f k) :
    MeetsContract w p f (buildTopRootLayoutContract w G) := by
  obtain ⟨hp, hh⟩ := hp
  have hl := hasAt_append_left (show p.HasAt k (_ ++ _) from hh)
  have ht : p.HasAt (k + 7) (portGraphProcs (k + 7)) :=
    hasAt_append_right (show p.HasAt k (_ ++ _) from hh)
  have hi : p.HasAt (k + 6) [iotaP] := by
    intro q hq
    have : q = 0 := by simp at hq; omega
    subst q
    simpa using hl 6 (by simp)
  have hPort := buildTopPort_meetsContract (G := G) (w := w) (hl 1 (by simp)) hi ht
  have hPad := buildTopRootPad_meetsContract (w := w) (J := portGraph cloud G G.verts)
    (owners := (List.range (2 * G.m)).map (portOwner G G.verts)) (hl 3 (by simp)) (hl 4 (by simp))
    (hl 5 (by simp))
  exact buildTopRootLayout_meetsContract hp
    (buildTopRootProc_meetsContract (by simpa using hl 0 (by simp)) hPort (hl 2 (by simp)) hPad)

end MinCostFlow.HierPaths

end
