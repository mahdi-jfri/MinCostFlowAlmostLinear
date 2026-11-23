module

public import MinCostFlow.HierPaths.InitSections
public import MinCostFlow.HierPaths.InitProgRest

/-!
# The builder of the block from 24 section writers

`buildContract_of_secs` reduces `BuildContract` (the builder of the block of `Init`) to 24
writers, one per section of `HierConcrete.encode`, run by `secsEntry`. Each writer meets
`SecContract` with the invariant `buildInv`: the arguments are those of the rest of `Init`, the
static output and the input graph are in memory below the heap pointer, and the static output is
`Good`. The invariant depends only on memory below the heap pointer (`buildInv_stable`), so the
writers keep it.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- A procedure meeting a contract meets every weaker one: a stronger precondition, a weaker
postcondition and a larger cost. -/
theorem meetsContract_mono {w : ℕ} {p : Program} {f : ℕ} {C C' : Contract}
    (h : MeetsContract w p f C) (hpre : ∀ args mem, C'.pre args mem → C.pre args mem)
    (hpost : ∀ args mem v mem', C'.pre args mem → C.post args mem v mem' →
      C'.post args mem v mem')
    (hcost : ∀ args mem, C'.pre args mem → C.cost args mem ≤ C'.cost args mem) :
    MeetsContract w p f C' := by
  intro args mem pos ω hw hp
  obtain ⟨body, hb, o, st', c, hr, hpo, hc⟩ := h args mem pos ω hw (hpre _ _ hp)
  exact ⟨body, hb, o, st', c, hr, hpost _ _ _ _ hp hpo, hc.trans (hcost _ _ hp)⟩

/-- A list in memory stays when the memory under it is unchanged. -/
theorem listAt_of_eq {mem mem' : ℕ → ℕ} {a : ℕ} {l : List ℕ} (h : ListAt mem a l)
    (heq : ∀ i < l.length, mem' (a + i) = mem (a + i)) : ListAt mem' a l :=
  fun i hi => (heq i hi).trans (h i hi)

/-- The invariant of the writers: the arguments of the rest of `Init`, the static output at `h`
and the graph at `gAddr`, both below the heap pointer `h₁`, and `Good`. -/
def buildInv (w : ℕ) (S : StaticData) (a : ℕ) (G : Graph) (base : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ (gAddr phiNum phiDen M h h₁ : ℕ), base = [gAddr, phiNum, phiDen, M, h, h₁] ∧
    StaticOut mem h S ∧ h + S.encode.length ≤ h₁ ∧ GraphAt mem gAddr G ∧
    gAddr + G.encode.length ≤ h ∧ 1 ≤ phiNum ∧ phiNum ≤ phiDen ∧
    S.Good a (dOf phiNum phiDen) M G ∧ h₁ + (initBlock S a G phiNum phiDen M).length < 2 ^ w ∧
    xiOf a (dOf phiNum phiDen) G.m < 2 ^ w ∧ lamOf a (dOf phiNum phiDen) G.m < 2 ^ w

/-- `buildInv` depends only on memory below the heap pointer. -/
theorem buildInv_stable (w : ℕ) (S : StaticData) (a : ℕ) (G : Graph) (base : List ℕ)
    (mem mem' : ℕ → ℕ) (h : buildInv w S a G base mem)
    (heq : ∀ y < base.getD 5 0, mem' y = mem y) : buildInv w S a G base mem' := by
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, hG, hgh, h1, h2, hgood, hbw⟩ := h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at heq
  refine ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, ?_, hlen, ?_, hgh, h1, h2, hgood, hbw⟩
  · exact listAt_of_eq hSO fun i hi => heq _ (by omega)
  · exact listAt_of_eq hG fun i hi => heq _ (by omega)

theorem initBlock_eq_layoutList (S : StaticData) (a : ℕ) (G : Graph) (phiNum phiDen M : ℕ) :
    initBlock S a G phiNum phiDen M =
      layoutList (initConcrete S a (initAbs phiNum phiDen M G)).sections := rfl

/-- **The builder from 24 section writers.** If `secsEntry`-style code meets `SecsContract`
with `buildInv` for writers whose sections are those of the initial block, whose cost is at most
`K` per step and per word, and the block fits in `sR`, then it meets `BuildContract`. -/
theorem buildContract_of_secs {w a K : ℕ} {sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {S : StaticData}
    {G : Graph} {p : Program} {j : ℕ} {ss : List SecProc}
    (hf : MeetsContract w p j (SecsContract w (buildInv w S a G) ss))
    (hsecs : ∀ gAddr phiNum phiDen M h h₁,
      S.Good a (dOf phiNum phiDen) M G →
      ss.map (fun s => s.l [gAddr, phiNum, phiDen, M, h, h₁]) =
        (initConcrete S a (initAbs phiNum phiDen M G)).sections)
    (hsp : ∀ gAddr phiNum phiDen M h h₁, 1 ≤ phiNum → phiNum ≤ phiDen →
      S.Good a (dOf phiNum phiDen) M G →
      (initBlock S a G phiNum phiDen M).length +
        secScratch [gAddr, phiNum, phiDen, M, h, h₁] ss ≤ sR phiNum phiDen G.n G.m M)
    (hcost : ∀ gAddr phiNum phiDen M h h₁,
      S.Good a (dOf phiNum phiDen) M G →
      (ss.map fun s => s.cost [gAddr, phiNum, phiDen, M, h, h₁] + 40).sum + 30 ≤
        K * (initRestSteps S.H S.x S.b S.owner S.label G.n G.m +
          (initBlock S a G phiNum phiDen M).length)) :
    MeetsContract w p j (BuildContract w a K sR S G) := by
  refine meetsContract_mono hf ?_ ?_ ?_
  · intro args mem hpre
    obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, hz, hG, hgh, h1, h2, hgood,
      hsR, hξ, hlamWord⟩ := hpre
    have hL := length_layoutList_map [gAddr, phiNum, phiDen, M, h, h₁] ss
    rw [hsecs gAddr phiNum phiDen M h h₁ hgood, ← initBlock_eq_layoutList] at hL
    have hb := hsp gAddr phiNum phiDen M h h₁ h1 h2 hgood
    refine ⟨rfl, ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, hG, hgh, h1, h2, hgood,
      by omega, hξ, hlamWord⟩,
      hz, ?_⟩
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have h24 : 24 ≤ ss.length := by
      have := congrArg List.length (hsecs gAddr phiNum phiDen M h h₁ hgood)
      simp [HierConcrete.sections] at this
      omega
    omega
  · intro args mem v mem' hpre hpost
    obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, -, -, -, -, -, h1, h2, hgood, -⟩ := hpre
    obtain ⟨hv, hlist, hz, hbelow⟩ := hpost
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hv hlist hz hbelow
    rw [hsecs gAddr phiNum phiDen M h h₁ hgood, ← initBlock_eq_layoutList] at hv hlist
    have hb := hsp gAddr phiNum phiDen M h h₁ h1 h2 hgood
    exact ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hv, by omega, hlist, hv ▸ hz, hbelow⟩
  · intro args mem hpre
    obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, -, -, -, -, -, -, -, hgood, -⟩ := hpre
    simp only [SecsContract, BuildContract, List.getD_cons_succ, List.getD_cons_zero]
    exact hcost gAddr phiNum phiDen M h h₁ hgood

theorem length_sections_initConcrete (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.length = 24 := by
  simp [HierConcrete.sections]

/-- **The sections of the writers, one at a time.** The hypothesis `hsecs` of
`buildContract_of_secs` holds when there are 24 writers and writer `i` writes section `i`. -/
theorem map_l_eq_sections {S : StaticData} {a : ℕ} {s : PathDSAbsState} {ss : List SecProc}
    {base : List ℕ} (hlen : ss.length = 24)
    (h : ∀ i (hi : i < ss.length), ss[i].l base = (initConcrete S a s).sections.getD i []) :
    ss.map (fun s => s.l base) = (initConcrete S a s).sections := by
  apply List.ext_getElem
  · rw [List.length_map, hlen, length_sections_initConcrete]
  · intro i h1 h2
    rw [List.getElem_map, h i (by simpa using h1), List.getD_eq_getElem _ _ h2]

end MinCostFlow.HierPaths

end
