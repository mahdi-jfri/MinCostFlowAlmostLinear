module

public import MinCostFlow.MinRatio.FreshTables
import WordRAM.Tactic

/-!
# Looking up the current names for Query and Detect

The two bounded tables used by Algorithm 2 distinguish the graph's
external edge names from the fresh internal names. Query reads the
forward table. Detect reads the inverse table before reporting an edge.
The same read-only procedure implements both lookups.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Read one entry from a name table. Arguments are its base and a name. -/
def freshLookupBody : Stmt := .ret (.load (.bin .add (.reg 0) (.reg 1)))

/-- The selected cell must be in memory and contain a machine word. -/
def freshLookupContract (w : ℕ) : Contract where
  pre args mem := ∃ base name, args = [base, name] ∧
    base + name < 2 ^ w ∧ mem (base + name) < 2 ^ w
  post args mem ret mem' := ret = mem (args.getD 0 0 + args.getD 1 0) ∧ mem' = mem
  cost _ _ := 5

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain

/-- The lookup reads one cell for every tape and leaves memory intact. -/
theorem freshLookup_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.HasAt entry [freshLookupBody]) :
    MeetsContract w p entry (freshLookupContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, name, rfl, haddr, hvalue⟩ := hpre
  apply runs_start_le
  unfold freshLookupBody
  refine runs_ret_le (v := mem (base + name)) (by eval_expr) ⟨rfl, rfl⟩ ?_
  change 5 ≤ 5
  exact le_rfl

/-- Query's forward lookup returns a live internal name below the fresh
counter. The reverse table takes that name back to the queried edge. -/
theorem freshLookup_query {w fwd inv counter extCap intCap next edge ret : ℕ}
    {G H : MGraph} {f g : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hF : FreshInv G H f g next)
    (hT : FreshTablesAt mem fwd inv counter extCap intCap f g next)
    (he : edge ∈ G.E) (hcap : edge < extCap)
    (hpost : (freshLookupContract w).post [fwd, edge] mem ret mem') :
    ret = f edge ∧ ret ∈ H.E ∧ ret < next ∧ g ret = edge ∧ mem' = mem := by
  have hr : ret = f edge := hpost.1.trans (hT.2.1 edge hcap)
  have hin : f edge ∈ H.E := by
    rw [hF.hE]
    exact Finset.mem_image_of_mem f he
  refine ⟨hr, hr ▸ hin, hr ▸ hF.hLtFresh _ hin, ?_, hpost.2⟩
  rw [hr]
  exact hF.hLeft edge he

/-- Detect's inverse lookup reports the live external name for the
selected internal edge. No other live internal edge has the same name. -/
theorem freshLookup_detect {w fwd inv counter extCap intCap next edge ret : ℕ}
    {G H : MGraph} {f g : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hF : FreshInv G H f g next)
    (hT : FreshTablesAt mem fwd inv counter extCap intCap f g next)
    (he : edge ∈ H.E) (hcap : edge < intCap)
    (hpost : (freshLookupContract w).post [inv, edge] mem ret mem') :
    ret = g edge ∧ ret ∈ G.E ∧ f ret = edge ∧
      (∀ other ∈ H.E, g other = ret → other = edge) ∧ mem' = mem := by
  have hr : ret = g edge := hpost.1.trans (hT.2.2 edge hcap)
  obtain ⟨hback, hlive⟩ := hF.hRight edge he
  refine ⟨hr, hr ▸ hlive, ?_, ?_, hpost.2⟩
  · rw [hr]
    exact hback
  · intro other ho hname
    calc
      other = f (g other) := (hF.hRight other ho).1.symm
      _ = f (g edge) := congrArg f (hname.trans hr)
      _ = edge := hback

end MinCostFlow.MinRatio
