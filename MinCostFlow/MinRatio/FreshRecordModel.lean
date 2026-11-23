module

public import MinCostFlow.MinRatio.FreshRecord

/-!
# One refresh record advances the Algorithm 2 name invariant

The batch translator uses the fresh-name step once per external record.
The machine dispatcher writes exactly the step's translated record and
realizes both name tables and the counter of its result. The graph
invariant follows from the existing `translateUpdate_preserves` theorem.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- A successful dispatch advances the heap by the written record's length
and represents the exact next model maps, counter, and translated record. -/
theorem freshRecord_model {w src fwd inv counter heap ret internal next extCap intCap : ℕ}
    {G : MGraph} {e2i i2e : ℕ → ℕ} {record : Update} {mem mem' : ℕ → ℕ}
    (hbefore : FreshTablesAt mem fwd inv counter extCap intCap e2i i2e next)
    (hf : fwd + extCap ≤ heap) (hi : inv + intCap ≤ heap) (hc : counter < heap)
    (hdisjoint : fwd + extCap ≤ inv ∨ inv + intCap ≤ fwd)
    (hfc : counter < fwd ∨ fwd + extCap ≤ counter)
    (hic : counter < inv ∨ inv + intCap ≤ counter)
    (hnames : match record with
      | .insert e _ _ => e < extCap ∧ next < intCap ∧ internal = next
      | .delete e => internal = e2i e
      | .split .. => False)
    (hout : (freshRecordContract w record internal).post [src, fwd, inv, counter, heap] mem ret mem') :
    let result := translateUpdate G e2i i2e next record
    FreshTablesAt mem' fwd inv counter extCap intCap result.2.1 result.2.2.1 result.2.2.2.1 ∧
      ListAt mem' heap (updateWords result.2.2.2.2) ∧
      ret = heap + (updateWords record).length ∧ ZeroFrom mem' ret := by
  cases record with
  | split _ _ _ => cases hnames
  | delete e =>
    have he : internal = e2i e := hnames
    subst internal
    change (freshDeleteContract w e (e2i e)).post [src, fwd, heap] mem ret mem' at hout
    exact ⟨freshDelete_tables hbefore hf hi hc hout, freshDelete_model hout, hout.1, hout.2.2.2.2.1⟩
  | insert e u v =>
    obtain ⟨he, hn, heq⟩ := hnames
    subst internal
    change (freshInsertContract w e u v next).post [e, u, v, fwd, inv, counter, heap] mem ret mem' at hout
    refine ⟨freshInsert_tables hbefore he hn hf hi hdisjoint hfc hic hout, freshInsert_model hout, ?_, ?_⟩
    · obtain ⟨_, _, _, heap', hargs, hret, _⟩ := hout
      have hh : heap = heap' := congrArg (fun l : List ℕ => l.getD 6 0) hargs
      subst heap'
      exact hret
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hz⟩ := hout
      exact hz

/-- The model graph step corresponding to the translated machine record
preserves the fresh-name invariant and makes a valid internal update. -/
theorem freshRecord_graph_valid {extG intG : MGraph}
    {e2i i2e : ℕ → ℕ} {next : ℕ} {record : Update}
    (hF : FreshInv extG intG e2i i2e next) (hu : extG.UpdateIsValid record) :
    let result := translateUpdate extG e2i i2e next record
    FreshInv result.1 (intG.applyUpdate result.2.2.2.2)
      result.2.1 result.2.2.1 result.2.2.2.1 ∧ intG.UpdateIsValid result.2.2.2.2 := by
  have h := translateUpdate_preserves hF hu
  dsimp only at h ⊢
  exact ⟨h.1, h.2.1⟩

end MinCostFlow.MinRatio

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- The dispatcher keeps cells between the name tables and the output
cursor, including unread input and previously written output records. -/
theorem freshRecord_frame_interval
    {w src fwd inv counter heap ret internal lo extCap intCap : ℕ}
    {record : Update} {mem mem' : ℕ → ℕ}
    (hf : fwd + extCap ≤ lo) (hi : inv + intCap ≤ lo) (hc : counter < lo)
    (hnames : match record with
      | .insert e _ _ => e < extCap ∧ internal < intCap
      | .delete _ => True
      | .split .. => False)
    (hout : (freshRecordContract w record internal).post [src, fwd, inv, counter, heap] mem ret mem') :
    ∀ a, lo ≤ a → a < heap → mem' a = mem a := by
  cases record with
  | split _ _ _ => cases hnames
  | delete e =>
    have hframe : ∀ a < heap, mem' a = mem a := hout.2.2.2.1
    exact fun a _ ha => hframe a ha
  | insert e u v =>
    rcases hnames with ⟨he, hn⟩
    obtain ⟨fwd', inv', ctr', heap', hargs, _, _, _, _, _, hframe, _⟩ := hout
    have hf' : fwd = fwd' := congrArg (fun l : List ℕ => l.getD 3 0) hargs
    have hi' : inv = inv' := congrArg (fun l : List ℕ => l.getD 4 0) hargs
    have hctr' : counter = ctr' := congrArg (fun l : List ℕ => l.getD 5 0) hargs
    have hh' : heap = heap' := congrArg (fun l : List ℕ => l.getD 6 0) hargs
    subst fwd' inv' ctr' heap'
    intro a hlo hheap
    exact hframe a hheap (by omega) (by omega) (by omega)

end MinCostFlow.MinRatio

public section

namespace MinCostFlow.MinRatio

open IPM.Machine

/-- A record leaves every earlier cell unchanged except the two table
entries and the counter used by an insertion. -/
theorem freshRecord_frame_before {w src fwd inv counter heap ret internal a : ℕ}
    {record : Update} {mem mem' : ℕ → ℕ} (ha : a < heap)
    (hsafe : match (motive := Update → Prop) record with
      | .insert e _ _ => a ≠ fwd + e ∧ a ≠ inv + internal ∧ a ≠ counter
      | .delete _ => True
      | .split .. => False)
    (hout : (freshRecordContract w record internal).post [src, fwd, inv, counter, heap] mem ret mem') :
    mem' a = mem a := by
  cases record with
  | split _ _ _ => cases hsafe
  | delete e => exact hout.2.2.2.1 a ha
  | insert e u v =>
    obtain ⟨fwd', inv', ctr', heap', hargs, _, _, _, _, _, hframe, _⟩ := hout
    have hf' : fwd = fwd' := congrArg (fun l : List ℕ => l.getD 3 0) hargs
    have hi' : inv = inv' := congrArg (fun l : List ℕ => l.getD 4 0) hargs
    have hctr' : counter = ctr' := congrArg (fun l : List ℕ => l.getD 5 0) hargs
    have hh' : heap = heap' := congrArg (fun l : List ℕ => l.getD 6 0) hargs
    subst fwd' inv' ctr' heap'
    exact hframe a ha hsafe.1 hsafe.2.1 hsafe.2.2

end MinCostFlow.MinRatio
