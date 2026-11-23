module

public import MinCostFlow.IPM.MinRatioSpec
public import MinCostFlow.IPM.EdgeRefresh

/-!
# Extending actual min-ratio input histories

Detect keeps the fixed graph and coefficient arrays unchanged. Update
refreshes exactly the reported edge names by deletion and insertion,
and preserves coefficients on every other edge. These are precisely the
structural clauses of Definition 4.5's valid histories. They require no
hidden stability, so they also apply to lower target tests.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- A Detect stage extends a valid history when its input graph and
coefficient arrays are unchanged, as in the machine Detect call. -/
theorem minRatioHistoryValid_succ_detect (D : DynamicInstance) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (_hop : op (T+1)=false)
    (hG : D.G (T+1)=D.G T) (hU : D.U (T+1)=[])
    (hg : D.g (T+1)=D.g T) (hl : D.ℓ (T+1)=D.ℓ T) :
    MinRatioHistoryValid D op (T+1) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht hbound
    by_cases hold : t≤T
    · exact hvalid.1 t ht hold
    · have heq : t=T+1 := by omega
      subst t
      simp only [Nat.add_sub_cancel,hU,hG]
      exact ⟨trivial,rfl⟩
  · intro t ht
    by_cases hold : t≤T
    · exact hvalid.2.1 t hold
    · have heq : t=T+1 := by omega
      subst t
      rw [hG,hl]
      exact hvalid.2.1 T le_rfl
  · intro t ht hbound hfalse
    by_cases hold : t≤T
    · exact hvalid.2.2.1 t ht hold hfalse
    · have heq : t=T+1 := by omega
      subst t
      simpa only [Nat.add_sub_cancel] using And.intro hU (And.intro hg hl)
  · intro t ht hbound e he hn
    by_cases hold : t≤T
    · exact hvalid.2.2.2 t ht hold e he hn
    · have heq : t=T+1 := by omega
      subst t
      simp only [Nat.add_sub_cancel,hg,hl,and_self]

/-- An Update stage extends a valid history when its actual batch
refreshes existing names, its lengths are positive, and all unreported
coefficient entries are preserved. -/
theorem minRatioHistoryValid_succ_refresh (D : DynamicInstance) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hop : op (T+1)=true)
    (es : List ℕ) (hes : ∀ e∈es,e∈(D.G T).E)
    (hG : D.G (T+1)=D.G T) (hU : D.U (T+1)=refreshEdges (D.G T) es)
    (hl : ∀ e∈(D.G (T+1)).E,0<D.ℓ (T+1) e)
    (hunchanged : ∀ e∈(D.G T).E,e∉es →
      D.g (T+1) e=D.g T e ∧ D.ℓ (T+1) e=D.ℓ T e) :
    MinRatioHistoryValid D op (T+1) := by
  have hGvalid := (hvalid.2.1 T le_rfl).1
  have hrefresh := refreshEdges_spec (D.G T) hGvalid es hes
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht hbound
    by_cases hold : t≤T
    · exact hvalid.1 t ht hold
    · have heq : t=T+1 := by omega
      subst t
      simp only [Nat.add_sub_cancel,hU,hG,hrefresh.2.1]
      exact ⟨hrefresh.1,True.intro⟩
  · intro t ht
    by_cases hold : t≤T
    · exact hvalid.2.1 t hold
    · have heq : t=T+1 := by omega
      subst t
      exact ⟨hG ▸ hGvalid,hl⟩
  · intro t ht hbound hfalse
    by_cases hold : t≤T
    · exact hvalid.2.2.1 t ht hold hfalse
    · have heq : t=T+1 := by omega
      subst t
      rw [hop] at hfalse
      contradiction
  · intro t ht hbound e he hn
    by_cases hold : t≤T
    · exact hvalid.2.2.2 t ht hold e he hn
    · have heq : t=T+1 := by omega
      subst t
      have hnot : e∉es := by
        intro heList
        obtain ⟨u,hu,hins⟩ := (refreshEdges_inserts (D.G T) es e).mpr heList
        have hu' : u∈D.U (T+1) := hU ▸ hu
        exact hn (T+1) (by omega) le_rfl u hu' hins
      have heOld : e∈(D.G T).E := hG ▸ he
      simpa only [Nat.add_sub_cancel] using hunchanged e heOld hnot

/-- Constant graph and positive coefficients give jointly satisfiable
history conditions at every horizon, for either constant schedule. -/
theorem minRatioHistoryValid_constant (G : MGraph) (g l : ℕ → ℝ)
    (hG : G.IsValid) (hl : ∀ e∈G.E,0<l e) (op : ℕ → Bool) (T : ℕ) :
    MinRatioHistoryValid ⟨fun _ => G,fun _ => [],fun _ => g,fun _ => l⟩ op T := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t _ _
    exact ⟨trivial,rfl⟩
  · intro t _
    exact ⟨hG,hl⟩
  · intro t _ _ _
    exact ⟨rfl,rfl,rfl⟩
  · intro t _ _ _ _ _
    exact ⟨rfl,rfl⟩

end MinCostFlow.IPM.Machine
