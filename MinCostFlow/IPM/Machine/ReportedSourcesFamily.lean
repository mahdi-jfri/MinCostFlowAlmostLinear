module

public import MinCostFlow.IPM.Machine.ScalarSourcesCongr
public import MinCostFlow.IPM.Machine.SourceFlowWriteFrame
public import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Preserving the whole family of reported numeric sources

A checked refresh changes one flow block within the numeric prefix.
The changed block is valid on success. All other flow blocks are
disjoint, and static tables and shared scalars avoid the whole flow
table. Hence every edge in the reported set retains its raw numeric
source conditions, including the edge just refreshed. This is the
source-family part of the reported-list invariant.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- A valid replacement of one dense flow entry preserves the numeric
source conditions of every reported edge. Table separation handles the
static sources and distinct entry indices handle all other flows. -/
theorem reported_sources_family_after_write
    {w h q K m c r lo f up a one mn mx L P E sourceEnd e : ℕ}
    {mem mem' : ℕ → ℕ} {S : Finset ℕ}
    (hfamily : ∀ j∈S,scalarCoefficientSourceConditions w h q K m
      (c+j*L) r (lo+j*L) (f+j*L) (up+j*L) a one mn mx L P E sourceEnd mem)
    (hS : ∀ j∈S,j<m) (he : e<m)
    (hframe : ∀ z<sourceEnd,(z<f+e*L ∨ f+e*L+L≤z) → mem' z=mem z)
    (hnew : Num.Valid mem' (f+e*L) h L)
    (hends : ∀ p∈[c,lo,f,up],p+m*L≤sourceEnd)
    (hshared : ∀ p∈[r,a,one,mn,mx],p+L≤sourceEnd)
    (htables : ∀ p∈[c,lo,up],p+m*L≤f ∨ f+m*L≤p)
    (hscalars : ∀ p∈[r,a,one,mn,mx],p+L≤f ∨ f+m*L≤p) :
    ∀ j∈S,scalarCoefficientSourceConditions w h q K m
      (c+j*L) r (lo+j*L) (f+j*L) (up+j*L) a one mn mx L P E sourceEnd mem' := by
  have static_disjoint (j : ℕ) (hj : j<m) :
      ∀ p∈[c+j*L,r,lo+j*L,up+j*L,a,one,mn,mx],
        p+L≤f+e*L ∨ f+e*L+L≤p := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
    all_goals subst p
    · exact reported_entries_separated c f L j e m hj he (htables c (by simp))
    · exact reported_scalar_separated r f L e m he (hscalars r (by simp))
    · exact reported_entries_separated lo f L j e m hj he (htables lo (by simp))
    · exact reported_entries_separated up f L j e m hj he (htables up (by simp))
    · exact reported_scalar_separated a f L e m he (hscalars a (by simp))
    · exact reported_scalar_separated one f L e m he (hscalars one (by simp))
    · exact reported_scalar_separated mn f L e m he (hscalars mn (by simp))
    · exact reported_scalar_separated mx f L e m he (hscalars mx (by simp))
  have all_ends (j : ℕ) (hj : j<m) :
      ∀ p∈[c+j*L,r,lo+j*L,f+j*L,up+j*L,a,one,mn,mx],p+L≤sourceEnd := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
    all_goals subst p
    · exact (reported_entry_end c L j m hj).trans (hends c (by simp))
    · exact hshared r (by simp)
    · exact (reported_entry_end lo L j m hj).trans (hends lo (by simp))
    · exact (reported_entry_end f L j m hj).trans (hends f (by simp))
    · exact (reported_entry_end up L j m hj).trans (hends up (by simp))
    · exact hshared a (by simp)
    · exact hshared one (by simp)
    · exact hshared mn (by simp)
    · exact hshared mx (by simp)
  intro j hj
  have hjm := hS j hj
  by_cases hje : j=e
  · subst j
    exact scalarCoefficientSourceConditions_after_flow_write (hfamily e hj) hframe le_rfl
      (hshared mn (by simp)) (hshared mx (by simp)) (static_disjoint e he) hnew
  · apply scalarCoefficientSourceConditions_congr (hfamily j hj) le_rfl
    intro p hp i hi
    have hdis : p+L≤f+e*L ∨ f+e*L+L≤p := by
      by_cases hpf : p=f+j*L
      · subst p
        exact reported_blocks_disjoint f L j e hje
      · apply static_disjoint j hjm p
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
        tauto
    apply hframe (p+i) (by have hh := all_ends j hjm p hp; omega)
    rcases hdis with hh | hh <;> omega

end MinCostFlow.IPM.Machine
