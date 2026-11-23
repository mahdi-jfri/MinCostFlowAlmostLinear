module

public import MinCostFlow.IPM.MinRatioSpec

/-!
# Validity of an unchanged input prefix

Validity reads only the graphs, batches, coefficients and schedule
through its horizon. Extending later machine inputs preserves those
conditions. The proof also transfers the insertion predicate used for
unchanged coefficients, so no edge-reset assumption is lost.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- A prefix that agrees on all input data inherits the full valid-history
specification, including insertion-based coefficient preservation. -/
theorem minRatioHistoryValid_prefix_congr (D E : DynamicInstance) (op other : ℕ → Bool) (T : ℕ)
    (h : ∀ j≤T,D.G j=E.G j ∧ D.U j=E.U j ∧ D.g j=E.g j ∧ D.ℓ j=E.ℓ j ∧ op j=other j)
    (hvalid : MinRatioHistoryValid D op T) : MinRatioHistoryValid E other T := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht hbound
    obtain ⟨hv,hG⟩ := hvalid.1 t ht hbound
    have hp := h (t-1) (by omega)
    have hc := h t hbound
    simpa only [hp.1,hc.1,hc.2.1] using And.intro hv hG
  · intro t ht
    obtain ⟨hG,hl⟩ := hvalid.2.1 t ht
    have hc := h t ht
    simpa only [hc.1,hc.2.2.2.1] using And.intro hG hl
  · intro t ht hbound hfalse
    have hc := h t hbound
    have hp := h (t-1) (by omega)
    have hop : op t=false := hc.2.2.2.2.trans hfalse
    have hh := hvalid.2.2.1 t ht hbound hop
    simpa only [hc.2.1,hc.2.2.1,hc.2.2.2.1,hp.2.2.1,hp.2.2.2.1] using hh
  · intro t ht hbound e he hn
    have hc := h t hbound
    have hp := h (t-1) (by omega)
    have heD : e∈(D.G t).E := hc.1 ▸ he
    have hnD : D.NotInsertedBetween e (t-1) t := by
      intro s hs hst u hu
      have hUs := (h s (hst.trans hbound)).2.1
      exact hn s hs hst u (hUs ▸ hu)
    have hh := hvalid.2.2.2 t ht hbound e heD hnD
    simpa only [hc.2.2.1,hc.2.2.2.1,hp.2.2.1,hp.2.2.2.1] using hh

/-- Prefix-validity agreement can hold simultaneously for every valid
history, with no added restriction on its graphs or operation schedule. -/
theorem historyValidity_agreement_refl (D : DynamicInstance) (op : ℕ → Bool) (T : ℕ) :
    ∀ j≤T,D.G j=D.G j ∧ D.U j=D.U j ∧ D.g j=D.g j ∧ D.ℓ j=D.ℓ j ∧ op j=op j := by
  intro j _
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end MinCostFlow.IPM.Machine
