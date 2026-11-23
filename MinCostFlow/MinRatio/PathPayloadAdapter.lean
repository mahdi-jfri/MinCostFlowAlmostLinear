module

public import MinCostFlow.LinkCut.Payload
public import MinCostFlow.MinRatio.PathPayloadLaws

/-! The directional flow payload instantiates the shared link-cut algebra. -/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.LinkCut

/-- Directional path payload of the proof of Theorem 5.1 (pages 29–30). -/
def pathPayload : LctPayload (Option PathEdgeValue) PathSummary PathTag where
  empty := .empty
  single _ := PathSummary.single
  combine := PathSummary.combine
  revVal := Option.map PathEdgeValue.reverse
  revSum := PathSummary.reverse
  idTag := .zero
  isIdTag t := decide (t = .zero)
  compTag := PathTag.compose
  actVal t := Option.map (PathEdgeValue.shift t)
  actSum := PathSummary.shift
  revTag := PathTag.reverse

/-- All algebraic laws of the shared link-cut payload interface hold. -/
theorem pathPayload_laws : pathPayload.Laws where
  combine_empty_left := PathSummary.empty_combine
  combine_empty_right := PathSummary.combine_empty
  combine_assoc := PathSummary.combine_assoc
  revVal_revVal v := by
    cases v <;> simp [pathPayload, PathEdgeValue.reverse_reverse]
  revSum_revSum := PathSummary.reverse_reverse
  revTag_revTag := PathTag.reverse_reverse
  revSum_empty := PathSummary.reverse_empty
  revSum_single _ v := PathSummary.reverse_single v
  revSum_combine := PathSummary.reverse_combine
  actVal_id v := by
    cases v <;> simp [pathPayload, PathEdgeValue.shift_zero]
  actSum_id := PathSummary.shift_zero
  actVal_comp a b v := by
    cases v <;> simp [pathPayload, PathEdgeValue.shift_compose]
  actSum_comp := PathSummary.shift_compose
  compTag_id_left := PathTag.zero_compose
  compTag_id_right := PathTag.compose_zero
  compTag_assoc := PathTag.compose_assoc
  actSum_empty := PathSummary.empty_shift
  actSum_single t _ v := PathSummary.shift_single t v
  actSum_combine := PathSummary.shift_combine
  revTag_id := PathTag.reverse_zero
  revTag_comp := PathTag.reverse_compose
  revVal_actVal t v := by
    cases v <;> simp [pathPayload, PathEdgeValue.reverse_shift]
  revSum_actSum := PathSummary.reverse_shift
  isIdTag_id := by simp [pathPayload]
  isIdTag_eq t h := (PathTag.isZero_iff t).mp h

end MinCostFlow.MinRatio
