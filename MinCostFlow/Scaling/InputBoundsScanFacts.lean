module

public import MinCostFlow.Scaling.StridedMaxProgram
public import MinCostFlow.Scaling.InputMaxLayout
import MinCostFlow.Scaling.InputMagnitudeBounds
import MinCostFlow.Scaling.SignedTableLayout
import WordRAM.LinkDefs

/-!
# Preconditions of the original-input bound scans

Each scan reads a magnitude field of the statement's encoding. The
capacity maximum bounds all lower, upper, and demand fields. Ten cells
of address slack cover the final recursive source pointer even when a
field lies past the end of an empty record block.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The four exact field scans are valid together in the original source
memory, with the statement's two maximum bounds. -/
theorem inputBounds_scan_pre (w : ℕ) (I : Instance) (hv : I.IsValid)
    (mem : ℕ → ℕ) (a : ℕ) (hat : ListAt mem a I.encode)
    (hs : a+I.encode.length+10<2^w) (hC : I.maxCost<2^w) (hU : I.maxCapacity<2^w) :
    (stridedMaxContract w (I.edges.map (fun e => e.lower.natAbs))).pre [a+5,I.m,8] mem ∧
    (stridedMaxContract w (I.edges.map (fun e => e.upper.natAbs))).pre [a+7,I.m,8] mem ∧
    (stridedMaxContract w (I.edges.map (fun e => e.cost.natAbs))).pre [a+9,I.m,8] mem ∧
    (stridedMaxContract w (I.demand.map Int.natAbs)).pre [a+3+8*I.m,I.n,2] mem := by
  have hlen := instance_encode_length I hv
  have h2 : 2<2^w := by omega
  have hl : (I.edges.map (fun e => e.lower.natAbs)).foldr max 0≤I.maxCapacity := by
    apply List.max_le_of_forall_le
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact lower_natAbs_le_maxCapacity I e he
  have hu : (I.edges.map (fun e => e.upper.natAbs)).foldr max 0≤I.maxCapacity := by
    apply List.max_le_of_forall_le
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact upper_natAbs_le_maxCapacity I e he
  have hd : (I.demand.map Int.natAbs).foldr max 0≤I.maxCapacity := by
    apply List.max_le_of_forall_le
    intro x hx
    exact Link.elem_le_foldr_max (List.mem_append_right _ hx)
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨a+5,8,by simp [Instance.m],?_,?_,hl.trans_lt hU,h2⟩
    · intro i
      exact lower_field_at I mem a hat ⟨i.val,by simpa using i.isLt⟩
    · simp only [List.length_map]; change a+5+8*I.m<2^w; omega
  · refine ⟨a+7,8,by simp [Instance.m],?_,?_,hu.trans_lt hU,h2⟩
    · intro i
      exact upper_field_at I mem a hat ⟨i.val,by simpa using i.isLt⟩
    · simp only [List.length_map]; change a+7+8*I.m<2^w; omega
  · refine ⟨a+9,8,by simp [Instance.m],?_,?_,hC,h2⟩
    · intro i
      exact cost_field_at I mem a hat ⟨i.val,by simpa using i.isLt⟩
    · simp only [List.length_map]; change a+9+8*I.m<2^w; omega
  · refine ⟨a+3+8*I.m,2,by simp [hv.2],?_,?_,hd.trans_lt hU,h2⟩
    · intro i
      have hi : i.val<I.demand.length := by simpa using i.isLt
      have h := integers_pair_at I.demand mem (a+2+8*I.m) (instance_demands_at I mem a hat) ⟨i.val,hi⟩
      have hm := h 1 (by change 1<2; omega)
      rw [List.getD_eq_getElem _ _ hi] at hm
      have he : a+2+8*I.m+2*i.val+1=a+3+8*I.m+2*i.val := by omega
      rw [he] at hm
      simpa [encodeInt] using hm
    · simp only [List.length_map,hv.2]; omega

end MinCostFlow.Scaling.Machine
