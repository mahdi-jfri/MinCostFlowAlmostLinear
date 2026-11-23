module

public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.AddCarry
public import MinCostFlow.LastLevelProgram.TreeDistance
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# Path length from three root-distance blocks

For each last-level stretch, subtract the common ancestor distance
from both endpoint distances and add the two remaining lengths.
This uses the root-distance identity for Definition 5.8 (pages 19–20).
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Arguments are `[distanceU, distanceV, distanceLCA, L, heap]`. -/
def pathLengthBody (sub add : ℕ) : Stmt :=
  .call 5 sub [.reg 0,.reg 2,.reg 3,.reg 4] ;;
  .call 6 sub [.reg 1,.reg 2,.reg 3,.reg 5] ;;
  .call 7 add [.bin .sub (.reg 5) (.reg 3),.bin .sub (.reg 6) (.reg 3),
    .reg 3,.const 0,.reg 6] ;;
  .ret (.reg 7)

private theorem blockFrame {mem out : ℕ → ℕ} {a heap h L : ℕ}
    (ha : a + L ≤ heap) (hf : ∀ x < heap, out x = mem x) :
    (Valid mem a h L → Valid out a h L) ∧ intVal out a h L = intVal mem a h L := by
  have hc (i : ℕ) (hi : i < L) := hf (a+i) (by omega)
  exact ⟨fun hv i hi => (hc i hi).trans_lt (hv i hi),intVal_congr hc⟩

/-- The distance lookup needs three blocks. The two differences and
their sum are computed exactly when they fit the chosen limb width. -/
theorem pathLength_runs {w h sub add : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (hs : p.HasAt sub (subtractModule sub h)) (ha : p.HasAt add (addCarryModule add h))
    (u v z L heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hu : u + L ≤ heap) (hv : v + L ≤ heap) (hz : z + L ≤ heap)
    (hvu : Valid mem u h L) (hvv : Valid mem v h L) (hvz : Valid mem z h L)
    (hzero : ZeroFrom mem heap) (hroom : heap + 5*L < 2 ^ w)
    (hfitU : Fits h L (intVal mem u h L - intVal mem z h L))
    (hfitV : Fits h L (intVal mem v h L - intVal mem z h L))
    (hfit : Fits h L ((intVal mem u h L - intVal mem z h L) +
      (intVal mem v h L - intVal mem z h L))) :
    ∃ o st c, Runs w p ω (pathLengthBody sub add)
      (startState [u,v,z,L,heap] mem pos) o st c ∧
      (o.value = heap + 5*L ∧ Valid st.mem (heap + 4*L) h L ∧
        intVal st.mem (heap + 4*L) h L =
          intVal mem u h L + intVal mem v h L - 2*intVal mem z h L ∧
        (∀ a < heap, st.mem a = mem a) ∧ ZeroFrom st.mem o.value) ∧
      c ≤ 186*L+120 := by
  let A := intVal mem u h L - intVal mem z h L
  let B := intVal mem v h L - intVal mem z h L
  have hsub := subtract_meetsContract hh hw hs
  have hsum := addCarry_meetsContract hh hw ha
  apply runs_start_le
  unfold pathLengthBody
  refine runs_seq_call_le hsub (vs := [u,z,L,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨u,z,L,heap,rfl,hu,hz,hvu,hvz⟩,hzero,by change heap+2*L < 2^w; omega⟩
  · intro r₁ m₁ pos₁ hpost
    obtain ⟨hr₁,_,_,hf₁,hz₁,hva,hA⟩ := hpost
    change r₁ = heap+2*L at hr₁
    change ∀ a < heap, m₁ a = mem a at hf₁
    change Valid m₁ (heap+L) h L at hva
    change intVal m₁ (heap+L) h L = wrap h L A at hA
    rw [wrap_of_fits hfitU] at hA
    have hV := blockFrame (h := h) hv hf₁
    have hZ := blockFrame (h := h) hz hf₁
    refine runs_seq_call_le hsub (vs := [v,z,L,r₁]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨v,z,L,r₁,rfl,by omega,by omega,hV.1 hvv,hZ.1 hvz⟩,hz₁,by
        change r₁+2*L < 2^w; omega⟩
    · intro r₂ m₂ pos₂ hpost₂
      obtain ⟨hr₂,_,_,hf₂,hz₂,hvb,hB⟩ := hpost₂
      change r₂ = r₁+2*L at hr₂
      change ∀ a < r₁, m₂ a = m₁ a at hf₂
      change Valid m₂ (r₁+L) h L at hvb
      change intVal m₂ (r₁+L) h L = wrap h L (intVal m₁ v h L - intVal m₁ z h L) at hB
      rw [hV.2,hZ.2,wrap_of_fits hfitV] at hB
      have hpres := blockFrame (h := h) (show heap+L+L ≤ r₁ by omega) hf₂
      have hbase₁ : r₁-L = heap+L := by omega
      have hbase₂ : r₂-L = r₁+L := by omega
      refine runs_seq_call_le hsum (vs := [r₁-L,r₂-L,L,0,r₂]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_,_,_,_,_,rfl,by omega,by omega,by decide,
          by rw [hbase₁]; exact hpres.1 hva,by rwa [hbase₂]⟩,hz₂,by
          change r₂+L < 2^w; omega⟩
      · intro r₃ m₃ pos₃ hpost₃
        obtain ⟨hr₃,_,_,hf₃,hz₃,hdigits⟩ := hpost₃
        change r₃ = r₂+L at hr₃
        change ∀ a < r₂, m₃ a = m₂ a at hf₃
        change ListAt m₃ r₂ (digits h L (unsignedVal m₂ (r₁-L) h L +
          unsignedVal m₂ (r₂-L) h L + 0)) at hdigits
        obtain ⟨hvalid,hval⟩ := addCarry_value hdigits
        rw [hbase₁,hbase₂,hpres.2,hA,hB,Nat.cast_zero,add_zero,wrap_of_fits hfit] at hval
        have hresult : r₂ = heap+4*L := by omega
        refine runs_ret_le (v := r₃) (by eval_expr) ?_ ?_
        · refine ⟨by change r₃ = heap+5*L; omega,hresult ▸ hvalid,?_,
            fun a h => (hf₃ a (by omega)).trans ((hf₂ a (by omega)).trans (hf₁ a h)),hz₃⟩
          rw [← hresult,hval]
          omega
        · simp [subtractContract,addCarryContract,heapContract,argsSize,Expr.size]
          omega

/-- Heap interface for the path-length call. -/
def pathLengthContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ u v z L heap, args = [u,v,z,L,heap] ∧
      u+L ≤ heap ∧ v+L ≤ heap ∧ z+L ≤ heap ∧
      Valid mem u h L ∧ Valid mem v h L ∧ Valid mem z h L ∧
      Fits h L (intVal mem u h L - intVal mem z h L) ∧
      Fits h L (intVal mem v h L - intVal mem z h L) ∧
      Fits h L ((intVal mem u h L - intVal mem z h L) +
        (intVal mem v h L - intVal mem z h L)))
    (fun args mem out =>
      let L := args.getD 3 0
      let result := heapArg args + 4*L
      Valid out result h L ∧ intVal out result h L =
        intVal mem (args.getD 0 0) h L + intVal mem (args.getD 1 0) h L -
          2 * intVal mem (args.getD 2 0) h L)
    (fun args _ => 186*args.getD 3 0+120)
    (fun args _ => 5*args.getD 3 0)
  { C with post := fun args mem ret out =>
      ret = heapArg args + 5*args.getD 3 0 ∧ C.post args mem ret out }

/-- Expose the path-length arithmetic as a procedure. -/
theorem pathLength_meetsContract {w h entry sub add : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (he : p.procs[entry]? = some (pathLengthBody sub add))
    (hs : p.HasAt sub (subtractModule sub h)) (ha : p.HasAt add (addCarryModule add h)) :
    MeetsContract w p entry (pathLengthContract w h) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨⟨u,v,z,L,heap,rfl,hu,hv,hz,hvu,hvv,hvz,hfitU,hfitV,hfit⟩,hzero,hroom⟩ := hpre
  obtain ⟨o, st, c, hr, ⟨hret, hvalid, hval, hframe, hzero'⟩, hcost⟩ :=
    pathLength_runs hh hw hs ha u v z L heap pos mem ω hu hv hz hvu hvv hvz
      hzero hroom hfitU hfitV hfit
  have hle : heap ≤ o.value := hret ▸ Nat.le_add_right _ _
  exact ⟨o, st, c, hr, ⟨hret,hle,hret.le,hframe,hzero',hvalid,hval⟩, hcost⟩

open LSF in
/-- If the three blocks store the tree's root distances, the computed
path block decodes to the length of the unique tree path. -/
theorem pathBlock_eq_length {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) (ℓ : ℕ → ℝ)
    {mem out : ℕ → ℕ} {a b d dest h L P : ℕ}
    (ha : fixVal mem a h L P = walkLength ℓ (T.forestPath u r))
    (hb : fixVal mem b h L P = walkLength ℓ (T.forestPath v r))
    (hd : fixVal mem d h L P = walkLength ℓ (T.forestPath (lca T r u v) r))
    (hout : intVal out dest h L =
      intVal mem a h L + intVal mem b h L - 2 * intVal mem d h L) :
    fixVal out dest h L P = walkLength ℓ (T.forestPath u v) := by
  rw [treeDistance_eq_rootDistances hT hu hv ℓ]
  rw [← ha, ← hb, ← hd]
  simp only [fixVal, hout, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  ring

end MinCostFlow.LastLevelProgram
