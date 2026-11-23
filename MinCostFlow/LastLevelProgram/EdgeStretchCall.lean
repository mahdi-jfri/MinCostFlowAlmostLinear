module

public import MinCostFlow.LastLevelProgram.PathLengthCall
public import MinCostFlow.LastLevelProgram.StretchFromLength
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# An edge stretch from a lowest common ancestor

For Definition 5.8 (pages 19–20), use the two endpoint distances
and the distance of their lowest common ancestor to compute the
path length. Feed that block into the upward-rounded stretch call.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Arguments are `[distanceU, distanceV, distanceLCA, edge, L, P, heap]`. -/
def edgeStretchBody (path stretch : ℕ) : Stmt :=
  .call 7 path [.reg 0,.reg 1,.reg 2,.reg 4,.reg 6] ;;
  .call 8 stretch [.bin .sub (.reg 7) (.reg 4),.reg 3,.reg 4,.reg 5,.reg 7] ;;
  .ret (.reg 8)

/-- Scratch for both calls, with the rounded result at the end. -/
def edgeStretchSpace (L : ℕ) : ℕ := 5*L + stretchFromLengthSpace L

/-- Cost of the two calls and the local instructions. -/
def edgeStretchCost (L : ℕ) : ℕ := 186*L + stretchFromLengthCost L + 150

/-- Compute a rounded stretch from three prepared distance blocks and
one edge length. All these length blocks have the same scale. -/
theorem edgeStretch_runs {w h path stretch : ℕ} {p : Program}
    (hp : MeetsContract w p path (pathLengthContract w h))
    (hs : MeetsContract w p stretch (stretchFromLengthContract w h))
    (u v z edge L P heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hu : u+L ≤ heap) (hv : v+L ≤ heap) (hz : z+L ≤ heap) (he : edge+L ≤ heap)
    (hvu : Valid mem u h L) (hvv : Valid mem v h L)
    (hvz : Valid mem z h L) (hve : Valid mem edge h L)
    (hPword : P < 2^w)
    (hzero : ZeroFrom mem heap) (hroom : heap+edgeStretchSpace L < 2^w)
    (hfitU : Fits h L (intVal mem u h L - intVal mem z h L))
    (hfitV : Fits h L (intVal mem v h L - intVal mem z h L))
    (hfitPath : Fits h L ((intVal mem u h L - intVal mem z h L) +
      (intVal mem v h L - intVal mem z h L)))
    (hedge : 0 < intVal mem edge h L)
    (hfitStretch : stretchArithmeticFits h L P
      (intVal mem u h L + intVal mem v h L - 2*intVal mem z h L) (intVal mem edge h L)) :
    ∃ o st c, Runs w p ω (edgeStretchBody path stretch)
      (startState [u,v,z,edge,L,P,heap] mem pos) o st c ∧
      (o.value = heap+edgeStretchSpace L ∧ Valid st.mem (o.value-L) h L ∧
        fixVal st.mem (o.value-L) h L P =
          roundStretch P (1 + ((intVal mem u h L + intVal mem v h L -
            2*intVal mem z h L : ℤ) : ℝ) / (intVal mem edge h L : ℝ)) ∧
        (∀ a < heap, st.mem a = mem a) ∧ ZeroFrom st.mem o.value) ∧
      c ≤ edgeStretchCost L := by
  have hbound : heap+5*L+stretchFromLengthSpace L < 2^w := by
    simpa only [edgeStretchSpace, Nat.add_assoc] using hroom
  apply runs_start_le
  unfold edgeStretchBody
  refine runs_seq_call_le hp (vs := [u,v,z,L,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨u,v,z,L,heap,rfl,hu,hv,hz,hvu,hvv,hvz,hfitU,hfitV,hfitPath⟩,hzero,by
      change heap+5*L < 2^w; omega⟩
  · intro r₁ m₁ pos₁ hpost
    obtain ⟨hr₁,_,_,hf₁,hz₁,hpath,hval⟩ := hpost
    change r₁ = heap+5*L at hr₁
    change ∀ a < heap, m₁ a = mem a at hf₁
    change ZeroFrom m₁ r₁ at hz₁
    change Valid m₁ (heap+4*L) h L at hpath
    change intVal m₁ (heap+4*L) h L =
      intVal mem u h L + intVal mem v h L - 2*intVal mem z h L at hval
    have hpbase : r₁-L = heap+4*L := by omega
    have heq (i : ℕ) (hi : i < L) := hf₁ (edge+i) (by omega)
    have heval : intVal m₁ edge h L = intVal mem edge h L := intVal_congr heq
    have hevalid : Valid m₁ edge h L := fun i hi => (heq i hi).trans_lt (hve i hi)
    refine runs_seq_call_le hs (vs := [r₁-L,edge,L,P,r₁]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨_,edge,L,P,r₁,rfl,by omega,by omega,by rwa [hpbase],hevalid,
        by rwa [heval],?_⟩,hz₁,?_⟩
      · rwa [hpbase,hval,heval]
      · change r₁+stretchFromLengthSpace L < 2^w
        omega
    · intro r₂ m₂ pos₂ hpost₂
      obtain ⟨hr₂,_,_,hf₂,hz₂,hvalid,hstretch⟩ := hpost₂
      change r₂ = r₁+stretchFromLengthSpace L at hr₂
      change ∀ a < r₁, m₂ a = m₁ a at hf₂
      change ZeroFrom m₂ r₂ at hz₂
      change Valid m₂ (r₁+stretchFromLengthSpace L-L) h L at hvalid
      change fixVal m₂ (r₁+stretchFromLengthSpace L-L) h L P =
        roundStretch P (1 + (intVal m₁ (r₁-L) h L : ℝ) / (intVal m₁ edge h L : ℝ)) at hstretch
      rw [hpbase,hval,heval] at hstretch
      refine runs_ret_le (v := r₂) (by eval_expr) ?_ ?_
      · refine ⟨by change r₂ = _; unfold edgeStretchSpace; omega,
          ?_,?_,fun a ha => (hf₂ a (by omega)).trans (hf₁ a ha),hz₂⟩
        · change Valid m₂ (r₂-L) h L
          rwa [hr₂]
        · change fixVal m₂ (r₂-L) h L P = _
          rwa [hr₂]
      · simp [edgeStretchCost,pathLengthContract,stretchFromLengthContract,heapContract,argsSize,Expr.size]
        omega

/-- Heap interface for one rounded edge stretch. The last block of the
allocated region holds the rounded stretch at scale `P`. -/
def edgeStretchContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ u v z edge L P heap, args = [u,v,z,edge,L,P,heap] ∧
      u+L ≤ heap ∧ v+L ≤ heap ∧ z+L ≤ heap ∧ edge+L ≤ heap ∧
      Valid mem u h L ∧ Valid mem v h L ∧ Valid mem z h L ∧ Valid mem edge h L ∧
      Fits h L (intVal mem u h L - intVal mem z h L) ∧
      Fits h L (intVal mem v h L - intVal mem z h L) ∧
      Fits h L ((intVal mem u h L - intVal mem z h L) +
        (intVal mem v h L - intVal mem z h L)) ∧
      0 < intVal mem edge h L ∧ stretchArithmeticFits h L P
        (intVal mem u h L + intVal mem v h L - 2*intVal mem z h L) (intVal mem edge h L))
    (fun args mem out =>
      let L := args.getD 4 0
      let P := args.getD 5 0
      let dest := heapArg args + edgeStretchSpace L - L
      let u := intVal mem (args.getD 0 0) h L
      let v := intVal mem (args.getD 1 0) h L
      let z := intVal mem (args.getD 2 0) h L
      let e := intVal mem (args.getD 3 0) h L
      Valid out dest h L ∧ fixVal out dest h L P =
        roundStretch P (1 + ((u+v-2*z : ℤ) : ℝ) / (e : ℝ)))
    (fun args _ => edgeStretchCost (args.getD 4 0))
    (fun args _ => edgeStretchSpace (args.getD 4 0))
  { C with post := fun args mem ret out =>
      ret = heapArg args + edgeStretchSpace (args.getD 4 0) ∧ C.post args mem ret out }

/-- The verified distance arithmetic and rounding satisfy the heap interface. -/
theorem edgeStretch_meetsContract {w h entry path stretch : ℕ} {p : Program}
    (he : p.procs[entry]? = some (edgeStretchBody path stretch))
    (hp : MeetsContract w p path (pathLengthContract w h))
    (hs : MeetsContract w p stretch (stretchFromLengthContract w h)) :
    MeetsContract w p entry (edgeStretchContract w h) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨⟨u,v,z,edge,L,P,heap,rfl,hu,hv,hz,hedge,hvu,hvv,hvz,hve,
    hfitU,hfitV,hfitPath,hpos,hfitStretch⟩,hzero,hroom⟩ := hpre
  obtain ⟨o,st,c,hr,⟨hret,hvalid,hval,hframe,hzero'⟩,hcost⟩ :=
    edgeStretch_runs hp hs u v z edge L P heap pos mem ω hu hv hz hedge
      hvu hvv hvz hve (hwords P (by simp)) hzero hroom hfitU hfitV hfitPath hpos hfitStretch
  have hle : heap ≤ o.value := hret ▸ Nat.le_add_right _ _
  rw [hret] at hvalid hval
  exact ⟨o,st,c,hr,⟨hret,hle,hret.le,hframe,hzero',hvalid,hval⟩,hcost⟩

open LSF in
/-- The input length scale cancels in the ratio, so the rounded result of
the machine call is the rounded tree stretch required by the model. -/
theorem edgeStretch_eq_model {G T : MGraph} {r e : ℕ} (hT : IsRootedTree T r)
    (hu : G.tail e ∈ T.V) (hv : G.head e ∈ T.V) (ℓ : ℕ → ℝ)
    {mem : ℕ → ℕ} {u v z d h L P Q : ℕ}
    (hdu : fixVal mem u h L Q = walkLength ℓ (T.forestPath (G.tail e) r))
    (hdv : fixVal mem v h L Q = walkLength ℓ (T.forestPath (G.head e) r))
    (hdz : fixVal mem z h L Q = walkLength ℓ (T.forestPath (lca T r (G.tail e) (G.head e)) r))
    (hde : fixVal mem d h L Q = ℓ e) :
    roundStretch P (1 + ((intVal mem u h L + intVal mem v h L -
      2*intVal mem z h L : ℤ) : ℝ) / (intVal mem d h L : ℝ)) =
      roundStretch P (treeStretch G T ℓ e) := by
  unfold treeStretch
  rw [treeDistance_eq_rootDistances hT hu hv ℓ]
  rw [← hdu, ← hdv, ← hdz, ← hde]
  simp only [fixVal, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  have hscale : (2 : ℝ)^Q ≠ 0 := by positivity
  rw [← div_div_div_cancel_right₀ hscale
    ((intVal mem u h L : ℝ) + (intVal mem v h L : ℝ) - 2*(intVal mem z h L : ℝ))]
  congr 3
  ring

end MinCostFlow.LastLevelProgram
