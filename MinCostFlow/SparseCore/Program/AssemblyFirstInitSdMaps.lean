module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitMid
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSideModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitCompMath
import Mathlib.Tactic

/-!
# The maps of the bundle side at the init (`AssemblyFirstInitSdMaps`)

The front of the build writes the maps of the bundle side (`AsmSdMapsAt`): the array from vertices
to their component at `cmpH`, the array from edges to their bucket at `bktH = o₁ + 16`, the table of
the components at `ctH`, and the list of each component inside the slot lists. Here we prove
`AsmSdMapsAt` for the side `asmFiSide` from the facts of the front (`AsmFiFrontOut`), for any later
memory that keeps the cells in `[o₁ + 16, sEnd)` and holds the four words of the record.

The list of component `c` is `cslList D B c`. It sits at `base + 2 · slotSegStart D B c`, where
`base = sH + 2 + eCap + 3 m` is the start of the pairs of the slot lists. The segments of two
components do not meet, since an entry of `D` names its component as `D[j] / B`
(`slotSeg_iff`). So the lists of two components do not meet (`asmFi_csl_cell`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

/-- **A cell of the list of component `c`** is a word of the pair of an entry `j` of `D` whose
component is `c`. -/
theorem asmFi_csl_cell {mem mem' : ℕ → ℕ} {G : MGraph} {fe : List ℕ}
    {cmpH bktH nComp k B ctH heap eCap : ℕ} {S D : List ℕ}
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D) {c a : ℕ}
    (hc : c < nComp) (ha1 : mem' (ctH + 3 * c + 1) ≤ a)
    (ha2 : a < mem' (ctH + 3 * c + 1) + 2 * (cslList D B c).length) :
    ∃ j < D.length, D.getD j 0 / B = c ∧
      (a = heap + 2 + eCap + 3 * G.m + 2 * j ∨ a = heap + 2 + eCap + 3 * G.m + 2 * j + 1) := by
  rw [hO.ptr c hc] at ha1 ha2
  rw [cslList_length] at ha2
  have hle := slotSeg_le D B c
  by_cases hpos : 0 < slotSegLen D B c
  · rw [ite_eq_left hpos] at ha1 ha2
    set j := slotSegStart D B c + (a - (heap + 2 + eCap + 3 * G.m + 2 * slotSegStart D B c)) / 2
      with hj
    have hjD : j < D.length := by omega
    refine ⟨j, hjD, (slotSeg_iff hO.D_sorted B c hjD).mpr ⟨by omega, by omega⟩, by omega⟩
  · omega

/-- The value of a cell of the list of a component: the code part `D[j] % B` or the slot `j`. -/
theorem asmFi_csl_val {mem mem' : ℕ → ℕ} {G : MGraph} {fe : List ℕ}
    {cmpH bktH nComp k B ctH heap eCap : ℕ} {S D : List ℕ}
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D) (hB : 0 < B) {j a : ℕ}
    (hj : j < D.length)
    (ha : a = heap + 2 + eCap + 3 * G.m + 2 * j ∨ a = heap + 2 + eCap + 3 * G.m + 2 * j + 1) :
    mem' a < B ∨ mem' a < D.length := by
  obtain ⟨h1, h2⟩ := hO.pairs j hj
  rcases ha with rfl | rfl
  · rw [h1]; exact Or.inl (Nat.mod_lt _ hB)
  · rw [h2]; exact Or.inr hj

set_option maxHeartbeats 2000000 in
/-- **The maps of the bundle side at the init.** After the front, every later memory `mem'` that
keeps the cells in `[o₁ + 16, sEnd)` and holds the four words of the maps in the record at `o₁`
meets `AsmSdMapsAt` for the side `asmFiSide`, with the list of component `c` at the word
`ctH + 3 c + 1` and equal to `cslList D B c`. -/
theorem asmFiSide_maps {w depth expEnd L capExp M N k P vCap eCap h o₁ tourH cmpH ctH sH
    expPtr : ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End} {G : MGraph} {ℓ₀ : ℕ → ℝ}
    {mem regs : ℕ → ℕ} {st₁ : State} {xTour : (tourAsmRep vCap eCap).τ}
    {comps : List (Finset ℕ)} {S D : List ℕ} {memC : ℕ → ℕ} {C_lsst : ℝ} {ℓ : ℕ → ℝ}
    {bunH spanH walkPot lgFac : ℕ} {S5 : Fin eCap → Option BundleState} {m5 : BundleTableMeta eCap}
    {x6 : BucketSpannerMeta depth eCap} {mem' : ℕ → ℕ}
    (hF : AsmFiFrontOut w depth tr ord G ℓ₀ mem regs expPtr k L P vCap eCap h o₁ tourH
      xTour cmpH ctH sH comps S D memC st₁)
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hcsG : tr.cs.G = G) (hG₀ : tr.cs.G₀ = G) (hI : CompLSFInv C_lsst ℓ tr.cs)
    (hAC : tr.activeComps = largeComps k G) (hGval : G.IsValid)
    (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap)
    (hbktM : ∀ e ∈ G.E, bucketOf (tr.cs.lsf.wstr e * ℓ₀ e) = tr.origBucket e)
    (hcode : ∀ e ∈ G.E,
      bucketCode (tr.origBucket e) < asmFirstInitKeyBase P (mem (expPtr + 6)) L)
    (hact : ∀ q, q ∈ activePairs tr ↔ q.1 ∈ largeComps k G ∧
      ∃ e ∈ G.E, e ∉ tr.cs.lsf.F.F.E ∧ G.tail e ∈ q.1 ∧ tr.origBucket e = q.2)
    (hcmp : mem' (o₁ + ASM_SD_CMP) = cmpH) (hbkt : mem' (o₁ + ASM_SD_BKT) = o₁ + 16)
    (hct : mem' (o₁ + ASM_SD_CT) = ctH) (hnc : mem' (o₁ + ASM_SD_NCOMP) = comps.length)
    (hag : ∀ a, o₁ + 16 ≤ a → a < sH + slotListSpace eCap G.m → mem' a = st₁.mem a)
    (hBw : asmFirstInitKeyBase P (mem (expPtr + 6)) L < 2 ^ w)
    (hsw : sH + slotListSpace eCap G.m < 2 ^ w) :
    AsmSdMapsAt w o₁ ⟨tr, ord, vCap, eCap⟩
      (asmFiSide k vCap eCap M bunH S5 m5 spanH x6 (sH + 2 + eCap + 5 * G.m) D.length G.m
        (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH (o₁ + 16) ctH comps
        (fun c => st₁.mem (ctH + 3 * c + 1))
        (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) walkPot lgFac) mem' := by
  set B := asmFirstInitKeyBase P (mem (expPtr + 6)) L with hB
  have hBpos : 0 < B := by rw [hB]; unfold asmFirstInitKeyBase; omega
  have hsl : slotListSpace eCap G.m = eCap + 10 * G.m + 3 := rfl
  have hDm : D.length ≤ G.m := hF.slots.D_len.trans hF.slots.S_len
  have hcmpE := hF.cmpH_eq
  have hctE := hF.ctH_eq
  have hsHE := hF.sH_eq
  -- the model of the slot lists, as in the middle
  have hvV : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], v ∈ G.V := by
    intro c hc v hv
    have hCc := (hF.comps_iff _).mp (List.getElem_mem hc)
    obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hCc
    rw [← hu] at hv
    exact (mem_compOf_iff.mp hv).1
  have hcmpC : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], memC (cmpH + v) = c := by
    intro c hc v hv
    have := hVlt v (hvV c hc v hv)
    exact (hF.memC_agree _ (by omega)).trans (hF.comps_idx c hc v hv)
  have hbkC : ∀ e ∈ G.E, memC (o₁ + 16 + e) = bucketCode (tr.origBucket e) := by
    intro e he
    have := hElt e he
    rw [hF.memC_agree _ (by omega), hF.bkt_in e he, hbktM e he]
  have hfe : ∀ e ∈ G.E, e ∈ slotForestEdges mem (mem (mem (expPtr + 1) + 3))
      (mem (mem (expPtr + 1) + 2)) ↔ e ∈ tr.cs.lsf.F.F.E := fun e _ => asmFi_fe_iff hExp e
  have H : SlotKeyHyps tr comps G tr.cs.lsf.F.F.E k B G.E.toList :=
    ⟨hGval, hF.comps_nodup, hF.comps_iff, fun e => Finset.mem_toList, hcode, hact⟩
  have hD := slotListOut_mem_D H hF.slots hcmpC hbkC hfe
  have hnd : D.Nodup := hF.slots.D_sorted.imp fun h => Nat.ne_of_lt h
  -- the cells of the list of a component
  have hcell : ∀ c < comps.length, ∀ a, st₁.mem (ctH + 3 * c + 1) ≤ a →
      a < st₁.mem (ctH + 3 * c + 1) + 2 * (cslList D B c).length →
      ∃ j < D.length, D.getD j 0 / B = c ∧ (a = sH + 2 + eCap + 3 * G.m + 2 * j ∨
        a = sH + 2 + eCap + 3 * G.m + 2 * j + 1) :=
    fun c hc a h1 h2 => asmFi_csl_cell hF.slots hc h1 h2
  refine ⟨hcmp, hbkt, hct, hnc, hF.comps_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C
    show C ∈ comps ↔ C ∈ components tr.cs.G₀
    rw [hG₀]
    exact hF.comps_iff C
  · intro c hc v hv
    have hc' : c < comps.length := hc
    have hC : comps[c] ∈ components tr.cs.G₀ := by
      rw [hG₀]; exact (hF.comps_iff _).mp (List.getElem_mem hc')
    have hvc : v ∈ comps[c] := compSt_V_subset_init hI (by rw [hcsG, hG₀]) hC hv
    have hlt := hVlt v (hvV c hc' v hvc)
    refine ⟨hlt, ?_⟩
    show mem' (cmpH + v) = c
    rw [hag _ (by omega) (by omega)]
    exact hF.comps_idx c hc' v hvc
  · intro e he
    have he' : e ∈ G.E := by rw [← hG₀]; exact he
    have hlt := hElt e he'
    refine ⟨hlt, ?_⟩
    show mem' (o₁ + 16 + e) = bucketCode (tr.origBucket e)
    rw [hag _ (by omega) (by omega), hF.bkt_in e he', hbktM e he']
  · intro c hc
    have hc' : c < comps.length := hc
    obtain ⟨hlen, hpairs⟩ := slotListOut_csl hF.slots hc'
    refine ⟨?_, ?_, ?_, cslList_nodup D B c, ?_, ?_⟩
    · show mem' (ctH + 3 * c) = if comps[c] ∈ tr.activeComps then 1 else 0
      rw [hag _ (by omega) (by omega), hAC]
      exact slotListOut_flag H hF.slots rfl hcmpC c hc'
    · show mem' (ctH + 3 * c + 1) = st₁.mem (ctH + 3 * c + 1)
      exact hag _ (by omega) (by omega)
    · show mem' (ctH + 3 * c + 2) = (cslList D B c).length
      rw [hag _ (by omega) (by omega)]
      exact hlen
    · intro i hi
      have hi' : i < (cslList D B c).length := hi
      obtain ⟨p1, p2⟩ := hpairs i hi'
      obtain ⟨j1, hj1, -, ha1⟩ := hcell c hc' (st₁.mem (ctH + 3 * c + 1) + 2 * i) (by omega)
        (by omega)
      obtain ⟨j2, hj2, -, ha2⟩ := hcell c hc' (st₁.mem (ctH + 3 * c + 1) + 2 * i + 1)
        (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · show mem' (st₁.mem (ctH + 3 * c + 1) + 2 * i) = _
        rw [hag _ (by omega) (by omega)]
        exact p1
      · show mem' (st₁.mem (ctH + 3 * c + 1) + 2 * i + 1) = _
        rw [hag _ (by omega) (by omega)]
        exact p2
    · intro b t
      exact mem_cslList_iff H hnd hD hc' b t
  · rintro a ⟨i, hi⟩
    rcases i with _ | _ | _ | c
    · obtain ⟨h1, h2⟩ := hi
      change cmpH ≤ a at h1
      change a < cmpH + vCap at h2
      rw [hag a (by omega) (by omega)]
      have := hF.comps_word (a - cmpH) (by omega)
      rwa [show cmpH + (a - cmpH) = a by omega] at this
    · obtain ⟨h1, h2⟩ := hi
      change o₁ + 16 ≤ a at h1
      change a < o₁ + 16 + eCap at h2
      rw [hag a (by omega) (by omega)]
      have := hF.bkt_word (a - (o₁ + 16)) (by omega)
      rwa [show o₁ + 16 + (a - (o₁ + 16)) = a by omega] at this
    · obtain ⟨h1, h2⟩ := hi
      change ctH ≤ a at h1
      change a < ctH + 3 * comps.length at h2
      rw [hag a (by omega) (by omega)]
      have hc : (a - ctH) / 3 < comps.length := by omega
      have hseg := slotSeg_le D B ((a - ctH) / 3)
      have hseg' := slotSeg_le D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) ((a - ctH) / 3)
      have hw : 2 ≤ 2 ^ w := by omega
      have hr : (a - ctH) % 3 = 0 ∨ (a - ctH) % 3 = 1 ∨ (a - ctH) % 3 = 2 := by omega
      rcases hr with hr | hr | hr
      · rw [show a = ctH + 3 * ((a - ctH) / 3) by omega, hF.slots.flag _ hc]
        split_ifs <;> omega
      · rw [show a = ctH + 3 * ((a - ctH) / 3) + 1 by omega, hF.slots.ptr _ hc]
        split_ifs <;> omega
      · rw [show a = ctH + 3 * ((a - ctH) / 3) + 2 by omega, hF.slots.len _ hc]
        omega
    · obtain ⟨hc, h1, h2⟩ := hi
      obtain ⟨j, hj, -, ha⟩ := hcell c hc a h1 h2
      rw [hag a (by omega) (by omega)]
      rcases asmFi_csl_val hF.slots hBpos hj ha with h | h <;> omega
  · intro i j hij a hi hj
    rcases i with _ | _ | _ | c <;> rcases j with _ | _ | _ | c' <;>
      simp only [asmSdMapPart, asmFiSide] at hi hj hij ⊢
    all_goals first
      | omega
      | (obtain ⟨hc, h1, h2⟩ := hi
         obtain ⟨j₁, hj₁, -, ha₁⟩ := hcell c hc a h1 h2
         omega)
      | (obtain ⟨hc, h1, h2⟩ := hj
         obtain ⟨j₁, hj₁, -, ha₁⟩ := hcell c' hc a h1 h2
         omega)
      | (obtain ⟨hc, h1, h2⟩ := hi
         obtain ⟨hc', h1', h2'⟩ := hj
         obtain ⟨j₁, hj₁, e₁, ha₁⟩ := hcell c hc a h1 h2
         obtain ⟨j₂, hj₂, e₂, ha₂⟩ := hcell c' hc' a h1' h2'
         have hjj : j₁ = j₂ := by omega
         subst hjj
         omega)
  · rintro a ⟨i, hi⟩
    rcases i with _ | _ | _ | c <;> simp only [asmSdMapPart, asmFiSide] at hi ⊢
    · omega
    · omega
    · omega
    · obtain ⟨hc, h1, h2⟩ := hi
      obtain ⟨j₁, hj₁, -, ha₁⟩ := hcell c hc a h1 h2
      omega

end MinCostFlow.SparseCore.Program
