module

public import MinCostFlow.MinRatio.WireSelectEvalKeyDefs
import Mathlib.Tactic

/-!
# Pure mathematical bridges and framing lemmas for `evalKeyProc`

This file provides:
1. `potGradInt`: integer-scaled `potGrad C g φ k f` read from `mem` at `mloc`.
2. Modular wrap-arithmetic helpers (`wrap_add_left`, `wrap_sub_left`, `wrap_add_both`,
   `wrap_sub_both`).
3. Memory framing lemmas (`selectLevelMetaBounded_mono`, `selectLevelMetaBounded_of_agree`,
   `dynGraphAt_of_agree`, `selectLevelMetaReadAt_of_agree`, `potGradInt_congr`).
4. Exact real-value bridges (`potGradInt_cast`, `walkInner_sparsifierCycle_eq`,
   `wlenAt_eq_sum_of_edgeSimple`, `chainLen_pos_of_holds`, `wlenAt_pos_of_pos`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-- Exact integer-scaled `potGrad C g φ k f` read from `mem` at `mloc`:
at level `0` this is `intVal g0[f]`, and each level `j` adds
`intVal φ[j][head_j f] - intVal φ[j][tail_j f]`. -/
def potGradInt (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (h : ℕ) (C : TreeChain) : ℕ → ℕ → ℤ
  | 0, f => Num.intVal mem (mloc.g0Ptr + f * mloc.Lk) h mloc.Lk
  | k + 1, f =>
    potGradInt mem mloc h C k f +
      Num.intVal mem (mloc.phiPtr k + (C.G k).head f * mloc.Lk) h mloc.Lk -
      Num.intVal mem (mloc.phiPtr k + (C.G k).tail f * mloc.Lk) h mloc.Lk


end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 2. Modular wrap helpers and pure mathematical bridges -/

theorem wrap_add_left (h L : ℕ) (x y : ℤ) :
    Num.wrap h L (Num.wrap h L x + y) = Num.wrap h L (x + y) := by
  rw [add_comm, Num.wrap_add_wrap, add_comm]

theorem wrap_sub_left (h L : ℕ) (x y : ℤ) :
    Num.wrap h L (Num.wrap h L x - y) = Num.wrap h L (x - y) := by
  apply Num.wrap_congr
  rw [Int.sub_emod, Num.wrap_emod, ← Int.sub_emod]

theorem wrap_add_both (h L : ℕ) (x y : ℤ) :
    Num.wrap h L (Num.wrap h L x + Num.wrap h L y) = Num.wrap h L (x + y) := by
  apply Num.wrap_congr
  rw [Int.add_emod, Num.wrap_emod, Num.wrap_emod, ← Int.add_emod]

theorem wrap_sub_both (h L : ℕ) (x y : ℤ) :
    Num.wrap h L (Num.wrap h L x - Num.wrap h L y) = Num.wrap h L (x - y) := by
  apply Num.wrap_congr
  rw [Int.sub_emod, Num.wrap_emod, Num.wrap_emod, ← Int.sub_emod]

theorem selectLevelMetaBounded_mono {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {hi hi' : ℕ} (hb : SelectLevelMetaBounded mem mloc C hi) (hle : hi ≤ hi') :
    SelectLevelMetaBounded mem mloc C hi' := by
  obtain ⟨hm, hg0, hlev, hemb⟩ := hb
  refine ⟨le_trans hm hle, le_trans hg0 hle, fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hlev j hj
    exact ⟨le_trans h1 hle, le_trans h2 hle, le_trans h3 hle⟩
  · obtain ⟨hlo, hhi, hbody⟩ := hemb j hj
    refine ⟨hlo, le_trans hhi hle, fun e he => ?_⟩
    obtain ⟨hec, hpl, hph, hw⟩ := hbody e he
    exact ⟨hec, hpl, le_trans hph hle, hw⟩

theorem selectLevelMetaBounded_of_agree {mem mem' : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {hi : ℕ} (hb : SelectLevelMetaBounded mem mloc C hi)
    (hag : ∀ a < hi, mem' a = mem a) :
    SelectLevelMetaBounded mem' mloc C hi := by
  obtain ⟨hm, hg0, hlev, hemb⟩ := hb
  refine ⟨hm, hg0, hlev, fun j hj => MEmbAt.of_agree (hemb j hj) fun a _ ha => hag a ha⟩

theorem dynGraphAt_of_agree {mem mem' : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G)
    (hag : ∀ x, a ≤ x → x < a + dynGraphSize vCap eCap → mem' x = mem x) :
    DynGraphAt mem' a vCap eCap G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, ⟨vL, hv1, hv2, hv3, hv4, hv5⟩, h10, h11, h12,
    ⟨eL, he1, he2, he3, he4, he5⟩, h14, ⟨incL, hinc⟩⟩ := hG
  have hag' : ∀ x, a ≤ x → x < a + (4 + 7 * vCap + 9 * eCap) → mem' x = mem x := hag
  refine ⟨h1, h2, h3,
    (hag' _ (by unfold dgVCapOff; omega) (by unfold dgVCapOff; omega)).trans h4,
    (hag' _ (by unfold dgECapOff; omega) (by unfold dgECapOff; omega)).trans h5,
    (hag' _ (by unfold dgNOff; omega) (by unfold dgNOff; omega)).trans h6,
    (hag' _ (by unfold dgMOff; omega) (by unfold dgMOff; omega)).trans h7,
    fun v hv => (hag' _ (by unfold dgVPresBase; omega) (by unfold dgVPresBase; omega)).trans (h8 v hv),
    ⟨vL, hv1, hv2, hv3,
      fun i hi => by
        have hvc : vL.length ≤ vCap := by
          have : vL.toFinset ⊆ Finset.range vCap := by
            intro x hx
            rw [List.mem_toFinset, hv3] at hx
            exact Finset.mem_range.mpr (h2 x hx)
          have hcard := Finset.card_le_card this
          rw [List.toFinset_card_of_nodup hv2, Finset.card_range] at hcard
          exact hcard
        exact (hag' _ (by unfold dgVListBase; omega) (by unfold dgVListBase; omega)).trans (hv4 i hi),
      fun i hi => by
        have hvlt : vL[i] < vCap := h2 _ ((hv3 _).mp (List.getElem_mem hi))
        exact (hag' _ (by unfold dgVPosBase; omega) (by unfold dgVPosBase; omega)).trans (hv5 i hi)⟩,
    fun v hv => by
      have hvlt := h2 v hv
      have heq1 : mem' (dgExtToIntBase a vCap + v) = mem (dgExtToIntBase a vCap + v) :=
        hag' _ (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega)
      have hslt := h2 _ (h10 v hv).1
      rw [heq1]
      exact ⟨(h10 v hv).1,
        (hag' _ (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)).trans (h10 v hv).2⟩,
    fun s hs => by
      have hslt := h2 s hs
      have heq1 : mem' (dgIntToExtBase a vCap + s) = mem (dgIntToExtBase a vCap + s) :=
        hag' _ (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)
      have hvlt := h2 _ (h11 s hs).1
      rw [heq1]
      exact ⟨(h11 s hs).1,
        (hag' _ (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega)).trans (h11 s hs).2⟩,
    fun e he => (hag' _ (by unfold dgEPresBase; omega) (by unfold dgEPresBase; omega)).trans (h12 e he),
    ⟨eL, he1, he2, he3,
      fun i hi => by
        have hec : eL.length ≤ eCap := by
          have : eL.toFinset ⊆ Finset.range eCap := by
            intro x hx
            rw [List.mem_toFinset, he3] at hx
            exact Finset.mem_range.mpr (h3 x hx)
          have hcard := Finset.card_le_card this
          rw [List.toFinset_card_of_nodup he2, Finset.card_range] at hcard
          exact hcard
        exact (hag' _ (by unfold dgEListBase; omega) (by unfold dgEListBase; omega)).trans (he4 i hi),
      fun i hi => by
        have helt : eL[i] < eCap := h3 _ ((he3 _).mp (List.getElem_mem hi))
        exact (hag' _ (by unfold dgEPosBase; omega) (by unfold dgEPosBase; omega)).trans (he5 i hi)⟩,
    fun e he => by
      have helt := h3 e he
      have htV := h2 _ (h1 e he).1
      have hhV := h2 _ (h1 e he).2
      refine ⟨?_, ?_⟩
      · rw [hag' _ (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega),
            hag' _ (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega)]
        exact (h14 e he).1
      · rw [hag' _ (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega),
            hag' _ (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega)]
        exact (h14 e he).2,
    ⟨incL, fun s hs => by
      obtain ⟨hdll, hdeg, hmem⟩ := hinc s hs
      obtain ⟨hnd, hlt, hhead, hlinks⟩ := hdll
      refine ⟨⟨hnd, hlt,
        (hag' _ (by unfold dgIncHeadBase; omega) (by unfold dgIncHeadBase; omega)).trans hhead,
        fun i hi => by
          have hhi := hlt _ (List.getElem_mem hi)
          exact ⟨(hag' _ (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega)).trans (hlinks i hi).1,
                 (hag' _ (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega)).trans (hlinks i hi).2⟩⟩,
        (hag' _ (by unfold dgSlotDegBase; omega) (by unfold dgSlotDegBase; omega)).trans hdeg,
        fun h => by
          rw [hmem h]
          constructor <;> rintro ⟨h1', h2', h3'⟩ <;> refine ⟨h1', h2', ?_⟩
          · have hlt2 : h / 2 < eCap := by omega
            split_ifs at h3' ⊢
            · exact (hag' _ (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega)).trans h3'
            · exact (hag' _ (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega)).trans h3'
          · have hlt2 : h / 2 < eCap := by omega
            split_ifs at h3' ⊢
            · exact (hag' _ (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega)).symm.trans h3'
            · exact (hag' _ (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega)).symm.trans h3'⟩⟩⟩

/-- Framing for `SelectLevelMetaReadAt`: preserved across any memory agreement below `hi`
whenever `SelectLevelMetaBounded mem mloc C hi` holds. -/
theorem selectLevelMetaReadAt_of_agree {mem mem' : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P hi : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    (hm : SelectLevelMetaReadAt mem mloc h P C g φ coreLen)
    (hb : SelectLevelMetaBounded mem mloc C hi)
    (hag : ∀ a < hi, mem' a = mem a) :
    SelectLevelMetaReadAt mem' mloc h P C g φ coreLen := by
  obtain ⟨hmd, hmG0, hmD, hmTab, hg0At, hGAt, hPhiAt, hCoreAt, hEmbAt, hPLast⟩ := hm
  obtain ⟨hmb, hg0b, hlevb, hembb⟩ := hb
  have hmsz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
  refine ⟨hmd,
    (hag _ (by unfold smG0Off; omega)).trans hmG0,
    (hag _ (by unfold smDOff; omega)).trans hmD,
    fun j hj => by
      have ht := hmTab j hj
      refine ⟨(hag _ (by unfold smEntryAddr smTableOff; omega)).trans ht.1,
              (hag _ (by unfold smEntryAddr smTableOff; omega)).trans ht.2.1,
              (hag _ (by unfold smEntryAddr smTableOff; omega)).trans ht.2.2.1,
              (hag _ (by unfold smEntryAddr smTableOff; omega)).trans ht.2.2.2.1,
              (hag _ (by unfold smEntryAddr smTableOff; omega)).trans ht.2.2.2.2.1,
              (hag _ (by unfold smEntryAddr smTableOff; omega)).trans ht.2.2.2.2.2⟩,
    hg0At.congr fun f hf0 i hiL => by
      have hfcap : f < mloc.eCap 0 := (hGAt 0 (Nat.zero_le _)).2.2.1 f hf0
      have hmul : f * mloc.Lk + mloc.Lk ≤ mloc.eCap 0 * mloc.Lk := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hfcap)
      exact hag _ (by omega),
    fun j hj => dynGraphAt_of_agree (hGAt j hj) fun x _ hx => hag x (by have := (hlevb j hj).1; omega),
    fun j hj => (hPhiAt j hj).congr fun v hv i hiL => by
      have hvcap : v < mloc.vCap j := (hGAt j hj).2.1 v hv
      have hmul : v * mloc.Lk + mloc.Lk ≤ mloc.vCap j * mloc.Lk := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hvcap)
      have := (hlevb j hj).2.1
      exact hag _ (by omega),
    fun j hj => (hCoreAt j hj).congr fun f hfj i hiL => by
      have hfcap : f < mloc.eCap j := (hGAt j hj).2.2.1 f hfj
      have hmul : f * mloc.Lk + mloc.Lk ≤ mloc.eCap j * mloc.Lk := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hfcap)
      have := (hlevb j hj).2.2
      exact hag _ (by omega),
    fun j hj => (MEmbAt.of_agree (hembb j hj) fun a _ ha => hag a ha).to_MEmbAt,
    (hag _ (by unfold smEntryAddr smTableOff; omega)).trans hPLast⟩

/-- `potGradInt` agrees across memories matching below `hi`. -/
theorem potGradInt_congr {mem mem' : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {h P hi : ℕ}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hm : SelectLevelMetaReadAt mem mloc h P C g φ coreLen)
    (hb : SelectLevelMetaBounded mem mloc C hi)
    (hag : ∀ a < hi, mem' a = mem a)
    {lvl k f : ℕ} (hlvl : lvl ≤ C.d) (hk : k ≤ lvl + 1) (hf : f ∈ (C.G lvl).E) :
    potGradInt mem' mloc h C k f = potGradInt mem mloc h C k f := by
  induction k with
  | zero =>
    unfold potGradInt
    apply Num.intVal_congr
    intro i hiL
    have hf0 : f ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le lvl) hlvl hf
    have hfcap : f < mloc.eCap 0 := (hm.2.2.2.2.2.1 0 (Nat.zero_le _)).2.2.1 f hf0
    have hmul : f * mloc.Lk + mloc.Lk ≤ mloc.eCap 0 * mloc.Lk := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hfcap)
    exact hag _ (by have := hb.2.1; omega)
  | succ j ih =>
    unfold potGradInt
    rw [ih (Nat.le_of_lt hk)]
    have hjlvl : j ≤ lvl := Nat.le_of_succ_le_succ hk
    have hjd : j ≤ C.d := le_trans hjlvl hlvl
    have hfj : f ∈ (C.G j).E := C.G_E_subset_of_le hH hjlvl hlvl hf
    have hval := C.G_isValid hH j hjd f hfj
    have hGAt := hm.2.2.2.2.2.1 j hjd
    have hphib := (hb.2.2.1 j hjd).2.1
    have hhead : Num.intVal mem' (mloc.phiPtr j + (C.G j).head f * mloc.Lk) h mloc.Lk =
        Num.intVal mem (mloc.phiPtr j + (C.G j).head f * mloc.Lk) h mloc.Lk := by
      apply Num.intVal_congr; intro i hiL
      have hlt : (C.G j).head f < mloc.vCap j := hGAt.2.1 _ hval.2
      have hmul : (C.G j).head f * mloc.Lk + mloc.Lk ≤ mloc.vCap j * mloc.Lk := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hlt)
      exact hag _ (by omega)
    have htail : Num.intVal mem' (mloc.phiPtr j + (C.G j).tail f * mloc.Lk) h mloc.Lk =
        Num.intVal mem (mloc.phiPtr j + (C.G j).tail f * mloc.Lk) h mloc.Lk := by
      apply Num.intVal_congr; intro i hiL
      have hlt : (C.G j).tail f < mloc.vCap j := hGAt.2.1 _ hval.1
      have hmul : (C.G j).tail f * mloc.Lk + mloc.Lk ≤ mloc.vCap j * mloc.Lk := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right mloc.Lk (Nat.succ_le_of_lt hlt)
      exact hag _ (by omega)
    rw [hhead, htail]

/-- Scaling `potGradInt mem mloc h C k f` by `2 ^ (-P)` recovers the exact real `potGrad C g φ k f`. -/
theorem potGradInt_cast {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {h P : ℕ}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hm : SelectLevelMetaReadAt mem mloc h P C g φ coreLen)
    {lvl k f : ℕ} (hlvl : lvl ≤ C.d) (hk : k ≤ lvl + 1) (hf : f ∈ (C.G lvl).E) :
    ((potGradInt mem mloc h C k f : ℤ) : ℝ) / (2 : ℝ) ^ P = potGrad C g φ k f := by
  induction k with
  | zero =>
    unfold potGradInt potGrad
    have hf0 : f ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le lvl) hlvl hf
    exact (hm.2.2.2.2.1 f hf0).2
  | succ j ih =>
    unfold potGradInt potGrad
    have hjlvl : j ≤ lvl := Nat.le_of_succ_le_succ hk
    have hjd : j ≤ C.d := le_trans hjlvl hlvl
    have hfj : f ∈ (C.G j).E := C.G_E_subset_of_le hH hjlvl hlvl hf
    have hval := C.G_isValid hH j hjd f hfj
    have hphi := hm.2.2.2.2.2.2.1 j hjd
    have hhead : ((Num.intVal mem (mloc.phiPtr j + (C.G j).head f * mloc.Lk) h mloc.Lk : ℤ) : ℝ) /
        (2 : ℝ) ^ P = φ j ((C.G j).head f) := (hphi _ hval.2).2
    have htail : ((Num.intVal mem (mloc.phiPtr j + (C.G j).tail f * mloc.Lk) h mloc.Lk : ℤ) : ℝ) /
        (2 : ℝ) ^ P = φ j ((C.G j).tail f) := (hphi _ hval.1).2
    rw [Int.cast_sub, Int.cast_add, sub_div, add_div, ih (Nat.le_of_lt hk), hhead, htail]

/-- Exact signed-sum expansion of `walkInner F (C.sparsifierCycle lvl e)`. -/
theorem walkInner_sparsifierCycle_eq (C : TreeChain) (F : ℕ → ℝ) (lvl e : ℕ) :
    walkInner F (C.sparsifierCycle lvl e) =
      F e + ((C.activeEmb lvl e).map fun x => if x.2 then -F x.1 else F x.1).sum := by
  unfold TreeChain.sparsifierCycle
  rw [walkInner_cons, walkInner_singleton]
  simp only [↓reduceIte]
  congr 1
  rw [walkInner_walkRev]
  have haux : ∀ (P : List (ℕ × Bool)),
      -walkInner F P = (P.map fun x => if x.2 then -F x.1 else F x.1).sum := by
    intro P
    induction P with
    | nil => simp [walkInner_nil]
    | cons x xs ih =>
      rw [walkInner_cons, walkInner_singleton, neg_add, ih]
      cases hx : x.2 <;> simp [hx]
  exact haux (C.activeEmb lvl e)

/-- `C.wlenAt ℓ lvl e` equals `C.chainLen ℓ (lvl + 1) e` plus the sum of
`C.chainLen ℓ (lvl + 1) x.1` over all steps `x` of `C.activeEmb lvl e` (unconditionally,
without `EdgeSimpleEmbeddings`). -/
theorem wlenAt_eq_sum_of_edgeSimple {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (_hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    {lvl e : ℕ} (_hlvl : lvl ≤ C.d) (_he : e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E) :
    C.wlenAt ℓ lvl e =
      C.chainLen ℓ (lvl + 1) e +
        ((C.activeEmb lvl e).map fun x => C.chainLen ℓ (lvl + 1) x.1).sum := by
  unfold TreeChain.wlenAt TreeChain.sparsifierCycle
  simp only [List.map_cons, List.sum_cons]
  congr 1
  have hrev : (walkRev (C.activeEmb lvl e)).map (fun x => C.chainLen ℓ (lvl + 1) x.1) =
      ((C.activeEmb lvl e).map (fun x => C.chainLen ℓ (lvl + 1) x.1)).reverse := by
    unfold walkRev; rw [List.map_reverse, List.map_map]; rfl
  rw [hrev, List.sum_reverse]

/-- Under `C.Holds` and positive base lengths `ℓ > 0` on `G_0`, every `C.chainLen ℓ j` (`j ≤ d`)
and `C.chainLen ℓ (j + 1)` is strictly positive on `(C.G j).E`. -/
theorem chainLen_pos_of_holds {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hℓPos : ∀ f ∈ (C.G 0).E, 0 < ℓ f) :
    ∀ j ≤ C.d,
      (∀ f ∈ (C.G j).E, 0 < C.chainLen ℓ j f) ∧
      (∀ f ∈ (C.G j).E, 0 < C.chainLen ℓ (j + 1) f) := by
  have hstep : ∀ j ≤ C.d, (∀ f ∈ (C.G j).E, 0 < C.chainLen ℓ j f) →
      ∀ f ∈ (C.G j).E, 0 < C.chainLen ℓ (j + 1) f := by
    intro j hj hpos f hf
    have hL := C.activeLSF_holds hH hj
    have hwstr := (hL.2.2.2 f hf).1
    have hFsub := hL.2.1.2.2.2.2
    have hwlNonneg : ∀ W : List (ℕ × Bool), (∀ x ∈ W, x.1 ∈ (C.activeLSF j).F.F.E) →
        0 ≤ walkLength (C.chainLen ℓ j) W := by
      intro W hW
      unfold walkLength
      refine Finset.sum_nonneg fun e he => mul_nonneg ?_ (abs_nonneg _)
      unfold walkEdges at he
      rw [List.mem_toFinset, List.mem_map] at he
      obtain ⟨x, hx, rfl⟩ := he
      exact le_of_lt (hpos x.1 (hFsub.2.1 (hW x hx)))
    have hfpEdges : ∀ a b, ∀ x ∈ (C.activeLSF j).F.F.forestPath a b, x.1 ∈ (C.activeLSF j).F.F.E := by
      intro a b x hx
      have hmem : x.1 ∈ walkEdges ((C.activeLSF j).F.F.forestPath a b) := by
        unfold walkEdges; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
      exact forestPath_edges_subset a b hmem
    have hstrGe1 : 1 ≤ (C.activeLSF j).F.stretch (C.G j) (C.chainLen ℓ j) f := by
      unfold RootedForest.stretch
      dsimp only
      split_ifs
      · have h1 := hwlNonneg _ (hfpEdges ((C.G j).tail f) ((C.G j).head f))
        have h2 := div_nonneg h1 (le_of_lt (hpos f hf))
        linarith
      · have h1 := hwlNonneg _ (hfpEdges ((C.G j).tail f) ((C.activeLSF j).F.root ((C.G j).tail f)))
        have h2 := hwlNonneg _ (hfpEdges ((C.G j).head f) ((C.activeLSF j).F.root ((C.G j).head f)))
        have h3 := div_nonneg (add_nonneg h1 h2) (le_of_lt (hpos f hf))
        linarith
    have hwPos : 0 < (C.activeLSF j).wstr f := by linarith
    change 0 < (C.activeLSF j).wstr f * C.chainLen ℓ j f
    exact mul_pos hwPos (hpos f hf)
  intro j
  induction j with
  | zero =>
    intro h0
    exact ⟨hℓPos, hstep 0 h0 hℓPos⟩
  | succ k ih =>
    intro hk
    have hklt : k < C.d := hk
    have ih' := ih (Nat.le_of_lt hklt)
    have hcur : ∀ f ∈ (C.G (k + 1)).E, 0 < C.chainLen ℓ (k + 1) f := fun f hf =>
      ih'.2 f (Finset.mem_sdiff.mp (C.G_succ_E_subset hH hklt hf)).1
    exact ⟨hcur, hstep (k + 1) hk hcur⟩

/-- Under `C.Holds` and `ℓ > 0` on `G_0`, `C.wlenAt ℓ lvl e` is strictly positive for every
candidate edge `e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E` (unconditionally, without
`EdgeSimpleEmbeddings`). -/
theorem wlenAt_pos_of_pos {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hℓPos : ∀ f ∈ (C.G 0).E, 0 < ℓ f)
    {lvl e : ℕ} (hlvl : lvl ≤ C.d) (he : e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E) :
    0 < C.wlenAt ℓ lvl e := by
  rw [wlenAt_eq_sum_of_edgeSimple hH hlvl he]
  have hpos := (chainLen_pos_of_holds hH hℓPos lvl hlvl).2
  have heG : e ∈ (C.G lvl).E := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
  have h1 : 0 < C.chainLen ℓ (lvl + 1) e := hpos e heG
  have h2 : 0 ≤ ((C.activeEmb lvl e).map fun x => C.chainLen ℓ (lvl + 1) x.1).sum := by
    apply List.sum_nonneg
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    by_cases hlt : lvl < C.d
    · have hSp := C.activeS_isSparsified hH hlt
      have hxS : x.1 ∈ (C.activeS lvl).E :=
        MGraph.isWalk_edges_mem (hSp.2.1.2 e (Finset.mem_sdiff.mp he).1) x hx
      have hxCore : x.1 ∈ (C.activeCore lvl).E := hSp.1.2.1 hxS
      exact le_of_lt (hpos x.1 (Finset.mem_sdiff.mp hxCore).1)
    · have hieq : lvl = C.d := Nat.le_antisymm hlvl (Nat.le_of_not_lt hlt)
      simp [TreeChain.activeEmb, hieq] at hx
  linarith


end MinCostFlow.MinRatio
