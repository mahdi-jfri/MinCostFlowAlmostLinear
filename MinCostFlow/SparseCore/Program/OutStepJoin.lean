module

public import MinCostFlow.SparseCore.Program.OutStepJoinBack
public import MinCostFlow.SparseCore.Program.OutStepJoinModel

/-!
# The six phases of the output step, joined

The lemma `osStep_runs` runs the whole body `outStepBody` from its start state. It joins
`osFront_runs` (setup, deletions, splits) and `osBack_runs` (insertions, rotations, the four
words). It is stated for any lists of leaving edges, splits and entering edges that meet the
facts the phases ask for, so it still does not mention the model. The next file gives these
lists from the model of a step.

The start frame comes from the pre of the step: the tour and the stored graph lie below `h`,
memory is zero from `h` on, and the batch and edit regions are empty. The regions have size
`R = 16 (vCap + 1) (eCap + 1)`, which leaves room for every record (`osRoom_R`), and the tour
grows from `h + 4 + 2 R` on, which stays below `h + outStepSpace` (`osRoom_space`). The cost of
the six phases is at most `5000 (mul + 1) n log` (`osCost_le`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-! ## Arithmetic -/

/-- The batch and edit regions have room for all records. -/
theorem osRoom_R {vCap eCap d pl Ep i t : ℕ} (hd : d ≤ eCap) (hp : pl ≤ vCap)
    (hE : Ep ≤ pl * (2 * eCap + 1)) (hi : i ≤ eCap) (ht : t ≤ vCap) :
    2 * d + 4 * pl + Ep + 8 * i + 3 * t + 4 * eCap + 6 ≤ (vCap + 1) * (eCap + 1) * 16 := by
  have h1 : pl * (2 * eCap + 1) ≤ vCap * (2 * eCap + 1) := Nat.mul_le_mul_right _ hp
  have h2 : vCap * (2 * eCap + 1) = 2 * (vCap * eCap) + vCap := by ring
  have h3 : (vCap + 1) * (eCap + 1) * 16 = 16 * (vCap * eCap) + 16 * vCap + 16 * eCap + 16 := by
    ring
  omega

/-- The tour stays below `h + outStepSpace`. -/
theorem osRoom_space {vCap eCap d i t q : ℕ} (hd : d ≤ eCap) (hi : i ≤ eCap) (ht : t ≤ vCap) :
    4 + (vCap + 1) * (eCap + 1) * 16 + (vCap + 1) * (eCap + 1) * 16 + 2 * d * q +
      (4 * i + t) * q ≤ 1000 * (vCap + 1) * (eCap + 1) * (q + 1) := by
  have hX : vCap + eCap + 1 ≤ (vCap + 1) * (eCap + 1) := by
    have : (vCap + 1) * (eCap + 1) = vCap * eCap + vCap + eCap + 1 := by ring
    omega
  have h1 : 2 * d * q + (4 * i + t) * q = (2 * d + 4 * i + t) * q := by ring
  have h2 : (2 * d + 4 * i + t) * q ≤ (7 * ((vCap + 1) * (eCap + 1))) * q :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : 1000 * (vCap + 1) * (eCap + 1) * (q + 1) =
      1000 * ((vCap + 1) * (eCap + 1) * q) + 1000 * ((vCap + 1) * (eCap + 1)) := by ring
  have h4 : (7 * ((vCap + 1) * (eCap + 1))) * q = 7 * ((vCap + 1) * (eCap + 1) * q) := by ring
  omega

/-- The counts of updates fit in a word. -/
theorem osRoom_word {w vCap eCap d pl i : ℕ} (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hd : d ≤ eCap) (hp : pl ≤ vCap) (hi : i ≤ eCap) : d + pl + i < 2 ^ w := by
  have h1 : (vCap + eCap + 2) * 2 ≤ (vCap + eCap + 2) * (vCap + eCap + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [sq] at hw
  omega

/-- The cost of the six phases. -/
theorem osCost_le {M l d Ep i Y t : ℕ} (hl : 1 ≤ l) :
    d * (2 * (M * l) + 1700) + 2000 * Y + 5000 * Ep + i * (4 * (M * l) + 3100) +
      t * (M * l + 110) + 335 ≤ 5000 * (M + 1) * (d + Ep + i + Y + t + 1) * l := by
  have hK : 5000 * (M + 1) * (d + Ep + i + Y + t + 1) * l =
      5000 * ((M + 1) * l) * (d + Ep + i + Y + t + 1) := by ring
  have hK1 : 1 ≤ (M + 1) * l := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hMl : M * l ≤ (M + 1) * l := Nat.mul_le_mul_right _ (by omega)
  rw [hK]
  generalize (M + 1) * l = K at hK1 hMl ⊢
  generalize M * l = X at hMl ⊢
  have h1 : d * (2 * X + 1700) ≤ d * (1702 * K) := Nat.mul_le_mul_left _ (by omega)
  have h2 : i * (4 * X + 3100) ≤ i * (3104 * K) := Nat.mul_le_mul_left _ (by omega)
  have h3 : t * (X + 110) ≤ t * (111 * K) := Nat.mul_le_mul_left _ (by omega)
  have h4 : Y ≤ Y * K := Nat.le_mul_of_pos_right _ hK1
  have h5 : Ep ≤ Ep * K := Nat.le_mul_of_pos_right _ hK1
  have h6 : 5000 * K * (d + Ep + i + Y + t + 1) =
      5000 * (d * K) + 5000 * (Ep * K) + 5000 * (i * K) + 5000 * (Y * K) + 5000 * (t * K) +
        5000 * K := by ring
  have h7 : d * (1702 * K) = 1702 * (d * K) := by ring
  have h8 : i * (3104 * K) = 3104 * (i * K) := by ring
  have h9 : t * (111 * K) = 111 * (t * K) := by ring
  have z1 : 0 ≤ d * K := Nat.zero_le _
  have z2 : 0 ≤ i * K := Nat.zero_le _
  have z3 : 0 ≤ t * K := Nat.zero_le _
  have z4 : 0 ≤ Y * K := Nat.zero_le _
  have z5 : 0 ≤ Ep * K := Nat.zero_le _
  linarith

/-- The words of the batch record. -/
theorem osWords_batch {a d p E i : ℕ} (hp : p ≤ E) :
    a + 5 + 2 * d + (4 * p + E) + 4 * i - (a + 5) ≤ 5 * (d + E + i) := by omega

/-- The words of the edit record. -/
theorem osWords_edits {a d p E i r : ℕ} (hp : p ≤ E) :
    a + 1 + 2 * d + (3 * p + E) + 8 * i + 3 * r - (a + 1) ≤ 5 * (d + E + 2 * i + r) := by
  omega

/-! ## The join -/

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm}

/-- **The body of the output step runs.** The lists `delL`, `P` and `insL` are any leaving
edges, splits and entering edges with the facts that the phases ask for. Afterwards the stored
graph is the old one after the deletions, the splits and the insertions; the four words at `h`
point to the batch record and to the edit record; the edits are those of the deletions, of the
splits, of the insertions (with the places from the tour) and of the rotations; and the cost is
at most `5000 (mul + 1) n log`. -/
theorem osStep_runs (A : OSArgs) {au gd flt wk : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    (hgd : ∀ G, MeetsContract w p gd (dgGetDegContract w vCap eCap G))
    (hflt : p.procs[flt]? = some outFilterBody) (hwk : p.procs[wk]? = some outWalkBody)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (hRdef : A.R = (vCap + 1) * (eCap + 1) * 16)
    {pos : ℕ} {s : OutTourAbs} {tx : T.rep.τ}
    {mem : ℕ → ℕ} {S₀ : MGraph} {cord : ℕ → List End} {E' E₀ keep : Finset ℕ}
    {delL insL T₀ : List ℕ} {P : List Update} {Ys : List (List End)} {tl hd : ℕ → ℕ}
    (hrepG : (outGraphRep vCap eCap).rep A.outH S₀ A.g mem) (hrepT : T.rep.rep A.tourH s tx mem)
    (hmk : OutMarksOf s cord E₀) (hE₀ : keep ⊆ E₀ ∧ E₀ ⊆ S₀.E)
    (hargs : ∀ a ∈ [A.outH, A.tourH, A.delPtr, A.splitPtr, A.insPtr, A.rotPtr, A.h], a < 2 ^ w)
    (hfootG : ∀ a, (outGraphRep vCap eCap).foot A.outH A.g a → a < A.h)
    (hfootT : ∀ a, T.rep.foot A.tourH tx a → a < A.h)
    (hdisj : ∀ a, (outGraphRep vCap eCap).foot A.outH A.g a → ¬ T.rep.foot A.tourH tx a)
    (hz : ZeroFrom mem A.h) (hspace : A.h + outStepSpace S vCap eCap < 2 ^ w)
    (hdel : OutDelAt mem A.delPtr delL E')
    (hdfree : OutCellsFree A.delPtr (1 + 2 * delL.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx a))
    (hdnd : delL.Nodup) (hdsub : ∀ e ∈ delL, e ∈ S₀.E)
    (hflag1 : ∀ e ∈ delL, e ∈ E' → ∀ b, ∃ v < vCap, (e, b) ∈ cord v)
    (hflag0 : ∀ e ∈ delL, e ∉ E' → ∀ b v, (e, b) ∉ cord v)
    (hkeep : S₀.E \ delL.toFinset = keep)
    (hsl : OutSplitListsAt mem A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx a)
      keep S₀.E A.splitPtr (S₀.applyBatch (delL.map Update.delete)) P Ys)
    (hGv : (S₀.applyBatch (delL.map Update.delete)).IsValid)
    (hbv : (S₀.applyBatch (delL.map Update.delete)).BatchIsValid P)
    (hsplit : ∀ u ∈ P, ∃ v v' St Sh, u = .split v v' St Sh)
    (hcap : ∀ u ∈ P, UpdateWithinCaps vCap eCap u) (hpl : P.length ≤ vCap)
    (hEp : (S₀.applyBatch (delL.map Update.delete)).batchEnc P ≤ P.length * (2 * eCap + 1))
    (hins : OutInsAt mem A.insPtr insL tl hd)
    (hifree : OutCellsFree A.insPtr (1 + 3 * insL.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx a))
    (hind : insL.Nodup)
    (hival : ∀ j (hj : j < insL.length),
      (((S₀.applyBatch (delL.map Update.delete)).applyBatch P).applyBatch
        ((insL.take j).map fun e => Update.insert e (tl e) (hd e))).UpdateIsValid
        (.insert insL[j] (tl insL[j]) (hd insL[j])))
    (hicap : ∀ e ∈ insL, e < eCap) (hends : ∀ e ∈ insL, tl e < vCap ∧ hd e < vCap)
    (hcord : ∀ e ∈ insL, (e, true) ∈ cord (tl e) ∧ (e, false) ∈ cord (hd e))
    (hcnt : mem A.rotPtr = T₀.length) (hT : ListAt mem (A.rotPtr + 1) T₀)
    (hrfree : OutCellsFree A.rotPtr (1 + T₀.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx a))
    (hTnd : T₀.Nodup) (hTv : ∀ v ∈ T₀, v < vCap) :
    ∃ o st' c tx' s₂,
      Runs w p ω (outStepBody nm sm fm au gd flt wk)
        (startState [A.outH, A.tourH, A.delPtr, A.splitPtr, A.insPtr, A.rotPtr, A.h] mem pos)
        o st' c ∧
      (outGraphRep vCap eCap).rep A.outH
        (((S₀.applyBatch (delL.map Update.delete)).applyBatch P).applyBatch
          (insL.map fun e => Update.insert e (tl e) (hd e))) A.g st'.mem ∧
      T.rep.rep A.tourH (insTourAfter s₂ insL) tx' st'.mem ∧ OutMarksOf s₂ cord keep ∧
      SmallBatchAt st'.mem (st'.mem A.h) S₀
        ((delL.map Update.delete ++ P) ++ insL.map fun e => Update.insert e (tl e) (hd e))
        (st'.mem (A.h + 1)) ∧
      OrdEditsAt st'.mem (st'.mem (A.h + 2))
        (delL.map OrdEdit.dropEdge ++ outPrefixEditsOn (S₀.applyBatch (delL.map Update.delete)) P ++
          insEditsTour tl hd s₂ insL ++ outRotateEdits (insTourAfter s₂ insL).markedList T₀)
        (st'.mem (A.h + 3)) ∧
      EditsTagsLe4 st'.mem
        (delL.map OrdEdit.dropEdge ++ outPrefixEditsOn (S₀.applyBatch (delL.map Update.delete)) P ++
          insEditsTour tl hd s₂ insL ++ outRotateEdits (insTourAfter s₂ insL).markedList T₀).length
        (st'.mem (A.h + 2) + 1) ∧
      A.h + 4 ≤ st'.mem A.h ∧ st'.mem A.h + st'.mem (A.h + 1) ≤ st'.mem (A.h + 2) ∧
      st'.mem (A.h + 2) + st'.mem (A.h + 3) ≤ o.value ∧
      o.value ≤ A.h + outStepSpace S vCap eCap ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < A.h, ¬ (outGraphRep vCap eCap).foot A.outH A.g a → ¬ T.rep.foot A.tourH tx a →
        st'.mem a = mem a) ∧
      (∀ a, T.rep.foot A.tourH tx' a →
        T.rep.foot A.tourH tx a ∨ (st'.mem (A.h + 2) + st'.mem (A.h + 3) ≤ a ∧ a < o.value)) ∧
      c + T.rep.phi A.tourH tx' st'.mem ≤
        5000 * (S.mul + 1) * (delL.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P +
          insL.length + (Ys.map List.length).sum + T₀.length + 1) * ordStoreLog eCap +
          T.rep.phi A.tourH tx mem := by
  have he0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0 : A.t0 = A.h + 4 + A.R + A.R := rfl
  have hRpos : 16 ≤ A.R := by
    rw [hRdef]
    have := Nat.mul_le_mul (show 1 ≤ vCap + 1 by omega) (show 1 ≤ eCap + 1 by omega)
    omega
  have hspace' : outStepSpace S vCap eCap =
      1000 * (vCap + 1) * (eCap + 1) * (S.querySpace + 1) := rfl
  -- counts and room
  have hS₀cap : ∀ e ∈ S₀.E, e < eCap := hrepG.2.2.2.2.1
  have hdl : delL.length ≤ eCap := nodup_length_le_of_lt hdnd fun e he => hS₀cap e (hdsub e he)
  have hil : insL.length ≤ eCap := nodup_length_le_of_lt hind hicap
  have htl : T₀.length ≤ vCap := nodup_length_le_of_lt hTnd hTv
  have hpE : P.length ≤ (S₀.applyBatch (delL.map Update.delete)).batchEnc P :=
    outLength_le_batchEnc _ P
  have hroomR := osRoom_R hdl hpl hEp hil htl
  have hroomS := osRoom_space (q := S.querySpace) hdl hil htl
  have hword := osRoom_word hw hdl hpl hil
  -- the start
  have hC : SCtx T A tx := by
    have hdgs : 4 ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    have hlast := hfootG (A.g + dynGraphSize vCap eCap - 1) (Or.inr ⟨by omega, by omega⟩)
    exact ⟨hfootT, hfootG A.outH (Or.inl rfl), by omega, hdisj, hrepG.2.1⟩
  have hB₀ : SBase T A tx mem S₀ S₀ [] [] (A.h + 5) (A.e0 + 1) A.t0 s tx
      (startState [A.outH, A.tourH, A.delPtr, A.splitPtr, A.insPtr, A.rotPtr, A.h] mem pos).mem := by
    refine ⟨hrepT, hz.mono (by omega), le_refl _, fun a ha => Or.inl ha, fun a _ _ _ => rfl,
      hrepG.1, hrepG.2.2, le_refl _, by omega, ?_, le_refl _, by omega, ?_⟩
    · show BatchBodyAt mem (A.h + 5) S₀ [] (A.h + 5 - (A.h + 5))
      exact Nat.sub_self _
    · show EditsBody mem (A.e0 + 1) [] (A.e0 + 1 - (A.e0 + 1))
      rw [Nat.sub_self]; exact editsBody_nil _ _
  have htour : A.tourH < 2 ^ w := hargs A.tourH (by simp)
  have ht0w : A.t0 < 2 ^ w := by omega
  -- the first three phases
  obtain ⟨st₁, c₁, st₂, c₂, st₃, c₃, s₂, tx₃, hr₁, hr₂, hr₃, hB₃, hmk₃, hR₃, h14₃, h16₃,
      h17₃, h18₃, hc3a, hc3b, hc₃⟩ :=
    osFront_runs (sm := sm) (ω := ω) (mem₀ := mem) (st :=
      startState [A.outH, A.tourH, A.delPtr, A.splitPtr, A.insPtr, A.rotPtr, A.h] mem pos) hC hau
      hgd hflt hwk hw hRdef ht0w htour rfl rfl rfl rfl rfl rfl rfl hB₀ hmk hE₀ hS₀cap hdel hdfree hdnd
      hdsub hflag1 hflag0 hkeep hsl hGv hbv hcap (by omega) (by omega) (by omega)
  -- the last three phases
  have hNI : ∀ u ∈ P, Update.NotInsert u := by
    intro u hu
    obtain ⟨v, v', St, Sh, rfl⟩ := hsplit u hu
    trivial
  have hE₀len : (delL.map OrdEdit.dropEdge ++
      outPrefixEditsOn (S₀.applyBatch (delL.map Update.delete)) P).length =
      delL.length + P.length := by
    rw [List.length_append, List.length_map, length_outPrefixEditsOn P _ hNI]
  have hkcap : ∀ e ∈ keep, e < eCap := by
    intro e he
    rw [← hkeep] at he
    exact hS₀cap e (Finset.mem_sdiff.mp he).1
  obtain ⟨st₄, c₄, st₅, c₅, st₆, c₆, tx₆, hr₄, hr₅, hr₆, hB₆, -, hm0, hm1, hm2, hm3, hm4,
      hme, hc6a, hc6b, hc₆⟩ :=
    osBack_runs (nm := nm) (fm := fm) (ω := ω) hC hau hw hRdef ht0w htour hB₃ hR₃ h14₃ h16₃
      (by rw [h17₃, List.length_append, List.length_map]) (by rw [h18₃, hE₀len]) hmk₃ hkcap
      (applyBatch_append S₀ _ _).symm hins hifree hival hicap hends hcord hcnt hT hrfree hTv
      (by omega) (by omega) (by omega) (by rw [List.length_append, List.length_map]; omega)
  -- the edits and the batch
  have hrle : (outRotateEdits (insTourAfter s₂ insL).markedList T₀).length ≤ T₀.length :=
    outRotateEdits_length_le _ _
  have hlenE : (delL.map OrdEdit.dropEdge ++
      outPrefixEditsOn (S₀.applyBatch (delL.map Update.delete)) P ++
      insEditsTour tl hd s₂ insL ++ outRotateEdits (insTourAfter s₂ insL).markedList T₀).length =
      delL.length + P.length + 2 * insL.length +
        (outRotateEdits (insTourAfter s₂ insL).markedList T₀).length := by
    rw [List.length_append, List.length_append, hE₀len, insEditsTour_length]
  have hlenB : ((delL.map Update.delete ++ P) ++
      insL.map fun e => Update.insert e (tl e) (hd e)).length =
      delL.length + P.length + insL.length := by
    simp only [List.length_append, List.length_map]
  obtain ⟨hrep₆, hz₆, -, hft₆, hfr₆, hout₆, hG₆, -, -, hU₆, -, -, hE₆⟩ := hB₆
  have hc1 : c₁ + c₂ + c₃ + T.rep.phi A.tourH tx₃ st₃.mem ≤
      delL.length * (2 * (S.mul * ordStoreLog eCap) + 1700) +
        2000 * (Ys.map List.length).sum +
        5000 * (S₀.applyBatch (delL.map Update.delete)).batchEnc P + 230 +
        T.rep.phi A.tourH tx mem := hc₃
  refine ⟨.returned (st₅.regs 7), st₆, c₁ + (c₂ + (c₃ + (c₄ + (c₅ + c₆ + 1) + 1) + 1) + 1) + 1,
    tx₆, s₂, runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃
      (runs_seq_normal hr₄ (runs_seq_normal hr₅ hr₆)))),
    ⟨hout₆, hrepG.2.1, hG₆⟩, hrep₆, hmk₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 =>
      hfr₆ a ha h1 h2, ?_, ?_⟩
  · -- the batch record
    have h1 : 1 + (A.h + 5 + 2 * delL.length +
        (4 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) +
        4 * insL.length - (A.h + 5)) = A.h + 5 + 2 * delL.length +
        (4 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) +
        4 * insL.length - (A.h + 4) := by clear hlenE hlenB hE₀len hrle; omega
    have hc : st₆.mem (A.h + 4) = ((delL.map Update.delete ++ P) ++
        insL.map fun e => Update.insert e (tl e) (hd e)).length := by
      rw [hm4, hlenB, List.length_append, List.length_map]
    have hU' : BatchBodyAt st₆.mem (A.h + 4 + 1) S₀ ((delL.map Update.delete ++ P) ++
        insL.map fun e => Update.insert e (tl e) (hd e)) (A.h + 5 + 2 * delL.length +
        (4 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) +
        4 * insL.length - (A.h + 5)) := by
      rw [show A.h + 4 + 1 = A.h + 5 by omega]; exact hU₆
    have hwd : A.h + 5 + 2 * delL.length +
        (4 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) +
        4 * insL.length - (A.h + 5) ≤ 5 * S₀.batchEnc ((delL.map Update.delete ++ P) ++
          insL.map fun e => Update.insert e (tl e) (hd e)) :=
      (osWords_batch hpE).trans_eq (congrArg (HMul.hMul 5) (by
        rw [outBatchEnc_append, outBatchEnc_append, batchEnc_dels, batchEnc_inserts]))
    have hb := smallBatchAt_of_body hc hU' hwd
    rw [hm0, hm1]
    rw [h1] at hb
    exact hb
  · -- the edit record
    have h1 : 1 + (A.e0 + 1 + 2 * delL.length +
        (3 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) +
        8 * insL.length + 3 * (outRotateEdits (insTourAfter s₂ insL).markedList T₀).length -
          (A.e0 + 1)) = A.e0 + 1 + 2 * delL.length +
        (3 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) +
        8 * insL.length + 3 * (outRotateEdits (insTourAfter s₂ insL).markedList T₀).length -
          A.e0 := by omega
    have hc : st₆.mem A.e0 = (delL.map OrdEdit.dropEdge ++
        outPrefixEditsOn (S₀.applyBatch (delL.map Update.delete)) P ++
        insEditsTour tl hd s₂ insL ++ outRotateEdits (insTourAfter s₂ insL).markedList T₀).length := by
      rw [hme, hlenE, hE₀len]
    have hwd : A.e0 + 1 + 2 * delL.length +
        (3 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) +
        8 * insL.length + 3 * (outRotateEdits (insTourAfter s₂ insL).markedList T₀).length -
          (A.e0 + 1) ≤ 5 * ordEditsEnc (delL.map OrdEdit.dropEdge ++
        outPrefixEditsOn (S₀.applyBatch (delL.map Update.delete)) P ++
        insEditsTour tl hd s₂ insL ++ outRotateEdits (insTourAfter s₂ insL).markedList T₀) :=
      (osWords_edits hpE).trans_eq (congrArg (HMul.hMul 5) (by
        rw [ordEditsEnc_append, ordEditsEnc_append, ordEditsEnc_append, ordEditsEnc_dropEdges,
          ordEditsEnc_outPrefixEditsOn_eq P _ hGv hbv hsplit, ordEditsEnc_insEditsTour,
          ordEditsEnc_outRotateEdits]))
    have hb := ordEditsAt_of_body hc hE₆ hwd
    rw [hm2, hm3]
    rw [h1] at hb
    exact hb
  · rw [hm2]; exact hE₆.2.2
  · rw [hm0]
  · rw [hm0, hm1, hm2]; clear hlenE hlenB hE₀len; omega
  · rw [hm2, hm3]; dsimp only [Outcome.value]; clear hlenE hlenB hE₀len; omega
  · dsimp only [Outcome.value]; clear hlenE hlenB hE₀len; omega
  · dsimp only [Outcome.value]; exact hz₆
  · intro a ha
    rcases hft₆ a ha with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨?_, by dsimp only [Outcome.value]; exact h2⟩
      rw [hm2, hm3]; clear hlenE hlenB hE₀len; omega
  · have hcost := osCost_le (M := S.mul) (l := ordStoreLog eCap) (d := delL.length)
      (Ep := (S₀.applyBatch (delL.map Update.delete)).batchEnc P)
      (i := insL.length) (Y := (Ys.map List.length).sum) (t := T₀.length) (by unfold ordStoreLog; omega)
    clear hlenE hlenB hE₀len
    omega

end MinCostFlow.SparseCore.Program
