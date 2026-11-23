module

public import MinCostFlow.MinRatio.FreshBatch
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
import WordRAM.Memory

/-!
# Passing a translated refresh batch to a chain level

Insertion and deletion records have the same encoding in the IPM and
dynamic named-graph layouts. A translated fixed-graph refresh consists
only of these records and uses the same number of words as its input. The output can therefore be passed to a sparse-core
level without another copy.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain
open IPM.Machine (updateWords batchWords)

private theorem bodyAt_of_fixed_records {mem : ℕ → ℕ} {U : List Update}
    (hU : ∀ v v' S T, Update.split v v' S T ∉ U)
    (a : ℕ) (G : MGraph) (hw : ListAt mem a (U.flatMap updateWords)) :
    DynSpanner.Program.BatchBodyAt mem a G U (U.flatMap updateWords).length ∧
      (U.flatMap updateWords).length ≤ 4 * G.batchEnc U := by
  induction U generalizing a G with
  | nil => exact ⟨rfl, Nat.zero_le _⟩
  | cons u us ih =>
    have htail : ∀ v v' S T, Update.split v v' S T ∉ us :=
      fun v v' S T h => hU v v' S T (List.mem_cons_of_mem _ h)
    rw [List.flatMap_cons, List.length_append] at *
    rcases listAt_append.mp hw with ⟨hu, hr⟩
    have hh := ih htail (a + (updateWords u).length) (G.applyUpdate u) hr
    have he : (updateWords u).length + (us.flatMap updateWords).length -
        (updateWords u).length = (us.flatMap updateWords).length := Nat.add_sub_cancel_left _ _
    have hkind : DynSpanner.Program.UpdateAt mem a G u (updateWords u).length ∧
        (updateWords u).length ≤ 4 * G.updateEnc u := by
      cases u with
      | split v v' S T => exact False.elim (hU v v' S T List.mem_cons_self)
      | insert e v v' => exact ⟨⟨rfl, hu⟩, le_rfl⟩
      | delete e => exact ⟨⟨rfl, hu⟩, by change 2 ≤ 4; decide⟩
    refine ⟨⟨_, Nat.le_add_right _ _, hkind.1, he.symm ▸ hh.1⟩, ?_⟩
    change _ ≤ 4 * (G.updateEnc u + (G.applyUpdate u).batchEnc us)
    rw [Nat.mul_add]
    exact Nat.add_le_add hkind.2 hh.2

/-- A refresh record list is already a compact dynamic-graph batch. -/
theorem smallBatchAt_of_fixed_records {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    (hU : ∀ v v' S T, Update.split v v' S T ∉ U)
    (ha : IPM.Machine.BatchAt mem a U) :
    DynSpanner.Program.SmallBatchAt mem a G U (batchWords U).length := by
  obtain ⟨hc, hbody⟩ := listAt_cons.mp ha
  have hs := bodyAt_of_fixed_records hU (a + 1) G hbody
  have hlen : (batchWords U).length = (U.flatMap updateWords).length + 1 := rfl
  have ht : (batchWords U).length - 1 = (U.flatMap updateWords).length := by omega
  refine ⟨⟨by omega, hc, ht.symm ▸ hs.1⟩, ?_⟩
  rw [hlen]
  have := hs.2
  omega

/-- Translating fixed-graph refresh records introduces no vertex splits. -/
theorem translateBatch_fixed_records {extCap : ℕ} (U : List Update)
    (hU : ∀ u ∈ U, FreshRecordFits extCap u) (G : MGraph) (f g : ℕ → ℕ) (next : ℕ) :
    ∀ v v' S T, Update.split v v' S T ∉ (translateBatch G f g next U).2.2.2.2 := by
  induction U generalizing G f g next with
  | nil => simp [translateBatch]
  | cons u us ih =>
    have hfit := hU u List.mem_cons_self
    have htail : ∀ u ∈ us, FreshRecordFits extCap u :=
      fun v hv => hU v (List.mem_cons_of_mem _ hv)
    cases u with
    | split _ _ _ _ => cases hfit
    | insert e a b =>
      intro v v' S
      simp [translateBatch, translateUpdate]
      exact ih htail _ _ _ _ v v' S
    | delete e =>
      intro v v' S
      simp [translateBatch, translateUpdate]
      exact ih htail _ _ _ _ v v' S

/-- Every insert or delete in the translated batch has its original
record width. The output buffer needs exactly the input's word count. -/
theorem translateBatch_refresh_words_length {extCap : ℕ} (U : List Update)
    (hU : ∀ u ∈ U, FreshRecordFits extCap u) (G : MGraph) (f g : ℕ → ℕ) (next : ℕ) :
    (batchWords (translateBatch G f g next U).2.2.2.2).length = (batchWords U).length := by
  suffices h :
      ((translateBatch G f g next U).2.2.2.2.flatMap updateWords).length =
        (U.flatMap updateWords).length by
    simp only [batchWords, List.length_cons, h]
  induction U generalizing G f g next with
  | nil => rfl
  | cons u us ih =>
    have hfit := hU u List.mem_cons_self
    have htail : ∀ v ∈ us, FreshRecordFits extCap v :=
      fun v hv => hU v (List.mem_cons_of_mem _ hv)
    cases u with
    | split _ _ _ _ => cases hfit
    | insert e a b =>
      simpa only [translateBatch, translateUpdate, List.flatMap_cons, updateWords, List.length_append, List.length_cons, List.length_nil]
        using congrArg (fun n => (4 : ℕ) + n) (ih htail (G.applyUpdate (.insert e a b))
          (Function.update f e next) (Function.update g next e) (next + 1))
    | delete e =>
      simpa only [translateBatch, translateUpdate, List.flatMap_cons, updateWords, List.length_append, List.length_cons, List.length_nil]
        using congrArg (fun n => (2 : ℕ) + n) (ih htail (G.applyUpdate (.delete e)) f g next)

/-- The batch translator's actual output can be passed directly to a
level that consumes the compact named-graph layout. -/
theorem freshBatchEntry_compact {w src heap ret next : ℕ} {r : FreshBatchRegions}
    {G H : MGraph} {f g : ℕ → ℕ} {updates : List Update} {mem mem' : ℕ → ℕ}
    (hU : ∀ u ∈ updates, FreshRecordFits r.externalCap u)
    (hout : (freshBatchEntryContract w r G H f g next updates).post
      [src, r.forward, r.inverse, r.counter, heap] mem ret mem') :
    DynSpanner.Program.SmallBatchAt mem' heap H (translateBatch G f g next updates).2.2.2.2
      (ret - heap) := by
  obtain ⟨hbatch, _, hret, _, _⟩ := hout
  change ret = heap + (batchWords (translateBatch G f g next updates).2.2.2.2).length at hret
  rw [hret, Nat.add_sub_cancel_left]
  exact smallBatchAt_of_fixed_records (translateBatch_fixed_records updates hU G f g next) hbatch

end MinCostFlow.MinRatio
