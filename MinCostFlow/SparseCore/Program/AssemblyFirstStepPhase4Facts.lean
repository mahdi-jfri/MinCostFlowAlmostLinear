module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase4Defs

/-!
# Small facts for the run of Phase 4 (`AssemblyFirstStepPhase4Facts`)

The run lemma of Phase 4 (`AssemblyFirstStepPhase4Proof`) moves the inputs of the step from one
call to the next and reads the record that the procedure writes. This file holds the small facts
it uses:
* the lists of the workspace have no repeats and entries below `eCap`, so their lengths are at
  most `eCap` (`p4_length_le_of_nodup_lt`, `card_le_length_of_mem`);
* `SplitEntriesAt` only reads its own cells (`splitEntriesAt_of_agree`);
* `readList` reads back a list that `ListAt` places (`readList_of_listAt`);
* the five words of the record (`p4RecordMem_rec` and the next four lemmas);
* the room of Phase 4 above the spanner part (`asmFirstPhase4Room`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The room that Phase 4 needs above the spanner part: the three selectors (`6 eCap` with the
flags of the batch), the output lists (`p4ListsSpace` with lists of at most `eCap` entries and a
tour query), `T₀` (`p4RotSpace`), and the re-embedded list (`2 + 4 m` with `m ≤ 2 eCap`). -/
def asmFirstPhase4Room (vCap eCap nSp nU nEd qE qR : ℕ) : ℕ :=
  6 * eCap + (6 + 18 * eCap) + qE + p4RotSpace vCap nSp eCap nU nEd qR + (2 + 8 * eCap)

end

public section

/-- A list without repeats whose entries are below `n` has at most `n` entries. -/
theorem p4_length_le_of_nodup_lt {L : List ℕ} {n : ℕ} (hnd : L.Nodup) (hlt : ∀ e ∈ L, e < n) :
    L.length ≤ n := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  calc L.toFinset.card ≤ (Finset.range n).card :=
        Finset.card_le_card fun e he => Finset.mem_range.mpr (hlt e (List.mem_toFinset.mp he))
    _ = n := Finset.card_range n

/-- A set inside a list without repeats has at most as many elements as the list. -/
theorem card_le_length_of_mem {S : Finset ℕ} {L : List ℕ} (hnd : L.Nodup)
    (h : ∀ e ∈ S, e ∈ L) : S.card ≤ L.length := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card fun e he => List.mem_toFinset.mpr (h e he)

/-- `SplitEntriesAt` only reads the cells `[p, p + splitEntriesWords L)`. -/
theorem splitEntriesAt_of_agree {mem mem' : ℕ → ℕ} {p : ℕ} {L : List CompSplitEntry}
    (h : SplitEntriesAt mem p L)
    (hag : ∀ x, p ≤ x → x < p + splitEntriesWords L → mem' x = mem x) :
    SplitEntriesAt mem' p L := by
  have hW : splitEntriesWords L = 1 + 4 * L.length := rfl
  refine ⟨(hag p le_rfl (by omega)).trans h.1, fun i hi => ?_⟩
  obtain ⟨h0, h1, h2, h3⟩ := h.2 i hi
  rw [hag _ (by omega) (by omega), hag _ (by omega) (by omega), hag _ (by omega) (by omega),
    hag _ (by omega) (by omega)]
  exact ⟨h0, h1, h2, h3⟩

/-- `readList` reads back a list that `ListAt` places. -/
theorem readList_of_listAt {mem : ℕ → ℕ} {a : ℕ} {L : List ℕ} (h : ListAt mem a L) :
    readList mem a L.length = L := by
  apply List.ext_getElem
  · simp [readList]
  · intro i hi1 hi2
    simp only [readList, List.getElem_map, List.getElem_range]
    exact h i hi2

theorem p4RecordMem_rec (mem : ℕ → ℕ) (rec hL hR hE : ℕ) :
    p4RecordMem mem rec hL hR hE rec = mem hL := by
  simp [p4RecordMem]

theorem p4RecordMem_ins (mem : ℕ → ℕ) (rec hL hR hE : ℕ) :
    p4RecordMem mem rec hL hR hE (rec + 2) = mem (hL + 1) := by
  simp [p4RecordMem]

theorem p4RecordMem_rot (mem : ℕ → ℕ) (rec hL hR hE : ℕ) :
    p4RecordMem mem rec hL hR hE (rec + 3) = mem hR := by
  simp [p4RecordMem]

theorem p4RecordMem_reemb (mem : ℕ → ℕ) (rec hL hR hE : ℕ) :
    p4RecordMem mem rec hL hR hE (rec + 4) = mem hE + 1 := by
  simp [p4RecordMem]

theorem p4RecordMem_reembLen (mem : ℕ → ℕ) (rec hL hR hE : ℕ) :
    p4RecordMem mem rec hL hR hE (rec + 5) = mem (mem hE) := by
  simp [p4RecordMem]

end

end MinCostFlow.SparseCore.Program
