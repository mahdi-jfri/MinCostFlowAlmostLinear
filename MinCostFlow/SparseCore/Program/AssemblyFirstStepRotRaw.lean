module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutEnds
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutEmbRotModel

import WordRAM.Tactic

/-!
# Phase 4 `T₀` candidate-vertex collector (`AssemblyFirstStepRotRaw`)

Implements and verifies the two deterministic Word-RAM procedures that populate the raw vertex
candidate array `rawL` for `asmFirstBuildRotStmt` (`AssemblyFirstRotProg.lean`) with
`rawL.toFinset = asmFirstRotRawSet sp tr U ord ed`:
1. `asmFirstCollectRotDirectStmt` (`[spPtr, insPtr, outPtr]`): appends `(s.kept, s.fresh)` for
   each entry of `SplitEntriesAt mem spPtr splits` and `(tl e, hd e)` for each entry of
   `OutInsAt mem insPtr insL tl hd` into `outPtr`, returning `2 * splits.length + 2 * insL.length`
   in `≤ 35 * (splits.length + insL.length) + 30` steps (zero tour queries, zero heap).
2. `asmFirstCollectRotBatchStmt fVertRoot` (`[tourH, batch, outPtr, cntAddr, hp]`): scans `batch`
   and appends `fVertRoot [tourH, v, hp]` for each vertex `v` of each `.insert` / `.split` into
   `outPtr + mem[cntAddr]`, updating `mem[cntAddr]` and returning `hp'`.
3. `asmFirstCollectRotEditsStmt fVertRoot` (`[tourH, edits, outPtr, cntAddr, hp]`): scans `edits`
   and appends `fVertRoot [tourH, v, hp]` for each vertex `v` of each `OrdEdit` into
   `outPtr + mem[cntAddr]`, updating `mem[cntAddr]` and returning `hp'`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

@[expose] public section

/-- **Direct `T₀` vertex collector**, `[spPtr, insPtr, outPtr]`: copies `(kept, fresh)` from
`spPtr` and `(tl, hd)` from `insPtr` into `outPtr`, returning `2 * spLen + 2 * insLen`. -/
def asmFirstCollectRotDirectStmt : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 3)
    (.assign 6 (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 4) (.reg 5))) ;;
     .store (.bin .add (.reg 2) (.reg 4)) (.load (.bin .add (.reg 6) (.const 2))) ;;
     .store (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 1)) (.load (.bin .add (.reg 6) (.const 3))) ;;
     .assign 4 (.bin .add (.reg 4) (.const 2))) ;;
  .assign 3 (.load (.reg 1)) ;;
  forRange 5 (.const 0) (.reg 3)
    (.assign 6 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 3) (.reg 5))) ;;
     .store (.bin .add (.reg 2) (.reg 4)) (.load (.bin .add (.reg 6) (.const 1))) ;;
     .store (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 1)) (.load (.bin .add (.reg 6) (.const 2))) ;;
     .assign 4 (.bin .add (.reg 4) (.const 2))) ;;
  .ret (.reg 4)

/-- Loop body for `asmFirstCollectRotBatchStmt`:
regs `0 = tourH`, `1 = batch`, `2 = outPtr`, `3 = cntAddr`, `4 = hp`, `5 = nU`, `6 = cur`,
`7 = i`, `8..13` scratch. -/
def asmFirstCollectRotBatchBody (fVertRoot : ℕ) : Stmt :=
  .assign 8 (.load (.reg 6)) ;;
  .cond (.bin .eq (.reg 8) (.const 0))
    (.assign 9 (.load (.bin .add (.reg 6) (.const 2))) ;;
     .assign 10 (.load (.bin .add (.reg 6) (.const 3))) ;;
     .assign 11 (.reg 4) ;;
     .call 4 fVertRoot [.reg 0, .reg 9, .reg 4] ;;
     .assign 12 (.load (.reg 3)) ;;
     .store (.bin .add (.reg 2) (.reg 12)) (.load (.reg 11)) ;;
     .assign 11 (.reg 4) ;;
     .call 4 fVertRoot [.reg 0, .reg 10, .reg 4] ;;
     .store (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1)) (.load (.reg 11)) ;;
     .store (.reg 3) (.bin .add (.reg 12) (.const 2)) ;;
     .assign 6 (.bin .add (.reg 6) (.const 4)))
    (.cond (.bin .eq (.reg 8) (.const 1))
      (.assign 6 (.bin .add (.reg 6) (.const 2)))
      (.assign 9 (.load (.bin .add (.reg 6) (.const 1))) ;;
       .assign 10 (.load (.bin .add (.reg 6) (.const 2))) ;;
       .assign 11 (.reg 4) ;;
       .call 4 fVertRoot [.reg 0, .reg 9, .reg 4] ;;
       .assign 12 (.load (.reg 3)) ;;
       .store (.bin .add (.reg 2) (.reg 12)) (.load (.reg 11)) ;;
       .assign 11 (.reg 4) ;;
       .call 4 fVertRoot [.reg 0, .reg 10, .reg 4] ;;
       .store (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1)) (.load (.reg 11)) ;;
       .store (.reg 3) (.bin .add (.reg 12) (.const 2)) ;;
       .assign 9 (.load (.bin .add (.reg 6) (.const 3))) ;;
       .assign 10 (.load (.bin .add (.reg 6) (.const 4))) ;;
       .assign 6 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 5)) (.reg 9)) (.reg 10))))

/-- **Batch `T₀` vertex-root collector**, `[tourH, batch, outPtr, cntAddr, hp]`. -/
def asmFirstCollectRotBatchStmt (fVertRoot : ℕ) : Stmt :=
  .assign 5 (.load (.reg 1)) ;;
  .assign 6 (.bin .add (.reg 1) (.const 1)) ;;
  forRange 7 (.const 0) (.reg 5) (asmFirstCollectRotBatchBody fVertRoot) ;;
  .ret (.reg 4)

/-- Loop body for `asmFirstCollectRotEditsStmt`:
regs `0 = tourH`, `1 = edits`, `2 = outPtr`, `3 = cntAddr`, `4 = hp`, `5 = nEd`, `6 = cur`,
`7 = i`, `8..13` scratch. -/
def asmFirstCollectRotEditsBody (fVertRoot : ℕ) : Stmt :=
  .assign 8 (.load (.reg 6)) ;;
  .cond (.bin .eq (.reg 8) (.const 0))
    (.assign 6 (.bin .add (.reg 6) (.const 2)))
    (.cond (.bin .add (.bin .eq (.reg 8) (.const 1)) (.bin .eq (.reg 8) (.const 2)))
      (.assign 9 (.load (.bin .add (.reg 6) (.const 1))) ;;
       .assign 10 (.load (.bin .add (.reg 6) (.const 2))) ;;
       .assign 11 (.reg 4) ;;
       .call 4 fVertRoot [.reg 0, .reg 9, .reg 4] ;;
       .assign 12 (.load (.reg 3)) ;;
       .store (.bin .add (.reg 2) (.reg 12)) (.load (.reg 11)) ;;
       .assign 11 (.reg 4) ;;
       .call 4 fVertRoot [.reg 0, .reg 10, .reg 4] ;;
       .store (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1)) (.load (.reg 11)) ;;
       .store (.reg 3) (.bin .add (.reg 12) (.const 2)) ;;
       .assign 9 (.load (.bin .add (.reg 6) (.const 3))) ;;
       .assign 6 (.bin .add (.bin .add (.reg 6) (.const 4)) (.reg 9)))
      (.assign 9 (.load (.bin .add (.reg 6) (.const 1))) ;;
       .assign 11 (.reg 4) ;;
       .call 4 fVertRoot [.reg 0, .reg 9, .reg 4] ;;
       .assign 12 (.load (.reg 3)) ;;
       .store (.bin .add (.reg 2) (.reg 12)) (.load (.reg 11)) ;;
       .store (.reg 3) (.bin .add (.reg 12) (.const 1)) ;;
       .cond (.bin .eq (.reg 8) (.const 3))
         (.assign 6 (.bin .add (.reg 6) (.const 4)))
         (.assign 6 (.bin .add (.reg 6) (.const 3)))))

/-- **Edits `T₀` vertex-root collector**, `[tourH, edits, outPtr, cntAddr, hp]`. -/
def asmFirstCollectRotEditsStmt (fVertRoot : ℕ) : Stmt :=
  .assign 5 (.load (.reg 1)) ;;
  .assign 6 (.bin .add (.reg 1) (.const 1)) ;;
  forRange 7 (.const 0) (.reg 5) (asmFirstCollectRotEditsBody fVertRoot) ;;
  .ret (.reg 4)

/-- Pure vertex list emitted by `asmFirstCollectRotDirectStmt`. -/
def rotDirectList (splits : List CompSplitEntry) (insL : List ℕ) (tl hd : ℕ → ℕ) : List ℕ :=
  (splits.flatMap fun s => [s.kept, s.fresh]) ++ (insL.flatMap fun e => [tl e, hd e])

/-- Pure vertex list emitted by `asmFirstCollectRotBatchStmt` for root function `rt`. -/
def rotBatchVertList (rt : ℕ → ℕ) : List Update → List ℕ
  | [] => []
  | .insert _ a b :: rest => rt a :: rt b :: rotBatchVertList rt rest
  | .delete _ :: rest => rotBatchVertList rt rest
  | .split v v' _ _ :: rest => rt v :: rt v' :: rotBatchVertList rt rest

/-- Pure vertex list emitted by `asmFirstCollectRotEditsStmt` for root function `rt`. -/
def rotEditVertList (rt : ℕ → ℕ) : List OrdEdit → List ℕ
  | [] => []
  | .dropEdge _ :: rest => rotEditVertList rt rest
  | .moveEnds v v' _ _ :: rest => rt v :: rt v' :: rotEditVertList rt rest
  | .insertBefore v _ _ :: rest => rt v :: rotEditVertList rt rest
  | .rotateTo v _ :: rest => rt v :: rotEditVertList rt rest

end

public section

theorem asmFirstCollectRotDirectStmt_noRand : asmFirstCollectRotDirectStmt.NoRand := by
  simp [asmFirstCollectRotDirectStmt, forRange, forUp, Stmt.NoRand]

theorem asmFirstCollectRotBatchStmt_noRand (f : ℕ) : (asmFirstCollectRotBatchStmt f).NoRand := by
  simp [asmFirstCollectRotBatchStmt, asmFirstCollectRotBatchBody, forRange, forUp, Stmt.NoRand]

theorem asmFirstCollectRotEditsStmt_noRand (f : ℕ) : (asmFirstCollectRotEditsStmt f).NoRand := by
  simp [asmFirstCollectRotEditsStmt, asmFirstCollectRotEditsBody, forRange, forUp, Stmt.NoRand]

/-! ## Pure list characterizations matching `asmFirstRotRawSet` -/

lemma rotDirectList_length (splits : List CompSplitEntry) (insL : List ℕ) (tl hd : ℕ → ℕ) :
    (rotDirectList splits insL tl hd).length = 2 * splits.length + 2 * insL.length := by
  have h1 : (splits.flatMap fun s => [s.kept, s.fresh]).length = 2 * splits.length := by
    induction splits with
    | nil => simp
    | cons _ _ ih => simp [ih]; omega
  have h2 : (insL.flatMap fun e => [tl e, hd e]).length = 2 * insL.length := by
    induction insL with
    | nil => simp
    | cons _ _ ih => simp [ih]; omega
  simp [rotDirectList, h1, h2]

lemma rotBatchVertList_length_le (rt : ℕ → ℕ) (U : List Update) :
    (rotBatchVertList rt U).length ≤ 2 * U.length := by
  induction U with
  | nil => simp [rotBatchVertList]
  | cons u rest ih => cases u <;> simp [rotBatchVertList] <;> omega

lemma rotEditVertList_length_le (rt : ℕ → ℕ) (ed : List OrdEdit) :
    (rotEditVertList rt ed).length ≤ 2 * ed.length := by
  induction ed with
  | nil => simp [rotEditVertList]
  | cons e rest ih => cases e <;> simp [rotEditVertList] <;> omega

lemma rotBatchVertList_toFinset (rt : ℕ → ℕ) (U : List Update) :
    (rotBatchVertList rt U).toFinset = (batchVerts U).image rt := by
  induction U with
  | nil => simp [rotBatchVertList, batchVerts]
  | cons u rest ih =>
    cases u <;> simp only [rotBatchVertList, batchVerts, updVerts, List.toFinset_cons, ih,
      Finset.image_insert, Finset.empty_union, Finset.insert_union, Finset.singleton_union]

lemma rotEditVertList_toFinset (rt : ℕ → ℕ) (ed : List OrdEdit) :
    (rotEditVertList rt ed).toFinset = (ordEditVerts ed).image rt := by
  induction ed with
  | nil => simp [rotEditVertList, ordEditVerts]
  | cons e rest ih =>
    cases e <;> simp only [rotEditVertList, ordEditVerts, OrdEdit.verts, List.toFinset_cons, ih,
      Finset.image_insert, Finset.empty_union, Finset.insert_union, Finset.singleton_union]

lemma rotAll_toFinset_eq_rawSet {L : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit)
    {insL : List ℕ} (hins : insL.toFinset = outInsSet sp tr U ord (applyOrdEdits ord ed)) :
    let cs' := compLSFBatch tr.cs U
    (rotDirectList (canonSplitList tr.cs U) insL
        (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e)) ++
      rotBatchVertList cs'.RF.root U ++ rotEditVertList cs'.RF.root ed).toFinset =
      asmFirstRotRawSet sp tr U ord ed := by
  intro cs'
  ext v
  simp only [List.toFinset_append, Finset.mem_union, rotBatchVertList_toFinset,
    rotEditVertList_toFinset, asmFirstRotRawSet, rotDirectList, List.mem_toFinset,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton, Finset.image_union, List.mem_map]
  rw [← hins]
  simp only [List.mem_toFinset]
  constructor
  · rintro (((⟨s, hs, rfl | rfl⟩ | ⟨e, he, rfl | rfl⟩) | hv) | hv)
    · exact Or.inl (Or.inl (Or.inl ⟨s, hs, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨s, hs, rfl⟩))
    · exact Or.inl (Or.inr ⟨e, he, Or.inl rfl⟩)
    · exact Or.inl (Or.inr ⟨e, he, Or.inr rfl⟩)
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  · rintro (((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨e, he, rfl | rfl⟩) | (hv | hv))
    · exact Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inl rfl⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inr rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨e, he, Or.inl rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨e, he, Or.inr rfl⟩))
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv

/-! ## Verification of `asmFirstCollectRotDirectStmt` -/

private lemma flatMap_pair_length {α : Type*} (L : List α) (f g : α → ℕ) :
    (L.flatMap fun x => [f x, g x]).length = 2 * L.length := by
  induction L with
  | nil => simp
  | cons _ _ ih => simp [ih]; omega

private lemma flatMap_pair_getElem {α : Type*} (L : List α) (f g : α → ℕ) (k : ℕ)
    (hk : k < (L.flatMap fun x => [f x, g x]).length) :
    (L.flatMap fun x => [f x, g x])[k]'hk =
      if k % 2 = 0 then f (L[k / 2]'(by rw [flatMap_pair_length] at hk; omega))
      else g (L[k / 2]'(by rw [flatMap_pair_length] at hk; omega)) := by
  induction L generalizing k with
  | nil => simp at hk
  | cons x rest ih =>
    cases k with
    | zero => simp
    | succ k' =>
      cases k' with
      | zero => simp
      | succ k'' =>
        have h1 : ((x :: rest).flatMap fun a => [f a, g a])[k'' + 2]'hk =
            (rest.flatMap fun a => [f a, g a])[k'']'(by simp at hk ⊢; omega) := rfl
        rw [h1, ih k'' _]
        simp only [show (k'' + 2) % 2 = k'' % 2 by omega, show (k'' + 2) / 2 = k'' / 2 + 1 by omega]
        rfl

theorem asmFirstCollectRotDirect_runs {w spPtr insPtr outPtr pos : ℕ} {p : Program}
    {splits : List CompSplitEntry} {insL : List ℕ} {tl hd : ℕ → ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hSp : SplitEntriesAt mem₀ spPtr splits)
    (hIns : OutInsAt mem₀ insPtr insL tl hd)
    (hSp_le : spPtr + splitEntriesWords splits ≤ outPtr)
    (hIns_le : insPtr + 1 + 3 * insL.length ≤ outPtr)
    (hout_w : outPtr + 2 * splits.length + 2 * insL.length < 2 ^ w) :
    let outL := rotDirectList splits insL tl hd
    ∃ st' cost,
      Runs w p ω asmFirstCollectRotDirectStmt (startState [spPtr, insPtr, outPtr] mem₀ pos)
        (.returned outL.length) st' cost ∧
      ListAt st'.mem outPtr outL ∧
      (∀ a, a < outPtr ∨ outPtr + outL.length ≤ a → st'.mem a = mem₀ a) ∧
      cost ≤ 48 * (splits.length + insL.length) + 45 := by
  intro outL
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have hSpW : splitEntriesWords splits = 1 + 4 * splits.length := rfl
  set s0 := startState [spPtr, insPtr, outPtr] mem₀ pos
  set r1 := Function.update s0.regs 3 splits.length
  set r2 := Function.update r1 4 0
  have ha3 : Runs w p ω (.assign 3 (.load (.reg 0))) s0 .normal ⟨mem₀, r1, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨splits.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [s0, startState])) hSp.1, rfl, rfl, rfl⟩
  have ha4 : Runs w p ω (.assign 4 (.const 0)) ⟨mem₀, r1, pos⟩ .normal ⟨mem₀, r2, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  let spFlat := splits.flatMap fun s => [s.kept, s.fresh]
  have hspFlat_len : spFlat.length = 2 * splits.length := by
    dsimp only [spFlat]; exact flatMap_pair_length _ _ _
  -- Loop 1: splits
  let inv1 : ℕ → State → Prop := fun i st =>
    st.regs 0 = spPtr ∧ st.regs 1 = insPtr ∧ st.regs 2 = outPtr ∧
    st.regs 3 = splits.length ∧ st.regs 4 = 2 * i ∧ st.regs 5 = i ∧
    (∀ j < i, st.mem (outPtr + 2 * j) = (splits.getD j ⟨false, 0, 0, 0⟩).kept ∧
      st.mem (outPtr + 2 * j + 1) = (splits.getD j ⟨false, 0, 0, 0⟩).fresh) ∧
    (∀ a, a < outPtr ∨ outPtr + 2 * i ≤ a → st.mem a = mem₀ a)
  have hL1 := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 3)
    (body := .assign 6 (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 4) (.reg 5))) ;;
      .store (.bin .add (.reg 2) (.reg 4)) (.load (.bin .add (.reg 6) (.const 2))) ;;
      .store (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 1)) (.load (.bin .add (.reg 6) (.const 3))) ;;
      .assign 4 (.bin .add (.reg 4) (.const 2)))
    (P := fun st => inv1 0 { st with regs := Function.update st.regs 5 0 })
    (Inv := inv1) (fun _ => 35) 0 splits.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.1)
    (fun i _ hi st ω' ⟨r0, r1', r2', r3', r4', r5', hcp, hfr⟩ => by
      set s := splits[i]'hi
      set base := spPtr + 1 + 4 * i
      have hkept : st.mem (base + 2) = s.kept := (hfr _ (Or.inl (by omega))).trans (hSp.2 i hi).2.2.1
      have hfresh : st.mem (base + 3) = s.fresh := (hfr _ (Or.inl (by omega))).trans (hSp.2 i hi).2.2.2
      set rA := Function.update st.regs 6 base
      set m1 := Function.update st.mem (outPtr + 2 * i) s.kept
      set m2 := Function.update m1 (outPtr + 2 * i + 1) s.fresh
      set rB := Function.update rA 4 (2 * (i + 1))
      have h6 : Runs w p ω' (.assign 6 (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 4) (.reg 5))))
          st .normal ⟨st.mem, rA, st.pos⟩ 8 := by
        have he1 : (Expr.bin .add (.reg 0) (.const 1)).eval w st = some (spPtr + 1) :=
          Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_const h1w) (by omega)
        have he2 : (Expr.bin .mul (.const 4) (.reg 5)).eval w st = some (4 * i) :=
          Expr.eval_mul (Expr.eval_const h4w) (Expr.eval_reg_of_eq r5') (by omega)
        exact runs_assign_iff.mpr ⟨base, Expr.eval_add he1 he2 (by omega), rfl, rfl, rfl⟩
      have hs1 : Runs w p ω' (.store (.bin .add (.reg 2) (.reg 4)) (.load (.bin .add (.reg 6) (.const 2))))
          ⟨st.mem, rA, st.pos⟩ .normal ⟨m1, rA, st.pos⟩ 8 :=
        runs_store_iff.mpr ⟨outPtr + 2 * i, s.kept,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r2'])) (Expr.eval_reg_of_eq (by simp [rA, r4'])) (by omega),
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA])) (Expr.eval_const h2w) (by omega))
            hkept, rfl, rfl, rfl⟩
      have hm1_f : m1 (base + 3) = s.fresh := by
        dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact hfresh
      have hs2 : Runs w p ω'
          (.store (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 1)) (.load (.bin .add (.reg 6) (.const 3))))
          ⟨m1, rA, st.pos⟩ .normal ⟨m2, rA, st.pos⟩ 10 := by
        have he1 : (Expr.bin .add (.reg 2) (.reg 4)).eval w ⟨m1, rA, st.pos⟩ = some (outPtr + 2 * i) :=
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r2'])) (Expr.eval_reg_of_eq (by simp [rA, r4'])) (by omega)
        exact runs_store_iff.mpr ⟨outPtr + 2 * i + 1, s.fresh,
          Expr.eval_add he1 (Expr.eval_const h1w) (by omega),
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA])) (Expr.eval_const h3w) (by omega))
            hm1_f, rfl, rfl, rfl⟩
      have h4s : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 2))) ⟨m2, rA, st.pos⟩ .normal ⟨m2, rB, st.pos⟩ 4 :=
        runs_assign_iff.mpr ⟨2 * (i + 1), by
          have he : (Expr.bin .add (.reg 4) (.const 2)).eval w ⟨m2, rA, st.pos⟩ = some (2 * i + 2) :=
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r4'])) (Expr.eval_const h2w) (by omega)
          simpa [show 2 * i + 2 = 2 * (i + 1) by omega] using he, rfl, rfl, rfl⟩
      refine ⟨.normal, ⟨m2, rB, st.pos⟩, 33,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, h6,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2, h4s, rfl⟩), rfl⟩), rfl⟩),
        ⟨⟨by simp [rB, rA, r0], by simp [rB, rA, r1'], by simp [rB, rA, r2'],
          by simp [rB, rA, r3'], by simp [rB], by simp, ?_, ?_⟩, by simp [rB, rA, r5']⟩,
        by show 33 ≤ 35; omega⟩
      · intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hji | rfl
        · simp only [m2, m1, Function.update_of_ne (by omega : outPtr + 2 * j ≠ outPtr + 2 * i + 1),
            Function.update_of_ne (by omega : outPtr + 2 * j ≠ outPtr + 2 * i),
            Function.update_of_ne (by omega : outPtr + 2 * j + 1 ≠ outPtr + 2 * i + 1),
            Function.update_of_ne (by omega : outPtr + 2 * j + 1 ≠ outPtr + 2 * i)]
          exact hcp j hji
        · rw [List.getD_eq_getElem _ _ hi]
          exact ⟨by dsimp only [m2]; rw [Function.update_of_ne (by omega)]; simp [m1, s], by simp [m2, s]⟩
      · intro a ha
        dsimp only [m2, m1]
        rw [Function.update_of_ne (show a ≠ outPtr + 2 * i + 1 by rcases ha with h | h <;> omega),
          Function.update_of_ne (show a ≠ outPtr + 2 * i by rcases ha with h | h <;> omega)]
        exact hfr a (by rcases ha with h | h <;> omega))
  obtain ⟨o1, st1, c1, hr1, hpost1, hc1⟩ := hL1 ⟨mem₀, r2, pos⟩ ω
    ⟨by simp [r2, r1, s0, startState], by simp [r2, r1, s0, startState], by simp [r2, r1, s0, startState],
     by simp [r2, r1], by simp [r2], by simp, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  cases o1 with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨_, r1_1, r2_1, _, r4_1, _, hcp1, hfr1⟩ := hpost1
  have hm_insLen : st1.mem insPtr = insL.length := (hfr1 insPtr (Or.inl (by omega))).trans hIns.1
  set r3' := Function.update st1.regs 3 insL.length
  have ha3' : Runs w p ω (.assign 3 (.load (.reg 1))) st1 .normal ⟨st1.mem, r3', st1.pos⟩ 3 :=
    runs_assign_iff.mpr ⟨insL.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r1_1) hm_insLen, rfl, rfl, rfl⟩
  -- Loop 2: insL
  let inv2 : ℕ → State → Prop := fun i st =>
    st.regs 1 = insPtr ∧ st.regs 2 = outPtr ∧ st.regs 3 = insL.length ∧
    st.regs 4 = 2 * splits.length + 2 * i ∧ st.regs 5 = i ∧
    (∀ j < i, st.mem (outPtr + 2 * splits.length + 2 * j) = tl (insL.getD j 0) ∧
      st.mem (outPtr + 2 * splits.length + 2 * j + 1) = hd (insL.getD j 0)) ∧
    (∀ a, a < outPtr + 2 * splits.length ∨ outPtr + 2 * splits.length + 2 * i ≤ a → st.mem a = st1.mem a)
  have hL2 := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 3)
    (body := .assign 6 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 3) (.reg 5))) ;;
      .store (.bin .add (.reg 2) (.reg 4)) (.load (.bin .add (.reg 6) (.const 1))) ;;
      .store (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 1)) (.load (.bin .add (.reg 6) (.const 2))) ;;
      .assign 4 (.bin .add (.reg 4) (.const 2)))
    (P := fun st => inv2 0 { st with regs := Function.update st.regs 5 0 })
    (Inv := inv2) (fun _ => 35) 0 insL.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.1)
    (fun i _ hi st ω' ⟨r1', r2', r3'', r4', r5', hcp2, hfr2⟩ => by
      set base := insPtr + 1 + 3 * i
      have htl : st.mem (base + 1) = tl (insL.getD i 0) := by
        rw [hfr2 _ (Or.inl (by omega)), hfr1 _ (Or.inl (by omega))]
        simpa [base, show insPtr + 1 + 3 * i + 1 = insPtr + 2 + 3 * i by omega] using (hIns.2 i hi).2.1
      have hhd : st.mem (base + 2) = hd (insL.getD i 0) := by
        rw [hfr2 _ (Or.inl (by omega)), hfr1 _ (Or.inl (by omega))]
        simpa [base, show insPtr + 1 + 3 * i + 2 = insPtr + 3 + 3 * i by omega] using (hIns.2 i hi).2.2
      set rA := Function.update st.regs 6 base
      set m1 := Function.update st.mem (outPtr + 2 * splits.length + 2 * i) (tl (insL.getD i 0))
      set m2 := Function.update m1 (outPtr + 2 * splits.length + 2 * i + 1) (hd (insL.getD i 0))
      set rB := Function.update rA 4 (2 * splits.length + 2 * (i + 1))
      have h6 : Runs w p ω' (.assign 6 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 3) (.reg 5))))
          st .normal ⟨st.mem, rA, st.pos⟩ 8 := by
        have he1 : (Expr.bin .add (.reg 1) (.const 1)).eval w st = some (insPtr + 1) :=
          Expr.eval_add (Expr.eval_reg_of_eq r1') (Expr.eval_const h1w) (by omega)
        have he2 : (Expr.bin .mul (.const 3) (.reg 5)).eval w st = some (3 * i) :=
          Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq r5') (by omega)
        exact runs_assign_iff.mpr ⟨base, Expr.eval_add he1 he2 (by omega), rfl, rfl, rfl⟩
      have hdst1 : (Expr.bin .add (.reg 2) (.reg 4)).eval w ⟨st.mem, rA, st.pos⟩ =
          some (outPtr + 2 * splits.length + 2 * i) := by
        have hr2 : rA 2 = outPtr := by simp [rA, r2']
        have hr4 : rA 4 = 2 * splits.length + 2 * i := by simp [rA, r4']
        rw [show outPtr + 2 * splits.length + 2 * i = outPtr + (2 * splits.length + 2 * i) by omega]
        exact Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr4) (by omega)
      have hs1 : Runs w p ω' (.store (.bin .add (.reg 2) (.reg 4)) (.load (.bin .add (.reg 6) (.const 1))))
          ⟨st.mem, rA, st.pos⟩ .normal ⟨m1, rA, st.pos⟩ 8 :=
        runs_store_iff.mpr ⟨outPtr + 2 * splits.length + 2 * i, tl (insL.getD i 0), hdst1,
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA])) (Expr.eval_const h1w) (by omega))
            htl, rfl, rfl, rfl⟩
      have hm1_h : m1 (base + 2) = hd (insL.getD i 0) := by
        dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact hhd
      have hs2 : Runs w p ω'
          (.store (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 1)) (.load (.bin .add (.reg 6) (.const 2))))
          ⟨m1, rA, st.pos⟩ .normal ⟨m2, rA, st.pos⟩ 10 := by
        have hr2 : rA 2 = outPtr := by simp [rA, r2']
        have hr4 : rA 4 = 2 * splits.length + 2 * i := by simp [rA, r4']
        have he1 : (Expr.bin .add (.reg 2) (.reg 4)).eval w ⟨m1, rA, st.pos⟩ =
            some (outPtr + 2 * splits.length + 2 * i) := by
          rw [show outPtr + 2 * splits.length + 2 * i = outPtr + (2 * splits.length + 2 * i) by omega]
          exact Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr4) (by omega)
        exact runs_store_iff.mpr ⟨outPtr + 2 * splits.length + 2 * i + 1, hd (insL.getD i 0),
          Expr.eval_add he1 (Expr.eval_const h1w) (by omega),
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA])) (Expr.eval_const h2w) (by omega))
            hm1_h, rfl, rfl, rfl⟩
      have h4s : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 2))) ⟨m2, rA, st.pos⟩ .normal ⟨m2, rB, st.pos⟩ 4 :=
        runs_assign_iff.mpr ⟨2 * splits.length + 2 * (i + 1), by
          have hr4 : rA 4 = 2 * splits.length + 2 * i := by simp [rA, r4']
          have he : (Expr.bin .add (.reg 4) (.const 2)).eval w ⟨m2, rA, st.pos⟩ =
              some (2 * splits.length + 2 * i + 2) :=
            Expr.eval_add (Expr.eval_reg_of_eq hr4) (Expr.eval_const h2w) (by omega)
          simpa [show 2 * splits.length + 2 * i + 2 = 2 * splits.length + 2 * (i + 1) by omega] using he,
          rfl, rfl, rfl⟩
      refine ⟨.normal, ⟨m2, rB, st.pos⟩, 33,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, h6,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2, h4s, rfl⟩), rfl⟩), rfl⟩),
        ⟨⟨by simp [rB, rA, r1'], by simp [rB, rA, r2'], by simp [rB, rA, r3''],
          by simp [rB], by simp, ?_, ?_⟩, by simp [rB, rA, r5']⟩,
        by show 33 ≤ 35; omega⟩
      · intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hji | rfl
        · simp only [m2, m1,
            Function.update_of_ne (by omega : outPtr + 2 * splits.length + 2 * j ≠ outPtr + 2 * splits.length + 2 * i + 1),
            Function.update_of_ne (by omega : outPtr + 2 * splits.length + 2 * j ≠ outPtr + 2 * splits.length + 2 * i),
            Function.update_of_ne (by omega : outPtr + 2 * splits.length + 2 * j + 1 ≠ outPtr + 2 * splits.length + 2 * i + 1),
            Function.update_of_ne (by omega : outPtr + 2 * splits.length + 2 * j + 1 ≠ outPtr + 2 * splits.length + 2 * i)]
          exact hcp2 j hji
        · exact ⟨by dsimp only [m2]; rw [Function.update_of_ne (by omega)]; simp [m1], by simp [m2]⟩
      · intro a ha
        dsimp only [m2, m1]
        rw [Function.update_of_ne (show a ≠ outPtr + 2 * splits.length + 2 * i + 1 by rcases ha with h | h <;> omega),
          Function.update_of_ne (show a ≠ outPtr + 2 * splits.length + 2 * i by rcases ha with h | h <;> omega)]
        exact hfr2 a (by rcases ha with h | h <;> omega))
  obtain ⟨o2, st2, c2, hr2, hpost2, hc2⟩ := hL2 ⟨st1.mem, r3', st1.pos⟩ ω
    ⟨by simp [r3', r1_1], by simp [r3', r2_1], by simp [r3'], by simp [r3', r4_1], by simp,
     fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  cases o2 with
  | returned _ => cases hpost2
  | normal =>
  obtain ⟨_, _, _, r4_2, _, hcp2, hfr2⟩ := hpost2
  have houtLen : outL.length = 2 * splits.length + 2 * insL.length :=
    rotDirectList_length splits insL tl hd
  have hret : Runs w p ω (.ret (.reg 4)) st2 (.returned outL.length) st2 2 :=
    runs_ret_iff.mpr ⟨outL.length, Expr.eval_reg_of_eq (r4_2.trans houtLen.symm), rfl, rfl, rfl⟩
  have hrc1 : rangeCost (fun _ => 35) 0 splits.length = 35 * splits.length := by
    simp [rangeCost, Nat.mul_comm]
  have hrc2 : rangeCost (fun _ => 35) 0 insL.length = 35 * insL.length := by
    simp [rangeCost, Nat.mul_comm]
  dsimp only at hc1 hc2; simp only [hrc1, hrc2, Nat.sub_zero, Expr.size] at hc1 hc2
  refine ⟨st2, _,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha3,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha4,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha3',
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr2, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    ?_, ?_, by omega⟩
  · intro k hk
    by_cases hk1 : k < 2 * splits.length
    · have hk_sp : k < spFlat.length := by omega
      have hget : outL[k]'hk = spFlat[k]'hk_sp := by
        dsimp only [outL, rotDirectList]; exact List.getElem_append_left hk_sp
      rw [hget]
      dsimp only [spFlat]
      rw [flatMap_pair_getElem splits CompSplitEntry.kept CompSplitEntry.fresh k]
      have hdiv : k / 2 < splits.length := by omega
      have hcp := hcp1 (k / 2) hdiv
      rw [List.getD_eq_getElem _ _ hdiv] at hcp
      rw [hfr2 (outPtr + k) (Or.inl (by omega))]
      by_cases hev : k % 2 = 0
      · simp only [hev, ↓reduceIte]; rw [show outPtr + k = outPtr + 2 * (k / 2) by omega]; exact hcp.1
      · simp only [hev, ↓reduceIte]; rw [show outPtr + k = outPtr + 2 * (k / 2) + 1 by omega]; exact hcp.2
    · have hk_ins : k - 2 * splits.length < (insL.flatMap fun e => [tl e, hd e]).length := by
        rw [houtLen] at hk
        have := flatMap_pair_length insL tl hd
        omega
      have hget : outL[k]'hk = (insL.flatMap fun e => [tl e, hd e])[k - 2 * splits.length]'hk_ins := by
        dsimp only [outL, rotDirectList]
        have hle : (splits.flatMap fun s => [s.kept, s.fresh]).length ≤ k := by
          rw [flatMap_pair_length]; omega
        refine (List.getElem_append_right hle).trans ?_
        simp only [flatMap_pair_length]
      rw [hget, flatMap_pair_getElem insL tl hd (k - 2 * splits.length)]
      have hdiv : (k - 2 * splits.length) / 2 < insL.length := by omega
      have hcp := hcp2 ((k - 2 * splits.length) / 2) hdiv
      rw [List.getD_eq_getElem _ _ hdiv] at hcp
      by_cases hev : (k - 2 * splits.length) % 2 = 0
      · simp only [hev, ↓reduceIte]
        rw [show outPtr + k = outPtr + 2 * splits.length + 2 * ((k - 2 * splits.length) / 2) by omega]
        exact hcp.1
      · simp only [hev, ↓reduceIte]
        rw [show outPtr + k = outPtr + 2 * splits.length + 2 * ((k - 2 * splits.length) / 2) + 1 by omega]
        exact hcp.2
  · intro a ha
    rw [hfr2 a (by rcases ha with h | h <;> omega), hfr1 a (by rcases ha with h | h <;> omega)]

end

end MinCostFlow.SparseCore.Program
