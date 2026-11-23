module

public import MinCostFlow.MinRatio.WireSelectSpec
import WordRAM.Tactic

/-!
# Verification of raw route-extraction loops (`selectFillRev`, `selectSplitSteps`, `selectEmitStitches`)

Verifies the three tail-recursive route-extraction loops of `WireSelectQuery.lean` (`jtree.tex`,
Algorithm 1, page 21; Algorithm 2, page 29):
1. `selectFillRev_meetsContract`: copies `walkRev P` from `MWalkAt mem wPtr P` into
   `stepsBase + 2 .. stepsBase + 2 * (P.length + 1)` in `≤ 70 * |P| + 15` steps.
2. `selectSplitSteps_meetsContract`: scans `stepsBase[0 .. |W|)` oriented by `flip`, partitioning
   off-tree edges (`mem[slots + f] = 0`) into `edgesBase` (`rawEdgesOfWalk`) and single-edge tree
   paths (`mem[slots + f] ≠ 0`) into `pathsBase` in `≤ 115 * |W| + 15` steps.
3. `selectEmitStitches_meetsContract`: appends the `|W|` stitching endpoint pairs of
   `(cycleSegments G0 W).2` (swapped when `flip = true`) into `pathsBase` in `≤ 130 * |W| + 15`
   steps, producing exact `rawPathsOfWalk`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Pure list / walk indexing helpers -/

/-- Reading edge and direction entries from `MWalkAt mem a P`. -/
theorem mWalkAt_read {mem : ℕ → ℕ} {a : ℕ} {P : List (ℕ × Bool)} (h : MWalkAt mem a P) :
    mem a = P.length ∧
    ∀ j (hj : j < P.length),
      mem (a + 1 + 2 * j) = P[j].1 ∧
      mem (a + 2 + 2 * j) = (if P[j].2 then 1 else 0) := by
  have hlen : (mWalkEncode P).length = 1 + 2 * P.length := mWalkEncode_length P
  refine ⟨by simpa [mWalkEncode] using h 0 (by omega), fun j hj => ?_⟩
  have hflat : ∀ (Q : List (ℕ × Bool)) (i : ℕ) (hi : i < Q.length),
      (Q.flatMap fun p => [p.1, if p.2 then 1 else 0])[2 * i]'(by rw [flatMap_pair_length]; omega) = Q[i].1 ∧
      (Q.flatMap fun p => [p.1, if p.2 then 1 else 0])[2 * i + 1]'(by rw [flatMap_pair_length]; omega) =
        (if Q[i].2 then 1 else 0) := by
    intro Q
    induction Q with
    | nil => intro i hi; simp at hi
    | cons q qs ih =>
      intro i hi
      cases i with
      | zero => simp [List.flatMap_cons]
      | succ k =>
        have hk : k < qs.length := by simpa using hi
        simpa [List.flatMap_cons, Nat.mul_succ, Nat.add_assoc] using ih k hk
  have h1 := h (1 + 2 * j) (by rw [hlen]; omega)
  have h2 := h (2 + 2 * j) (by rw [hlen]; omega)
  have hf := hflat P j hj
  constructor
  · rw [Nat.add_assoc, h1]
    have hidx : 1 + 2 * j = 2 * j + 1 := by omega
    simp only [mWalkEncode, hidx, List.getElem_cons_succ]
    exact hf.1
  · rw [Nat.add_assoc, h2]
    have hidx : 2 + 2 * j = (2 * j + 1) + 1 := by omega
    simp only [mWalkEncode, hidx, List.getElem_cons_succ]
    exact hf.2

/-- Indexing into `walkRev P`: entry `t` is `(P[P.length - 1 - t].1, !P[P.length - 1 - t].2)`. -/
theorem walkRev_getElem (P : List (ℕ × Bool)) {t : ℕ} (ht : t < P.length) :
    (walkRev P)[t]'(by simp [walkRev, ht]) =
      (P[P.length - 1 - t]'(by omega) |>.1, !(P[P.length - 1 - t]'(by omega) |>.2)) := by
  simp [walkRev]

/-- Exact element-wise formula for `(cycleSegments G W).2` on a nonempty walk `W`:
entry `t` is `(G.dst W[t], G.src W[(t + 1) % W.length])`. -/
theorem cycleSegments_snd_getElem (G : MGraph) (W : List (ℕ × Bool))
    {t : ℕ} (ht : t < W.length) :
    (cycleSegments G W).2[t]'(by rw [(cycleSegments_eq G W).2]; exact ht) =
      (G.dst W[t], G.src (W[(t + 1) % W.length]'(Nat.mod_lt _ (by omega)))) := by
  have hauxLen : ∀ (target : ℕ) (xs : List (ℕ × Bool)) (prev : ℕ × Bool),
      (cycleSegmentsAux G target prev xs).2.length = xs.length + 1 := by
    intro target xs
    induction xs with
    | nil => intro prev; simp [cycleSegmentsAux]
    | cons y ys ih => intro prev; simp only [cycleSegmentsAux, List.length_cons, ih]
  have haux : ∀ (target : ℕ) (xs : List (ℕ × Bool)) (prev : ℕ × Bool) (k : ℕ)
      (hk : k < xs.length + 1),
      (cycleSegmentsAux G target prev xs).2[k]'(by rw [hauxLen]; exact hk) =
      (G.dst ((prev :: xs)[k]'(by simp; omega)),
       if hlt : k < xs.length then G.src (xs[k]'hlt) else target) := by
    intro target xs
    induction xs with
    | nil =>
      intro prev k hk
      simp only [List.length_nil] at hk
      have hk0 : k = 0 := by omega
      subst hk0; simp [cycleSegmentsAux]
    | cons y ys ih =>
      intro prev k hk
      cases k with
      | zero => simp [cycleSegmentsAux]
      | succ m =>
        have hm : m < ys.length + 1 := by simpa using hk
        simpa [cycleSegmentsAux] using ih y m hm
  cases W with
  | nil => simp at ht
  | cons x₀ xs =>
    have hk : t < xs.length + 1 := by simpa using ht
    have h1 := haux (G.src x₀) xs x₀ t hk
    simp only [cycleSegments]
    rw [h1]
    by_cases hlt : t < xs.length
    · have hmod : (t + 1) % (xs.length + 1) = t + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [dite_eq_left hlt, List.length_cons, hmod, List.getElem_cons_succ]
    · have hteq : t = xs.length := by omega
      have hmod : (t + 1) % (xs.length + 1) = 0 := by rw [hteq]; exact Nat.mod_self _
      simp only [dite_eq_right hlt, List.length_cons, hmod, List.getElem_cons_zero]

/-! ## 2. Contracts for `selectFillRevBody`, `selectSplitStepsBody`, and `selectEmitStitchesBody` -/

/-- Contract for `selectFillRevBody` (`[wPtr, embLen, stepsBase, t]`). -/
def selectFillRevContract (w : ℕ) (P : List (ℕ × Bool)) : Contract where
  pre args mem :=
    ∃ wPtr stepsBase t,
      args = [wPtr, P.length, stepsBase, t] ∧
      16 < 2 ^ w ∧ t ≤ P.length ∧
      MWalkAt mem wPtr P ∧
      wPtr + 1 + 2 * P.length ≤ stepsBase ∧
      stepsBase + 2 * (P.length + 1) < 2 ^ w ∧
      (∀ j (hj : j < P.length), P[j].1 < 2 ^ w) ∧
      ExplicitEdgesAt mem (stepsBase + 2) ((walkRev P).take t)
  post args mem _ mem' :=
    let stepsBase := args.getD 2 0
    let t := args.getD 3 0
    ExplicitEdgesAt mem' (stepsBase + 2) (walkRev P) ∧
    ∀ a, (a < stepsBase + 2 * (t + 1) ∨ stepsBase + 2 * (P.length + 1) ≤ a) → mem' a = mem a
  cost args _ := (P.length - args.getD 3 0) * 70 + 15

/-- Write footprint of `selectSplitStepsBody`. -/
def splitWriteRegion (edgesBase pathsBase descBase K a : ℕ) : Prop :=
  (edgesBase ≤ a ∧ a < edgesBase + 2 * K) ∨
  (pathsBase ≤ a ∧ a < pathsBase + 2 * K) ∨
  a = descBase + 3 ∨ a = descBase + 5

/-- Contract for `selectSplitStepsBody`
(`[slots, intToExt, tailSlot, headSlot, stepsBase, K, flip, edgesBase, pathsBase, descBase, t]`). -/
def selectSplitStepsContract (w : ℕ) (G0 F : MGraph) (W : List (ℕ × Bool)) (flip : Bool) :
    Contract where
  pre args mem :=
    ∃ slots intToExt tailSlot headSlot stepsBase edgesBase pathsBase descBase t,
      args = [slots, intToExt, tailSlot, headSlot, stepsBase, W.length,
        (if flip then 1 else 0), edgesBase, pathsBase, descBase, t] ∧
      16 < 2 ^ w ∧ t ≤ W.length ∧
      ExplicitEdgesAt mem stepsBase W ∧
      (∀ x ∈ W,
        mem (intToExt + mem (tailSlot + x.1)) = G0.tail x.1 ∧
        mem (intToExt + mem (headSlot + x.1)) = G0.head x.1 ∧
        tailSlot + x.1 < 2 ^ w ∧ headSlot + x.1 < 2 ^ w ∧
        intToExt + mem (tailSlot + x.1) < 2 ^ w ∧ intToExt + mem (headSlot + x.1) < 2 ^ w ∧
        G0.tail x.1 < 2 ^ w ∧ G0.head x.1 < 2 ^ w) ∧
      (∀ x ∈ W, x.1 ∈ G0.E ∧ (x.1 ∈ F.E ↔ mem (slots + x.1) ≠ 0) ∧
        slots + x.1 < 2 ^ w ∧ x.1 < 2 ^ w) ∧
      descBase + 5 < stepsBase ∧
      descBase + 5 < edgesBase ∧
      edgesBase + 2 * W.length ≤ pathsBase ∧
      pathsBase + 2 * W.length < 2 ^ w ∧
      stepsBase + 2 * W.length ≤ edgesBase ∧
      (∀ a, splitWriteRegion edgesBase pathsBase descBase W.length a →
        ∀ x ∈ W, a ≠ slots + x.1 ∧ a ≠ tailSlot + x.1 ∧ a ≠ headSlot + x.1 ∧
          a ≠ intToExt + mem (tailSlot + x.1) ∧ a ≠ intToExt + mem (headSlot + x.1)) ∧
      let ePref := rawEdgesOfWalk F (W.take t) flip
      let pPref := ((orientWalkSteps (W.take t) flip).filter (fun x => decide (x.1 ∈ F.E))).map
        (fun x => (G0.src x, G0.dst x))
      mem (descBase + 3) = ePref.length ∧
      ExplicitEdgesAt mem edgesBase ePref ∧
      mem (descBase + 5) = pPref.length ∧
      PathEndpointsAt mem pathsBase pPref
  post args mem _ mem' :=
    let edgesBase := args.getD 7 0
    let pathsBase := args.getD 8 0
    let descBase := args.getD 9 0
    let eAll := rawEdgesOfWalk F W flip
    let pAll := ((orientWalkSteps W flip).filter (fun x => decide (x.1 ∈ F.E))).map
      (fun x => (G0.src x, G0.dst x))
    mem' (descBase + 3) = eAll.length ∧
    ExplicitEdgesAt mem' edgesBase eAll ∧
    mem' (descBase + 5) = pAll.length ∧
    PathEndpointsAt mem' pathsBase pAll ∧
    ∀ a, ¬ splitWriteRegion edgesBase pathsBase descBase W.length a → mem' a = mem a
  cost args _ := (W.length - args.getD 10 0) * 140 + 15

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain DynSpanner.Program

/-! ## 3. Verification of `selectFillRevBody` -/

theorem selectFillRev_meetsContract {w self : ℕ} {P : List (ℕ × Bool)} {p : Program}
    (hp : p.procs[self]? = some (selectFillRevBody self)) :
    MeetsContract w p self (selectFillRevContract w P) := by
  apply meetsContract_of_rec (fun args _ => P.length - args.getD 3 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨wPtr, stepsBase, t, rfl, hw16, htLe, hMW, hwDisj, hstW, hPw, hPref⟩ := hpre
  change P.length - t = rem at hremEq
  subst hremEq
  have hwPtrW : wPtr < 2 ^ w := hwords wPtr (by simp)
  have hlenW : P.length < 2 ^ w := hwords P.length (by simp)
  have hsbW : stepsBase < 2 ^ w := hwords stepsBase (by simp)
  have htw : t < 2 ^ w := hwords t (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold selectFillRevBody
  by_cases hlt : t < P.length
  · set idx := P.length - 1 - t
    have hidxLt : idx < P.length := by omega
    obtain ⟨_, hRead⟩ := mWalkAt_read hMW
    obtain ⟨hEread, hDread⟩ := hRead idx hidxLt
    have hEword : P[idx].1 < 2 ^ w := hPw idx hidxLt
    have hDbit : (if P[idx].2 then 1 else 0) ≤ 1 := by split <;> omega
    have hFlipD : 1 - (if P[idx].2 then 1 else 0) = if !P[idx].2 then 1 else 0 := by
      cases P[idx].2 <;> simp
    have hFlipW : (if !P[idx].2 then 1 else 0) < 2 ^ w := by split <;> omega
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hlt, show 1 < 2 ^ w by omega])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_seq_assign_flat (v := idx) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := P[idx].1)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
            show wPtr + 1 < 2 ^ w by omega, show 2 * idx < 2 ^ w by omega,
            show wPtr + 1 + 2 * idx < 2 ^ w by omega, hEread]) ?_
    refine runs_seq_assign_flat (v := if !P[idx].2 then 1 else 0)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
            show wPtr + 2 < 2 ^ w by omega, show 2 * idx < 2 ^ w by omega,
            show wPtr + 2 + 2 * idx < 2 ^ w by omega, hDread]
          cases P[idx].2 <;> simp [show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega]) ?_
    refine runs_seq_assign_flat (v := t + 1) (by eval_expr) ?_
    refine runs_seq_store_flat (x := stepsBase + 2 * (t + 1)) (v := P[idx].1)
      (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_flat (x := stepsBase + 2 * (t + 1) + 1) (v := if !P[idx].2 then 1 else 0)
      (by eval_expr) (by eval_expr) ?_
    set mem1 := Function.update (Function.update mem (stepsBase + 2 * (t + 1)) P[idx].1)
      (stepsBase + 2 * (t + 1) + 1) (if !P[idx].2 then 1 else 0)
    have hm1_out (a : ℕ) (ha : a ≠ stepsBase + 2 * (t + 1)) (hb : a ≠ stepsBase + 2 * (t + 1) + 1) :
        mem1 a = mem a := by
      change Function.update (Function.update mem _ _) _ _ a = mem a
      rw [Function.update_of_ne hb, Function.update_of_ne ha]
    have hm1_e : mem1 (stepsBase + 2 * (t + 1)) = P[idx].1 := by
      change Function.update (Function.update mem _ _) _ _ _ = _
      rw [Function.update_of_ne (by omega), Function.update_self]
    have hm1_d : mem1 (stepsBase + 2 * (t + 1) + 1) = if !P[idx].2 then 1 else 0 := by
      change Function.update _ _ _ _ = _; exact Function.update_self ..
    clear_value mem1
    have hMW1 : MWalkAt mem1 wPtr P := fun j hj => by
      have hlen := mWalkEncode_length P
      exact (hm1_out _ (by omega) (by omega)).trans (hMW j hj)
    have hPref1 : ExplicitEdgesAt mem1 (stepsBase + 2) ((walkRev P).take (t + 1)) := by
      intro j hj
      have hlenRev : (walkRev P).length = P.length := by simp [walkRev]
      simp only [List.length_map, List.length_take, hlenRev] at hj
      have hjT : j < t + 1 := lt_of_lt_of_le hj (Nat.min_le_left _ _)
      have hjP : j < P.length := by omega
      simp only [List.getElem_map, List.getElem_take]
      by_cases hjeq : j = t
      · subst j
        rw [walkRev_getElem P hlt]
        exact ⟨by rw [show stepsBase + 2 + 2 * t = stepsBase + 2 * (t + 1) by omega]; exact hm1_e,
          by rw [show stepsBase + 2 + 2 * t + 1 = stepsBase + 2 * (t + 1) + 1 by omega]; exact hm1_d⟩
      · have hjLt : j < t := by omega
        have h0 := hPref.read (by rw [List.length_take, hlenRev]; omega : j < ((walkRev P).take t).length)
        simp only [List.getElem_take] at h0
        exact ⟨(hm1_out _ (by omega) (by omega)).trans h0.1,
          (hm1_out _ (by omega) (by omega)).trans h0.2⟩
    refine runs_seq_call_flat ih (vs := [wPtr, P.length, stepsBase, t + 1])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨wPtr, stepsBase, t + 1, rfl, hw16, by omega, hMW1, hwDisj, hstW, hPw, hPref1⟩,
        by change P.length - (t + 1) < P.length - t; omega⟩
    · intro ret mem2 pos2 hp2
      obtain ⟨hEd2, hfr2⟩ := hp2
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hEd2 hfr2
      refine WordRAM.runs_ret_le (v := 0) (by eval_expr) ?_ ?_
      · dsimp only [selectFillRevContract]
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        exact ⟨hEd2, fun a ha => (hfr2 a (by omega)).trans (hm1_out a (by omega) (by omega))⟩
      · simp only [Contract.below, selectFillRevContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size, argsSize]; omega
  · have hteq : t = P.length := by omega
    subst hteq
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine WordRAM.runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · dsimp only [selectFillRevContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      have htk : (walkRev P).take P.length = walkRev P := List.take_of_length_le (by simp [walkRev])
      exact ⟨htk ▸ hPref, fun _ _ => trivial⟩
    · simp only [selectFillRevContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size]; omega

/-! ## 4. Verification of `selectSplitStepsBody` -/

private lemma rawEdgesOfWalk_take_succ (F : MGraph) (W : List (ℕ × Bool)) (flip : Bool)
    {t : ℕ} (ht : t < W.length) :
    rawEdgesOfWalk F (W.take (t + 1)) flip =
      rawEdgesOfWalk F (W.take t) flip ++
        if W[t].1 ∈ F.E then [] else [(W[t].1, if flip then !W[t].2 else W[t].2)] := by
  unfold rawEdgesOfWalk orientWalkSteps
  cases flip
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [List.take_succ_eq_append_getElem ht, List.filter_append]
    by_cases h : W[t].1 ∈ F.E <;> simp [h]
  · simp only [↓reduceIte]
    rw [List.take_succ_eq_append_getElem ht, List.map_append, List.filter_append]
    by_cases h : W[t].1 ∈ F.E <;> simp [h]

private lemma treePathsOfWalk_take_succ (G0 F : MGraph) (W : List (ℕ × Bool)) (flip : Bool)
    {t : ℕ} (ht : t < W.length) :
    ((orientWalkSteps (W.take (t + 1)) flip).filter (fun x => decide (x.1 ∈ F.E))).map
        (fun x => (G0.src x, G0.dst x)) =
      (((orientWalkSteps (W.take t) flip).filter (fun x => decide (x.1 ∈ F.E))).map
        (fun x => (G0.src x, G0.dst x))) ++
      if W[t].1 ∈ F.E then
        let step := (W[t].1, if flip then !W[t].2 else W[t].2)
        [(G0.src step, G0.dst step)]
      else [] := by
  unfold orientWalkSteps
  cases flip
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [List.take_succ_eq_append_getElem ht, List.filter_append, List.map_append]
    by_cases h : W[t].1 ∈ F.E <;> simp [h]
  · simp only [↓reduceIte]
    rw [List.take_succ_eq_append_getElem ht, List.map_append, List.filter_append, List.map_append]
    by_cases h : W[t].1 ∈ F.E <;> simp [h]

theorem selectSplitSteps_meetsContract {w self : ℕ} {G0 F : MGraph} {W : List (ℕ × Bool)}
    {flip : Bool} {p : Program}
    (hp : p.procs[self]? = some (selectSplitStepsBody self)) :
    MeetsContract w p self (selectSplitStepsContract w G0 F W flip) := by
  apply meetsContract_of_rec (fun args _ => W.length - args.getD 10 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨slots, intToExt, tailSlot, headSlot, stepsBase, edgesBase, pathsBase, descBase, t,
    rfl, hw16, htLe, hWAt, hEnds, hWinfo, hdbSt, hdbEd, hedPt, hptW, hstEd, hDisj,
    heLen, hePref, hpLen, hpPref⟩ := hpre
  change W.length - t = rem at hremEq
  subst hremEq
  have hslotsW : slots < 2 ^ w := hwords slots (by simp)
  have hi2eW : intToExt < 2 ^ w := hwords intToExt (by simp)
  have htsW : tailSlot < 2 ^ w := hwords tailSlot (by simp)
  have hhsW : headSlot < 2 ^ w := hwords headSlot (by simp)
  have hsbW : stepsBase < 2 ^ w := hwords stepsBase (by simp)
  have hKW : W.length < 2 ^ w := hwords W.length (by simp)
  have hflW : (if flip then 1 else 0) < 2 ^ w := by split <;> omega
  have hedW : edgesBase < 2 ^ w := hwords edgesBase (by simp)
  have hptBaseW : pathsBase < 2 ^ w := hwords pathsBase (by simp)
  have hdbW : descBase < 2 ^ w := hwords descBase (by simp)
  have htW : t < 2 ^ w := hwords t (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold selectSplitStepsBody
  by_cases hlt : t < W.length
  · set f := W[t].1
    set dBool := W[t].2
    set dOrBool := if flip then !dBool else dBool
    set dOr : ℕ := if dOrBool then 1 else 0
    have hfMem : W[t] ∈ W := List.getElem_mem hlt
    obtain ⟨hfG0, hfFiff, hslotsF, hfW⟩ := hWinfo W[t] hfMem
    obtain ⟨hTailEq, hHeadEq, htsF, hhsF, hi2eT, hi2eH, hTailW, hHeadW⟩ := hEnds W[t] hfMem
    obtain ⟨hRdF, hRdD⟩ := hWAt.read hlt
    have hdBitW : (if dBool then 1 else 0) < 2 ^ w := by split <;> omega
    have hdOrW : dOr < 2 ^ w := by dsimp only [dOr]; split <;> omega
    have hPrefLens :
        (rawEdgesOfWalk F (W.take t) flip).length ≤ t ∧
        (((orientWalkSteps (W.take t) flip).filter (fun x => decide (x.1 ∈ F.E))).map
          (fun x => (G0.src x, G0.dst x))).length ≤ t := by
      constructor
      · exact (List.length_filter_le _ _).trans (by unfold orientWalkSteps; cases flip <;> simp [htLe])
      · rw [List.length_map]
        exact (List.length_filter_le _ _).trans (by unfold orientWalkSteps; cases flip <;> simp [htLe])
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hlt, show 1 < 2 ^ w by omega])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_seq_assign_flat (v := f)
      (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show 2 * t < 2 ^ w by omega,
            show stepsBase + 2 * t < 2 ^ w by omega, hRdF, f]) ?_
    refine runs_seq_assign_flat (v := if dBool then 1 else 0)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
            show 2 * t < 2 ^ w by omega, show stepsBase + 2 * t < 2 ^ w by omega,
            show stepsBase + 2 * t + 1 < 2 ^ w by omega, hRdD, dBool]) ?_
    -- Continuation after `.cond (.reg 6)` (orienting `d` into `dOr`)
    have hAfterOrient : ∀ (regs1 : ℕ → ℕ) (k0 : ℕ),
        regs1 0 = slots → regs1 1 = intToExt → regs1 2 = tailSlot → regs1 3 = headSlot →
        regs1 4 = stepsBase → regs1 5 = W.length → regs1 6 = (if flip then 1 else 0) →
        regs1 7 = edgesBase → regs1 8 = pathsBase → regs1 9 = descBase → regs1 10 = t →
        regs1 11 = f → regs1 12 = dOr →
        k0 + (W.length - (t + 1)) * 140 + 120 ≤ (W.length - t) * 140 + 15 →
        ∃ o st' c, Runs w p ω
          (.assign 13 (.load (.bin .add (.reg 0) (.reg 11))) ;;
           .cond (.bin .eq (.reg 13) (.const 0))
             (.assign 14 (.load (.bin .add (.reg 9) (.const 3))) ;;
              .store (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 14))) (.reg 11) ;;
              .store (.bin .add (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 14))) (.const 1)) (.reg 12) ;;
              .store (.bin .add (.reg 9) (.const 3)) (.bin .add (.reg 14) (.const 1)))
             (.assign 14 (.load (.bin .add (.reg 9) (.const 5))) ;;
              .assign 15 (.load (.bin .add (.reg 1) (.load (.bin .add (.reg 2) (.reg 11))))) ;;
              .assign 16 (.load (.bin .add (.reg 1) (.load (.bin .add (.reg 3) (.reg 11))))) ;;
              .cond (.reg 12)
                (.store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 14))) (.reg 15) ;;
                 .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 14))) (.const 1)) (.reg 16))
                (.store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 14))) (.reg 16) ;;
                 .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 14))) (.const 1)) (.reg 15)) ;;
              .store (.bin .add (.reg 9) (.const 5)) (.bin .add (.reg 14) (.const 1))) ;;
           .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
             .bin .add (.reg 10) (.const 1)] ;;
           .ret (.const 0))
          ⟨mem, regs1, pos⟩ o st' c ∧
          (selectSplitStepsContract w G0 F W flip).post
            [slots, intToExt, tailSlot, headSlot, stepsBase, W.length,
              (if flip then 1 else 0), edgesBase, pathsBase, descBase, t] mem o.value st'.mem ∧
          k0 + c ≤ (selectSplitStepsContract w G0 F W flip).cost
            [slots, intToExt, tailSlot, headSlot, stepsBase, W.length,
              (if flip then 1 else 0), edgesBase, pathsBase, descBase, t] mem := by
      intro regs1 k0 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hk0
      refine runs_seq_assign_flat (v := mem (slots + f))
        (by simp [Expr.eval, BinOp.eval, hr0, hr11, f, hslotsF]) ?_
      -- Shared continuation after branching on `mem (slots + f) = 0`
      have hAfterStep : ∀ (mem1 : ℕ → ℕ) (regs2 : ℕ → ℕ) (k1 : ℕ),
          regs2 0 = slots → regs2 1 = intToExt → regs2 2 = tailSlot → regs2 3 = headSlot →
          regs2 4 = stepsBase → regs2 5 = W.length → regs2 6 = (if flip then 1 else 0) →
          regs2 7 = edgesBase → regs2 8 = pathsBase → regs2 9 = descBase → regs2 10 = t →
          (∀ a, ¬ splitWriteRegion edgesBase pathsBase descBase W.length a → mem1 a = mem a) →
          mem1 (descBase + 3) = (rawEdgesOfWalk F (W.take (t + 1)) flip).length →
          ExplicitEdgesAt mem1 edgesBase (rawEdgesOfWalk F (W.take (t + 1)) flip) →
          mem1 (descBase + 5) =
            (((orientWalkSteps (W.take (t + 1)) flip).filter (fun x => decide (x.1 ∈ F.E))).map
              (fun x => (G0.src x, G0.dst x))).length →
          PathEndpointsAt mem1 pathsBase
            (((orientWalkSteps (W.take (t + 1)) flip).filter (fun x => decide (x.1 ∈ F.E))).map
              (fun x => (G0.src x, G0.dst x))) →
          k1 + (W.length - (t + 1)) * 140 + 32 ≤ (W.length - t) * 140 + 15 →
          ∃ o st' c, Runs w p ω
            (.call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
              .bin .add (.reg 10) (.const 1)] ;;
             .ret (.const 0))
            ⟨mem1, regs2, pos⟩ o st' c ∧
            (selectSplitStepsContract w G0 F W flip).post
              [slots, intToExt, tailSlot, headSlot, stepsBase, W.length,
                (if flip then 1 else 0), edgesBase, pathsBase, descBase, t] mem o.value st'.mem ∧
            k1 + c ≤ (selectSplitStepsContract w G0 F W flip).cost
              [slots, intToExt, tailSlot, headSlot, stepsBase, W.length,
                (if flip then 1 else 0), edgesBase, pathsBase, descBase, t] mem := by
        intro mem1 regs2 k1 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 hfr1 heL1 heA1 hpL1 hpA1 hk1
        have hWAt1 : ExplicitEdgesAt mem1 stepsBase W :=
          hWAt.congr fun x hx1 hx2 => hfr1 x (by unfold splitWriteRegion; omega)
        have hm1_read (x : ℕ × Bool) (hx : x ∈ W) :
            mem1 (slots + x.1) = mem (slots + x.1) ∧
            mem1 (tailSlot + x.1) = mem (tailSlot + x.1) ∧
            mem1 (headSlot + x.1) = mem (headSlot + x.1) ∧
            mem1 (intToExt + mem (tailSlot + x.1)) = mem (intToExt + mem (tailSlot + x.1)) ∧
            mem1 (intToExt + mem (headSlot + x.1)) = mem (intToExt + mem (headSlot + x.1)) := by
          refine ⟨hfr1 _ fun hr => (hDisj _ hr x hx).1 rfl,
            hfr1 _ fun hr => (hDisj _ hr x hx).2.1 rfl,
            hfr1 _ fun hr => (hDisj _ hr x hx).2.2.1 rfl,
            hfr1 _ fun hr => (hDisj _ hr x hx).2.2.2.1 rfl,
            hfr1 _ fun hr => (hDisj _ hr x hx).2.2.2.2 rfl⟩
        refine runs_seq_call_flat ih
          (vs := [slots, intToExt, tailSlot, headSlot, stepsBase, W.length,
            (if flip then 1 else 0), edgesBase, pathsBase, descBase, t + 1])
          (by simp [evalArgs, Expr.eval, BinOp.eval, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
                show 1 < 2 ^ w by omega, show t + 1 < 2 ^ w by omega])
          (by wram_words) ?_ ?_
        · refine ⟨⟨slots, intToExt, tailSlot, headSlot, stepsBase, edgesBase, pathsBase, descBase,
            t + 1, rfl, hw16, by omega, hWAt1, fun x hx => ?_, fun x hx => ?_,
            hdbSt, hdbEd, hedPt, hptW, hstEd, fun a ha x hx => ?_, heL1, heA1, hpL1, hpA1⟩,
            by change W.length - (t + 1) < W.length - t; omega⟩
          · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hEnds x hx
            have hr := hm1_read x hx
            rw [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
            exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩
          · obtain ⟨a1, a2, a3, a4⟩ := hWinfo x hx
            exact ⟨a1, by rw [(hm1_read x hx).1]; exact a2, a3, a4⟩
          · obtain ⟨b1, b2, b3, b4, b5⟩ := hDisj a ha x hx
            rw [(hm1_read x hx).2.1, (hm1_read x hx).2.2.1]
            exact ⟨b1, b2, b3, b4, b5⟩
        · intro ret mem2 pos2 hp2
          obtain ⟨heL2, heA2, hpL2, hpA2, hfr2⟩ := hp2
          simp only [List.getD_cons_zero, List.getD_cons_succ] at heL2 heA2 hpL2 hpA2 hfr2
          refine WordRAM.runs_ret_le (v := 0) (by eval_expr) ?_ ?_
          · dsimp only [selectSplitStepsContract]
            simp only [List.getD_cons_zero, List.getD_cons_succ]
            exact ⟨heL2, heA2, hpL2, hpA2, fun a ha => (hfr2 a ha).trans (hfr1 a ha)⟩
          · simp only [Contract.below, selectSplitStepsContract, List.getD_cons_zero,
              List.getD_cons_succ, Expr.size, argsSize]; omega
      by_cases hfF : f ∈ F.E
      · -- Tree edge (`mem (slots + f) ≠ 0`): emit single-edge tree path `(src, dst)`
        have hslotNZ : mem (slots + f) ≠ 0 := hfFiff.mp hfF
        set pCnt := (((orientWalkSteps (W.take t) flip).filter (fun x => decide (x.1 ∈ F.E))).map
          (fun x => (G0.src x, G0.dst x))).length
        have hpCntLe : pCnt ≤ t := hPrefLens.2
        refine WordRAM.runs_seq_cond_le (v := 0)
          (by simp [Expr.eval, BinOp.eval, hslotNZ, show 0 < 2 ^ w by omega])
          (fun h => absurd rfl h) ?_
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := pCnt)
          (by simp [Expr.eval, BinOp.eval, hr9, show 5 < 2 ^ w by omega, show descBase + 5 < 2 ^ w by omega, hpLen, pCnt]) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := G0.tail f)
          (by simp [Expr.eval, BinOp.eval, hr1, hr2, hr11, f, htsF, hi2eT, hTailEq]) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := G0.head f)
          (by simp [Expr.eval, BinOp.eval, hr1, hr3, hr11, f, hhsF, hi2eH, hHeadEq]) ?_
        have hPostPair : ∀ (u v : ℕ) (hu : u = G0.src (f, dOrBool)) (hv : v = G0.dst (f, dOrBool))
            (mem1 : ℕ → ℕ) (regs2 : ℕ → ℕ) (k1 : ℕ),
            regs2 0 = slots → regs2 1 = intToExt → regs2 2 = tailSlot → regs2 3 = headSlot →
            regs2 4 = stepsBase → regs2 5 = W.length → regs2 6 = (if flip then 1 else 0) →
            regs2 7 = edgesBase → regs2 8 = pathsBase → regs2 9 = descBase → regs2 10 = t →
            regs2 14 = pCnt →
            mem1 = Function.update (Function.update mem (pathsBase + 2 * pCnt) u) (pathsBase + 2 * pCnt + 1) v →
            k1 + (W.length - (t + 1)) * 140 + 42 ≤ (W.length - t) * 140 + 15 →
            ∃ o st' c, Runs w p ω
              (.store (.bin .add (.reg 9) (.const 5)) (.bin .add (.reg 14) (.const 1)) ;;
               .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
                 .bin .add (.reg 10) (.const 1)] ;;
               .ret (.const 0))
              ⟨mem1, regs2, pos⟩ o st' c ∧
              (selectSplitStepsContract w G0 F W flip).post
                [slots, intToExt, tailSlot, headSlot, stepsBase, W.length,
                  (if flip then 1 else 0), edgesBase, pathsBase, descBase, t] mem o.value st'.mem ∧
              k1 + c ≤ (selectSplitStepsContract w G0 F W flip).cost
                [slots, intToExt, tailSlot, headSlot, stepsBase, W.length,
                  (if flip then 1 else 0), edgesBase, pathsBase, descBase, t] mem := by
          intro u v hu hv mem1 regs2 k1 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r14 hmem1 hk1
          refine runs_seq_store_flat (x := descBase + 5) (v := pCnt + 1)
            (by simp [Expr.eval, BinOp.eval, r9, show 5 < 2 ^ w by omega, show descBase + 5 < 2 ^ w by omega])
            (by simp [Expr.eval, BinOp.eval, r14, show 1 < 2 ^ w by omega, show pCnt + 1 < 2 ^ w by omega]) ?_
          set mem2 := Function.update mem1 (descBase + 5) (pCnt + 1)
          have hfr2 : ∀ a, ¬ splitWriteRegion edgesBase pathsBase descBase W.length a → mem2 a = mem a := by
            intro a ha
            have hne5 : a ≠ descBase + 5 := fun h => ha (Or.inr (Or.inr (Or.inr h)))
            have hneP0 : a ≠ pathsBase + 2 * pCnt := fun h => ha (Or.inr (Or.inl ⟨by omega, by omega⟩))
            have hneP1 : a ≠ pathsBase + 2 * pCnt + 1 := fun h => ha (Or.inr (Or.inl ⟨by omega, by omega⟩))
            change Function.update mem1 _ _ a = mem a
            rw [Function.update_of_ne hne5, hmem1, Function.update_of_ne hneP1, Function.update_of_ne hneP0]
          have hm2_e3 : mem2 (descBase + 3) = (rawEdgesOfWalk F (W.take (t + 1)) flip).length := by
            rw [rawEdgesOfWalk_take_succ F W flip hlt, ite_eq_left hfF, List.append_nil]
            change Function.update mem1 _ _ _ = _
            rw [Function.update_of_ne (by omega), hmem1, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), heLen]
          have hm2_eAt : ExplicitEdgesAt mem2 edgesBase (rawEdgesOfWalk F (W.take (t + 1)) flip) := by
            rw [rawEdgesOfWalk_take_succ F W flip hlt, ite_eq_left hfF, List.append_nil]
            exact hePref.congr fun x hx1 hx2 => by
              change Function.update mem1 _ _ x = mem x
              rw [Function.update_of_ne (by omega), hmem1, Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
          have hm2_p5 : mem2 (descBase + 5) =
              (((orientWalkSteps (W.take (t + 1)) flip).filter (fun x => decide (x.1 ∈ F.E))).map
                (fun x => (G0.src x, G0.dst x))).length := by
            rw [treePathsOfWalk_take_succ G0 F W flip hlt, ite_eq_left hfF, List.length_append]
            change Function.update mem1 _ _ _ = _
            rw [Function.update_self]; rfl
          have hm2_pAt : PathEndpointsAt mem2 pathsBase
              (((orientWalkSteps (W.take (t + 1)) flip).filter (fun x => decide (x.1 ∈ F.E))).map
                (fun x => (G0.src x, G0.dst x))) := by
            rw [treePathsOfWalk_take_succ G0 F W flip hlt, ite_eq_left hfF]
            dsimp only
            intro j hj
            rw [List.length_append, List.length_singleton] at hj
            by_cases hjEq : j = pCnt
            · subst j
              have hsub0 : pCnt - (((orientWalkSteps (W.take t) flip).filter (fun x => decide (x.1 ∈ F.E))).map
                (fun x => (G0.src x, G0.dst x))).length = 0 := Nat.sub_self pCnt
              simp only [List.getElem_append_right (le_refl pCnt), hsub0, List.getElem_cons_zero]
              change Function.update mem1 _ _ _ = _ ∧ Function.update mem1 _ _ _ = _
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hmem1,
                Function.update_of_ne (by omega), Function.update_self, Function.update_self]
              exact ⟨hu, hv⟩
            · have hjLt : j < pCnt := by omega
              simp only [List.getElem_append_left hjLt]
              have h0 := hpPref j hjLt
              change Function.update mem1 _ _ _ = _ ∧ Function.update mem1 _ _ _ = _
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hmem1,
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact h0
          exact hAfterStep mem2 _ _ (by simp [r0]) (by simp [r1]) (by simp [r2]) (by simp [r3])
            (by simp [r4]) (by simp [r5]) (by simp [r6]) (by simp [r7]) (by simp [r8]) (by simp [r9])
            (by simp [r10]) hfr2 hm2_e3 hm2_eAt hm2_p5 hm2_pAt (by simp [Expr.size]; omega)
        cases hdB : dOrBool
        · refine runs_seq_assoc_le ?_
          refine WordRAM.runs_seq_cond_le (v := 0)
            (by simp [Expr.eval, hr12, dOr, hdB]) (fun h => absurd rfl h) ?_
          intro _
          refine runs_seq_assoc_le ?_
          refine runs_seq_store_flat (x := pathsBase + 2 * pCnt) (v := G0.head f)
            (by simp [Expr.eval, BinOp.eval, hr8, show 2 < 2 ^ w by omega, show 2 * pCnt < 2 ^ w by omega,
                  show pathsBase + 2 * pCnt < 2 ^ w by omega])
            (by eval_expr) ?_
          refine runs_seq_store_flat (x := pathsBase + 2 * pCnt + 1) (v := G0.tail f)
            (by simp [Expr.eval, BinOp.eval, hr8, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
                  show 2 * pCnt < 2 ^ w by omega, show pathsBase + 2 * pCnt < 2 ^ w by omega,
                  show pathsBase + 2 * pCnt + 1 < 2 ^ w by omega])
            (by eval_expr) ?_
          exact hPostPair (G0.head f) (G0.tail f) (by simp [MGraph.src, hdB]) (by simp [MGraph.dst, hdB])
            _ _ _ (by simp [hr0]) (by simp [hr1]) (by simp [hr2]) (by simp [hr3])
            (by simp [hr4]) (by simp [hr5]) (by simp [hr6]) (by simp [hr7]) (by simp [hr8])
            (by simp [hr9]) (by simp [hr10]) (by simp) rfl (by simp [Expr.size]; omega)
        · refine runs_seq_assoc_le ?_
          refine WordRAM.runs_seq_cond_le (v := 1)
            (by simp [Expr.eval, hr12, dOr, hdB]) ?_ (fun h => absurd h (by decide))
          intro _
          refine runs_seq_assoc_le ?_
          refine runs_seq_store_flat (x := pathsBase + 2 * pCnt) (v := G0.tail f)
            (by simp [Expr.eval, BinOp.eval, hr8, show 2 < 2 ^ w by omega, show 2 * pCnt < 2 ^ w by omega,
                  show pathsBase + 2 * pCnt < 2 ^ w by omega])
            (by eval_expr) ?_
          refine runs_seq_store_flat (x := pathsBase + 2 * pCnt + 1) (v := G0.head f)
            (by simp [Expr.eval, BinOp.eval, hr8, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
                  show 2 * pCnt < 2 ^ w by omega, show pathsBase + 2 * pCnt < 2 ^ w by omega,
                  show pathsBase + 2 * pCnt + 1 < 2 ^ w by omega])
            (by eval_expr) ?_
          exact hPostPair (G0.tail f) (G0.head f) (by simp [MGraph.src, hdB]) (by simp [MGraph.dst, hdB])
            _ _ _ (by simp [hr0]) (by simp [hr1]) (by simp [hr2]) (by simp [hr3])
            (by simp [hr4]) (by simp [hr5]) (by simp [hr6]) (by simp [hr7]) (by simp [hr8])
            (by simp [hr9]) (by simp [hr10]) (by simp) rfl (by simp [Expr.size]; omega)
      · -- Off-tree edge (`mem (slots + f) = 0`): emit `(f, dOr)` into `edgesBase`
        have hslot0 : mem (slots + f) = 0 := by
          by_contra hnz; exact hfF (hfFiff.mpr hnz)
        set eCnt := (rawEdgesOfWalk F (W.take t) flip).length
        have heCntLe : eCnt ≤ t := hPrefLens.1
        refine WordRAM.runs_seq_cond_le (v := 1)
          (by simp [Expr.eval, BinOp.eval, hslot0, show 1 < 2 ^ w by omega])
          ?_ (fun h => absurd h (by decide))
        intro _
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := eCnt)
          (by simp [Expr.eval, BinOp.eval, hr9, show 3 < 2 ^ w by omega, show descBase + 3 < 2 ^ w by omega, heLen, eCnt]) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_store_flat (x := edgesBase + 2 * eCnt) (v := f)
          (by simp [Expr.eval, BinOp.eval, hr7, show 2 < 2 ^ w by omega, show 2 * eCnt < 2 ^ w by omega,
                show edgesBase + 2 * eCnt < 2 ^ w by omega])
          (by simp [Expr.eval, hr11]) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_store_flat (x := edgesBase + 2 * eCnt + 1) (v := dOr)
          (by simp [Expr.eval, BinOp.eval, hr7, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
                show 2 * eCnt < 2 ^ w by omega, show edgesBase + 2 * eCnt < 2 ^ w by omega,
                show edgesBase + 2 * eCnt + 1 < 2 ^ w by omega])
          (by simp [Expr.eval, hr12]) ?_
        refine runs_seq_store_flat (x := descBase + 3) (v := eCnt + 1)
          (by simp [Expr.eval, BinOp.eval, hr9, show 3 < 2 ^ w by omega, show descBase + 3 < 2 ^ w by omega])
          (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, show eCnt + 1 < 2 ^ w by omega]) ?_
        set mem1 := Function.update (Function.update (Function.update mem (edgesBase + 2 * eCnt) f)
          (edgesBase + 2 * eCnt + 1) dOr) (descBase + 3) (eCnt + 1)
        have hfr1 : ∀ a, ¬ splitWriteRegion edgesBase pathsBase descBase W.length a → mem1 a = mem a := by
          intro a ha
          have hne3 : a ≠ descBase + 3 := fun h => ha (Or.inr (Or.inr (Or.inl h)))
          have hneE0 : a ≠ edgesBase + 2 * eCnt := fun h => ha (Or.inl ⟨by omega, by omega⟩)
          have hneE1 : a ≠ edgesBase + 2 * eCnt + 1 := fun h => ha (Or.inl ⟨by omega, by omega⟩)
          change Function.update (Function.update (Function.update mem _ _) _ _) _ _ a = mem a
          rw [Function.update_of_ne hne3, Function.update_of_ne hneE1, Function.update_of_ne hneE0]
        have hm1_e3 : mem1 (descBase + 3) = (rawEdgesOfWalk F (W.take (t + 1)) flip).length := by
          rw [rawEdgesOfWalk_take_succ F W flip hlt, ite_eq_right hfF, List.length_append]
          change Function.update _ _ _ _ = _; rw [Function.update_self]; rfl
        have hm1_eAt : ExplicitEdgesAt mem1 edgesBase (rawEdgesOfWalk F (W.take (t + 1)) flip) := by
          rw [rawEdgesOfWalk_take_succ F W flip hlt, ite_eq_right hfF]
          intro j hj
          simp only [List.length_map, List.length_append, List.length_singleton] at hj
          simp only [List.getElem_map]
          by_cases hjEq : j = eCnt
          · subst j
            have hsub0 : eCnt - (rawEdgesOfWalk F (W.take t) flip).length = 0 := Nat.sub_self eCnt
            simp only [List.getElem_append_right (le_refl eCnt), hsub0, List.getElem_cons_zero]
            change Function.update (Function.update (Function.update mem _ _) _ _) _ _ _ = _ ∧
              Function.update (Function.update (Function.update mem _ _) _ _) _ _ _ = _
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self, Function.update_of_ne (by omega), Function.update_self]
            exact ⟨rfl, rfl⟩
          · have hjLt : j < eCnt := by omega
            simp only [List.getElem_append_left hjLt]
            have h0 := hePref.read hjLt
            change Function.update (Function.update (Function.update mem _ _) _ _) _ _ _ = _ ∧
              Function.update (Function.update (Function.update mem _ _) _ _) _ _ _ = _
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact h0
        have hm1_p5 : mem1 (descBase + 5) =
            (((orientWalkSteps (W.take (t + 1)) flip).filter (fun x => decide (x.1 ∈ F.E))).map
              (fun x => (G0.src x, G0.dst x))).length := by
          rw [treePathsOfWalk_take_succ G0 F W flip hlt, ite_eq_right hfF, List.append_nil]
          change Function.update (Function.update (Function.update mem _ _) _ _) _ _ _ = _
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), hpLen]
        have hm1_pAt : PathEndpointsAt mem1 pathsBase
            (((orientWalkSteps (W.take (t + 1)) flip).filter (fun x => decide (x.1 ∈ F.E))).map
              (fun x => (G0.src x, G0.dst x))) := by
          rw [treePathsOfWalk_take_succ G0 F W flip hlt, ite_eq_right hfF, List.append_nil]
          intro j hj
          have h0 := hpPref j hj
          change Function.update (Function.update (Function.update mem _ _) _ _) _ _ _ = _ ∧
            Function.update (Function.update (Function.update mem _ _) _ _) _ _ _ = _
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact h0
        exact hAfterStep mem1 _ _ (by simp [hr0]) (by simp [hr1]) (by simp [hr2]) (by simp [hr3])
          (by simp [hr4]) (by simp [hr5]) (by simp [hr6]) (by simp [hr7]) (by simp [hr8])
          (by simp [hr9]) (by simp [hr10]) hfr1 hm1_e3 hm1_eAt hm1_p5 hm1_pAt (by simp [Expr.size]; omega)
    cases hfl : flip
    · refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval]) (fun h => absurd rfl h) ?_
      intro _
      refine runs_seq_nop_le ?_
      rw [hfl] at hAfterOrient
      apply hAfterOrient
      all_goals first | (simp [dOr, dOrBool, hfl]; done) | (simp [Expr.size]; omega)
    · refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval]) ?_ (fun h => absurd h (by decide))
      intro _
      refine runs_seq_assign_flat (v := dOr)
        (by cases hdb : W[t].2 <;>
            simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega,
              dOr, dOrBool, dBool, hfl, hdb]) ?_
      rw [hfl] at hAfterOrient
      apply hAfterOrient
      all_goals first | (simp; done) | (simp [Expr.size]; omega)
  · have hteq : t = W.length := by omega
    subst hteq
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine WordRAM.runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · dsimp only [selectSplitStepsContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [List.take_of_length_le le_rfl] at heLen hePref hpLen hpPref
      exact ⟨heLen, hePref, hpLen, hpPref, fun _ _ => trivial⟩
    · simp only [selectSplitStepsContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size]; omega

end MinCostFlow.MinRatio
