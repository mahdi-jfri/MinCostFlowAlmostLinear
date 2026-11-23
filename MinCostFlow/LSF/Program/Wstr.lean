module

public import MinCostFlow.LSF.Program.WstrPrep
public import MinCostFlow.LSF.Program.WstrThresh
public import MinCostFlow.LSF.Program.WstrOut
public import MinCostFlow.LSF.Program.LevelLoop

/-!
# The stretch pass

`wstrProc` computes the stretch overestimates `wstr` of all edges of `G₀` in the `WstrAt`
layout, and the flags of the high edges. It runs

1. `threshProc`: the threshold block `θ`, the block `2 H` and the number of levels `H`;
2. `wstrPrepProc`: the identity array, the tree-edge lengths, the weighted depths, the tree
   distances `duv` and zero accumulators;
3. `levelsProc`: the `H` levels, which add the level distances to the accumulators;
4. `blkExtLoopProc`: the edge lengths `ℓ_int`, widened to `LB` limbs;
5. `wstrOutProc`: the numerators, denominators and flags.

The contract states the result in memory terms (`WstrPost`): a snapshot `mem₀` of the memory
before the levels, with the facts of `wstrPrepProc`, the level roots and the accumulators, and the
output of each edge. `Wstr*Bridge.lean` turns this into `WstrAt` for the model's `wstr`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-- Args (`43`): `[n, tM, m0, k, LB, Lw, Lin, nOrig, r, logCap, lenArr, fidPtr, qPtr, parPtr,
    pePtr, piPtr, thDepPtr, euPtr, evPtr, upPtr, depPtr, eList, numPtr, denPtr, idPtr, ltBase,
    ldBase, duvBase, inRPtr, mpPtr, ownPtr, rtPtr, dRBase, accBase, leBase, k2Out, thOut, tA, tB,
    tF, tmp1, tmp2, highPtr]`.
Register `43` is the number of levels `H`, register `44` the result of the other calls. -/
def wstrProc (bTh bPrep bLev bExt bOut : ℕ) : Stmt :=
  .call 43 bTh [.reg 0, .reg 3, .reg 4, .reg 36, .reg 35, .reg 37, .reg 38, .reg 39] ;;
  .call 44 bPrep [.reg 0, .reg 1, .reg 2, .reg 24, .reg 25, .reg 26, .reg 27, .reg 33, .reg 4,
    .reg 10, .reg 11, .reg 6, .reg 7, .reg 12, .reg 13, .reg 14, .reg 17, .reg 18, .reg 9,
    .reg 19, .reg 20, .reg 8] ;;
  .call 44 bLev [.reg 43, .reg 0, .reg 12, .reg 13, .reg 14, .reg 15, .reg 16, .reg 28, .reg 29,
    .reg 30, .reg 31, .reg 1, .reg 8, .reg 2, .reg 17, .reg 18, .reg 26, .reg 27, .reg 33, .reg 4,
    .reg 24, .reg 32, .reg 9, .reg 19, .reg 20] ;;
  .call 44 bExt [.reg 2, .reg 34, .reg 4, .reg 10, .reg 21, .reg 6, .reg 2] ;;
  .call 44 bOut [.reg 2, .reg 21, .reg 22, .reg 23, .reg 33, .reg 34, .reg 36, .reg 35, .reg 40,
    .reg 41, .reg 4, .reg 5, .reg 42] ;;
  .ret (.const 0)

lemma wstrProc_noRand (bTh bPrep bLev bExt bOut : ℕ) :
    (wstrProc bTh bPrep bLev bExt bOut).NoRand := by
  simp [wstrProc, Stmt.NoRand]

/-- The inputs and the layout of `wstrProc`. The inputs lie below `numPtr`; then come the two
output arrays, the scratch arrays in the order of the arguments, and the flags. -/
def WstrPre (w h C : ℕ) (mem : ℕ → ℕ)
    (n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr piPtr thDepPtr euPtr evPtr
    upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase inRPtr mpPtr ownPtr rtPtr dRBase
    accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr : ℕ) :
    Prop :=
  16 ≤ 2 ^ w ∧ 0 < n ∧ 1 ≤ Lin ∧ Lin ≤ Lw ∧ Lw ≤ LB ∧ nOrig ≤ tM ∧ r < n ∧
  C < capacity h LB ∧ 2 * (hldDepthBound n + 1) < 2 ^ w ∧ n + 2 < 2 ^ w ∧
  (∃ (Q : List ℕ) (tl hd dep : ℕ → ℕ), TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧
    ListAt mem qPtr Q ∧
    RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x)) dep ∧
    LcaTables w n logCap upPtr depPtr parPtr (fun x => mem (parPtr + x)) dep mem) ∧
  mem (thDepPtr + r) = 0 ∧
  (∀ i < nOrig, Valid mem (lenArr + mem (fidPtr + i) * Lin) h Lin ∧
    lenArr + mem (fidPtr + i) * Lin + LB ≤ numPtr) ∧
  (∀ t < m0, Valid mem (lenArr + mem (eList + t) * Lin) h Lin ∧
    lenArr + mem (eList + t) * Lin + LB ≤ numPtr) ∧
  lenArr + LB ≤ numPtr ∧
  (∀ t < m0, mem (euPtr + t) < n ∧ mem (evPtr + t) < n) ∧
  (∃ eCap, (∀ t < m0, mem (eList + t) < eCap) ∧
    (∀ t < m0, ∀ t' < m0, mem (eList + t) = mem (eList + t') → t = t') ∧
    numPtr + eCap * Lw ≤ denPtr ∧ denPtr + eCap * Lw ≤ idPtr) ∧
  fidPtr + tM ≤ numPtr ∧ qPtr + n ≤ numPtr ∧ parPtr + n ≤ numPtr ∧ pePtr + n ≤ numPtr ∧
  piPtr + tM ≤ numPtr ∧ thDepPtr + n ≤ numPtr ∧ euPtr + m0 ≤ numPtr ∧ evPtr + m0 ≤ numPtr ∧
  upPtr + n * logCap ≤ numPtr ∧ depPtr + n ≤ numPtr ∧ eList + m0 ≤ numPtr ∧
  idPtr + n ≤ ltBase ∧ ltBase + tM * LB ≤ ldBase ∧ ldBase + n * LB ≤ duvBase ∧
  duvBase + m0 * LB ≤ inRPtr ∧ inRPtr + n ≤ mpPtr ∧ mpPtr + n ≤ ownPtr ∧ ownPtr + tM ≤ rtPtr ∧
  rtPtr + n ≤ dRBase ∧ dRBase + n * LB ≤ accBase ∧ accBase + m0 * LB ≤ leBase ∧
  leBase + m0 * LB ≤ k2Out ∧ k2Out + LB ≤ thOut ∧ thOut + LB ≤ tA ∧ tA + LB ≤ tB ∧
  tB + LB ≤ tF ∧ tF + LB ≤ tmp1 ∧ tmp1 + LB ≤ tmp2 ∧ tmp2 + LB ≤ highPtr ∧ highPtr + m0 < 2 ^ w

/-- What `wstrProc` leaves in memory `mem'`. The snapshot `mem₀` is the memory before the levels:
it agrees with `mem` on the inputs and holds the arrays of `wstrPrepProc`. -/
def WstrPost (w h C : ℕ) (mem mem' : ℕ → ℕ)
    (n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr piPtr thDepPtr euPtr evPtr
    upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase inRPtr mpPtr ownPtr rtPtr dRBase
    accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr : ℕ) :
    Prop :=
  ∃ mem₀ : ℕ → ℕ, (∀ a, a < idPtr → mem₀ a = mem a) ∧
    WstrPrepOut w h mem mem₀ n tM m0 idPtr ltBase ldBase duvBase accBase LB lenArr fidPtr Lin
      nOrig qPtr parPtr pePtr euPtr evPtr logCap upPtr depPtr r ∧
    (∃ rts lxs : ℕ → ℕ → ℕ,
      (∀ j < hldDepthBound n + 1, LevelRt n tM r (fun x => mem₀ (parPtr + x))
        (fun x => mem₀ (pePtr + x)) (fun i => mem₀ (piPtr + i)) (levelFlag mem₀ thDepPtr j)
        (rts j)) ∧
      (∀ (tl hd dep : ℕ → ℕ),
        RootedArrays n tM r tl hd (fun x => mem₀ (parPtr + x)) (fun x => mem₀ (pePtr + x)) dep →
        LcaTables w n logCap upPtr depPtr parPtr (fun x => mem₀ (parPtr + x)) dep mem₀ →
        ∀ j < hldDepthBound n + 1, ∀ x < n,
          lxs j x < n ∧ IsLcaOf (fun y => mem₀ (parPtr + y)) dep (lxs j x) x (rts j x)) ∧
      ∀ t < m0, unsignedVal mem' (accBase + t * LB) h LB =
        accFold h LB mem₀ euPtr evPtr ldBase duvBase accBase rts lxs t (hldDepthBound n + 1)) ∧
    (∀ t < m0, unsignedVal mem' (leBase + t * LB) h LB =
      unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin) ∧
    unsignedVal mem' thOut h LB = threshProd C n k % capacity h LB ∧
    unsignedVal mem' k2Out h LB = 2 * (hldDepthBound n + 1) % capacity h LB ∧
    (∀ a, a < idPtr → (∀ t < m0, (a < numPtr + mem (eList + t) * Lw ∨
        numPtr + mem (eList + t) * Lw + Lw ≤ a) ∧ (a < denPtr + mem (eList + t) * Lw ∨
        denPtr + mem (eList + t) * Lw + Lw ≤ a)) → mem' a = mem a) ∧
    (∀ a, highPtr + m0 ≤ a → mem' a = mem a) ∧
    ∀ t < m0, WstrEdgeOut h LB Lw mem' mem' (numPtr + mem (eList + t) * Lw)
      (denPtr + mem (eList + t) * Lw) (accBase + t * LB) (leBase + t * LB) thOut k2Out
      (mem' (highPtr + t))

/-- The cost of `wstrProc`, with `H = hldDepthBound n + 1` levels. -/
def wstrCost (n tM m0 LB logCap : ℕ) : ℕ :=
  (hldDepthBound n + 1) * (400 * n + 30 * tM + n * (100 * logCap + 400 * LB + 400) +
    m0 * (150 * LB + 160) + 600) +
  m0 * (200 * LB * LB + 1100 * LB + 100 * logCap + 1200) + n * (200 * LB + 300) +
  tM * (30 * LB + 80) + 500 * LB * LB + 1000 * LB + 40 * Nat.log 2 (n + 2) + 2000

/-- The contract of `wstrProc` for the constant `C`. -/
def wstrContract (w h C : ℕ) : Contract where
  pre args mem := ∃ (n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr piPtr
      thDepPtr euPtr evPtr upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase inRPtr
      mpPtr ownPtr rtPtr dRBase accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr : ℕ),
    args = [n, tM, m0, k, LB, Lw, Lin, nOrig, r, logCap, lenArr, fidPtr, qPtr, parPtr, pePtr,
      piPtr, thDepPtr, euPtr, evPtr, upPtr, depPtr, eList, numPtr, denPtr, idPtr, ltBase, ldBase,
      duvBase, inRPtr, mpPtr, ownPtr, rtPtr, dRBase, accBase, leBase, k2Out, thOut, tA, tB, tF,
      tmp1, tmp2, highPtr] ∧
    WstrPre w h C mem n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr piPtr
      thDepPtr euPtr evPtr upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase inRPtr
      mpPtr ownPtr rtPtr dRBase accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr
  post args mem ret mem' := ∃ (n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr
      piPtr thDepPtr euPtr evPtr upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase
      inRPtr mpPtr ownPtr rtPtr dRBase accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr : ℕ),
    args = [n, tM, m0, k, LB, Lw, Lin, nOrig, r, logCap, lenArr, fidPtr, qPtr, parPtr, pePtr,
      piPtr, thDepPtr, euPtr, evPtr, upPtr, depPtr, eList, numPtr, denPtr, idPtr, ltBase, ldBase,
      duvBase, inRPtr, mpPtr, ownPtr, rtPtr, dRBase, accBase, leBase, k2Out, thOut, tA, tB, tF,
      tmp1, tmp2, highPtr] ∧ ret = 0 ∧
    WstrPost w h C mem mem' n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr
      piPtr thDepPtr euPtr evPtr upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase
      inRPtr mpPtr ownPtr rtPtr dRBase accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr
  cost args _ := wstrCost (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 4 0)
    (args.getD 9 0)

/-- The tree inputs move to a memory that agrees below a bound `B` above all of them. -/
lemma treeIn_transfer {w n tM r logCap qPtr parPtr pePtr upPtr depPtr B : ℕ} {mem mem' : ℕ → ℕ}
    {Q : List ℕ} {tl hd dep : ℕ → ℕ} (hr : r < n)
    (hQ : TopDownOrder n r (fun x => mem (parPtr + x)) Q) (hQat : ListAt mem qPtr Q)
    (hRA : RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x)) dep)
    (hT : LcaTables w n logCap upPtr depPtr parPtr (fun x => mem (parPtr + x)) dep mem)
    (hag : ∀ a, a < B → mem' a = mem a) (hq : qPtr + n ≤ B) (hpa : parPtr + n ≤ B)
    (hpe : pePtr + n ≤ B) (hup : upPtr + n * logCap ≤ B) (hdp : depPtr + n ≤ B) :
    TopDownOrder n r (fun x => mem' (parPtr + x)) Q ∧ ListAt mem' qPtr Q ∧
    RootedArrays n tM r tl hd (fun x => mem' (parPtr + x)) (fun x => mem' (pePtr + x)) dep ∧
    LcaTables w n logCap upPtr depPtr parPtr (fun x => mem' (parPtr + x)) dep mem' := by
  have hpar : ∀ x < n, mem (parPtr + x) = mem' (parPtr + x) := fun x hx => (hag _ (by omega)).symm
  have hpe' : ∀ x < n, mem (pePtr + x) = mem' (pePtr + x) := fun x hx => (hag _ (by omega)).symm
  refine ⟨hQ.congr hpar, hQat.congr fun k hk1 hk2 => hag k (by rw [hQ.len] at hk2; omega),
    hRA.congr hr hpar hpe' (fun _ _ => rfl), ?_⟩
  exact (hT.of_agree (B := B) hag hup hdp hpa).congr hRA hpar (fun _ _ => rfl)

theorem wstr_meetsContract {w h C : ℕ} {p : Program} {b bTh bPrep bLev bExt bOut : ℕ}
    (hTh : MeetsContract w p bTh (threshContract w h C))
    (hPrep : MeetsContract w p bPrep (wstrPrepContract w h))
    (hLev : MeetsContract w p bLev (levelsContract w h))
    (hExt : MeetsContract w p bExt (blkExtLoopContract w h))
    (hOut : MeetsContract w p bOut (wstrOutContract w h))
    (hp : p.procs[b]? = some (wstrProc bTh bPrep bLev bExt bOut)) :
    MeetsContract w p b (wstrContract w h C) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, tM, m0, k, LB, Lw, Lin, nOrig, r, logCap, lenArr, fidPtr, qPtr, parPtr, pePtr, piPtr,
    thDepPtr, euPtr, evPtr, upPtr, depPtr, eList, numPtr, denPtr, idPtr, ltBase, ldBase, duvBase,
    inRPtr, mpPtr, ownPtr, rtPtr, dRBase, accBase, leBase, k2Out, thOut, tA, tB, tF, tmp1, tmp2,
    highPtr, rfl, hpre⟩ := hpre
  obtain ⟨h16, hn, hLin1, hLinw, hLwB, hnO, hr, hC, hHw, hn2, ⟨Q, tl, hd, dep, hQ, hQat, hRA, hT⟩,
    hth0, hlenT, hlenE, hlen0, heuv, ⟨eCap, heC, heInj, hnd, hdi⟩, L1, L2, L3, L4, L5, L6, L7, L8,
    L9, L10, L11, L12, L13, L14, L15, L16, L17, L18, L19, L20, L21, L22, L23, L24, L25, L26, L27,
    L28, L29, L30⟩ := hpre
  set args := [n, tM, m0, k, LB, Lw, Lin, nOrig, r, logCap, lenArr, fidPtr, qPtr, parPtr, pePtr,
      piPtr, thDepPtr, euPtr, evPtr, upPtr, depPtr, eList, numPtr, denPtr, idPtr, ltBase, ldBase,
      duvBase, inRPtr, mpPtr, ownPtr, rtPtr, dRBase, accBase, leBase, k2Out, thOut, tA, tB, tF,
      tmp1, tmp2, highPtr] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hnLB : n ≤ n * LB := Nat.le_mul_of_pos_right _ (by omega)
  have hm0LB : m0 ≤ m0 * LB := Nat.le_mul_of_pos_right _ (by omega)
  have htLB : tM ≤ tM * LB := Nat.le_mul_of_pos_right _ (by omega)
  have hlc : logCap ≤ n * logCap := Nat.le_mul_of_pos_left _ hn
  have hH1 : 1 ≤ hldDepthBound n + 1 := by omega
  refine runs_start_le ?_
  unfold wstrProc
  -- 1. the threshold
  refine runs_seq_call_le (vs := [n, k, LB, thOut, k2Out, tA, tB, tF]) hTh
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | exact hwords _ (by simp [hargs]))
    ⟨_, _, _, _, _, _, _, _, rfl, h16, hn, hHw, hn2, hC, by omega, by omega, by omega, by omega,
      by omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨n₁, k₁, LB₁, th₁, k2₁, tA₁, tB₁, tF₁, heq₁, hv₁, hfr₁, hvth₁, huth₁, hvk₁,
    huk₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  subst hv₁
  try dsimp only at hfr₁ hvth₁ huth₁ hvk₁ huk₁
  have hlow₁ : ∀ a, a < k2Out → m₁ a = mem a := fun a ha => hfr₁ a (Or.inl ha)
  -- 2. the arrays before the levels
  obtain ⟨hQ₁, hQat₁, hRA₁, hT₁⟩ := treeIn_transfer (mem' := m₁) (B := numPtr) hr hQ hQat hRA hT
    (fun a ha => hlow₁ a (by omega)) L2 L3 L4 L9 L10
  refine runs_seq_call_le (vs := [n, tM, m0, idPtr, ltBase, ldBase, duvBase, accBase, LB, lenArr,
      fidPtr, Lin, nOrig, qPtr, parPtr, pePtr, euPtr, evPtr, logCap, upPtr, depPtr, r]) hPrep
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))))))))))))))))
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | exact hwords _ (by simp [hargs]))
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, h16, hn, hLin1,
      by omega, hnO, hr, ⟨Q, tl, hd, dep, hQ₁, hQat₁, hRA₁, hT₁⟩,
      fun i hi => ?_, by omega, fun t ht => ?_, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ ?_
  · dsimp only
    rw [hlow₁ (fidPtr + i) (by omega)]
    obtain ⟨hv, hb⟩ := hlenT i hi
    exact ⟨fun j hj => by rw [hlow₁ _ (by omega)]; exact hv j hj, by omega⟩
  · dsimp only
    rw [hlow₁ _ (by omega), hlow₁ _ (by omega)]
    exact heuv t ht
  rintro v₂ m₂ pos₂ ⟨n₂, tM₂, m0₂, idPtr₂, ltBase₂, ldBase₂, duvBase₂, accBase₂, LB₂, lenArr₂,
    fidPtr₂, Lin₂, nOrig₂, qPtr₂, parPtr₂, pePtr₂, euPtr₂, evPtr₂, logCap₂, upPtr₂, depPtr₂, r₂,
    heq₂, -, hfr₂, hout₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hfr₂ hout₂
  have hlow₂ : ∀ a, a < idPtr → m₂ a = mem a := fun a ha =>
    (hfr₂ a (Or.inl ha)).trans (hlow₁ a (by omega))
  obtain ⟨hid₂, hlt₂, hld₂, ⟨hroot₂, hrule₂⟩, hduvV₂, hduvF₂, hacc₂⟩ := hout₂
  -- 3. the levels
  obtain ⟨hQ₂, hQat₂, hRA₂, hT₂⟩ := treeIn_transfer (mem' := m₂) (B := numPtr) hr hQ hQat hRA hT
    (fun a ha => hlow₂ a (by omega)) L2 L3 L4 L9 L10
  refine runs_seq_call_le (vs := [hldDepthBound n + 1, n, qPtr, parPtr, pePtr, piPtr, thDepPtr,
      inRPtr, mpPtr, ownPtr, rtPtr, tM, r, m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr,
      dRBase, logCap, upPtr, depPtr]) hLev
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))))))))))))))))))))
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | exact hwords _ (by simp [hargs]))
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by omega, h16,
      hn, ⟨Q, tl, hd, dep, hQ₂, hQat₂, hRA₂, hT₂⟩, hid₂, by omega,
      by omega, by omega, by dsimp only; rw [hlow₂ _ (by omega)]; exact hth0, by omega,
      fun t ht => by dsimp only; rw [hlow₂ _ (by omega), hlow₂ _ (by omega)]; exact heuv t ht,
      hld₂,
      fun t ht => ⟨hduvV₂ t ht, (hacc₂ t ht).1⟩, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩ ?_
  rintro v₃ m₃ pos₃ ⟨K₃, n₃, qPtr₃, parPtr₃, pePtr₃, piPtr₃, thDepPtr₃, inRPtr₃, mpPtr₃, ownPtr₃,
    rtPtr₃, tM₃, r₃, m0₃, euPtr₃, evPtr₃, ldBase₃, duvBase₃, accBase₃, LB₃, idPtr₃, dRBase₃,
    logCap₃, upPtr₃, depPtr₃, heq₃, -, hfr₃, rts, lxs, hrts, hlxs, hacc₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hfr₃ hrts hlxs hacc₃
  have hlow₃ : ∀ a, a < inRPtr → m₃ a = m₂ a := fun a ha => hfr₃ a (Or.inl ha)
  have hlow32 : ∀ a, a < idPtr → m₃ a = mem a := fun a ha =>
    (hlow₃ a (by omega)).trans (hlow₂ a ha)
  -- 4. the edge lengths
  refine runs_seq_call_le (vs := [m0, leBase, LB, lenArr, eList, Lin, m0]) hExt
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | exact hwords _ (by simp [hargs]))
    ⟨_, _, _, _, _, _, _, rfl, h16, hLin1, by omega, fun t ht _ => ?_, by omega, by omega,
      by omega⟩ ?_
  · dsimp only
    rw [hlow32 _ (by omega)]
    obtain ⟨hv, hb⟩ := hlenE t ht
    exact ⟨fun j hj => by rw [hlow32 _ (by omega)]; exact hv j hj, by omega⟩
  rintro v₄ m₄ pos₄ ⟨n₄, d₄, L₄, s₄, x₄, i₄, l₄, heq₄, -, hfr₄, hle₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₄
  try dsimp only at hfr₄ hle₄
  have hlow₄ : ∀ a, a < leBase → m₄ a = m₃ a := fun a ha => hfr₄ a (Or.inl ha)
  have hhi₄ : ∀ a, leBase + m0 * LB ≤ a → a < tmp1 → m₄ a = m₁ a := fun a ha1 ha2 =>
    (hfr₄ a (Or.inr ha1)).trans ((hfr₃ a (Or.inr (by omega))).trans
      (hfr₂ a (Or.inr (Or.inr (by omega)))))
  have hE4 : ∀ t < m0, m₄ (eList + t) = mem (eList + t) := fun t ht =>
    (hlow₄ _ (by omega)).trans (hlow32 _ (by omega))
  have hacc4 : ∀ t < m0, ∀ j < LB, m₄ (accBase + t * LB + j) = m₃ (accBase + t * LB + j) := by
    intro t ht j hj
    have := blk_end LB ht
    exact hlow₄ _ (by omega)
  have hth4 : ∀ j < LB, m₄ (thOut + j) = m₁ (thOut + j) := fun j hj => hhi₄ _ (by omega) (by omega)
  have hk4 : ∀ j < LB, m₄ (k2Out + j) = m₁ (k2Out + j) := fun j hj => hhi₄ _ (by omega) (by omega)
  -- 5. the outputs
  refine runs_seq_call_le (vs := [m0, eList, numPtr, denPtr, accBase, leBase, thOut, k2Out, tmp1,
      tmp2, LB, Lw, highPtr]) hOut
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))))))))
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | exact hwords _ (by simp [hargs]))
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, eCap, rfl, h16, hLwB,
      fun t ht => by dsimp only; rw [hE4 t ht]; exact heC t ht,
      fun t ht t' ht' he => by
        dsimp only at he; rw [hE4 t ht, hE4 t' ht'] at he; exact heInj t ht t' ht' he,
      fun t ht => ⟨fun j hj => by dsimp only; rw [hacc4 t ht j hj]; exact (hacc₃ t ht).1 j hj,
        (hle₄ t ht).1⟩,
      fun j hj => by dsimp only; rw [hth4 j hj]; exact hvth₁ j hj,
      fun j hj => by dsimp only; rw [hk4 j hj]; exact hvk₁ j hj,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega⟩ ?_
  rintro v₅ m₅ pos₅ ⟨m0₅, eList₅, numPtr₅, denPtr₅, accBase₅, leBase₅, thOut₅, k2Out₅, tmp1₅,
    tmp2₅, LB₅, Lw₅, highPtr₅, heq₅, -, hfr5a, hfr5b, hout₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  try dsimp only at hfr5a hfr5b hout₅
  have hsrc5 : ∀ a, denPtr + eCap * Lw ≤ a → a < tmp1 → m₅ a = m₄ a := by
    intro a ha1 ha2
    refine hfr5a a ha2 fun t ht => ?_
    have := blk_end Lw (heC t ht)
    rw [hE4 t ht]
    constructor <;> right <;> omega
  have hblk5 : ∀ x, denPtr + eCap * Lw ≤ x → x + LB ≤ tmp1 → ∀ j < LB, m₅ (x + j) = m₄ (x + j) :=
    fun x hx1 hx2 j hj => hsrc5 _ (by omega) (by omega)
  have hbev : ∀ i < tM, blkExtVal h m₁ lenArr fidPtr Lin nOrig i =
      blkExtVal h mem lenArr fidPtr Lin nOrig i := by
    intro i hi
    unfold blkExtVal
    split_ifs with hiO
    · rw [hlow₁ (fidPtr + i) (by omega)]
      have hb := (hlenT i hiO).2
      exact unsignedVal_congr fun j hj => hlow₁ _ (by omega)
    · rfl
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, tM, m0, k, LB, Lw, Lin, nOrig, r, logCap, lenArr,
    fidPtr, qPtr, parPtr, pePtr, piPtr, thDepPtr, euPtr, evPtr, upPtr, depPtr, eList, numPtr,
    denPtr, idPtr, ltBase, ldBase, duvBase, inRPtr, mpPtr, ownPtr, rtPtr, dRBase, accBase, leBase,
    k2Out, thOut, tA, tB, tF, tmp1, tmp2, highPtr,
    rfl, rfl, m₂, hlow₂, ⟨hid₂, fun i hi => ⟨(hlt₂ i hi).1, by rw [(hlt₂ i hi).2, hbev i hi]⟩,
      hld₂, ⟨hroot₂, hrule₂⟩, hduvV₂, hduvF₂, hacc₂⟩, ⟨rts, lxs, hrts, hlxs, fun t ht => ?_⟩,
    fun t ht => ?_, ?_, ?_, fun a ha hout => ?_, fun a ha => ?_, fun t ht => ?_⟩ ?_
  · have hb := blk_end LB ht
    rw [unsignedVal_congr (hblk5 _ (by omega) (by omega)), unsignedVal_congr (hacc4 t ht)]
    exact (hacc₃ t ht).2
  · have hb := blk_end LB ht
    rw [unsignedVal_congr (hblk5 _ (by omega) (by omega)), (hle₄ t ht).2]
    unfold blkExtVal
    rw [if_pos ht, hlow32 (eList + t) (by omega)]
    have hb' := (hlenE t ht).2
    exact unsignedVal_congr fun j hj => hlow32 _ (by omega)
  · rw [unsignedVal_congr (hblk5 _ (by omega) (by omega)), unsignedVal_congr hth4]
    exact huth₁
  · rw [unsignedVal_congr (hblk5 _ (by omega) (by omega)), unsignedVal_congr hk4]
    exact huk₁
  · dsimp only
    rw [hfr5a a (by omega) (fun t ht => by rw [hE4 t ht]; exact hout t ht), hlow₄ a (by omega)]
    exact hlow32 a ha
  · dsimp only
    rw [hfr5b a ha, hfr₄ a (Or.inr (by omega)), hfr₃ a (Or.inr (by omega)),
      hfr₂ a (Or.inr (Or.inr (by omega))), hfr₁ a (Or.inr (by omega))]
    rfl
  · dsimp only
    have hO := hout₅ t ht
    rw [hE4 t ht] at hO
    have hb := blk_end LB ht
    exact hO.of_src (unsignedVal_congr (hblk5 _ (by omega) (by omega))).symm
      (unsignedVal_congr (hblk5 _ (by omega) (by omega))).symm
      (unsignedVal_congr (hblk5 _ (by omega) (by omega))).symm
      (unsignedVal_congr (hblk5 _ (by omega) (by omega))).symm
  · simp only [wstrContract, wstrCost, threshContract, wstrPrepContract, levelsContract,
      blkExtLoopContract, wstrOutContract, hargs, List.getD_cons_zero, List.getD_cons_succ,
      argsSize, Expr.size_const, Expr.size_reg]
    ring_nf
    omega

end MinCostFlow.LSF.Program
