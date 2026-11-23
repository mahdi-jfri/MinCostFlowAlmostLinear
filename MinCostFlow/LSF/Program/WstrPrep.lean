module

public import MinCostFlow.LSF.Program.BlkFill
public import MinCostFlow.LSF.Program.WDepth
public import MinCostFlow.LSF.Program.DuvPass
public import MinCostFlow.LSF.Program.Utils

/-!
# The arrays before the levels

`wstrPrepProc` writes the arrays that the level loop (`LevelLoop.lean`) reads:

1. the identity array `id` (`idFillProc`);
2. the lengths `lt i` of the tree edges, widened to `LB` limbs; the first `nOrig` tree edges
   are edges of `G₀`, the others are bridges with length `0` (`blkExtLoopProc`);
3. the weighted depths `Ld` (`wDepthProc`, after zeroing their blocks);
4. the tree distance `duv t` of the ends of each edge position `t` (`duvProc`);
5. zero accumulators.

The post states the facts in the final memory (`WstrPrepOut`). The cost is
`O((n + tM + m0) LB + m0 logCap)`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-- Args: `[n, tM, m0, idPtr, ltBase, ldBase, duvBase, accBase, LB, lenArr, fidPtr, Lin, nOrig,
qPtr, parPtr, pePtr, euPtr, evPtr, logCap, upPtr, depPtr, r]`. The root index `r` is not read;
it names the root in the contract. Register `22` is the result of each call. -/
def wstrPrepProc (bId bExt bFill bWD bDuv : ℕ) : Stmt :=
  .call 22 bId [.reg 0, .reg 3] ;;
  .call 22 bExt [.reg 1, .reg 4, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12] ;;
  .call 22 bFill [.reg 5, .bin .mul (.reg 0) (.reg 8), .const 0] ;;
  .call 22 bWD [.reg 0, .reg 13, .reg 14, .reg 15, .reg 4, .reg 5, .reg 8] ;;
  .call 22 bDuv [.reg 2, .reg 16, .reg 17, .reg 6, .reg 5, .reg 8, .reg 18, .reg 19, .reg 20,
    .reg 14] ;;
  .call 22 bFill [.reg 7, .bin .mul (.reg 2) (.reg 8), .const 0] ;;
  .ret (.const 0)

lemma wstrPrepProc_noRand (bId bExt bFill bWD bDuv : ℕ) :
    (wstrPrepProc bId bExt bFill bWD bDuv).NoRand := by
  simp [wstrPrepProc, Stmt.NoRand]

/-- The inputs of `wstrPrepProc`: the rooted tree arrays with their top-down order and lowest
common ancestor tables, the end indices of the edges, the length blocks of the first `nOrig`
tree edges, and the layout. All inputs lie below `idPtr`. -/
def WstrPrepPre (w h : ℕ) (mem : ℕ → ℕ) (n tM m0 idPtr ltBase ldBase duvBase accBase LB lenArr
    fidPtr Lin nOrig qPtr parPtr pePtr euPtr evPtr logCap upPtr depPtr r : ℕ) : Prop :=
  16 ≤ 2 ^ w ∧ 0 < n ∧ 1 ≤ Lin ∧ Lin ≤ LB ∧ nOrig ≤ tM ∧ r < n ∧
  (∃ (Q : List ℕ) (tl hd dep : ℕ → ℕ), TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧
    ListAt mem qPtr Q ∧
    RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x)) dep ∧
    LcaTables w n logCap upPtr depPtr parPtr (fun x => mem (parPtr + x)) dep mem) ∧
  (∀ i < nOrig, Valid mem (lenArr + mem (fidPtr + i) * Lin) h Lin ∧
    lenArr + mem (fidPtr + i) * Lin + LB ≤ idPtr) ∧
  lenArr + LB ≤ idPtr ∧
  (∀ t < m0, mem (euPtr + t) < n ∧ mem (evPtr + t) < n) ∧
  fidPtr + tM ≤ idPtr ∧ qPtr + n ≤ idPtr ∧ parPtr + n ≤ idPtr ∧ pePtr + n ≤ idPtr ∧
  euPtr + m0 ≤ idPtr ∧ evPtr + m0 ≤ idPtr ∧ upPtr + n * logCap ≤ idPtr ∧ depPtr + n ≤ idPtr ∧
  idPtr + n ≤ ltBase ∧ ltBase + tM * LB ≤ ldBase ∧ ldBase + n * LB ≤ duvBase ∧
  duvBase + m0 * LB ≤ accBase ∧ accBase + m0 * LB < 2 ^ w

/-- What `wstrPrepProc` leaves in memory `mem'`, read against the input memory `mem` for the
lengths. -/
def WstrPrepOut (w h : ℕ) (mem mem' : ℕ → ℕ) (n tM m0 idPtr ltBase ldBase duvBase accBase LB
    lenArr fidPtr Lin nOrig qPtr parPtr pePtr euPtr evPtr logCap upPtr depPtr r : ℕ) : Prop :=
  (∀ x < n, mem' (idPtr + x) = x) ∧
  (∀ i < tM, Valid mem' (ltBase + i * LB) h LB ∧
    unsignedVal mem' (ltBase + i * LB) h LB = blkExtVal h mem lenArr fidPtr Lin nOrig i) ∧
  (∀ x < n, Valid mem' (ldBase + x * LB) h LB) ∧
  (unsignedVal mem' (ldBase + r * LB) h LB = 0 ∧
    ∀ x < n, x ≠ r → LdRule h LB (fun y => mem' (parPtr + y)) (fun y => mem' (pePtr + y))
      (fun i => unsignedVal mem' (ltBase + i * LB) h LB)
      (fun y => unsignedVal mem' (ldBase + y * LB) h LB) x) ∧
  (∀ t < m0, Valid mem' (duvBase + t * LB) h LB) ∧
  (∀ (tM' r' : ℕ) (tl hd par pe dep : ℕ → ℕ), RootedArrays n tM' r' tl hd par pe dep →
    LcaTables w n logCap upPtr depPtr parPtr par dep mem' →
    ∀ t < m0, ∃ l, l < n ∧ IsLcaOf par dep l (mem' (euPtr + t)) (mem' (evPtr + t)) ∧
      unsignedVal mem' (duvBase + t * LB) h LB =
        distMod (capacity h LB) (unsignedVal mem' (ldBase + mem' (euPtr + t) * LB) h LB)
          (unsignedVal mem' (ldBase + mem' (evPtr + t) * LB) h LB)
          (unsignedVal mem' (ldBase + l * LB) h LB)) ∧
  (∀ t < m0, Valid mem' (accBase + t * LB) h LB ∧ unsignedVal mem' (accBase + t * LB) h LB = 0)

/-- The contract of `wstrPrepProc`. -/
def wstrPrepContract (w h : ℕ) : Contract where
  pre args mem := ∃ (n tM m0 idPtr ltBase ldBase duvBase accBase LB lenArr fidPtr Lin nOrig qPtr
      parPtr pePtr euPtr evPtr logCap upPtr depPtr r : ℕ),
    args = [n, tM, m0, idPtr, ltBase, ldBase, duvBase, accBase, LB, lenArr, fidPtr, Lin, nOrig,
      qPtr, parPtr, pePtr, euPtr, evPtr, logCap, upPtr, depPtr, r] ∧
    WstrPrepPre w h mem n tM m0 idPtr ltBase ldBase duvBase accBase LB lenArr fidPtr Lin nOrig
      qPtr parPtr pePtr euPtr evPtr logCap upPtr depPtr r
  post args mem ret mem' := ∃ (n tM m0 idPtr ltBase ldBase duvBase accBase LB lenArr fidPtr Lin
      nOrig qPtr parPtr pePtr euPtr evPtr logCap upPtr depPtr r : ℕ),
    args = [n, tM, m0, idPtr, ltBase, ldBase, duvBase, accBase, LB, lenArr, fidPtr, Lin, nOrig,
      qPtr, parPtr, pePtr, euPtr, evPtr, logCap, upPtr, depPtr, r] ∧ ret = 0 ∧
    (∀ a, a < idPtr ∨ (duvBase + m0 * LB ≤ a ∧ a < accBase) ∨ accBase + m0 * LB ≤ a →
      mem' a = mem a) ∧
    WstrPrepOut w h mem mem' n tM m0 idPtr ltBase ldBase duvBase accBase LB lenArr fidPtr Lin
      nOrig qPtr parPtr pePtr euPtr evPtr logCap upPtr depPtr r
  cost args _ := args.getD 0 0 * (200 * args.getD 8 0 + 300) +
    args.getD 1 0 * (30 * args.getD 8 0 + 80) +
    args.getD 2 0 * (100 * args.getD 18 0 + 450 * args.getD 8 0 + 500) + 400

theorem wstrPrep_meetsContract {w h : ℕ} {p : Program} {b bId bExt bFill bWD bDuv : ℕ}
    (hId : MeetsContract w p bId (idFillContract w))
    (hExt : MeetsContract w p bExt (blkExtLoopContract w h))
    (hFill : MeetsContract w p bFill (memFillContract w))
    (hWD : MeetsContract w p bWD (wDepthContract w h))
    (hDuv : MeetsContract w p bDuv (duvContract w h))
    (hp : p.procs[b]? = some (wstrPrepProc bId bExt bFill bWD bDuv)) :
    MeetsContract w p b (wstrPrepContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, tM, m0, idPtr, ltBase, ldBase, duvBase, accBase, LB, lenArr, fidPtr, Lin, nOrig,
    qPtr, parPtr, pePtr, euPtr, evPtr, logCap, upPtr, depPtr, r, rfl, h16, hn, hLin1, hLin, hnO,
    hr, ⟨Q, tl, hd, dep, hQ, hQat, hRA, hT⟩, hlen, hlen0, heuv, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    b10, b11, b12, b13⟩ := hpre
  set args := [n, tM, m0, idPtr, ltBase, ldBase, duvBase, accBase, LB, lenArr, fidPtr, Lin, nOrig,
      qPtr, parPtr, pePtr, euPtr, evPtr, logCap, upPtr, depPtr, r] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hnLB : n ≤ n * LB := Nat.le_mul_of_pos_right _ (by omega)
  have hm0LB : m0 ≤ m0 * LB := Nat.le_mul_of_pos_right _ (by omega)
  have htLB : tM ≤ tM * LB := Nat.le_mul_of_pos_right _ (by omega)
  have hlc : logCap ≤ n * logCap := Nat.le_mul_of_pos_left _ hn
  refine runs_start_le ?_
  unfold wstrPrepProc
  -- 1. the identity array
  refine runs_seq_call_le (vs := [n, idPtr]) hId
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> omega)
    ⟨n, idPtr, rfl, h16, by omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨n₁, i₁, heq₁, -, hfr₁, hid₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl⟩ := heq₁
  try dsimp only at hfr₁ hid₁
  have hlow₁ : ∀ a, a < idPtr → m₁ a = mem a := fun a ha => hfr₁ a (Or.inl ha)
  -- 2. the lengths of the tree edges
  refine runs_seq_call_le (vs := [tM, ltBase, LB, lenArr, fidPtr, Lin, nOrig]) hExt
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, _, _, _, rfl, h16, hLin1, hLin, fun i hi hiO => ?_, by omega, by omega,
      by omega⟩ ?_
  · dsimp only
    rw [hlow₁ (fidPtr + i) (by omega)]
    obtain ⟨hv, hb⟩ := hlen i hiO
    exact ⟨fun j hj => by rw [hlow₁ _ (by omega)]; exact hv j hj, by omega⟩
  rintro v₂ m₂ pos₂ ⟨n₂, d₂, L₂, s₂, x₂, i₂, l₂, heq₂, -, hfr₂, hlt₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hfr₂ hlt₂
  have hlow₂ : ∀ a, a < idPtr → m₂ a = mem a := fun a ha =>
    (hfr₂ a (Or.inl (by omega))).trans (hlow₁ a ha)
  have hbev : ∀ i < tM, blkExtVal h m₁ lenArr fidPtr Lin nOrig i =
      blkExtVal h mem lenArr fidPtr Lin nOrig i := by
    intro i hi
    unfold blkExtVal
    split_ifs with hiO
    · rw [hlow₁ (fidPtr + i) (by omega)]
      have hb := (hlen i hiO).2
      exact unsignedVal_congr fun j hj => hlow₁ _ (by omega)
    · rfl
  -- 3. zero weighted depths
  refine runs_seq_call_le (vs := [ldBase, n * LB, 0]) hFill
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega⟩ ?_
  rintro v₃ m₃ pos₃ ⟨d₃, l₃, x₃, heq₃, -, hz₃, hfr₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hfr₃ hz₃
  have hlow₃ : ∀ a, a < idPtr → m₃ a = mem a := fun a ha =>
    (hfr₃ a (Or.inl (by omega))).trans (hlow₂ a ha)
  -- 4. weighted depths
  have hQ₃ : TopDownOrder n r (fun x => m₃ (parPtr + x)) Q :=
    hQ.congr fun x hx => (hlow₃ _ (by omega)).symm
  have hQat₃ : ListAt m₃ qPtr Q :=
    hQat.congr fun k hk1 hk2 => hlow₃ k (by rw [hQ.len] at hk2; omega)
  have hlt₃ : ∀ i < tM, ∀ j < LB, m₃ (ltBase + i * LB + j) = m₂ (ltBase + i * LB + j) := by
    intro i hi j hj
    have := blk_end LB hi
    exact hfr₃ _ (Or.inl (by omega))
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, pePtr, ltBase, ldBase, LB]) hWD
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, _, _, _, tM, r, Q, rfl, hn, hQ₃, hQat₃, fun x hx hxr => ?_,
      fun i hi => fun j hj => by dsimp only; rw [hlt₃ i hi j hj]; exact (hlt₂ i hi).1 j hj,
      fun a ha1 ha2 => by
        dsimp only
        have := hz₃ (a - ldBase) (by omega)
        rwa [Nat.add_sub_cancel' ha1] at this,
      by omega, by omega, by omega, by omega, by omega⟩ ?_
  · dsimp only; rw [hlow₃ _ (by omega)]; exact (hRA.step x hx hxr).1
  rintro v₄ m₄ pos₄ ⟨n₄, q₄, pa₄, pe₄, lt₄, ld₄, L₄, heq₄, -, hfr₄, hvld₄, hrule₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₄
  try dsimp only at hfr₄ hvld₄ hrule₄
  obtain ⟨hroot₄, hrule₄⟩ := hrule₄ Q r hQ₃ hQat₃
  have hlow₄ : ∀ a, a < ldBase → m₄ a = m₃ a := fun a ha => hfr₄ a (Or.inl ha)
  -- 5. the tree distances
  have hT₄ : LcaTables w n logCap upPtr depPtr parPtr (fun x => mem (parPtr + x)) dep m₄ :=
    hT.of_agree (B := idPtr) (fun a ha => (hlow₄ a (by omega)).trans (hlow₃ a ha)) b7 b8 b3
  refine runs_seq_call_le (vs := [m0, euPtr, evPtr, duvBase, ldBase, LB, logCap, upPtr, depPtr,
      parPtr]) hDuv
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, _, _, _, _, _, _, n, tM, r, tl, hd, _, _, dep, rfl, h16, hRA, hT₄,
      fun t ht => by
        dsimp only
        rw [hlow₄ _ (by omega), hlow₃ _ (by omega), hlow₄ _ (by omega), hlow₃ _ (by omega)]
        exact heuv t ht,
      hvld₄, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v₅ m₅ pos₅ ⟨m₅', eu₅, ev₅, du₅, ld₅, L₅, lc₅, up₅, dp₅, pa₅, heq₅, -, hfr₅, hduv₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  try dsimp only at hfr₅ hduv₅
  -- 6. zero accumulators
  refine runs_seq_call_le (vs := [accBase, m0 * LB, 0]) hFill
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega⟩ ?_
  rintro v₆ m₆ pos₆ ⟨d₆, l₆, x₆, heq₆, -, hz₆, hfr₆⟩
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl⟩ := heq₆
  try dsimp only at hfr₆ hz₆
  have hz₆' : ∀ t < m0, ∀ j < LB, m₆ (accBase + t * LB + j) = 0 := by
    intro t ht j hj
    have := blk_end LB ht
    have := hz₆ (t * LB + j) (by omega)
    rwa [← Nat.add_assoc] at this
  have F5 : ∀ a, a < accBase → m₆ a = m₅ a := fun a ha => hfr₆ a (Or.inl ha)
  have F4 : ∀ a, a < duvBase → m₆ a = m₄ a := fun a ha =>
    (F5 a (by omega)).trans (hfr₅ a (Or.inl ha))
  have F3 : ∀ a, a < ldBase → m₆ a = m₃ a := fun a ha =>
    (F4 a (by omega)).trans (hfr₄ a (Or.inl ha))
  have F2 : ∀ a, a < ldBase → m₆ a = m₂ a := fun a ha =>
    (F3 a ha).trans (hfr₃ a (Or.inl ha))
  have F0 : ∀ a, a < idPtr → m₆ a = mem a := fun a ha =>
    (F3 a (by omega)).trans (hlow₃ a ha)
  have hpar : ∀ x < n, m₆ (parPtr + x) = mem (parPtr + x) := fun x hx => F0 _ (by omega)
  have hpe : ∀ x < n, m₆ (pePtr + x) = mem (pePtr + x) := fun x hx => F0 _ (by omega)
  have hLdB : ∀ y < n, unsignedVal m₆ (ldBase + y * LB) h LB =
      unsignedVal m₄ (ldBase + y * LB) h LB := by
    intro y hy
    have := blk_end LB hy
    exact unsignedVal_congr fun j hj => F4 _ (by omega)
  have hLtB : ∀ i < tM, unsignedVal m₆ (ltBase + i * LB) h LB =
      unsignedVal m₃ (ltBase + i * LB) h LB := by
    intro i hi
    have := blk_end LB hi
    exact unsignedVal_congr fun j hj => F3 _ (by omega)
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, tM, m0, idPtr, ltBase, ldBase, duvBase, accBase,
    LB, lenArr, fidPtr, Lin, nOrig, qPtr, parPtr, pePtr, euPtr, evPtr, logCap, upPtr, depPtr, r,
    rfl, rfl, fun a ha => ?_, fun x hx => ?_, fun i hi => ?_, fun x hx => ?_,
    ⟨?_, fun x hx hxr => ?_⟩,
    fun t ht => ?_, ?_, fun t ht => ?_⟩ ?_
  · -- the frame
    dsimp only
    rcases ha with ha | ⟨ha1, ha2⟩ | ha
    · exact F0 a ha
    · rw [hfr₆ a (Or.inl ha2), hfr₅ a (Or.inr ha1), hfr₄ a (Or.inr (by omega)),
        hfr₃ a (Or.inr (by omega)), hfr₂ a (Or.inr (by omega)), hfr₁ a (Or.inr (by omega))]
      rfl
    · rw [hfr₆ a (Or.inr ha), hfr₅ a (Or.inr (by omega)), hfr₄ a (Or.inr (by omega)),
        hfr₃ a (Or.inr (by omega)), hfr₂ a (Or.inr (by omega)), hfr₁ a (Or.inr (by omega))]
      rfl
  · dsimp only
    rw [F2 _ (by omega), hfr₂ _ (Or.inl (by omega))]; exact hid₁ x hx
  · dsimp only
    have hb := blk_end LB hi
    have hag : ∀ j < LB, m₆ (ltBase + i * LB + j) = m₂ (ltBase + i * LB + j) :=
      fun j hj => F2 _ (by omega)
    obtain ⟨hv, hu⟩ := hlt₂ i hi
    exact ⟨fun j hj => by rw [hag j hj]; exact hv j hj,
      by rw [unsignedVal_congr hag, hu, hbev i hi]⟩
  · dsimp only
    have hb := blk_end LB hx
    exact fun j hj => by rw [F4 _ (by omega)]; exact hvld₄ x hx j hj
  · dsimp only
    rw [hLdB r hr]; exact hroot₄
  · dsimp only
    have hrx := hrule₄ x hx hxr
    have hpx : mem (parPtr + x) < n := hRA.par_lt x hx
    have hpex : mem (pePtr + x) < tM := (hRA.step x hx hxr).1
    unfold LdRule at hrx ⊢
    dsimp only at hrx ⊢
    rw [hpar x hx, hpe x hx, hLdB x hx, hLdB _ hpx, hLtB _ hpex]
    rw [hlow₃ _ (by omega), hlow₃ _ (by omega)] at hrx
    exact hrx
  · dsimp only
    have hb := blk_end LB ht
    exact fun j hj => by rw [F5 _ (by omega)]; exact (hduv₅ t ht).1 j hj
  · dsimp only
    intro tM' r' tl' hd' par' pe' dep' hRA' hT' t ht
    obtain ⟨-, l, hdl, hl⟩ := hduv₅ t ht
    have hT₄' : LcaTables w n logCap upPtr depPtr parPtr par' dep' m₄ :=
      hT'.of_agree (B := duvBase) (fun a ha => (F4 a ha).symm) (by omega) (by omega) (by omega)
    have heu : m₄ (euPtr + t) = mem (euPtr + t) := (hlow₄ _ (by omega)).trans (hlow₃ _ (by omega))
    have hev : m₄ (evPtr + t) = mem (evPtr + t) := (hlow₄ _ (by omega)).trans (hlow₃ _ (by omega))
    have heu6 : m₆ (euPtr + t) = mem (euPtr + t) := F0 _ (by omega)
    have hev6 : m₆ (evPtr + t) = mem (evPtr + t) := F0 _ (by omega)
    obtain ⟨hun, hvn⟩ := heuv t ht
    obtain ⟨hln, hlca⟩ := hl n tM' r' tl' hd' par' pe' dep' hRA' (by rw [heu]; exact hun)
      (by rw [hev]; exact hvn) hT₄' (by omega) (by omega) (by omega)
    have hb := blk_end LB ht
    refine ⟨l, hln, by rw [heu6, hev6]; rw [heu, hev] at hlca; exact hlca, ?_⟩
    rw [unsignedVal_congr (fun j hj => F5 _ (by omega)), hdl, heu6, hev6, heu, hev,
      hLdB _ hun, hLdB _ hvn, hLdB _ hln]
  · dsimp only
    have hb := blk_end LB ht
    refine ⟨fun j hj => by rw [hz₆' t ht j hj]; exact base_pos h, ?_⟩
    exact unsignedVal_eq_zero_iff.mpr (hz₆' t ht)
  · simp only [wstrPrepContract, idFillContract, blkExtLoopContract, memFillContract,
      wDepthContract, duvContract, hargs, List.getD_cons_zero, List.getD_cons_succ, argsSize,
      Expr.size_const, Expr.size_reg, Expr.size_bin]
    ring_nf
    omega

end MinCostFlow.LSF.Program
