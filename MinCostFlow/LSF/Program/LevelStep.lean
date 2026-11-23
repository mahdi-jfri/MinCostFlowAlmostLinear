module

public import MinCostFlow.LSF.Program.FRLevel
public import MinCostFlow.LSF.Program.DuvPass

/-!
# One level of the stretch sum: the driver

`levelStepProc` runs the passes of one level (`FRLevel.lean`) on a scratch area
`[inRPtr, accBase)` that holds the flags, `mp`, `own`, `rt` and the blocks `dR x` of the tree
distance from `x` to `rt x` (`duvProc` with the identity array and `rt` as the two end arrays),
and then updates the accumulators at `accBase`. Its post gives the roots as an array `rt` with
`LevelRt` for the flags `levelFlag`, the lowest common ancestors `lx x` of `x` and `rt x`, and
the new accumulators as `accLevelVal` of the old ones.

Each pass reads the arrays of the earlier passes from a later memory, so the rules are moved
between memories with the congruence lemmas `mpRule_congr`, `ownState_congr`, `rtRule_congr`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

@[expose] public section

/-! ## Congruence of the rules -/

lemma mpRule_congr {inR par pe piv mp inR' par' pe' piv' : ℕ → ℕ} {x : ℕ}
    (hpar : par' x = par x) (hpe : pe' x = pe x) (hin : inR' (par x) = inR (par x))
    (hpv1 : piv' (pe x) = piv (pe x)) (hpv2 : piv' (mp (par x)) = piv (mp (par x)))
    (h : MpRule inR par pe piv mp x) : MpRule inR' par' pe' piv' mp x := by
  unfold MpRule at h ⊢
  rw [hpar, hpe, hin, hpv1, hpv2]; exact h

lemma ownState_congr {r tM n : ℕ} {inR mp own inR' mp' : ℕ → ℕ}
    (hin : ∀ y < n, inR' y = inR y) (hmp : ∀ y < n, mp' y = mp y)
    (h : OwnState r tM inR mp own n) : OwnState r tM inR' mp' own n := by
  intro i hi
  obtain ⟨h1, h2⟩ := h i hi
  refine ⟨fun hne => ?_, fun hz y hy hyr hyR => ?_⟩
  · obtain ⟨a, b, c, d⟩ := h1 hne
    exact ⟨a, b, by rw [hin _ a]; exact c, by rw [hmp _ a]; exact d⟩
  · rw [hmp y hy]; exact h2 hz y hy hyr (by rw [← hin y hy]; exact hyR)

lemma rtRule_congr {inR par pe own rt inR' par' pe' own' rt' : ℕ → ℕ} {x : ℕ}
    (hin : inR' x = inR x) (hpar : par' x = par x) (hpe : pe' x = pe x)
    (hown : own' (pe x) = own (pe x)) (hrt : rt' x = rt x) (hrtp : rt' (par x) = rt (par x))
    (h : RtRule inR par pe own rt x) : RtRule inR' par' pe' own' rt' x := by
  unfold RtRule at h ⊢
  rw [hin, hpar, hpe, hown, hrt, hrtp]; exact h

/-- The depths of rooted arrays are fixed by the parents. -/
lemma rootedArrays_dep_eq {n tM r : ℕ} {tl hd par pe dep tl' hd' pe' dep' : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) (hR' : RootedArrays n tM r tl' hd' par pe' dep') :
    ∀ x < n, dep x = dep' x := by
  suffices H : ∀ d, ∀ x < n, dep x = d → dep x = dep' x from fun x hx => H _ x hx rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro x hx hd
  by_cases hxr : x = r
  · subst hxr; rw [hR.dep_r, hR'.dep_r]
  obtain ⟨-, -, h1⟩ := hR.step x hx hxr
  obtain ⟨-, -, h2⟩ := hR'.step x hx hxr
  rw [h1, h2, ih _ (by omega) _ (hR.par_lt x hx) rfl]

/-! ## The procedure -/

/-- Args: `[i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r,
m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr]`. -/
def levelStepProc (bFlag bMp bOwn bRt bDuv bAccL : ℕ) : Stmt :=
  .call 25 bFlag [.reg 1, .reg 6, .reg 7, .reg 0] ;;
  .call 25 bMp [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 7, .reg 8, .reg 11] ;;
  .call 25 bOwn [.reg 1, .reg 12, .reg 8, .reg 7, .reg 9, .reg 11] ;;
  .call 25 bRt [.reg 1, .reg 2, .reg 3, .reg 4, .reg 7, .reg 9, .reg 10] ;;
  .call 25 bDuv [.reg 1, .reg 20, .reg 10, .reg 21, .reg 16, .reg 19, .reg 22, .reg 23, .reg 24,
    .reg 3] ;;
  .call 25 bAccL [.reg 13, .reg 14, .reg 15, .reg 10, .reg 21, .reg 17, .reg 18, .reg 19] ;;
  .ret (.const 0)

lemma levelStepProc_noRand (bFlag bMp bOwn bRt bDuv bAccL : ℕ) :
    (levelStepProc bFlag bMp bOwn bRt bDuv bAccL).NoRand := by
  simp [levelStepProc, Stmt.NoRand]

/-- The block value of the distance from `z` to its root `rt z`, through the lowest common
ancestor `lx z`. -/
def dRVal (h LB : ℕ) (mem : ℕ → ℕ) (ldBase : ℕ) (rt lx : ℕ → ℕ) (z : ℕ) : ℕ :=
  distMod (capacity h LB) (unsignedVal mem (ldBase + z * LB) h LB)
    (unsignedVal mem (ldBase + rt z * LB) h LB) (unsignedVal mem (ldBase + lx z * LB) h LB)

/-- The new accumulator of edge position `t`, for the roots `rt`. -/
def accStepVal (h LB : ℕ) (mem : ℕ → ℕ) (euPtr evPtr ldBase duvBase accBase : ℕ)
    (rt lx : ℕ → ℕ) (t : ℕ) : ℕ :=
  let u := mem (euPtr + t)
  let v := mem (evPtr + t)
  accLevelVal (capacity h LB) (unsignedVal mem (accBase + t * LB) h LB)
    (unsignedVal mem (duvBase + t * LB) h LB) (dRVal h LB mem ldBase rt lx u)
    (dRVal h LB mem ldBase rt lx v) (rt u) (rt v)

/-- The layout and the facts that the passes need. -/
def LevelStepPre (w h : ℕ) (mem : ℕ → ℕ) (i n qPtr parPtr pePtr piPtr thDepPtr inRPtr mpPtr
    ownPtr rtPtr tM r m0 euPtr evPtr ldBase duvBase accBase LB idPtr dRBase logCap upPtr
    depPtr : ℕ) : Prop :=
  16 ≤ 2 ^ w ∧ 0 < n ∧
  (∃ (Q : List ℕ) (tl hd dep : ℕ → ℕ), TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧
    ListAt mem qPtr Q ∧
    RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x)) dep ∧
    LcaTables w n logCap upPtr depPtr parPtr (fun x => mem (parPtr + x)) dep mem) ∧
  (∀ x < n, mem (idPtr + x) = x) ∧ idPtr + n ≤ inRPtr ∧ upPtr + n * logCap ≤ inRPtr ∧
  depPtr + n ≤ inRPtr ∧
  mem (thDepPtr + r) = 0 ∧ i + 1 < 2 ^ w ∧
  (∀ t < m0, mem (euPtr + t) < n ∧ mem (evPtr + t) < n) ∧
  (∀ x < n, Valid mem (ldBase + x * LB) h LB) ∧
  (∀ t < m0, Valid mem (duvBase + t * LB) h LB ∧ Valid mem (accBase + t * LB) h LB) ∧
  qPtr + n ≤ inRPtr ∧ parPtr + n ≤ inRPtr ∧ pePtr + n ≤ inRPtr ∧ piPtr + tM ≤ inRPtr ∧
  thDepPtr + n ≤ inRPtr ∧ euPtr + m0 ≤ inRPtr ∧ evPtr + m0 ≤ inRPtr ∧
  ldBase + n * LB ≤ inRPtr ∧ duvBase + m0 * LB ≤ inRPtr ∧
  inRPtr + n ≤ mpPtr ∧ mpPtr + n ≤ ownPtr ∧ ownPtr + tM ≤ rtPtr ∧ rtPtr + n ≤ dRBase ∧
  dRBase + n * LB ≤ accBase ∧ accBase + m0 * LB < 2 ^ w

/-- The contract of `levelStepProc`. -/
def levelStepContract (w h : ℕ) : Contract where
  pre args mem := ∃ (i n qPtr parPtr pePtr piPtr thDepPtr inRPtr mpPtr ownPtr rtPtr tM r m0
      euPtr evPtr ldBase duvBase accBase LB idPtr dRBase logCap upPtr depPtr : ℕ),
    args = [i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r,
      m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr] ∧
    LevelStepPre w h mem i n qPtr parPtr pePtr piPtr thDepPtr inRPtr mpPtr ownPtr rtPtr tM r m0
      euPtr evPtr ldBase duvBase accBase LB idPtr dRBase logCap upPtr depPtr
  post args mem ret mem' := ∃ (i n qPtr parPtr pePtr piPtr thDepPtr inRPtr mpPtr ownPtr rtPtr
      tM r m0 euPtr evPtr ldBase duvBase accBase LB idPtr dRBase logCap upPtr depPtr : ℕ),
    args = [i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r,
      m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr] ∧
    ret = 0 ∧ (∀ a, a < inRPtr ∨ accBase + m0 * LB ≤ a → mem' a = mem a) ∧
    ∃ rt lx : ℕ → ℕ,
      LevelRt n tM r (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x))
        (fun j => mem (piPtr + j)) (levelFlag mem thDepPtr i) rt ∧
      (∀ (tl hd dep : ℕ → ℕ),
        RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x)) dep →
        LcaTables w n logCap upPtr depPtr parPtr (fun x => mem (parPtr + x)) dep mem →
        ∀ x < n, lx x < n ∧ IsLcaOf (fun y => mem (parPtr + y)) dep (lx x) x (rt x)) ∧
      ∀ t < m0, Valid mem' (accBase + t * LB) h LB ∧
        unsignedVal mem' (accBase + t * LB) h LB =
          accStepVal h LB mem euPtr evPtr ldBase duvBase accBase rt lx t
  cost args _ := 400 * args.getD 1 0 + 30 * args.getD 11 0 +
    args.getD 1 0 * (100 * args.getD 22 0 + 400 * args.getD 19 0 + 400) +
    args.getD 13 0 * (150 * args.getD 19 0 + 160) + 500

theorem levelStep_meetsContract {w h : ℕ} {p : Program}
    {b bFlag bMp bOwn bRt bDuv bAccL : ℕ}
    (hFlag : MeetsContract w p bFlag (levelFlagContract w))
    (hMp : MeetsContract w p bMp (frMpContract w))
    (hOwn : MeetsContract w p bOwn (frOwnContract w))
    (hRt : MeetsContract w p bRt (frRtContract w))
    (hDuv : MeetsContract w p bDuv (duvContract w h))
    (hAccL : MeetsContract w p bAccL (accLevelContract w h))
    (hp : p.procs[b]? = some (levelStepProc bFlag bMp bOwn bRt bDuv bAccL)) :
    MeetsContract w p b (levelStepContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r, m0,
    euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr, rfl, h16, hn,
    ⟨Q, tl, hd, dep, hQ, hQat, hRA, hLT⟩, hid, hida, hupa, hdepa, hth, hi1, hend, hld, hblk, hqa,
    hpa, hpea, hpia, hta, heua, heva, hlda, hduva, hia, hma, hoa, hra, hdRa, hacw⟩ := hpre
  set args := [i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r,
    m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr]
    with hargs
  have hR0 : ∀ k < 25, (startState args mem pos).regs k = args.getD k 0 := by
    intro k hk
    interval_cases k <;> simp [startState, hargs]
  have r0 := hR0 0 (by omega); have r1 := hR0 1 (by omega); have r2 := hR0 2 (by omega)
  have r3 := hR0 3 (by omega); have r4 := hR0 4 (by omega); have r5 := hR0 5 (by omega)
  have r6 := hR0 6 (by omega); have r7 := hR0 7 (by omega); have r8 := hR0 8 (by omega)
  have r9 := hR0 9 (by omega); have r10 := hR0 10 (by omega); have r11 := hR0 11 (by omega)
  have r12 := hR0 12 (by omega); have r13 := hR0 13 (by omega); have r14 := hR0 14 (by omega)
  have r15 := hR0 15 (by omega); have r16 := hR0 16 (by omega); have r17 := hR0 17 (by omega)
  have r18 := hR0 18 (by omega); have r19 := hR0 19 (by omega); have r20 := hR0 20 (by omega)
  have r21 := hR0 21 (by omega); have r22 := hR0 22 (by omega); have r23 := hR0 23 (by omega)
  have r24 := hR0 24 (by omega)
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at r10 r11 r12 r13 r14 r15 r16
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at r17 r18 r19 r20 r21 r22
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at r23 r24
  have hw : ∀ v ∈ args, v < 2 ^ w := hwords
  have hrn : r < n := hQ.lt r (by rw [← hQ.head_eq hn]; exact List.getElem_mem _)
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set pe : ℕ → ℕ := fun x => mem (pePtr + x) with hpe
  set piv : ℕ → ℕ := fun j => mem (piPtr + j) with hpiv
  set inR : ℕ → ℕ := levelFlag mem thDepPtr i with hinR
  have hinR1 : ∀ x, inR x ≤ 1 := fun x => by
    simp only [hinR, levelFlag]; split_ifs <;> omega
  have hinRr : inR r = 1 := by simp [hinR, levelFlag, hth]
  have hpe_lt : ∀ x < n, x ≠ r → pe x < tM := fun x hx hxr => (hRA.step x hx hxr).1
  have hnw : n < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold levelStepProc
  -- 1. the flags
  refine runs_seq_call_le (vs := [n, thDepPtr, inRPtr, i]) hFlag
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨n, thDepPtr, inRPtr, i, rfl, h16, hta, by omega, hi1⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨n₁, a₁, b₁, c₁, heq₁, -, hfr₁, hflag⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hfr₁ hflag
  have hlow₁ : ∀ a, a < inRPtr → mem₁ a = mem a := fun a ha => hfr₁ a (Or.inl ha)
  have hin₁ : ∀ x < n, mem₁ (inRPtr + x) = inR x := hflag
  -- 2. `mp`
  have hQ₁ : TopDownOrder n r (fun x => mem₁ (parPtr + x)) Q :=
    hQ.congr fun x hx => (hlow₁ _ (by omega)).symm
  have hQat₁ : ListAt mem₁ qPtr Q :=
    hQat.congr fun k hk1 hk2 => hlow₁ k (by rw [hQ.len] at hk2; omega)
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM]) hMp
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM, r, Q, rfl, hn, hQ₁, hQat₁,
      fun x hx hxr => by dsimp only; rw [hlow₁ _ (by omega)]; exact hpe_lt x hx hxr,
      fun x hx => by dsimp only; rw [hin₁ x hx]; exact hinR1 x,
      by dsimp only; rw [hin₁ r hrn]; exact hinRr,
      by omega, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨n₂, a₂, b₂, c₂, d₂, e₂, f₂, g₂, heq₂, -, hfr₂, hmpQ⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hfr₂ hmpQ
  obtain ⟨hmp_r, hmp⟩ := hmpQ Q r hQ₁ hQat₁
  have hlow₂ : ∀ a, a < mpPtr → mem₂ a = mem₁ a := fun a ha => hfr₂ a (Or.inl ha)
  set mp : ℕ → ℕ := fun x => mem₂ (mpPtr + x) with hmpdef
  -- 3. `own`
  refine runs_seq_call_le (vs := [n, r, mpPtr, inRPtr, ownPtr, tM]) hOwn
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_nil _ _)))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨n, r, mpPtr, inRPtr, ownPtr, tM, rfl, hrn,
      fun y hy => by dsimp only; rw [hlow₂ _ (by omega), hin₁ y hy]; exact hinR1 y,
      fun y hy hyr _ => (hmp y hy hyr).1, by omega, by omega, by omega⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨n₃, a₃, b₃, c₃, d₃, e₃, heq₃, -, hfr₃, hown⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hfr₃ hown
  have hlow₃ : ∀ a, a < ownPtr → mem₃ a = mem₂ a := fun a ha => hfr₃ a (Or.inl ha)
  set own : ℕ → ℕ := fun j => mem₃ (ownPtr + j) with howndef
  -- 4. `rt`
  have hQ₃ : TopDownOrder n r (fun x => mem₃ (parPtr + x)) Q :=
    hQ.congr fun x hx => by
      rw [hlow₃ _ (by omega), hlow₂ _ (by omega), hlow₁ _ (by omega)]
  have hQat₃ : ListAt mem₃ qPtr Q :=
    hQat.congr fun k hk1 hk2 => by
      rw [hQ.len] at hk2
      rw [hlow₃ k (by omega), hlow₂ k (by omega), hlow₁ k (by omega)]
  have hin₃ : ∀ x < n, mem₃ (inRPtr + x) = inR x := fun x hx => by
    rw [hlow₃ _ (by omega), hlow₂ _ (by omega), hin₁ x hx]
  have hpe₃ : ∀ x < n, mem₃ (pePtr + x) = pe x := fun x hx => by
    rw [hlow₃ _ (by omega), hlow₂ _ (by omega), hlow₁ _ (by omega)]
  have hpar₃ : ∀ x < n, mem₃ (parPtr + x) = par x := fun x hx => by
    rw [hlow₃ _ (by omega), hlow₂ _ (by omega), hlow₁ _ (by omega)]
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr]) hRt
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr, tM, r, Q, rfl, hn, hQ₃, hQat₃,
      fun x hx hxr => by dsimp only; rw [hpe₃ x hx]; exact hpe_lt x hx hxr,
      fun x hx => by dsimp only; rw [hin₃ x hx]; exact hinR1 x,
      fun j hj => by
        by_cases h0 : own j = 0
        · show own j ≤ n; omega
        · have := ((hown j hj).1 h0).1; show own j ≤ n; omega,
      by omega, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v₄ mem₄ pos₄ ⟨n₄, a₄, b₄, c₄, d₄, e₄, f₄, heq₄, -, hfr₄, hrtQ⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₄
  try dsimp only at hfr₄ hrtQ
  obtain ⟨hrt_r, hrt⟩ := hrtQ Q r hQ₃ hQat₃
  have hlow₄ : ∀ a, a < rtPtr → mem₄ a = mem₃ a := fun a ha => hfr₄ a (Or.inl ha)
  set rt : ℕ → ℕ := fun x => mem₄ (rtPtr + x) with hrtdef
  -- the rules, in terms of the first memory
  have hmp0 : ∀ x < n, x ≠ r → mp x < tM := fun x hx hxr => (hmp x hx hxr).1
  have hmp_lt : ∀ x < n, x ≠ r → mp (par x) < tM := fun x hx hxr => by
    have hpx := hRA.par_lt x hx
    by_cases hpr : par x = r
    · rw [hpr]
      have h0 : mp r = 0 := hmp_r
      have := hpe_lt x hx hxr
      omega
    · exact hmp0 _ hpx hpr
  have hLR : LevelRt n tM r par pe piv inR rt := by
    refine ⟨mp, own, fun x hx hxr => ⟨hmp0 x hx hxr, ?_⟩, ?_, hrt_r, fun x hx hxr => ?_⟩
    · have hpx := hRA.par_lt x hx
      refine mpRule_congr (inR := fun y => mem₁ (inRPtr + y)) (par := fun y => mem₁ (parPtr + y))
        (pe := fun y => mem₁ (pePtr + y)) (piv := fun j => mem₁ (piPtr + j))
        (hlow₁ _ (by omega)).symm (hlow₁ _ (by omega)).symm (hin₁ _ ?_).symm
        (hlow₁ _ ?_).symm (hlow₁ _ ?_).symm (hmp x hx hxr).2
      · beta_reduce; rw [hlow₁ _ (by omega)]; exact hpx
      · have h1 := hpe_lt x hx hxr
        have h2 : mem₁ (pePtr + x) = pe x := hlow₁ _ (by omega)
        beta_reduce; rw [h2]; omega
      · have h1 := hmp_lt x hx hxr
        have h2 : mem₁ (parPtr + x) = par x := hlow₁ _ (by omega)
        beta_reduce; rw [h2]; omega
    · exact ownState_congr (fun y hy => by rw [hlow₂ _ (by omega), hin₁ y hy])
        (fun y _ => rfl)
        hown
    · have hpx := hRA.par_lt x hx
      exact rtRule_congr (hin₃ x hx).symm (hpar₃ x hx).symm (hpe₃ x hx).symm rfl rfl rfl
        (hrt x hx hxr)
  -- 5. the distances to the roots
  have hrt_lt := levelRt_lt hRA hrn hLR
  have hlow : ∀ a, a < inRPtr → mem₄ a = mem a := fun a ha => by
    rw [hlow₄ _ (by omega), hlow₃ _ (by omega), hlow₂ _ (by omega), hlow₁ _ ha]
  have hhigh : ∀ a, dRBase ≤ a → mem₄ a = mem a := fun a ha => by
    rw [hfr₄ a (Or.inr (by omega)), hfr₃ a (Or.inr (by omega)), hfr₂ a (Or.inr (by omega)),
      hfr₁ a (Or.inr (by omega))]
    rfl
  have hLT₄ : LcaTables w n logCap upPtr depPtr parPtr par dep mem₄ :=
    hLT.of_agree (B := inRPtr) hlow hupa hdepa (by omega)
  have hRA₄ : RootedArrays n tM r tl hd (fun x => mem₄ (parPtr + x)) (fun x => mem₄ (pePtr + x))
      dep :=
    hRA.congr hrn (fun x hx => (hlow _ (by omega)).symm) (fun x hx => (hlow _ (by omega)).symm)
      (fun _ _ => rfl)
  have hLT₄' : LcaTables w n logCap upPtr depPtr parPtr (fun x => mem₄ (parPtr + x)) dep mem₄ :=
    hLT₄.congr hRA (fun x hx => (hlow _ (by omega)).symm) (fun _ _ => rfl)
  have hblkL : ∀ x < n, (∀ j < LB, mem₄ (ldBase + x * LB + j) = mem (ldBase + x * LB + j)) :=
    fun x hx j hj => hlow _ (by have := blk_end LB hx; omega)
  refine runs_seq_call_le (vs := [n, idPtr, rtPtr, dRBase, ldBase, LB, logCap, upPtr, depPtr,
      parPtr]) hDuv
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hw _ (by simp [hargs]))
    ⟨n, idPtr, rtPtr, dRBase, ldBase, LB, logCap, upPtr, depPtr, parPtr, n, tM, r, tl, hd,
      (fun x => mem₄ (parPtr + x)), (fun x => mem₄ (pePtr + x)), dep, rfl, h16, hRA₄, hLT₄',
      fun x hx => ⟨by dsimp only; rw [hlow _ (by omega), hid x hx]; exact hx, hrt_lt x hx⟩,
      fun x hx j hj => by dsimp only; rw [hblkL x hx j hj]; exact hld x hx j hj,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v₅ mem₅ pos₅ ⟨m₅, a₅, b₅, c₅, d₅, e₅, f₅, g₅, i₅, j₅, heq₅, -, hfr₅, hdR⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  try dsimp only at hfr₅ hdR
  have hdR' : ∀ x < n, ∃ l, DuvOut w h mem₄ mem₅ idPtr rtPtr dRBase ldBase LB logCap upPtr depPtr
      parPtr x ∧ l = l := fun x hx => ⟨0, hdR x hx, rfl⟩
  have hex : ∀ x, ∃ l, x < n → (unsignedVal mem₅ (dRBase + x * LB) h LB =
      distMod (capacity h LB) (unsignedVal mem₄ (ldBase + mem₄ (idPtr + x) * LB) h LB)
        (unsignedVal mem₄ (ldBase + mem₄ (rtPtr + x) * LB) h LB)
        (unsignedVal mem₄ (ldBase + l * LB) h LB) ∧
      ∀ (n' tM' r' : ℕ) (tl' hd' par' pe' dep' : ℕ → ℕ), RootedArrays n' tM' r' tl' hd' par' pe' dep' →
        mem₄ (idPtr + x) < n' → mem₄ (rtPtr + x) < n' →
        LcaTables w n' logCap upPtr depPtr parPtr par' dep' mem₄ →
        upPtr + n' * logCap ≤ dRBase → depPtr + n' ≤ dRBase → parPtr + n' ≤ dRBase →
        l < n' ∧ IsLcaOf par' dep' l (mem₄ (idPtr + x)) (mem₄ (rtPtr + x))) := by
    intro x
    by_cases hx : x < n
    · obtain ⟨-, l, hl1, hl2⟩ := hdR x hx
      exact ⟨l, fun _ => ⟨hl1, hl2⟩⟩
    · exact ⟨0, fun h' => absurd h' hx⟩
  choose lx hlx using hex
  have hlx_lt : ∀ x < n, lx x < n ∧
      IsLcaOf (fun y => mem₄ (parPtr + y)) dep (lx x) x (rt x) := fun x hx => by
    have := ((hlx x hx).2 n tM r tl hd _ _ dep hRA₄ (by rw [hlow _ (by omega), hid x hx]; exact hx)
      (hrt_lt x hx) hLT₄' (by omega) (by omega) (by omega))
    rw [hlow _ (by omega), hid x hx] at this
    exact this
  have hdRv : ∀ x < n, Valid mem₅ (dRBase + x * LB) h LB ∧
      unsignedVal mem₅ (dRBase + x * LB) h LB = dRVal h LB mem ldBase rt lx x := fun x hx => by
    refine ⟨(hdR x hx).1, ?_⟩
    rw [(hlx x hx).1, hlow (idPtr + x) (by omega), hid x hx]
    simp only [dRVal]
    rw [unsignedVal_congr (hblkL x hx), unsignedVal_congr (hblkL _ (hrt_lt x hx)),
      unsignedVal_congr (hblkL _ (hlx_lt x hx).1)]
  -- 6. the accumulators
  have hlow5 : ∀ a, a < dRBase → mem₅ a = mem₄ a := fun a ha => hfr₅ a (Or.inl ha)
  have hlow' : ∀ a, a < inRPtr → mem₅ a = mem a := fun a ha => by
    rw [hlow5 a (by omega), hlow a ha]
  have hhigh' : ∀ a, accBase ≤ a → mem₅ a = mem a := fun a ha => by
    rw [hfr₅ a (Or.inr (by omega)), hhigh a (by omega)]
  have hrt5 : ∀ x < n, mem₅ (rtPtr + x) = rt x := fun x hx => hlow5 _ (by omega)
  have hblkD : ∀ t < m0, (∀ j < LB, mem₅ (duvBase + t * LB + j) = mem (duvBase + t * LB + j)) :=
    fun t ht j hj => hlow' _ (by have := blk_end LB ht; omega)
  have hblkA : ∀ t < m0, (∀ j < LB, mem₅ (accBase + t * LB + j) = mem (accBase + t * LB + j)) :=
    fun t ht j hj => hhigh' _ (by omega)
  refine runs_seq_call_le (vs := [m0, euPtr, evPtr, rtPtr, dRBase, duvBase, accBase, LB]) hAccL
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hw _ (by simp [hargs]))
    ⟨m0, euPtr, evPtr, rtPtr, dRBase, duvBase, accBase, LB, n, rfl, h16,
      fun t ht => by dsimp only; rw [hlow' _ (by omega), hlow' _ (by omega)]; exact hend t ht,
      fun x hx => by dsimp only; rw [hrt5 x hx]; exact hrt_lt x hx,
      fun x hx => (hdRv x hx).1,
      fun t ht => ⟨fun j hj => by dsimp only; rw [hblkD t ht j hj]; exact (hblk t ht).1 j hj,
        fun j hj => by dsimp only; rw [hblkA t ht j hj]; exact (hblk t ht).2 j hj⟩,
      by omega, by omega, by omega, by omega, by omega, hacw⟩ ?_
  rintro v₆ mem₆ pos₆ ⟨m₆, a₆, b₆, c₆, d₆, e₆, f₆, g₆, heq₆, -, hfr₆, hacc⟩
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₆
  try dsimp only at hfr₆ hacc
  refine runs_ret_le (v := 0) (by eval_expr) ⟨i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr,
    mpPtr, ownPtr, rtPtr, tM, r, m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase,
    logCap, upPtr, depPtr, rfl, rfl, fun a ha => ?_, rt, lx, hLR, ?_,
    fun t ht => ⟨(hacc t ht).1, ?_⟩⟩ ?_
  · dsimp only
    rcases ha with ha | ha
    · rw [hfr₆ a (Or.inl (by omega)), hlow' a ha]
    · rw [hfr₆ a (Or.inr ha), hhigh' a (by omega)]
  · intro tl' hd' dep' hRA' hLT' x hx
    -- the lowest common ancestor does not depend on the choice of depths
    obtain ⟨h1, h2⟩ := hlx_lt x hx
    refine ⟨h1, (isLcaOf_congr (n := n) (fun y hy => hlow _ (by omega))
      (rootedArrays_dep_eq hRA hRA') (fun y hy => hRA₄.par_lt y hy) hx (hrt_lt x hx) h1).mp h2⟩
  · rw [(hacc t ht).2]
    obtain ⟨hut, hvt⟩ := hend t ht
    simp only [accLevelAt, accStepVal]
    rw [hlow' (euPtr + t) (by omega), hlow' (evPtr + t) (by omega),
      unsignedVal_congr (hblkA t ht), unsignedVal_congr (hblkD t ht), hrt5 _ hut, hrt5 _ hvt,
      (hdRv _ hut).2, (hdRv _ hvt).2]
  · simp only [levelStepContract, levelFlagContract, frMpContract, frOwnContract, frRtContract,
      duvContract, accLevelContract, hargs, List.getD_cons_zero, List.getD_cons_succ, argsSize,
      Expr.size_const, Expr.size_reg]
    omega
end

end MinCostFlow.LSF.Program
