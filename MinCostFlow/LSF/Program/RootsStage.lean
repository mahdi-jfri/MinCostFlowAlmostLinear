module

public import MinCostFlow.LSF.Program.UpClosure
public import MinCostFlow.LSF.Program.FRMp
public import MinCostFlow.LSF.Program.FROwn
public import MinCostFlow.LSF.Program.FRRt
public import MinCostFlow.LSF.Program.UpClosureMath
public import MinCostFlow.LSF.Program.FForestMath

/-!
# The roots of `F` in one procedure

`rootsStageProc` turns a set of flagged vertex indices into the index arrays of the forest `F`.
It first closes the flags upward in `T_H` (`upClosureProc`). Then it runs the three parts of the
roots pass on the closed flags: the smallest edge on the way up (`frMpProc`), the owner of each
deleted edge (`frOwnProc`) and the forest root of each vertex (`frRtProc`).

`rootsStage_meetsContract` states the result in memory terms: the closed flags, `MpRule`,
`OwnState` and `RtRule`. These are the facts that `RootPassIdx` (`FForestMath.lean`) asks for.
The cost is `O(D n + tM)`, where `D` bounds the depths in `T_H`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- Args: `[n, tM, r, qPtr, parPtr, pePtr, piPtr, thParPtr, thDepPtr, D, inRPtr, mpPtr, ownPtr,
rtPtr]`. -/
def rootsStageProc (bUp bMp bOwn bRt : ℕ) : Stmt :=
  .call 14 bUp [.reg 0, .reg 7, .reg 8, .reg 10, .reg 9] ;;
  .call 14 bMp [.reg 0, .reg 3, .reg 4, .reg 5, .reg 6, .reg 10, .reg 11, .reg 1] ;;
  .call 14 bOwn [.reg 0, .reg 2, .reg 11, .reg 10, .reg 12, .reg 1] ;;
  .call 14 bRt [.reg 0, .reg 3, .reg 4, .reg 5, .reg 10, .reg 12, .reg 13] ;;
  .ret (.const 0)

lemma rootsStageProc_noRand (bUp bMp bOwn bRt : ℕ) : (rootsStageProc bUp bMp bOwn bRt).NoRand := by
  simp [rootsStageProc, Stmt.NoRand]

open Classical in
/-- The contract of `rootsStageProc`. The inputs lie below the flags at `inRPtr`, and the outputs
`mp`, `own`, `rt` lie above them. -/
def rootsStageContract (w : ℕ) : Contract where
  pre args mem := ∃ (n tM r qPtr parPtr pePtr piPtr thParPtr thDepPtr D inRPtr mpPtr ownPtr
      rtPtr : ℕ) (Q : List ℕ),
    args = [n, tM, r, qPtr, parPtr, pePtr, piPtr, thParPtr, thDepPtr, D, inRPtr, mpPtr, ownPtr,
      rtPtr] ∧ 16 ≤ 2 ^ w ∧ 0 < n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    (∀ x < n, x ≠ r → mem (pePtr + x) < tM) ∧
    ParDep n (fun x => mem (thDepPtr + x)) (fun x => mem (thParPtr + x)) ∧
    (∀ x < n, mem (thDepPtr + x) ≤ D) ∧
    (∀ x < n, mem (inRPtr + x) ≤ 1) ∧ mem (inRPtr + r) = 1 ∧
    qPtr + n ≤ inRPtr ∧ parPtr + n ≤ inRPtr ∧ pePtr + n ≤ inRPtr ∧ piPtr + tM ≤ inRPtr ∧
    thParPtr + n ≤ inRPtr ∧ thDepPtr + n ≤ inRPtr ∧
    inRPtr + n ≤ mpPtr ∧ mpPtr + n ≤ ownPtr ∧ ownPtr + tM ≤ rtPtr ∧ rtPtr + n < 2 ^ w
  post args mem ret mem' := ∃ (n tM r qPtr parPtr pePtr piPtr thParPtr thDepPtr D inRPtr mpPtr
      ownPtr rtPtr : ℕ),
    args = [n, tM, r, qPtr, parPtr, pePtr, piPtr, thParPtr, thDepPtr, D, inRPtr, mpPtr, ownPtr,
      rtPtr] ∧ ret = 0 ∧
    (∀ a, (a < inRPtr ∨ inRPtr + n ≤ a) → (a < mpPtr ∨ rtPtr + n ≤ a) → mem' a = mem a) ∧
    (∀ y < n, mem' (inRPtr + y) =
      if ∃ u < n, mem (inRPtr + u) = 1 ∧
        IdxAnc (fun x => mem (thDepPtr + x)) (fun x => mem (thParPtr + x)) y u then 1 else 0) ∧
    mem' (mpPtr + r) = 0 ∧
    (∀ x < n, x ≠ r → mem' (mpPtr + x) < tM ∧
      MpRule (fun y => mem' (inRPtr + y)) (fun y => mem (parPtr + y)) (fun y => mem (pePtr + y))
        (fun i => mem (piPtr + i)) (fun y => mem' (mpPtr + y)) x) ∧
    OwnState r tM (fun y => mem' (inRPtr + y)) (fun y => mem' (mpPtr + y))
      (fun i => mem' (ownPtr + i)) n ∧
    mem' (rtPtr + r) = r ∧
    (∀ x < n, x ≠ r → RtRule (fun y => mem' (inRPtr + y)) (fun y => mem (parPtr + y))
      (fun y => mem (pePtr + y)) (fun i => mem' (ownPtr + i)) (fun y => mem' (rtPtr + y)) x)
  cost args _ := args.getD 9 0 * (70 * args.getD 0 0 + 80) + 30 * args.getD 1 0 +
    400 * args.getD 0 0 + 400

lemma mpRule_congrM {inR par pe piv mp inR' par' pe' piv' mp' : ℕ → ℕ} {x : ℕ}
    (h1 : inR' (par' x) = inR (par x)) (h2 : par' x = par x) (h3 : pe' x = pe x)
    (h4 : piv' (pe x) = piv (pe x)) (h5 : mp' x = mp x) (h6 : mp' (par x) = mp (par x))
    (h7 : inR (par x) ≠ 1 → piv' (mp (par x)) = piv (mp (par x)))
    (h : MpRule inR par pe piv mp x) : MpRule inR' par' pe' piv' mp' x := by
  unfold MpRule at h ⊢
  rw [h5, h1, h2, h3, h6]
  by_cases hc : inR (par x) = 1
  · simp only [hc, if_true] at h ⊢
    exact h
  · simp only [hc, if_false] at h ⊢
    rw [h4, h7 hc]
    exact h

lemma rtRule_congrM {inR par pe own rt inR' par' pe' own' rt' : ℕ → ℕ} {x : ℕ}
    (h1 : inR' x = inR x) (h2 : par' x = par x) (h3 : pe' x = pe x)
    (h4 : own' (pe x) = own (pe x)) (h5 : rt' x = rt x) (h6 : rt' (par x) = rt (par x))
    (h : RtRule inR par pe own rt x) : RtRule inR' par' pe' own' rt' x := by
  unfold RtRule at h ⊢
  rw [h5, h1, h3, h4, h2, h6]
  exact h

lemma ownState_congr3 {r tM n : ℕ} {inR mp own inR' mp' own' : ℕ → ℕ}
    (hI : ∀ y < n, inR' y = inR y) (hM : ∀ y < n, mp' y = mp y) (hO : ∀ i < tM, own' i = own i)
    (h : OwnState r tM inR mp own n) : OwnState r tM inR' mp' own' n := by
  intro i hi
  rw [hO i hi]
  obtain ⟨h1, h2⟩ := h i hi
  refine ⟨fun hne => ?_, fun h0 y hy hyr hy1 => ?_⟩
  · obtain ⟨a, b, c, d⟩ := h1 hne
    exact ⟨a, b, by rw [hI _ a]; exact c, by rw [hM _ a]; exact d⟩
  · rw [hM y hy]
    exact h2 h0 y hy hyr (by rw [← hI y hy]; exact hy1)

theorem rootsStage_meetsContract {w : ℕ} {p : Program} {b bUp bMp bOwn bRt : ℕ}
    (hp : p.procs[b]? = some (rootsStageProc bUp bMp bOwn bRt))
    (hUp : MeetsContract w p bUp (upClosureContract w))
    (hMp : MeetsContract w p bMp (frMpContract w))
    (hOwn : MeetsContract w p bOwn (frOwnContract w))
    (hRt : MeetsContract w p bRt (frRtContract w)) :
    MeetsContract w p b (rootsStageContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, tM, r, qPtr, parPtr, pePtr, piPtr, thParPtr, thDepPtr, D, inRPtr, mpPtr, ownPtr,
    rtPtr, Q, rfl, hw16, hn, hQ, hQat, hpe, hPD, hDle, hin, hinr, hq, hpar, hpeb, hpib, htp, htd,
    hmpb, hownb, hrtb, hrtw⟩ := hpre
  set args := [n, tM, r, qPtr, parPtr, pePtr, piPtr, thParPtr, thDepPtr, D, inRPtr, mpPtr, ownPtr,
    rtPtr] with hargs
  have hR0 : ∀ i < 14, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 14, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hrn : r < n := by
    have h0 := hQ.head_eq hn
    rw [← h0]; exact hQ.lt _ (List.getElem_mem _)
  have hQlen := hQ.len
  have hparlt : ∀ x < n, x ≠ r → mem (parPtr + x) < n := by
    intro x hx hxr
    obtain ⟨i, hi, hQi⟩ := List.getElem_of_mem (hQ.cover x hx)
    have hp := hQ.after i hi (by rw [hQi]; exact hxr)
    rw [hQi] at hp
    exact hQ.lt _ (List.mem_of_mem_take hp)
  -- the inputs below `inRPtr` stay
  have hlow : ∀ memX : ℕ → ℕ, (∀ a < inRPtr, memX a = mem a) →
      (∀ x < n, memX (parPtr + x) = mem (parPtr + x)) ∧
      TopDownOrder n r (fun x => memX (parPtr + x)) Q ∧ ListAt memX qPtr Q := by
    intro memX hX
    have hpX : ∀ x < n, memX (parPtr + x) = mem (parPtr + x) := fun x hx => hX _ (by omega)
    exact ⟨hpX, hQ.congr (fun x hx => (hpX x hx).symm),
      fun i hi => by rw [hX _ (by rw [hQlen] at hi; omega)]; exact hQat i hi⟩
  refine runs_start_le ?_
  unfold rootsStageProc
  have r0 := hR0 0 (by omega)
  have r1 := hR0 1 (by omega)
  have r2 := hR0 2 (by omega)
  have r3 := hR0 3 (by omega)
  have r4 := hR0 4 (by omega)
  have r5 := hR0 5 (by omega)
  have r6 := hR0 6 (by omega)
  have r7 := hR0 7 (by omega)
  have r8 := hR0 8 (by omega)
  have r9 := hR0 9 (by omega)
  have r10 := hR0 10 (by omega)
  have r11 := hR0 11 (by omega)
  have r12 := hR0 12 (by omega)
  have r13 := hR0 13 (by omega)
  -- 1. the upward closure of the flags
  refine runs_seq_call_le (vs := [n, thParPtr, thDepPtr, inRPtr, D]) hUp
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 7 (by omega)
      · exact hwa 8 (by omega)
      · exact hwa 10 (by omega)
      · exact hwa 9 (by omega))
    ⟨n, thParPtr, thDepPtr, inRPtr, D, rfl, hw16, htp, htd, by omega, hPD, hDle, hin⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨n', thParPtr', thDepPtr', inRPtr', D', heq₁, -, hfr₁, hcl⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hfr₁ hcl
  have hA1 : ∀ a < inRPtr, mem₁ a = mem a := fun a ha => hfr₁ a (Or.inl ha)
  obtain ⟨hp₁, hQ₁, hQat₁⟩ := hlow mem₁ hA1
  have hin₁ : ∀ y < n, mem₁ (inRPtr + y) ≤ 1 := by
    intro y hy
    rw [hcl y hy]
    split_ifs <;> omega
  have hinr₁ : mem₁ (inRPtr + r) = 1 := by
    rw [hcl r hrn, if_pos ⟨r, hrn, hinr, le_refl _, by simp⟩]
  have hpe₁ : ∀ x < n, x ≠ r → mem₁ (pePtr + x) < tM := fun x hx hxr => by
    rw [hA1 _ (by omega)]; exact hpe x hx hxr
  -- 2. the smallest edges going up
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM]) hMp
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 6 (by omega)
      · exact hwa 10 (by omega)
      · exact hwa 11 (by omega)
      · exact hwa 1 (by omega))
    ⟨n, qPtr, parPtr, pePtr, piPtr, inRPtr, mpPtr, tM, r, Q, rfl, hn, hQ₁, hQat₁, hpe₁, hin₁,
      hinr₁, by omega, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨n', qPtr', parPtr', pePtr', piPtr', inRPtr', mpPtr', tM', heq₂, -, hfr₂,
    hmp₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hfr₂ hmp₂
  obtain ⟨hmpr, hmpx⟩ := hmp₂ Q r hQ₁ hQat₁
  have hA2 : ∀ a, a < mpPtr ∨ mpPtr + n ≤ a → mem₂ a = mem₁ a := hfr₂
  have hin₂ : ∀ y < n, mem₂ (inRPtr + y) = mem₁ (inRPtr + y) := fun y hy => hA2 _ (by omega)
  obtain ⟨hp₂, hQ₂, hQat₂⟩ := hlow mem₂ (fun a ha => (hA2 a (by omega)).trans (hA1 a ha))
  -- 3. the owners of the deleted edges
  refine runs_seq_call_le (vs := [n, r, mpPtr, inRPtr, ownPtr, tM]) hOwn
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _)))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 11 (by omega)
      · exact hwa 10 (by omega)
      · exact hwa 12 (by omega)
      · exact hwa 1 (by omega))
    ⟨n, r, mpPtr, inRPtr, ownPtr, tM, rfl, hrn,
      fun y hy => by dsimp only; rw [hin₂ y hy]; exact hin₁ y hy,
      fun y hy hyr _ => (hmpx y hy hyr).1, by omega, by omega, by omega⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨n', r', mpPtr', inRPtr', ownPtr', tM', heq₃, -, hfr₃, hown₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hfr₃ hown₃
  have hA3 : ∀ a, a < ownPtr ∨ ownPtr + tM ≤ a → mem₃ a = mem₂ a := hfr₃
  have hin₃ : ∀ y < n, mem₃ (inRPtr + y) = mem₁ (inRPtr + y) := fun y hy =>
    (hA3 _ (by omega)).trans (hin₂ y hy)
  have hmp₃ : ∀ y < n, mem₃ (mpPtr + y) = mem₂ (mpPtr + y) := fun y hy => hA3 _ (by omega)
  obtain ⟨hp₃, hQ₃, hQat₃⟩ := hlow mem₃ (fun a ha => ((hA3 a (by omega)).trans
    (hA2 a (by omega))).trans (hA1 a ha))
  have hpe₃ : ∀ x < n, x ≠ r → mem₃ (pePtr + x) < tM := fun x hx hxr => by
    rw [hA3 _ (by omega), hA2 _ (by omega)]; exact hpe₁ x hx hxr
  have hownle : ∀ i < tM, mem₃ (ownPtr + i) ≤ n := by
    intro i hi
    by_cases h0 : mem₃ (ownPtr + i) = 0
    · omega
    · have : mem₃ (ownPtr + i) - 1 < n := ((hown₃ i hi).1 h0).1
      omega
  -- 4. the forest roots
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr]) hRt
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 10 (by omega)
      · exact hwa 12 (by omega)
      · exact hwa 13 (by omega))
    ⟨n, qPtr, parPtr, pePtr, inRPtr, ownPtr, rtPtr, tM, r, Q, rfl, hn, hQ₃, hQat₃, hpe₃,
      fun y hy => by dsimp only; rw [hin₃ y hy]; exact hin₁ y hy, hownle,
      by omega, by omega, by omega, by omega, by omega, hrtw⟩ ?_
  rintro v₄ mem₄ pos₄ ⟨n', qPtr', parPtr', pePtr', inRPtr', ownPtr', rtPtr', heq₄, -, hfr₄,
    hrt₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₄
  try dsimp only at hfr₄ hrt₄
  obtain ⟨hrtr, hrtx⟩ := hrt₄ Q r hQ₃ hQat₃
  have hA4 : ∀ a, a < rtPtr ∨ rtPtr + n ≤ a → mem₄ a = mem₃ a := hfr₄
  -- what the final memory holds
  have hlo4 : ∀ a < inRPtr, mem₄ a = mem a := fun a ha =>
    (((hA4 a (by omega)).trans (hA3 a (by omega))).trans (hA2 a (by omega))).trans (hA1 a ha)
  have hin4 : ∀ y < n, mem₄ (inRPtr + y) = mem₁ (inRPtr + y) := fun y hy =>
    (hA4 _ (by omega)).trans (hin₃ y hy)
  have hmp4 : ∀ y < n, mem₄ (mpPtr + y) = mem₂ (mpPtr + y) := fun y hy =>
    (hA4 _ (by omega)).trans (hmp₃ y hy)
  have hown4 : ∀ i < tM, mem₄ (ownPtr + i) = mem₃ (ownPtr + i) := fun i hi => hA4 _ (by omega)
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, tM, r, qPtr, parPtr, pePtr, piPtr, thParPtr,
    thDepPtr, D, inRPtr, mpPtr, ownPtr, rtPtr, rfl, rfl, fun a ha1 ha2 => ?_,
    fun y hy => ?_, ?_, fun x hx hxr => ?_, ?_, hrtr, fun x hx hxr => ?_⟩ ?_
  · show mem₄ a = mem a
    rw [hA4 a (by omega), hA3 a (by omega), hA2 a (by omega), hfr₁ a ha1]
    rfl
  · show mem₄ (inRPtr + y) = _
    rw [hin4 y hy]
    exact hcl y hy
  · show mem₄ (mpPtr + r) = 0
    rw [hmp4 r hrn]
    exact hmpr
  · have hpx := hparlt x hx hxr
    have hpx₁ : mem₁ (parPtr + x) = mem (parPtr + x) := hp₁ x hx
    have hpe₁x := hpe₁ x hx hxr
    obtain ⟨hlt, hrule⟩ := hmpx x hx hxr
    refine ⟨by show mem₄ (mpPtr + x) < tM; rw [hmp4 x hx]; exact hlt, ?_⟩
    refine mpRule_congrM (by (try dsimp only); rw [hpx₁, hin4 _ hpx]) (by (try dsimp only); rw [hpx₁])
      (by (try dsimp only); exact (hA1 _ (by omega)).symm) (by (try dsimp only); exact (hA1 _ (by omega)).symm)
      (by (try dsimp only); rw [hmp4 x hx]) (by (try dsimp only); rw [hmp4 _ (by rw [hpx₁]; exact hpx)])
      (fun hc => ?_) hrule
    try dsimp only at hc ⊢
    have hpr : mem₁ (parPtr + x) ≠ r := by
      intro he
      rw [he, hinr₁] at hc
      exact hc rfl
    have := (hmpx _ (by rw [hpx₁]; exact hpx) hpr).1
    exact (hA1 _ (by omega)).symm
  · exact ownState_congr3 (fun y hy => (hin4 y hy).trans (hin₂ y hy).symm) hmp4 hown4 hown₃
  · have hpx := hparlt x hx hxr
    have hpx₃ : mem₃ (parPtr + x) = mem (parPtr + x) := hp₃ x hx
    refine rtRule_congrM (by (try dsimp only); rw [hin4 x hx, hin₃ x hx]) (by (try dsimp only); rw [hpx₃])
      (by (try dsimp only); exact (((hA3 _ (by omega)).trans (hA2 _ (by omega))).trans
        (hA1 _ (by omega))).symm)
      (by (try dsimp only); rw [hown4 _ (hpe₃ x hx hxr)]) rfl rfl (hrtx x hx hxr)
  · simp only [rootsStageContract, upClosureContract, frMpContract, frOwnContract,
      frRtContract, hargs, List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size_const,
      Expr.size_reg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

open Classical in
/-- The output of `rootsStageProc` is the roots pass for the upward closure of the flagged set
`R` in `T_H`. -/
theorem rootsStage_rootPassIdx {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep dTH thPar f inR piv mp own rt π : ℕ → ℕ} {R : Finset ℕ}
    (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) (hTH : THIdx T₀ vList r dTH thPar)
    (hRV : ∀ v ∈ R, v ∈ vList) (hf : ∀ u < vList.length, f u = 1 ↔ vList.getD u 0 ∈ R)
    (hrR : vList.getD r 0 ∈ R) (hπ : IsEdgeOrder T₀ π) (hpiv : ∀ i < tM, π (fid i) = piv i)
    (hinR : ∀ y < vList.length, inR y =
      if ∃ u < vList.length, f u = 1 ∧ IdxAnc dTH thPar y u then 1 else 0)
    (hmp : ∀ x < vList.length, x ≠ r → MpRule inR par pe piv mp x)
    (hown : OwnState r tM inR mp own vList.length) (hrt : rt r = r)
    (hrule : ∀ x < vList.length, x ≠ r → RtRule inR par pe own rt x) :
    RootPassIdx T₀ vList tM r fid par pe
      (upClosure (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) R) π inR piv mp own rt := by
  refine ⟨⟨upClosure_isBranchFree hI.hT (fun v hv => (hI.hV v).mpr (hRV v hv)),
    subset_upClosure hrR, fun x hx => ?_, hπ, hpiv⟩, hmp, hown, hrt, hrule⟩
  rw [hinR x hx, ← hTH.upClosure_flag hI hRV hf hx]
  split_ifs with h <;> simp [h]

end

end MinCostFlow.LSF.Program
