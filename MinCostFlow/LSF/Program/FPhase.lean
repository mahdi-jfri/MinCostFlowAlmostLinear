module

public import MinCostFlow.LSF.Program.CallSeq
public import MinCostFlow.LSF.Program.FAncFill
public import MinCostFlow.LSF.Program.WBlockProof
public import MinCostFlow.LSF.Program.OrderPhasePre

/-!
# The forest phase of the initialization

After the decomposition phase, the root set, the owner of each tree edge (`own`) and the root of
each vertex in `F` (`rt`) are in scratch. The forest phase writes three static blocks with a call
sequence of three calls:
1. `fGraphProc`: the graph block of `F`, from the tree edges whose owner is `0`;
2. `fAncFillProc`: the `FAnc` block (root flags, root list, component ids, roots and sizes);
3. `wBlockProc`: the `W` block, the pieces of `W_init`, with keys of `logCap` limbs.

The three blocks lie in the static area, below every array that the calls read, and the work
area of `wBlockProc` lies above them. So no call writes what a later call reads, and the pre of
each call holds on the start memory up to its zero areas (`fPhase_seqPre`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The places of the forest phase. -/
structure FLayout where
  dgF : ℕ
  vCap : ℕ
  eCap : ℕ
  n : ℕ
  vListPtr : ℕ
  tM : ℕ
  tTail : ℕ
  tHead : ℕ
  fid : ℕ
  own : ℕ
  fAnc : ℕ
  inR : ℕ
  rt : ℕ
  auxPar : ℕ
  dBase : ℕ
  logCap : ℕ
  wBase : ℕ
  wPtr : ℕ

/-- The `21` arguments of the phase. -/
def FLayout.args (X : FLayout) : List ℕ :=
  [X.dgF, X.vCap, X.eCap, X.n, X.vListPtr, X.tM, X.tTail, X.tHead, X.fid, X.own,
    X.fAnc, X.inR, X.rt, 0, X.auxPar + X.n, X.dBase + 6 * X.n, X.dBase + 7 * X.n, X.logCap,
    X.wBase, X.auxPar, X.wPtr]

/-- The calls of the forest phase. -/
def fPhaseItems (w h : ℕ) (bG bA bW : ℕ) : List CallItem :=
  [⟨bG, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], fGraphContract w⟩,
   ⟨bA, [10, 1, 3, 4, 11, 12], fAncFillContract w⟩,
   ⟨bW, [3, 13, 14, 9, 15, 16, 12, 17, 18, 19, 8, 4, 20, 3], wBlockContract w h⟩]

/-- The cost of the forest phase, from its arguments. -/
def fPhaseCost (a : List ℕ) (_ : ℕ → ℕ) : ℕ :=
  (150 * a.getD 3 0 + 620 * a.getD 5 0 + 112) + (120 * a.getD 3 0 + 108) +
  (a.getD 3 0 * (90 * a.getD 17 0 + 250) +
    (270 * a.getD 17 0 + 180) * a.getD 3 0 * (Nat.clog 2 (a.getD 3 0) + 1) +
    400 * a.getD 3 0 + 616) + 2

/-- The contract of the forest phase. -/
def fPhaseContract (w h : ℕ) (bG bA bW : ℕ) : Contract :=
  callSeqContract w 21 13 (fPhaseItems w h bG bA bW) fPhaseCost

/-- The body of the forest phase. -/
def fPhaseProc (w h : ℕ) (bG bA bW : ℕ) : Stmt := callSeqStmt 21 13 0 (fPhaseItems w h bG bA bW)

theorem fPhase_meetsContract {w h : ℕ} {p : Program} {b bG bA bW : ℕ}
    (hp : p.procs[b]? = some (fPhaseProc w h bG bA bW))
    (hG : MeetsContract w p bG (fGraphContract w))
    (hA : MeetsContract w p bA (fAncFillContract w))
    (hW : MeetsContract w p bW (wBlockContract w h)) :
    MeetsContract w p b (fPhaseContract w h bG bA bW) := by
  refine callSeq_meetsContract hp ?_
  intro it hit
  simp only [fPhaseItems, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl
  exacts [hG, hA, hW]

/-- The memory at the start of the forest phase. -/
structure FPhaseIn (w h : ℕ) (X : FLayout) (mem : ℕ → ℕ) : Prop where
  hw16 : 16 ≤ 2 ^ w
  hh : 1 ≤ h
  hn : 0 < X.n
  hnv : X.n ≤ X.vCap
  hL : 1 ≤ X.logCap
  hnL : X.n < 2 ^ X.logCap
  hzG : ∀ i < dynGraphSize X.vCap X.eCap, mem (X.dgF + i) = 0
  hzA : ∀ i < fAncSize X.vCap, mem (X.fAnc + i) = 0
  hzW : ∀ y < X.n, mem (X.wBase + X.n * (3 * X.logCap) + 2 * X.n + y) = 0
  hvL : ∀ x < X.n, mem (X.vListPtr + x) < X.vCap
  hvInj : ∀ x < X.n, ∀ y < X.n, mem (X.vListPtr + x) = mem (X.vListPtr + y) → x = y
  hT : ∀ i < X.tM, mem (X.tTail + i) < X.n ∧ mem (X.tHead + i) < X.n ∧ mem (X.fid + i) < X.eCap
  hrt : ∀ x < X.n, mem (X.rt + x) < X.n
  hlab : ∀ x < X.n, mem (X.dBase + 6 * X.n + x) < X.n ∧ mem (X.dBase + 7 * X.n + x) < X.n
  hpar : ∀ x < X.n, mem (X.auxPar + x) < X.n
  hpe : ∀ x < X.n, x ≠ 0 → mem (X.auxPar + X.n + x) < X.tM
  -- the layout: the static blocks, then the read arrays, then the work area
  l1 : X.fid + X.tM ≤ X.dgF
  l2 : X.dgF + dynGraphSize X.vCap X.eCap ≤ X.fAnc
  l3 : X.fAnc + fAncSize X.vCap ≤ X.wPtr
  l4 : X.wPtr + wBlockSize X.n ≤ X.vListPtr
  l5 : X.wPtr + wBlockSize X.n ≤ X.tTail
  l6 : X.wPtr + wBlockSize X.n ≤ X.tHead
  l7 : X.wPtr + wBlockSize X.n ≤ X.own
  l8 : X.wPtr + wBlockSize X.n ≤ X.inR
  l9 : X.wPtr + wBlockSize X.n ≤ X.rt
  l10 : X.wPtr + wBlockSize X.n ≤ X.auxPar
  l11 : X.wPtr + wBlockSize X.n ≤ X.dBase
  l12 : X.vListPtr + X.n ≤ X.wBase
  l13 : X.tTail + X.tM ≤ X.wBase
  l14 : X.tHead + X.tM ≤ X.wBase
  l15 : X.own + X.tM ≤ X.wBase
  l16 : X.inR + X.n ≤ X.wBase
  l17 : X.rt + X.n ≤ X.wBase
  l18 : X.auxPar + 2 * X.n ≤ X.wBase
  l19 : X.dBase + 8 * X.n ≤ X.wBase
  l20 : X.wBase + wWorkSize X.n X.logCap < 2 ^ w

/-- `FPhaseIn` gives the pre of the forest phase. -/
theorem fPhase_seqPre {w h : ℕ} {X : FLayout} {mem : ℕ → ℕ} (I : FPhaseIn w h X mem)
    (bG bA bW : ℕ) :
    SeqPre w 21 0 (fPhaseItems w h bG bA bW) (fun j => X.args.getD j 0) mem
      (fPhaseCost X.args mem) := by
  have hn := I.hn; have hL := I.hL
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
  have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10
  have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15
  have l16 := I.l16; have l17 := I.l17; have l18 := I.l18; have l19 := I.l19; have l20 := I.l20
  have hws : X.n * (3 * X.logCap) + 3 * X.n = wWorkSize X.n X.logCap := rfl
  have h3L : 3 * X.logCap ≤ X.n * (3 * X.logCap) := Nat.le_mul_of_pos_left _ hn
  have hvC : X.vCap ≤ dynGraphSize X.vCap X.eCap := by unfold dynGraphSize; omega
  have heC : X.eCap ≤ dynGraphSize X.vCap X.eCap := by unfold dynGraphSize; omega
  have hgd : ∀ j < 21, (fun j => X.args.getD j 0) j < 2 ^ w := by
    intro j hj
    interval_cases j <;> simp only [FLayout.args, List.getD_cons_zero, List.getD_cons_succ] <;>
      omega
  set c1 := 150 * X.n + 620 * X.tM + 112 with hc1
  set c2 := 120 * X.n + 108 with hc2
  set c3 := X.n * (90 * X.logCap + 250) +
    (270 * X.logCap + 180) * X.n * (Nat.clog 2 X.n + 1) + 400 * X.n + 616 with hc3
  have hB : fPhaseCost X.args mem = c1 + c2 + c3 + 2 := rfl
  -- 1. the graph block of `F`
  refine SeqPre.cons [X.dgF, X.vCap, X.eCap, X.n, X.vListPtr, X.tM, X.tTail, X.tHead, X.fid,
      X.own] c1 rfl
    (words_of_map fun j hj => hgd j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    ⟨_, _, _, _, _, _, _, _, _, _, rfl, I.hw16, by omega, I.hzG, ⟨Or.inr (by omega), by omega⟩,
      ⟨Or.inr (by omega), by omega⟩, ⟨Or.inr (by omega), by omega⟩,
      ⟨Or.inl (by omega), by omega⟩, ⟨Or.inr (by omega), by omega⟩, I.hvL, I.hT⟩
    (by simp [fGraphContract]; omega) (by omega) ?_
  intro v₁ m₁ hp₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₁, -, -, hfr₁⟩ := hp₁
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  have hw1 := upd_words (i := 21 + 0) (v := v₁) hgd (by omega)
  have hm₁ : ∀ a, X.fAnc ≤ a → m₁ a = mem a := fun a ha => hfr₁ a (Or.inr (by omega))
  -- 2. the `FAnc` block
  refine SeqPre.cons [X.fAnc, X.vCap, X.n, X.vListPtr, X.inR, X.rt] c2 rfl
    (words_of_map fun j hj => hw1 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    ⟨_, _, _, _, _, _, rfl, I.hw16, by unfold fAncSize at *; omega, I.hnv,
      fun i hi => by rw [hm₁ _ (by omega)]; exact I.hzA i hi,
      ⟨Or.inr (by omega), by omega⟩, ⟨Or.inr (by omega), by omega⟩,
      ⟨Or.inr (by omega), by omega⟩,
      fun x hx => by
        rw [hm₁ _ (by omega), hm₁ _ (by omega)]; exact ⟨I.hvL x hx, I.hrt x hx⟩,
      fun x hx y hy hxy => I.hvInj x hx y hy (by
        rw [hm₁ _ (by omega), hm₁ _ (by omega)] at hxy; exact hxy)⟩
    (by simp [fAncFillContract]; omega) (by omega) ?_
  intro v₂ m₂ hp₂
  obtain ⟨_, _, _, _, _, _, heq₂, -, hfr₂, -⟩ := hp₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  have hw2 := upd_words (i := 21 + 1) (v := v₂) hw1 (by omega)
  have hm₂ : ∀ a, X.wPtr ≤ a → m₂ a = mem a := fun a ha => by
    rw [hfr₂ a (Or.inr (by omega)), hm₁ a (by omega)]
  -- 3. the `W` block
  refine SeqPre.cons [X.n, 0, X.auxPar + X.n, X.own, X.dBase + 6 * X.n, X.dBase + 7 * X.n, X.rt,
      X.logCap, X.wBase, X.auxPar, X.fid, X.vListPtr, X.wPtr, X.n] c3 rfl
    (words_of_map fun j hj => hw2 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    ⟨X.n, 0, X.auxPar + X.n, X.own, X.dBase + 6 * X.n, X.dBase + 7 * X.n, X.rt, X.logCap, X.wBase,
      X.auxPar, X.fid, X.vListPtr, X.wPtr, X.n, X.tM, rfl, I.hw16, hL, by omega,
      le_trans I.hnL.le (by
        rw [capacity, base, ← pow_mul]
        exact Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ I.hh)),
      le_rfl, by omega, by unfold wBlockSize at *; omega, Or.inr (by omega),
      fun y hy => by rw [hm₂ _ (by omega)]; exact I.hzW y hy,
      ⟨Or.inl (by omega), Or.inr (by omega), by omega⟩,
      ⟨Or.inl (by omega), Or.inr (by omega), by omega⟩,
      ⟨Or.inl (by omega), Or.inr (by omega), by omega⟩,
      ⟨Or.inl (by omega), Or.inr (by omega), by omega⟩,
      ⟨Or.inl (by omega), Or.inr (by omega), by omega⟩,
      ⟨Or.inl (by omega), Or.inr (by omega), by omega⟩,
      ⟨Or.inl (by omega), Or.inl (by omega), by omega⟩,
      ⟨Or.inl (by omega), Or.inr (by omega), by omega⟩,
      fun x hx hx0 => by rw [hm₂ _ (by omega)]; exact I.hpe x hx hx0,
      fun x hx => by rw [hm₂ _ (by omega)]; exact I.hpar x hx,
      fun x hx => by
        rw [hm₂ _ (by omega), hm₂ _ (by omega), hm₂ _ (by omega)]
        exact ⟨(I.hlab x hx).1, (I.hlab x hx).2, I.hrt x hx⟩⟩
    (by simp [wBlockContract]; omega) (by omega) ?_
  intro v₃ m₃ _
  show 2 ≤ _
  omega

/-- The post of the forest phase, call by call, with the arguments written out. -/
theorem fPhase_post {w h : ℕ} {X : FLayout} {bG bA bW : ℕ} {mem mem₃ : ℕ → ℕ} {ret : ℕ}
    (hpost : (fPhaseContract w h bG bA bW).post X.args mem ret mem₃) :
    ∃ v₁ m₁ v₂ m₂ v₃,
      (fGraphContract w).post [X.dgF, X.vCap, X.eCap, X.n, X.vListPtr, X.tM, X.tTail, X.tHead,
        X.fid, X.own] mem v₁ m₁ ∧
      (fAncFillContract w).post [X.fAnc, X.vCap, X.n, X.vListPtr, X.inR, X.rt] m₁ v₂ m₂ ∧
      (wBlockContract w h).post [X.n, 0, X.auxPar + X.n, X.own, X.dBase + 6 * X.n,
        X.dBase + 7 * X.n, X.rt, X.logCap, X.wBase, X.auxPar, X.fid, X.vListPtr, X.wPtr, X.n]
        m₂ v₃ mem₃ := by
  obtain ⟨v₁, m₁, h₁, v₂, m₂, h₂, v₃, m₃, h₃, h₄, -⟩ := hpost
  subst h₄
  exact ⟨v₁, m₁, v₂, m₂, v₃, h₁, h₂, h₃⟩

end

end MinCostFlow.LSF.Program
