module

public import MinCostFlow.LSF.Program.FGraph

/-!
# The root and component block of `F`

`fAncFillProc` writes the block of `FAncAt` (`BlockRep.lean`) from three index arrays: the
vertex list `vL`, the root flags `inR` and the forest root `rt x` of every index. It makes one
pass over the indices `x`. With `v = vL x` and `c = vL (rt x)` it writes

* `compId[v] := c` and `compSize[c] += 1`;
* if `x` is a root: `isRoot[v] := 1`, `compRoot[v] := v`, and `v` at the end of the root list.

Then it writes the header. The block must be zero at the start. The result is
`fAncFill_meetsContract`, at cost `O(n)`. The component of a vertex is named by its root, so
the component IDs are the roots.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## The values -/

/-- The roots among the first `j` indices, in index order. -/
def rootList (vL inR : ℕ → ℕ) (j : ℕ) : List ℕ :=
  ((List.range j).filter (fun x => inR x = 1)).map vL

lemma rootList_succ (vL inR : ℕ → ℕ) (j : ℕ) :
    rootList vL inR (j + 1) = if inR j = 1 then rootList vL inR j ++ [vL j]
      else rootList vL inR j := by
  unfold rootList
  rw [List.range_succ, List.filter_append]
  by_cases h : inR j = 1 <;> simp [h]

lemma rootList_length_le (vL inR : ℕ → ℕ) (j : ℕ) : (rootList vL inR j).length ≤ j := by
  unfold rootList
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

open Classical in
/-- The root flag of `v` after the first `j` indices. -/
noncomputable def isRootVal (vL inR : ℕ → ℕ) (j v : ℕ) : ℕ :=
  if ∃ x < j, inR x = 1 ∧ vL x = v then 1 else 0

/-- The size of the component named `v` after the first `j` indices. -/
def sizeVal (vL rt : ℕ → ℕ) (j v : ℕ) : ℕ :=
  ((Finset.range j).filter (fun x => vL (rt x) = v)).card

lemma sizeVal_succ (vL rt : ℕ → ℕ) (j v : ℕ) :
    sizeVal vL rt (j + 1) v = sizeVal vL rt j v + if vL (rt j) = v then 1 else 0 := by
  unfold sizeVal
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma isRootVal_succ (vL inR : ℕ → ℕ) (j v : ℕ) :
    isRootVal vL inR (j + 1) v = if inR j = 1 ∧ vL j = v then 1 else isRootVal vL inR j v := by
  unfold isRootVal
  by_cases h : inR j = 1 ∧ vL j = v
  · rw [if_pos h, if_pos ⟨j, by omega, h⟩]
  · rw [if_neg h]
    refine if_congr ⟨fun ⟨x, hx, hP⟩ => ⟨x, ?_, hP⟩, fun ⟨x, hx, hP⟩ => ⟨x, by omega, hP⟩⟩ rfl rfl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
    · exact hx
    · exact absurd hP h

lemma sizeVal_le (vL rt : ℕ → ℕ) (j v : ℕ) : sizeVal vL rt j v ≤ j := by
  unfold sizeVal
  exact (Finset.card_filter_le _ _).trans (by simp)

/-! ## The procedure -/

/-- The loop body (register `6` is `x`, register `7` the number of roots so far). -/
def fAncBody : Stmt :=
  .assign 8 (.load (.bin .add (.reg 3) (.reg 6))) ;;
  .assign 9 (.load (.bin .add (.reg 3) (.load (.bin .add (.reg 5) (.reg 6))))) ;;
  .store (.bin .add (.reg 12) (.reg 8)) (.reg 9) ;;
  .store (.bin .add (.reg 14) (.reg 9))
    (.bin .add (.load (.bin .add (.reg 14) (.reg 9))) (.const 1)) ;;
  .cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 6))) (.const 1))
    (.store (.bin .add (.reg 10) (.reg 8)) (.const 1) ;;
     .store (.bin .add (.reg 11) (.reg 7)) (.reg 8) ;;
     .store (.bin .add (.reg 13) (.reg 8)) (.reg 8) ;;
     .assign 7 (.bin .add (.reg 7) (.const 1)))
    .nop

/-- Args: `[fAncPtr, vCap, n, vListPtr, inRPtr, rtPtr]`. Registers `10`–`14` hold the bases of
the five arrays. -/
def fAncFillProc : Stmt :=
  .assign 10 (.bin .add (.reg 0) (.const 6)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 1)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 1)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 1)) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 1)) ;;
  .assign 7 (.const 0) ;;
  forRange 6 (.const 0) (.reg 2) fAncBody ;;
  .store (.reg 0) (.reg 7) ;;
  .store (.bin .add (.reg 0) (.const 1)) (.reg 10) ;;
  .store (.bin .add (.reg 0) (.const 2)) (.reg 11) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.reg 12) ;;
  .store (.bin .add (.reg 0) (.const 4)) (.reg 13) ;;
  .store (.bin .add (.reg 0) (.const 5)) (.reg 14) ;;
  .ret (.const 0)

lemma fAncFillProc_noRand : fAncFillProc.NoRand := by
  simp [fAncFillProc, fAncBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `fAncFillProc`. -/
def fAncFillContract (w : ℕ) : Contract where
  pre args mem := ∃ (fAncPtr vCap n vListPtr inRPtr rtPtr : ℕ),
    args = [fAncPtr, vCap, n, vListPtr, inRPtr, rtPtr] ∧
    16 ≤ 2 ^ w ∧ fAncPtr + fAncSize vCap < 2 ^ w ∧ n ≤ vCap ∧
    (∀ i < fAncSize vCap, mem (fAncPtr + i) = 0) ∧
    OutsideBlock w fAncPtr (fAncSize vCap) vListPtr n ∧
    OutsideBlock w fAncPtr (fAncSize vCap) inRPtr n ∧
    OutsideBlock w fAncPtr (fAncSize vCap) rtPtr n ∧
    (∀ x < n, mem (vListPtr + x) < vCap ∧ mem (rtPtr + x) < n) ∧
    (∀ x < n, ∀ y < n, mem (vListPtr + x) = mem (vListPtr + y) → x = y)
  post args mem ret mem' := ∃ (fAncPtr vCap n vListPtr inRPtr rtPtr : ℕ),
    args = [fAncPtr, vCap, n, vListPtr, inRPtr, rtPtr] ∧ ret = 0 ∧
    (∀ a, a < fAncPtr ∨ fAncPtr + fAncSize vCap ≤ a → mem' a = mem a) ∧
    let vL := fun x => mem (vListPtr + x)
    let inR := fun x => mem (inRPtr + x)
    let rt := fun x => mem (rtPtr + x)
    mem' (fAncPtr + fOffRCount) = (rootList vL inR n).length ∧
    mem' (fAncPtr + fOffIsRootPtr) = fIsRootBase fAncPtr ∧
    mem' (fAncPtr + fOffRListPtr) = fRListBase fAncPtr vCap ∧
    mem' (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap ∧
    mem' (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap ∧
    mem' (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap ∧
    (∀ v < vCap, mem' (fIsRootBase fAncPtr + v) = isRootVal vL inR n v) ∧
    ListAt mem' (fRListBase fAncPtr vCap) (rootList vL inR n) ∧
    (∀ x < n, mem' (fCompIdBase fAncPtr vCap + vL x) = vL (rt x)) ∧
    (∀ x < n, inR x = 1 → mem' (fCompRootBase fAncPtr vCap + vL x) = vL x) ∧
    (∀ v < vCap, mem' (fCompSizeBase fAncPtr vCap + v) = sizeVal vL rt n v)
  cost args _ := 120 * args.getD 2 0 + 100

set_option maxHeartbeats 1600000 in
theorem fAncFill_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some fAncFillProc) :
    MeetsContract w p b (fAncFillContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨fAncPtr, vCap, n, vListPtr, inRPtr, rtPtr, rfl, h16, hbw, hnv, hzero, ⟨hvD, hvW⟩,
    ⟨hiD, hiW⟩, ⟨hrD, hrW⟩, hlt, hinj⟩ := hpre
  set args := [fAncPtr, vCap, n, vListPtr, inRPtr, rtPtr] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := hwords _ (by simp [hargs])
  obtain ⟨vL, hvL⟩ : ∃ f : ℕ → ℕ, f = fun x => mem (vListPtr + x) := ⟨_, rfl⟩
  obtain ⟨inR, hinR⟩ : ∃ f : ℕ → ℕ, f = fun x => mem (inRPtr + x) := ⟨_, rfl⟩
  obtain ⟨rt, hrt⟩ : ∃ f : ℕ → ℕ, f = fun x => mem (rtPtr + x) := ⟨_, rfl⟩
  have hvLx : ∀ x, mem (vListPtr + x) = vL x := fun x => by rw [hvL]
  have hinRx : ∀ x, mem (inRPtr + x) = inR x := fun x => by rw [hinR]
  have hrtx : ∀ x, mem (rtPtr + x) = rt x := fun x => by rw [hrt]
  simp only [hvLx, hrtx] at hlt hinj
  set IB := fAncPtr + 6 with hIB
  set RB := IB + vCap with hRB
  set CB := RB + vCap with hCB
  set KB := CB + vCap with hKB
  set SB := KB + vCap with hSB
  have hsz : fAncSize vCap = 6 + 5 * vCap := by simp [fAncSize, fAncHdrSize]
  let Fr : (ℕ → ℕ) → Prop := fun m =>
    ∀ a, a < fAncPtr ∨ fAncPtr + fAncSize vCap ≤ a → m a = mem a
  have hRd : ∀ {a : ℕ}, (a + n ≤ fAncPtr ∨ fAncPtr + fAncSize vCap ≤ a) →
      ∀ m, Fr m → ∀ i < n, m (a + i) = mem (a + i) := fun hD m hm i hi =>
    hm _ (by rcases hD with h | h <;> [left; right] <;> omega)
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 6, st.regs i = args.getD i 0) ∧ st.regs 6 = j ∧
    st.regs 7 = (rootList vL inR j).length ∧ st.regs 10 = IB ∧ st.regs 11 = RB ∧
    st.regs 12 = CB ∧ st.regs 13 = KB ∧ st.regs 14 = SB ∧ Fr st.mem ∧
    (∀ v < vCap, st.mem (IB + v) = isRootVal vL inR j v) ∧
    ListAt st.mem RB (rootList vL inR j) ∧
    (∀ x < j, st.mem (CB + vL x) = vL (rt x)) ∧
    (∀ x < j, inR x = 1 → st.mem (KB + vL x) = vL x) ∧
    (∀ v < vCap, st.mem (SB + v) = sizeVal vL rt j v)
  have hloop : Triple w p (Inv 0) (forRange 6 (.const 0) (.reg 2) fAncBody) (normalPost (Inv n))
      (fun _ => (n - 0) * (100 + (Expr.reg 2).size + 8) +
        ((Expr.const 0).size + (Expr.reg 2).size + 5)) := by
    refine Triple.forRange_const 100 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · intro st hI
      refine ⟨by eval_expr, ?_⟩
      obtain ⟨hR, -, h7, h10, h11, h12, h13, h14, rest⟩ := hI
      refine ⟨fun i hi => ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, rest⟩
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hR i hi
      all_goals (dsimp only; rw [Function.update_of_ne (by omega)]; assumption)
    · intro j st _ _ hI; exact hI.2.1
    · intro j st _ _ hI
      have r2 : st.regs 2 = n := hI.1 2 (by omega)
      eval_expr
    · intro j _ hj st ω' hI
      obtain ⟨hR, r6, r7, r10, r11, r12, r13, r14, hfr, hIs, hRL, hCI, hCR, hCS⟩ := hI
      have r3 : st.regs 3 = vListPtr := hR 3 (by omega)
      have r4 : st.regs 4 = inRPtr := hR 4 (by omega)
      have r5 : st.regs 5 = rtPtr := hR 5 (by omega)
      obtain ⟨hvj, hrj⟩ := hlt j hj
      obtain ⟨hvr, -⟩ := hlt (rt j) hrj
      have hm1 : st.mem (vListPtr + j) = vL j := (hRd hvD _ hfr j hj).trans (hvLx j)
      have hm2 : st.mem (rtPtr + j) = rt j := (hRd hrD _ hfr j hj).trans (hrtx j)
      have hm3 : st.mem (vListPtr + rt j) = vL (rt j) := (hRd hvD _ hfr _ hrj).trans (hvLx _)
      obtain ⟨v, hv⟩ : ∃ v, vL j = v := ⟨_, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, vL (rt j) = c := ⟨_, rfl⟩
      obtain ⟨len, hlen⟩ : ∃ len, (rootList vL inR j).length = len := ⟨_, rfl⟩
      rw [hv] at hm1 hvj
      rw [hc] at hm3 hvr
      rw [hlen] at r7
      have hlenj : len ≤ j := hlen ▸ rootList_length_le vL inR j
      have hsc : st.mem (SB + c) = sizeVal vL rt j c := hCS c hvr
      have hscle := sizeVal_le vL rt j c
      set m1 := Function.update st.mem (CB + v) c with hm1d
      have hm1S : m1 (SB + c) = sizeVal vL rt j c := by
        rw [hm1d, Function.update_of_ne (by omega)]; exact hsc
      set m2 := Function.update m1 (SB + c) (sizeVal vL rt j c + 1) with hm2d
      have hm2I : m2 (inRPtr + j) = inR j := by
        rw [hm2d, Function.update_of_ne (by rcases hiD with h | h <;> omega), hm1d,
          Function.update_of_ne (by rcases hiD with h | h <;> omega)]
        exact (hRd hiD _ hfr j hj).trans (hinRx j)
      -- the facts that hold in both branches
      have hinj' : ∀ x < j, vL x ≠ v := fun x hx he => by
        have := hinj x (by omega) j hj (he.trans hv.symm); omega
      refine runs_start_le ?_
      unfold fAncBody
      refine runs_seq_assign_le (v := v) (by rw [← hm1]; eval_expr) ?_
      refine runs_seq_assign_le (v := c) (by rw [← hm3, ← hm2]; eval_expr) ?_
      refine runs_seq_store_le (x := CB + v) (v := c) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := SB + c) (v := sizeVal vL rt j c + 1) (by eval_expr)
        (by rw [← hm1S]; eval_expr) ?_
      refine WordRAM.runs_cond_le (v := if inR j = 1 then 1 else 0) (by rw [← hm2I]; eval_expr)
        (fun hb => ?_) (fun hb => ?_)
      · have hj1 : inR j = 1 := by by_contra hne; exact hb (if_neg hne)
        refine runs_seq_store_le (x := IB + v) (v := 1) (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_le (x := RB + len) (v := v) (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_le (x := KB + v) (v := v) (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (v := len + 1) (by eval_expr) ⟨⟨fun i hi => ?_, by simp, ?_,
          by simpa using r10, by simpa using r11, by simpa using r12, by simpa using r13,
          by simpa using r14, fun a ha => ?_, fun u hu => ?_, ?_, fun x hx => ?_,
          fun x hx hx1 => ?_, fun u hu => ?_⟩, by simpa using r6⟩ (by simp [Expr.size])
        · simp only [Function.update_of_ne (show i ≠ 6 by omega),
            Function.update_of_ne (show i ≠ 7 by omega), Function.update_of_ne (show i ≠ 9 by omega),
            Function.update_of_ne (show i ≠ 8 by omega)]
          exact hR i hi
        · simp only [Function.update_of_ne (show (7 : ℕ) ≠ 6 by omega), Function.update_self]
          rw [rootList_succ, if_pos hj1, List.length_append, hlen]; rfl
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hfr a ha
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), isRootVal_succ]
          by_cases hu' : u = v
          · subst hu'
            rw [Function.update_self, if_pos ⟨hj1, hv⟩]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), if_neg (fun h => hu' (h.2.symm.trans hv)), hIs u hu]
        · dsimp only
          rw [rootList_succ, if_pos hj1, hv]
          intro i hi
          rw [List.length_append, hlen, List.length_singleton] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), List.getElem_append_left (by omega)]
            exact hRL i (by omega)
          · rw [Function.update_of_ne (by omega), Function.update_self]
            simp [hlen]
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
          · have hxv := hinj' x hx
            have hxl := (hlt x (by omega)).1
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hCI x hx
          · rw [hv, hc, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
          · have hxv := hinj' x hx
            have hxl := (hlt x (by omega)).1
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hCR x hx hx1
          · rw [hv, Function.update_self]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), sizeVal_succ, hc]
          by_cases hu' : u = c
          · subst hu'
            rw [Function.update_self, if_pos rfl]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hCS u hu,
              if_neg (Ne.symm hu'), Nat.add_zero]
      · have hj1 : inR j ≠ 1 := by intro he; exact absurd hb (by simp [he])
        refine runs_nop_le ⟨⟨fun i hi => ?_, by simp, ?_,
          by simpa using r10, by simpa using r11, by simpa using r12, by simpa using r13,
          by simpa using r14, fun a ha => ?_, fun u hu => ?_, ?_, fun x hx => ?_,
          fun x hx hx1 => ?_, fun u hu => ?_⟩, by simpa using r6⟩ (by simp [Expr.size])
        · simp only [Function.update_of_ne (show i ≠ 6 by omega),
            Function.update_of_ne (show i ≠ 9 by omega), Function.update_of_ne (show i ≠ 8 by omega)]
          exact hR i hi
        · simp only [Function.update_of_ne (show (7 : ℕ) ≠ 6 by omega),
            Function.update_of_ne (show (7 : ℕ) ≠ 9 by omega),
            Function.update_of_ne (show (7 : ℕ) ≠ 8 by omega)]
          rw [rootList_succ, if_neg hj1, hlen]; exact r7
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr a ha
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), isRootVal_succ,
            if_neg (fun h => hj1 h.1), hIs u hu]
        · dsimp only
          rw [rootList_succ, if_neg hj1]
          intro i hi
          have hi' := hi
          rw [hlen] at hi'
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hRL i hi
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
          · have hxv := hinj' x hx
            have hxl := (hlt x (by omega)).1
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hCI x hx
          · rw [hv, hc, Function.update_of_ne (by omega), Function.update_self]
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
          · have hxl := (hlt x (by omega)).1
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hCR x hx hx1
          · exact absurd hx1 hj1
        · dsimp only
          rw [sizeVal_succ, hc]
          by_cases hu' : u = c
          · subst hu'
            rw [Function.update_self, if_pos rfl]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hCS u hu,
              if_neg (Ne.symm hu'), Nat.add_zero]
  have hst : ∀ i < 6, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hfw : fAncPtr < 2 ^ w := by omega
  have hvw : vCap < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold fAncFillProc
  have r0 := hst 0 (by omega)
  have r1 := hst 1 (by omega)
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at r0 r1
  refine runs_seq_assign_le (v := IB) (by eval_expr) ?_
  refine runs_seq_assign_le (v := RB) (by eval_expr) ?_
  refine runs_seq_assign_le (v := CB) (by eval_expr) ?_
  refine runs_seq_assign_le (v := KB) (by eval_expr) ?_
  refine runs_seq_assign_le (v := SB) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨fun i hi => ?_, by simp [startState, hargs], by simp [rootList],
    by simp, by simp, by simp, by simp, by simp, fun a _ => rfl, fun u hu => ?_, fun i hi => ?_,
    fun x hx => absurd hx (Nat.not_lt_zero _), fun x hx => absurd hx (Nat.not_lt_zero _),
    fun u hu => ?_⟩ ?_
  · simp only [Function.update_of_ne (show i ≠ 7 by omega), Function.update_of_ne (show i ≠ 14 by omega),
      Function.update_of_ne (show i ≠ 13 by omega), Function.update_of_ne (show i ≠ 12 by omega),
      Function.update_of_ne (show i ≠ 11 by omega), Function.update_of_ne (show i ≠ 10 by omega)]
    exact hst i hi
  · simp only [startState, isRootVal, Nat.not_lt_zero, false_and, exists_false, if_false]
    have := hzero (6 + u) (by omega)
    rwa [show fAncPtr + (6 + u) = IB + u by omega] at this
  · simp [rootList] at hi
  · simp only [startState, sizeVal, Finset.range_zero, Finset.filter_empty, Finset.card_empty]
    have := hzero (6 + 4 * vCap + u) (by omega)
    rwa [show fAncPtr + (6 + 4 * vCap + u) = SB + u by omega] at this
  rintro st ⟨hR, -, r7, r10, r11, r12, r13, r14, hfr, hIs, hRL, hCI, hCR, hCS⟩
  have r0' : st.regs 0 = fAncPtr := hR 0 (by omega)
  have hlenw : (rootList vL inR n).length < 2 ^ w := by
    have := rootList_length_le vL inR n; omega
  refine runs_seq_store_le (x := fAncPtr) (v := (rootList vL inR n).length) (by eval_expr)
    (by eval_expr) ?_
  refine runs_seq_store_le (x := fAncPtr + 1) (v := IB) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := fAncPtr + 2) (v := RB) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := fAncPtr + 3) (v := CB) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := fAncPtr + 4) (v := KB) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := fAncPtr + 5) (v := SB) (by eval_expr) (by eval_expr) ?_
  subst hvL hinR hrt
  refine runs_ret_le (v := 0) (by eval_expr) ⟨fAncPtr, vCap, n, vListPtr, inRPtr, rtPtr, rfl, rfl,
    fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun u hu => ?_, fun i hi => ?_, fun x hx => ?_,
    fun x hx hx1 => ?_, fun u hu => ?_⟩ ?_
  all_goals try dsimp only
  · have : a < fAncPtr ∨ fAncPtr + (6 + 5 * vCap) ≤ a := by rw [← hsz]; exact ha
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hfr a ha
  all_goals try (simp only [fOffRCount, fOffIsRootPtr, fOffRListPtr, fOffCompIdPtr,
    fOffCompRootPtr, fOffCompSizePtr, fIsRootBase, fRListBase, fCompIdBase, fCompRootBase,
    fCompSizeBase, fAncHdrSize, Function.update_apply] <;>
    split_ifs <;> first | omega | rfl | skip)
  · exact hIs u hu
  · exact hRL i hi
  · have := (hlt x hx).1; exact hCI x hx
  · have := (hlt x hx).1; exact hCR x hx hx1
  · exact hCS u hu
  · simp only [fAncFillContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
      Expr.size_reg, Expr.size_bin, Nat.sub_zero]
    omega

end

end MinCostFlow.LSF.Program
