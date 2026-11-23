module

public import MinCostFlow.LSF.Program.Wstr

/-!
# `wstrProc` with its scratch layout

`wstrProc` takes `43` arguments, and `18` of them are places in its scratch area. `wstrStageProc`
takes the start `idPtr` of the scratch area and computes the other `18` places itself, in the
order that `WstrPre` asks for. Place `j` is `wsPt idPtr n tM m0 LB (j + 1)`: the start plus the
sizes of the arrays before it (`wsStep`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

@[expose] public section

/-- The size of the scratch array before place `j` of `wstrProc`: first the `n` words at
`idPtr`, then `ltBase, ldBase, duvBase, inRPtr, mpPtr, ownPtr, rtPtr, dRBase, accBase, leBase`,
and one block of `LB` limbs for each of the others. -/
def wsStep (n tM m0 LB : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => tM * LB
  | 2 => n * LB
  | 3 => m0 * LB
  | 4 => n
  | 5 => n
  | 6 => tM
  | 7 => n
  | 8 => n * LB
  | 9 => m0 * LB
  | 10 => m0 * LB
  | _ => LB

/-- `wsPt … 0 = idPtr`, and `wsPt … (j + 1)` is place `j` of the scratch area. -/
def wsPt (idPtr n tM m0 LB : ℕ) : ℕ → ℕ
  | 0 => idPtr
  | j + 1 => wsPt idPtr n tM m0 LB j + wsStep n tM m0 LB j

/-- `wsStep` as an expression in the registers `0 = n`, `1 = tM`, `2 = m0`, `4 = LB`. -/
def wsStepExpr : ℕ → Expr
  | 0 => .reg 0
  | 1 => .bin .mul (.reg 1) (.reg 4)
  | 2 => .bin .mul (.reg 0) (.reg 4)
  | 3 => .bin .mul (.reg 2) (.reg 4)
  | 4 => .reg 0
  | 5 => .reg 0
  | 6 => .reg 1
  | 7 => .reg 0
  | 8 => .bin .mul (.reg 0) (.reg 4)
  | 9 => .bin .mul (.reg 2) (.reg 4)
  | 10 => .bin .mul (.reg 2) (.reg 4)
  | _ => .reg 4

/-- `k` assigns: register `25 + j` gets register `24 + j` plus `wsStep j`, for `j` from `j₀`. -/
def wsAssigns (j₀ : ℕ) : ℕ → Stmt → Stmt
  | 0, s => s
  | k + 1, s => .assign (25 + j₀) (.bin .add (.reg (24 + j₀)) (wsStepExpr j₀)) ;;
      wsAssigns (j₀ + 1) k s

/-- Args (`25`): the first `25` arguments of `wstrProc`, ending with `idPtr`. The body computes
the other places into registers `25`–`42`, calls `wstrProc`, and returns the last place `highPtr`
(register `42`), so that a caller can read the flags there. -/
def wstrStageProc (bW : ℕ) : Stmt :=
  wsAssigns 0 18 (.call 43 bW ((List.range 43).map Expr.reg) ;; .ret (.reg 42))

lemma wsAssigns_noRand (j₀ k : ℕ) {s : Stmt} (hs : s.NoRand) : (wsAssigns j₀ k s).NoRand := by
  induction k generalizing j₀ with
  | zero => exact hs
  | succ k ih => exact ⟨trivial, ih (j₀ + 1)⟩

lemma wstrStageProc_noRand (bW : ℕ) : (wstrStageProc bW).NoRand :=
  wsAssigns_noRand 0 18 (by simp [Stmt.NoRand])

/-- The `43` arguments of `wstrProc`. -/
def wstrStageArgs (a : List ℕ) : List ℕ :=
  a ++ (List.range 18).map fun j =>
    wsPt (a.getD 24 0) (a.getD 0 0) (a.getD 1 0) (a.getD 2 0) (a.getD 4 0) (j + 1)

/-- The contract of `wstrStageProc`: the contract of `wstrProc` on `wstrStageArgs args`. The
last place, the flags at `highPtr`, ends below `2 ^ w`. -/
def wstrStageContract (w h C : ℕ) : Contract where
  pre args mem := args.length = 25 ∧
    wsPt (args.getD 24 0) (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 4 0) 18 <
      2 ^ w ∧
    (wstrContract w h C).pre (wstrStageArgs args) mem
  post args mem ret mem' :=
    ret = wsPt (args.getD 24 0) (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 4 0) 18 ∧
    (wstrContract w h C).post (wstrStageArgs args) mem 0 mem'
  cost args mem := (wstrContract w h C).cost (wstrStageArgs args) mem + 200

lemma wsPt_mono (idPtr n tM m0 LB : ℕ) {i j : ℕ} (hij : i ≤ j) :
    wsPt idPtr n tM m0 LB i ≤ wsPt idPtr n tM m0 LB j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => simp only [wsPt]; omega

lemma wsStepExpr_size (j : ℕ) : (wsStepExpr j).size ≤ 3 := by
  unfold wsStepExpr
  split <;> simp [Expr.size]

/-- The value of `wsStepExpr j`. -/
lemma wsStepExpr_eval {w : ℕ} {st : State} {n tM m0 LB : ℕ} (j : ℕ)
    (h0 : st.regs 0 = n) (h1 : st.regs 1 = tM) (h2 : st.regs 2 = m0) (h4 : st.regs 4 = LB)
    (hw : wsStep n tM m0 LB j < 2 ^ w) :
    (wsStepExpr j).eval w st = some (wsStep n tM m0 LB j) := by
  unfold wsStepExpr wsStep at *
  split <;> simp_all [Expr.eval, BinOp.eval]

/-- Running the assigns: afterwards registers `24 + j₀ … 24 + j₀ + k` hold the places, and the
other registers below `24 + j₀ + 1` are unchanged. -/
lemma runs_wsAssigns {w : ℕ} {p : Program} {ω : ℕ → Bool} {n tM m0 LB idPtr : ℕ}
    {Q : Outcome → State → Prop} (k : ℕ) :
    ∀ (j₀ : ℕ) (st : State) (s : Stmt) (K T : ℕ),
    st.regs 0 = n → st.regs 1 = tM → st.regs 2 = m0 → st.regs 4 = LB →
    st.regs (24 + j₀) = wsPt idPtr n tM m0 LB j₀ →
    wsPt idPtr n tM m0 LB (j₀ + k) < 2 ^ w →
    (∀ st' : State, st'.mem = st.mem → st'.pos = st.pos →
      (∀ i, i ≤ 24 + j₀ → st'.regs i = st.regs i) →
      (∀ j, j₀ ≤ j → j ≤ j₀ + k → st'.regs (24 + j) = wsPt idPtr n tM m0 LB j) →
      ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧ (K + 7 * k) + c ≤ T) →
    ∃ o st' c, Runs w p ω (wsAssigns j₀ k s) st o st' c ∧ Q o st' ∧ K + c ≤ T := by
  induction k with
  | zero =>
    intro j₀ st s K T _ _ _ _ hj _ hrest
    obtain ⟨o, st'', c, hr, hq, hc⟩ := hrest st rfl rfl (fun _ _ => rfl) (fun j h1 h2 => by
      rw [show j = j₀ by omega]; exact hj)
    exact ⟨o, st'', c, hr, hq, by omega⟩
  | succ k ih =>
    intro j₀ st s K T h0 h1 h2 h4 hj hw hrest
    have hle : wsPt idPtr n tM m0 LB (j₀ + 1) ≤ wsPt idPtr n tM m0 LB (j₀ + (k + 1)) :=
      wsPt_mono _ _ _ _ _ (by omega)
    have hstep : wsPt idPtr n tM m0 LB (j₀ + 1) =
        wsPt idPtr n tM m0 LB j₀ + wsStep n tM m0 LB j₀ := rfl
    have hev : (Expr.bin .add (.reg (24 + j₀)) (wsStepExpr j₀)).eval w st =
        some (wsPt idPtr n tM m0 LB (j₀ + 1)) := by
      have hse := wsStepExpr_eval (w := w) (st := st) j₀ h0 h1 h2 h4 (by omega)
      simp only [Expr.eval, hse, hj, BinOp.eval, hstep]
      exact if_pos (by omega)
    unfold wsAssigns
    refine runs_seq_assign_le hev ?_
    have hne : ∀ i, i ≤ 24 + j₀ → Function.update st.regs (25 + j₀)
        (wsPt idPtr n tM m0 LB (j₀ + 1)) i = st.regs i := fun i hi =>
      Function.update_of_ne (by omega) _ _
    refine ih (j₀ + 1) _ s _ T (by dsimp only; rw [hne 0 (by omega)]; exact h0)
      (by dsimp only; rw [hne 1 (by omega)]; exact h1)
      (by dsimp only; rw [hne 2 (by omega)]; exact h2)
      (by dsimp only; rw [hne 4 (by omega)]; exact h4)
      (by
        show Function.update st.regs (25 + j₀) _ (24 + (j₀ + 1)) = _
        rw [show 24 + (j₀ + 1) = 25 + j₀ by omega, Function.update_self])
      (by rw [show j₀ + 1 + k = j₀ + (k + 1) by omega]; exact hw) ?_
    intro st' hm hpos hregs hpl
    obtain ⟨o, st'', c, hr, hq, hc⟩ := hrest st' hm hpos
      (fun i hi => by
        rw [hregs i (by omega)]
        dsimp only
        exact hne i hi)
      (fun j h1' h2' => by
        rcases Nat.eq_or_lt_of_le h1' with rfl | hlt
        · rw [hregs _ (by omega)]; dsimp only; rw [hne _ le_rfl]; exact hj
        · exact hpl j (by omega) (by omega))
    refine ⟨o, st'', c, hr, hq, ?_⟩
    have := wsStepExpr_size j₀
    simp only [Expr.size] at *
    omega

/-- The registers hold the values of a list of register expressions. -/
lemma evalArgs_map_reg {w : ℕ} {st : State} (l : List ℕ) :
    evalArgs w st (l.map Expr.reg) = some (l.map st.regs) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [evalArgs, Expr.eval, ih]

lemma argsSize_map_reg (l : List ℕ) : argsSize (l.map Expr.reg) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [argsSize, Expr.size, ih]; omega

theorem wstrStage_meetsContract {w h C : ℕ} {p : Program} {b bW : ℕ}
    (hp : p.procs[b]? = some (wstrStageProc bW))
    (hW : MeetsContract w p bW (wstrContract w h C)) :
    MeetsContract w p b (wstrStageContract w h C) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨hlen, hlast, hpre⟩ := hpre
  set n := args.getD 0 0 with hn
  set tM := args.getD 1 0 with htM
  set m0 := args.getD 2 0 with hm0
  set LB := args.getD 4 0 with hLB
  set idPtr := args.getD 24 0 with hid
  have hR0 : ∀ i < 25, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    simp only [startState]
  refine runs_start_le ?_
  unfold wstrStageProc
  refine runs_wsAssigns (n := n) (tM := tM) (m0 := m0) (LB := LB) (idPtr := idPtr) 18 0 _ _ 0 _
    (hR0 0 (by omega)) (hR0 1 (by omega)) (hR0 2 (by omega)) (hR0 4 (by omega))
    (by rw [hR0 24 (by omega)]; rfl) hlast ?_
  intro st' hm hpos hregs hpl
  have hregsA : (List.range 43).map st'.regs = wstrStageArgs args := by
    apply List.ext_getElem
    · simp [wstrStageArgs, hlen]
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    by_cases hi : i < 25
    · simp only [wstrStageArgs]
      rw [hregs i (by omega), hR0 i hi, List.getElem_append_left (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    · have hj := hpl (i - 24) (by omega) (by omega)
      rw [show 24 + (i - 24) = i by omega] at hj
      rw [hj]
      simp only [wstrStageArgs]
      rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, List.getElem_range, hlen]
      rw [show i - 25 + 1 = i - 24 by omega]
  have hAw : ∀ v ∈ wstrStageArgs args, v < 2 ^ w := by
    intro v hv
    simp only [wstrStageArgs, List.mem_append, List.mem_map, List.mem_range] at hv
    rcases hv with hv | ⟨j, hj, rfl⟩
    · exact hwords v hv
    · exact lt_of_le_of_lt (wsPt_mono _ _ _ _ _ (by omega)) hlast
  refine runs_seq_call_le (vs := wstrStageArgs args) hW
    (by rw [evalArgs_map_reg, hregsA]) hAw (by rw [hm]; exact hpre) ?_
  intro v mem' pos' hpost
  refine runs_ret_le (v := wsPt idPtr n tM m0 LB 18) ?_ ⟨rfl, ?_⟩ ?_
  · show some (Function.update st'.regs 43 v 42) = some _
    rw [Function.update_of_ne (by omega), hpl 18 (by omega) (by omega)]
  · rw [hm] at hpost
    obtain ⟨n', tM', m0', k', LB', Lw', Lin', nOrig', r', logCap', lenArr', fidPtr', qPtr', parPtr',
      pePtr', piPtr', thDepPtr', euPtr', evPtr', upPtr', depPtr', eList', numPtr', denPtr',
      idPtr', ltBase', ldBase', duvBase', inRPtr', mpPtr', ownPtr', rtPtr', dRBase', accBase',
      leBase', k2Out', thOut', tA', tB', tF', tmp1', tmp2', highPtr', hArgs, -, hP⟩ := hpost
    exact ⟨n', tM', m0', k', LB', Lw', Lin', nOrig', r', logCap', lenArr', fidPtr', qPtr', parPtr',
      pePtr', piPtr', thDepPtr', euPtr', evPtr', upPtr', depPtr', eList', numPtr', denPtr',
      idPtr', ltBase', ldBase', duvBase', inRPtr', mpPtr', ownPtr', rtPtr', dRBase', accBase',
      leBase', k2Out', thOut', tA', tB', tF', tmp1', tmp2', highPtr', hArgs, rfl, hP⟩
  · rw [argsSize_map_reg, hm]
    simp only [wstrStageContract, List.length_range, Expr.size, startState]
    omega

end

end MinCostFlow.LSF.Program
