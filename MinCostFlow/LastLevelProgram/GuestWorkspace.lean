module

public import MinCostFlow.LastLevelProgram.GuestSimulationWidth
public import MinCostFlow.LastLevelProgram.GuestWordWidth
public import MinCostFlow.Machine.WideWord.LSSTSimDecode
import WordRAM.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Integer workspace bound for the relocated tree call

Theorem 2.2 (page 7) bounds the cited procedure's cost with real
logarithms. Binary bit counts give a larger integer workspace bound
that the last-level builder can compute from runtime words.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord Scaling.Machine

private theorem log_nat_le_size (x : ℕ) (hx : 0 < x) :
    Real.log (x : ℝ) ≤ x.size := by
  have hb : (x : ℝ) ≤ (2 : ℝ)^x.size := by exact_mod_cast (Nat.lt_size_self x).le
  have hl := Real.log_le_log (by exact_mod_cast hx) hb
  rw [Real.log_pow] at hl
  have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  exact hl.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) x.size])

/-- The integer bound uses bit counts for both logarithmic factors. -/
def guestCitedCostBound (D n m sim : ℕ) : ℕ :=
  D*(4*m+1)*(n+2).size*((n+2).size+(sim+4).size)

/-- The real-valued cited cost bound fits the integer bound at one-bit
guest limbs. Only the fixed integer ceiling of its constant is needed. -/
theorem anCostBound_le_guestCitedCostBound (K : ℝ) (D n m sim : ℕ)
    (hK : max K 0 ≤ (D : ℝ)) :
    anCostBound K n m sim 1 ≤ guestCitedCostBound D n m sim := by
  let t := Real.log ((n:ℝ)+2)
  let s := ((n+2).size : ℝ)
  let u := ((sim+4).size : ℝ)
  have ht : 0 < t := by dsimp [t]; apply Real.log_pos; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hts : t ≤ s := by
    dsimp [t,s]
    exact_mod_cast log_nat_le_size (n+2) (by omega)
  have hlogt : Real.log t ≤ s :=
    (Real.log_le_sub_one_of_pos ht).trans (by linarith)
  have hW : (((2^sim : ℕ) : ℝ)+2) ≤ (2:ℝ)^(sim+2) := by
    have htwo : (1:ℝ) ≤ (2:ℝ)^sim := one_le_pow₀ (by norm_num)
    rw [Nat.cast_pow,pow_add]
    norm_num
    linarith
  have hlogW := Real.log_le_log (by positivity) hW
  rw [Real.log_pow] at hlogW
  have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  have hlogW' : Real.log (((2^sim : ℕ) : ℝ)+2)+2 ≤ (sim:ℝ)+4 := by
    have hmul := mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 1 by linarith)
      (Nat.cast_nonneg (α := ℝ) (sim+2))
    push_cast at hlogW hmul ⊢
    linarith
  have hposW : 0 < Real.log (((2^sim : ℕ) : ℝ)+2)+2 := by
    have hl : 0 ≤ Real.log (((2^sim : ℕ) : ℝ)+2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (2^sim)])
    linarith
  have hweight : Real.log (Real.log (((2^sim : ℕ) : ℝ)+2)+2) ≤ u := by
    apply (Real.log_le_log hposW hlogW').trans
    dsimp [u]
    exact_mod_cast log_nat_le_size (sim+4) (by omega)
  have hsum : Cited.logLogFactor n + Cited.weightFactor n (2^sim) ≤ s*(s+u) := by
    unfold Cited.logLogFactor Cited.weightFactor
    change t*Real.log t + t*Real.log (Real.log (((2^sim : ℕ) : ℝ)+2)+2) ≤ _
    calc
      _ = t*(Real.log t + Real.log (Real.log (((2^sim : ℕ) : ℝ)+2)+2)) := by ring
      _ ≤ t*(s+u) := mul_le_mul_of_nonneg_left (add_le_add hlogt hweight) ht.le
      _ ≤ s*(s+u) := mul_le_mul_of_nonneg_right hts (by dsimp [s,u]; positivity)
  unfold anCostBound
  simp only [Nat.mul_one]
  apply Nat.ceil_le.mpr
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ max K 0 * (((4*m:ℕ):ℝ)+1) by positivity)
  refine hmul.trans ?_
  unfold guestCitedCostBound
  push_cast
  change max K 0 * (4*(m:ℝ)+1) * (s*(s+u)) ≤
    (D:ℝ)*(4*(m:ℝ)+1)*s*(s+u)
  have hh := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ (4*(m:ℝ)+1)*(s*(s+u)) by dsimp [s,u]; positivity)
  linarith only [hh]

/-- Integer workspace sufficient for the canonical guest at one-bit limbs. -/
def guestWorkspace (guest : Program) (D n m sim : ℕ) : ℕ :=
  (4+9*n+4*m+m*sim)+weightsSpace m sim+2*m+(2+3*(4*m))*sim+
    simDecodeSpace guest (2*m) (4*m) sim 1 (guestCitedCostBound D n m sim)

/-- The computable workspace dominates the space used in Theorem 2.2. -/
theorem lsstSpace_le_guestWorkspace (guest : Program) (K : ℝ) (D n m sim : ℕ)
    (hK : max K 0 ≤ (D:ℝ)) :
    lsstSpace guest K n m sim 1 ≤ guestWorkspace guest D n m sim := by
  unfold lsstSpace guestWorkspace simDecodeSpace
  dsimp only
  gcongr
  exact anCostBound_le_guestCitedCostBound K D n m sim hK

/-- The canonical guest can run at the width computed from the
integer workspace bound. -/
def paddedGuestWidth (guest : Program) (D n m sim heap : ℕ) : ℕ :=
  max 5 (Nat.log 2 (heap+guestWorkspace guest D n m sim)+1)

/-- The runtime width dominates the original canonical guest width. -/
theorem canonicalGuestWidth_le_padded (guest : Program) (K : ℝ) (D n m sim heap : ℕ)
    (hK : max K 0 ≤ (D:ℝ)) :
    max 5 (Nat.log 2 (heap+lsstSpace guest K n m sim 1)+1) ≤
      paddedGuestWidth guest D n m sim heap := by
  unfold paddedGuestWidth
  exact max_le_max_left 5 (Nat.succ_le_succ
    (Nat.log_mono_right (Nat.add_le_add_left
      (lsstSpace_le_guestWorkspace guest K D n m sim hK) heap)))

/-- The padded region contains the complete workspace and guest input. -/
theorem guestAllocation_lt_paddedModulus (guest : Program) (D n m sim heap : ℕ) :
    heap+guestWorkspace guest D n m sim < 2^paddedGuestWidth guest D n m sim heap := by
  apply (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).trans_le
  exact Nat.pow_le_pow_right (by decide) (le_max_right _ _)

/-- Padding the guest workspace preserves the original canonical
LSST run, including its cost, result cells, and selected tree. -/
theorem canonicalGuestRun_padded (guest : Program) (K : ℝ) (D n m sim heap : ℕ)
    (hK : max K 0 ≤ (D:ℝ)) {ω : ℕ → Bool} {st out : State} {o : Outcome} {cost : ℕ}
    (hr : Runs (max 5 (Nat.log 2 (heap+lsstSpace guest K n m sim 1)+1))
      ⟨lsstModule guest 0 1⟩ ω (lsstEntryProc 0 1) st o out cost) :
    Runs (paddedGuestWidth guest D n m sim heap)
      ⟨lsstModule guest 0 1⟩ ω (lsstEntryProc 0 1) st o out cost :=
  deterministicRuns_widen (canonicalGuestWidth_le_padded guest K D n m sim heap hK)
    (lsstModule_noRand guest 0 1) (lsstEntryProc_noRand 0 1) hr

/-- Word arithmetic for the integer workspace bound. The two bit counts are
computed separately, and the only program-specific factor is fixed at link time. -/
def guestWorkspaceExpr (guest : Program) (D : ℕ) (n m sim nb sb : Expr) : Expr :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let c := Expr.const
  let enc := add (c 2) (mul (c 12) m)
  let twice := mul (c 2) sim
  let unsigned := add (add (mul (c 3) twice) (c 2))
    (mul (mul (c 5) twice) (add twice (c 1)))
  let signed := add unsigned (mul (c 3) twice)
  let weights := add (mul (c 13) sim)
    (mul m (add (mul (c 18) sim) (mul (c 2) signed)))
  let cited := mul (mul (mul (c D) (add (mul (c 4) m) (c 1))) nb) (add nb sb)
  let decode := add (add (add (c 5) (mul (add (c 1) (mul (c 2) m)) sim)) sim)
    (add (mul enc (add twice sim))
      (mul (mul (c (2 * simScale guest)) sim) (add (add cited enc) (c 1))))
  add (add (add (add (add (add (c 4) (mul (c 9) n)) (mul (c 4) m))
    (mul m sim)) weights) (mul (c 2) m)) (add (mul enc sim) decode)

/-- Evaluating the workspace formula in unbounded natural arithmetic gives
the workspace bound used for the padded Theorem 2.2 call (page 7). -/
theorem guestWorkspace_formula (guest : Program) (D n m sim : ℕ) :
    let enc := 2 + 12*m
    let twice := 2*sim
    let unsigned := 3*twice+2+5*twice*(twice+1)
    let signed := unsigned+3*twice
    let weights := 13*sim+m*(18*sim+2*signed)
    let cited := D*(4*m+1)*(n+2).size*((n+2).size+(sim+4).size)
    let decode := 5+(1+2*m)*sim+sim+
      (enc*(twice+sim)+(2*simScale guest)*sim*(cited+enc+1))
    4+9*n+4*m+m*sim+weights+2*m+(enc*sim+decode) =
      guestWorkspace guest D n m sim := by
  unfold guestWorkspace weightsSpace Num.integerDivideSpace Num.unsignedDivideSpace
    simDecodeSpace guestCitedCostBound
  dsimp only
  norm_num
  ring

private theorem workspace_add_eval {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (h : x+y < 2^w) :
    (Expr.bin .add a b).eval w st = some (x+y) := by
  simp [Expr.eval,BinOp.eval,ha,hb,h]

private theorem workspace_mul_eval {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (h : x*y < 2^w) :
    (Expr.bin .mul a b).eval w st = some (x*y) := by
  simp [Expr.eval,BinOp.eval,ha,hb,h]

private theorem workspace_const_eval {w x : ℕ} {st : State} (h : x < 2^w) :
    (Expr.const x).eval w st = some x := by
  simp [Expr.eval,h]

syntax "workspace_eval" term : tactic
macro_rules
  | `(tactic| workspace_eval $bound) =>
  `(tactic|
    first
    | assumption
    | refine workspace_add_eval ?_ ?_ $bound
      · have childBound := lt_of_le_of_lt (Nat.le_add_right _ _) $bound
        workspace_eval childBound
      · have childBound := lt_of_le_of_lt (Nat.le_add_left _ _) $bound
        workspace_eval childBound
    | refine workspace_mul_eval ?_ ?_ $bound
      · have childBound := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) $bound
        workspace_eval childBound
      · have childBound := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) $bound
        workspace_eval childBound
    | exact workspace_const_eval $bound)

/-- Increasing the graph counts, scale constant, or simulation size
can only increase the guest allocation bound. -/
theorem guestWorkspace_mono (guest : Program) {D n m sim D' n' m' sim' : ℕ}
    (hD : D ≤ D') (hn : n ≤ n') (hm : m ≤ m') (hs : sim ≤ sim') :
    guestWorkspace guest D n m sim ≤ guestWorkspace guest D' n' m' sim' := by
  have hnSize := Nat.size_le_size (Nat.add_le_add_right hn 2)
  have hsSize := Nat.size_le_size (Nat.add_le_add_right hs 4)
  rw [← guestWorkspace_formula, ← guestWorkspace_formula]
  gcongr

/-- The width of a larger guest allocation also bounds the width of
each representative query that fits inside it. -/
theorem paddedGuestWidth_mono (guest : Program)
    {D n m sim heap D' n' m' sim' heap' : ℕ}
    (hD : D ≤ D') (hn : n ≤ n') (hm : m ≤ m') (hs : sim ≤ sim') (hh : heap ≤ heap') :
    paddedGuestWidth guest D n m sim heap ≤ paddedGuestWidth guest D' n' m' sim' heap' := by
  unfold paddedGuestWidth
  exact max_le_max le_rfl (Nat.add_le_add_right
    (Nat.log_mono_right (Nat.add_le_add hh (guestWorkspace_mono guest hD hn hm hs))) 1)

/-- On a nonempty graph, each term of the workspace expression is bounded
by its final value. Thus all operations fit in a host word if the
workspace itself fits. -/
theorem guestWorkspaceExpr_eval {w : ℕ} {st : State} {ne me se nb sb : Expr}
    (guest : Program) (D n m sim : ℕ)
    (hn : ne.eval w st = some n) (hm : me.eval w st = some m)
    (hs : se.eval w st = some sim) (hb : nb.eval w st = some (n+2).size)
    (hd : sb.eval w st = some (sim+4).size)
    (_hn : 0 < n) (_hm : 0 < m) (_hs : 0 < sim) (_hD : 0 < D)
    (hfit : guestWorkspace guest D n m sim < 2^w) :
    (guestWorkspaceExpr guest D ne me se nb sb).eval w st =
      some (guestWorkspace guest D n m sim) := by
  rw [← guestWorkspace_formula guest D n m sim] at hfit ⊢
  have hnb : 0 < (n+2).size := Nat.size_pos.mpr (by omega)
  have hsb : 0 < (sim+4).size := Nat.size_pos.mpr (by omega)
  have hscale : 0 < simScale guest := by unfold simScale; omega
  unfold guestWorkspaceExpr
  dsimp only at hfit ⊢
  -- Propagate the word bound down through additions and positive products.
  workspace_eval hfit

/-- The runtime inputs are the vertex count, edge count and simulation
width. Two ceiling-log calls compute the required bit counts. -/
def guestWorkspaceBody (guest : Program) (D log : ℕ) : Stmt :=
  .seq (.call 3 log [.bin .add (.reg 0) (.const 3)])
    (.seq (.call 4 log [.bin .add (.reg 2) (.const 5)])
      (.ret (guestWorkspaceExpr guest D (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 4))))

private theorem clog_succ_size {n : ℕ} (hn : 0 < n) : Nat.clog 2 (n+1) = n.size := by
  rw [clogTwo_succ_eq_log_add_one hn]
  apply le_antisymm
  · exact Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne'))
  · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

/-- The workspace procedure returns a word bound for the padded Theorem 2.2
call (page 7), with two logarithmic calls and no memory writes. -/
theorem guestWorkspace_runs {w log : ℕ} {p : Program}
    (hp : p.HasAt log (clogTwoModule log)) (guest : Program)
    (D n m sim pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hn : 0 < n) (hm : 0 < m) (hs : 0 < sim) (hD : 0 < D)
    (hnFit : n+4 < 2^w) (hsFit : sim+6 < 2^w)
    (hfit : guestWorkspace guest D n m sim < 2^w) :
    ∃ o out cost, Runs w p ω (guestWorkspaceBody guest D log)
      (startState [n,m,sim] mem pos) o out cost ∧
      (o.value = guestWorkspace guest D n m sim ∧ out.mem = mem) ∧
      cost ≤ 40*((n+2).size+(sim+4).size) + 80 +
        (guestWorkspaceExpr guest D (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 4)).size := by
  have ha : Nat.clog 2 (n+3) = (n+2).size := clog_succ_size (by omega)
  have hb : Nat.clog 2 (sim+5) = (sim+4).size := clog_succ_size (by omega)
  apply runs_start_le
  unfold guestWorkspaceBody
  refine runs_seq_call_le (clogTwo_meetsContract hp (n+3)) (vs := [n+3])
    (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro a mem₁ pos₁ ⟨hmem₁,ha'⟩
  rw [ha] at ha'
  subst a
  refine runs_seq_call_le (clogTwo_meetsContract hp (sim+5)) (vs := [sim+5])
    (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro b mem₂ pos₂ ⟨hmem₂,hb'⟩
  rw [hb] at hb'
  subst b
  refine runs_ret_le (v := guestWorkspace guest D n m sim)
    (guestWorkspaceExpr_eval guest D n m sim (by eval_expr) (by eval_expr)
      (by eval_expr) (by eval_expr) (by eval_expr) hn hm hs hD hfit)
    ⟨rfl,hmem₂.trans hmem₁⟩ ?_
  simp only [clogTwoContract,argsSize,Expr.size,ha,hb,Nat.zero_add,Nat.mul_add]
  omega

/-- From the guest heap and workspace sizes, compute the bit count of
their sum and enforce the five-bit minimum. -/
def paddedGuestWidthBody (log : ℕ) : Stmt :=
  .seq (.call 2 log [.bin .add (.bin .add (.reg 0) (.reg 1)) (.const 1)])
    (.ret (.bin .add (.reg 2) (.bin .sub (.const 5) (.reg 2))))

private theorem paddedWidth_runs {w log : ℕ} {p : Program}
    (hp : p.HasAt log (clogTwoModule log)) (heap space pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hpos : 0 < heap+space)
    (hroom : heap+space+2 < 2^w)
    (hwidth : max 5 (Nat.log 2 (heap+space)+1) < 2^w) :
    ∃ o out cost, Runs w p ω (paddedGuestWidthBody log)
      (startState [heap,space] mem pos) o out cost ∧
      (o.value = max 5 (Nat.log 2 (heap+space)+1) ∧ out.mem = mem) ∧
      cost ≤ 40*(Nat.log 2 (heap+space)+1)+50 := by
  let count := Nat.log 2 (heap+space)+1
  have hlog : Nat.clog 2 (heap+space+1) = count := clogTwo_succ_eq_log_add_one hpos
  have hw : count+(5-count) = max 5 (Nat.log 2 (heap+space)+1) := by
    change count+(5-count) = max 5 count
    omega
  have hsub : 5-count < 2^w := by omega
  have hfive : 5 < 2^w := by
    exact (le_max_left 5 count).trans_lt hwidth
  have hsum : count+(5-count) < 2^w := hw.symm ▸ hwidth
  apply runs_start_le
  unfold paddedGuestWidthBody
  refine runs_seq_call_le (clogTwo_meetsContract hp (heap+space+1)) (vs := [heap+space+1])
    (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro r out pos' ⟨hm,hr⟩
  rw [hlog] at hr
  subst r
  refine runs_ret_le (v := count+(5-count)) (by eval_expr) ⟨hw,hm⟩ ?_
  simp only [clogTwoContract,argsSize,Expr.size,hlog,Nat.zero_add]
  omega

/-- The width computation preserves memory and has logarithmic cost in
the guest allocation size for Theorem 2.2 (page 7). -/
theorem paddedGuestWidth_runs {w log : ℕ} {p : Program}
    (hp : p.HasAt log (clogTwoModule log)) (guest : Program)
    (D n m sim heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hpos : 0 < heap+guestWorkspace guest D n m sim)
    (hroom : heap+guestWorkspace guest D n m sim+2 < 2^w)
    (hwidth : paddedGuestWidth guest D n m sim heap < 2^w) :
    let space := guestWorkspace guest D n m sim
    ∃ o out cost, Runs w p ω (paddedGuestWidthBody log)
      (startState [heap,space] mem pos) o out cost ∧
      (o.value = paddedGuestWidth guest D n m sim heap ∧ out.mem = mem) ∧
      cost ≤ 40*(Nat.log 2 (heap+space)+1)+50 :=
  paddedWidth_runs hp heap (guestWorkspace guest D n m sim) pos mem ω hpos hroom hwidth

/-- Cost of computing the integer workspace with two ceiling logarithms. -/
def guestWorkspaceCost (guest : Program) (D n sim : ℕ) : ℕ :=
  40*((n+2).size+(sim+4).size) + 80 +
    (guestWorkspaceExpr guest D (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 4)).size

/-- The linked workspace calculation with runtime graph and simulation sizes. -/
def guestWorkspaceContract (w : ℕ) (guest : Program) (D : ℕ) : Contract where
  pre args _ := ∃ n m sim, args = [n,m,sim] ∧
    0 < n ∧ 0 < m ∧ 0 < sim ∧ 0 < D ∧ n+4 < 2^w ∧ sim+6 < 2^w ∧
    guestWorkspace guest D n m sim < 2^w
  post args mem ret out := ∃ n m sim, args = [n,m,sim] ∧
    ret = guestWorkspace guest D n m sim ∧ out = mem
  cost args _ := guestWorkspaceCost guest D (args.getD 0 0) (args.getD 2 0)

/-- Install the verified workspace arithmetic as a procedure. -/
theorem guestWorkspace_meetsContract {w entry log : ℕ} {p : Program}
    (guest : Program) (D : ℕ)
    (he : p.procs[entry]? = some (guestWorkspaceBody guest D log))
    (hp : p.HasAt log (clogTwoModule log)) :
    MeetsContract w p entry (guestWorkspaceContract w guest D) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨n,m,sim,rfl,hn,hm,hs,hD,hnFit,hsFit,hfit⟩ := hpre
  obtain ⟨o,out,c,hr,hpost,hc⟩ :=
    guestWorkspace_runs hp guest D n m sim pos mem ω hn hm hs hD hnFit hsFit hfit
  exact ⟨o,out,c,hr,⟨n,m,sim,rfl,hpost⟩,hc⟩

/-- The word-width calculation for the padded guest allocation. -/
def paddedGuestWidthContract (w : ℕ) : Contract where
  pre args _ := ∃ heap space, args = [heap,space] ∧ 0 < heap+space ∧
    heap+space+2 < 2^w ∧ max 5 (Nat.log 2 (heap+space)+1) < 2^w
  post args mem ret out := ∃ heap space, args = [heap,space] ∧
    ret = max 5 (Nat.log 2 (heap+space)+1) ∧ out = mem
  cost args _ := 40*(Nat.log 2 (args.getD 0 0+args.getD 1 0)+1)+50

/-- Install the padded word-width calculation. -/
theorem paddedGuestWidth_meetsContract {w entry log : ℕ} {p : Program}
    (he : p.procs[entry]? = some (paddedGuestWidthBody log))
    (hp : p.HasAt log (clogTwoModule log)) :
    MeetsContract w p entry (paddedGuestWidthContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨heap,space,rfl,hpos,hroom,hwidth⟩ := hpre
  obtain ⟨o,out,c,hr,hpost,hc⟩ := paddedWidth_runs hp heap space pos mem ω hpos hroom hwidth
  exact ⟨o,out,c,hr,⟨heap,space,rfl,hpost⟩,hc⟩

/-- Compute the workspace and pass it to the padded width procedure. -/
def selectPaddedGuestWidthBody (workspace width : ℕ) : Stmt :=
  .seq (.call 4 workspace [.reg 0,.reg 1,.reg 2])
    (.seq (.call 5 width [.reg 3,.reg 4]) (.ret (.reg 5)))

/-- Runtime width selection for the relocated tree call takes graph counts,
the simulation width, and the guest input allocation endpoint. -/
theorem selectPaddedGuestWidth_runs {w workspace width : ℕ} {p : Program}
    (guest : Program) (D n m sim heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hwork : MeetsContract w p workspace (guestWorkspaceContract w guest D))
    (hwidth : MeetsContract w p width (paddedGuestWidthContract w))
    (hn : 0 < n) (hm : 0 < m) (hs : 0 < sim) (hD : 0 < D)
    (hnFit : n+4 < 2^w) (hmFit : m < 2^w) (hsFit : sim+6 < 2^w)
    (hpos : 0 < heap+guestWorkspace guest D n m sim)
    (hroom : heap+guestWorkspace guest D n m sim+2 < 2^w)
    (hret : paddedGuestWidth guest D n m sim heap < 2^w) :
    ∃ o out cost, Runs w p ω (selectPaddedGuestWidthBody workspace width)
      (startState [n,m,sim,heap] mem pos) o out cost ∧
      (o.value = paddedGuestWidth guest D n m sim heap ∧ out.mem = mem) ∧
      cost ≤ guestWorkspaceCost guest D n sim +
        40*(Nat.log 2 (heap+guestWorkspace guest D n m sim)+1)+65 := by
  let space := guestWorkspace guest D n m sim
  have hsRoom : space < 2^w := by omega
  apply runs_start_le
  unfold selectPaddedGuestWidthBody
  refine runs_seq_call_le hwork (vs := [n,m,sim]) (by eval_expr) (by wram_words)
    ⟨n,m,sim,rfl,hn,hm,hs,hD,hnFit,hsFit,hsRoom⟩ ?_
  intro a mid pos₁ ha
  obtain ⟨x,y,z,he,ha,hmid⟩ := ha
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl⟩ := he
  subst a
  refine runs_seq_call_le hwidth (vs := [heap,space]) (by eval_expr) (by wram_words)
    ⟨heap,space,rfl,hpos,hroom,hret⟩ ?_
  intro b out pos₂ hb
  obtain ⟨x,y,he,hb,hout⟩ := hb
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl⟩ := he
  refine runs_ret_le (v := b) (by eval_expr) ⟨hb,hout.trans hmid⟩ ?_
  simp only [guestWorkspaceContract,paddedGuestWidthContract,argsSize,Expr.size,
    List.getD_cons_zero,List.getD_cons_succ,Nat.zero_add,space]
  omega

/-- The workspace and width calculation takes only runtime counts and
leaves the staged graph and weight arrays unchanged. -/
def selectPaddedGuestWidthContract (w : ℕ) (guest : Program) (D : ℕ) : Contract where
  pre args _ := ∃ n m sim heap, args = [n,m,sim,heap] ∧
    0 < n ∧ 0 < m ∧ 0 < sim ∧ 0 < D ∧ n+4 < 2^w ∧ sim+6 < 2^w ∧
    heap+guestWorkspace guest D n m sim+2 < 2^w ∧
    paddedGuestWidth guest D n m sim heap < 2^w
  post args mem ret out := ∃ n m sim heap, args = [n,m,sim,heap] ∧
    ret = paddedGuestWidth guest D n m sim heap ∧ out = mem
  cost args _ :=
    let n := args.getD 0 0
    let m := args.getD 1 0
    let sim := args.getD 2 0
    let heap := args.getD 3 0
    guestWorkspaceCost guest D n sim +
      40*(Nat.log 2 (heap+guestWorkspace guest D n m sim)+1)+65

/-- Charge the second logarithm in the selector to the width of its
guest allocation. The first two logarithms are in the workspace cost. -/
theorem selectPaddedGuestWidth_cost_le (w : ℕ) (guest : Program) (D n m sim heap : ℕ)
    (mem : ℕ → ℕ) :
    (selectPaddedGuestWidthContract w guest D).cost [n,m,sim,heap] mem ≤
      guestWorkspaceCost guest D n sim+40*paddedGuestWidth guest D n m sim heap+65 := by
  change guestWorkspaceCost guest D n sim+
    40*(Nat.log 2 (heap+guestWorkspace guest D n m sim)+1)+65 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left 40 (le_max_right _ _)) _) _

/-- Install the runtime width selection for the relocated Theorem 2.2
call (page 7). -/
theorem selectPaddedGuestWidth_meetsContract {w entry workspace width : ℕ} {p : Program}
    (guest : Program) (D : ℕ)
    (he : p.procs[entry]? = some (selectPaddedGuestWidthBody workspace width))
    (hwork : MeetsContract w p workspace (guestWorkspaceContract w guest D))
    (hwidth : MeetsContract w p width (paddedGuestWidthContract w)) :
    MeetsContract w p entry (selectPaddedGuestWidthContract w guest D) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨n,m,sim,heap,rfl,hn,hm,hs,hD,hnFit,hsFit,hroom,hret⟩ := hpre
  have hpos : 0 < heap+guestWorkspace guest D n m sim := by
    unfold guestWorkspace
    omega
  obtain ⟨o,out,c,hr,hpost,hc⟩ := selectPaddedGuestWidth_runs guest D n m sim heap pos
    mem ω hwork hwidth hn hm hs hD hnFit (hwords m (by simp)) hsFit hpos hroom hret
  exact ⟨o,out,c,hr,⟨n,m,sim,heap,rfl,hpost⟩,hc⟩

end MinCostFlow.LastLevelProgram
