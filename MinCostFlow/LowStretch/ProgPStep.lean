module

public import MinCostFlow.LowStretch.ProgDijRun
public import MinCostFlow.LowStretch.ProgPSum
public import MinCostFlow.LowStretch.ProgPTest

/-!
# One step of the petal search

`pstep` does one step of the search for a petal. Three cells at `CTL` hold the bucket pointer
`qp`, the number `ns` of settled nodes and the highway pointer `h`. Let `k` be the least key of
the queue (`INF` or more when it is empty).
* If bucket `qp` exists and starts below `k`, the step tests the radius `r = min(k - 1, b_qp)`
  with `ptest`, where `b_qp = lo + qp · bw` is the right end of the bucket. On success it
  returns `r + 2`. If the test fails and the bucket ends below `k`, it moves the pointer to the
  next bucket and returns `1`.
* Otherwise it runs `dijStep`. It returns `0` if the queue was empty. If a node `u` was settled,
  it appends `u` to the list at `SL`, adds the arcs of `u` but its slot to the sums (`psum`),
  and, if `u` is the highway pointer, moves the pointer to `h' = NXT[u]` and turns on the slot
  of `h'` (its head becomes `NXT[h']`) when `h' < S`.

`pstep_spec` states this at the level of the memory. The meaning of the tests and of the slots
is proved elsewhere.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The body of the test phase, with `qp` in register `32` and `k` in register `33`. -/
def ptestB (bTest : ℕ) : Stmt :=
  .seq (.assign 34 (.bin .add (.reg 23) (.bin .mul (.reg 32) (.reg 24))))
  (.seq (.cond (.bin .lt (.reg 34) (.reg 33)) (.assign 35 (.reg 34))
    (.assign 35 (.bin .sub (.reg 33) (.const 1))))
  (.seq (.call 36 bTest [.reg 35, .reg 19, .reg 20, .reg 21,
    .load (.bin .add (.reg 26) (.reg 32)), .load (.bin .add (.reg 27) (.reg 32)), .reg 22])
  (.cond (.reg 36) (.ret (.bin .add (.reg 35) (.const 2)))
    (.cond (.bin .lt (.reg 34) (.reg 33))
      (.seq (.store (.reg 31) (.bin .add (.reg 32) (.const 1))) (.ret (.const 1)))
      .nop))))

/-- The settle phase, after `dijStep` returned `2`. -/
def psettleB (bSum : ℕ) : Stmt :=
  .seq (.assign 38 (.load (.bin .add (.reg 14) (.const 1))))
  (.seq (.assign 39 (.load (.reg 14)))
  (.seq (.assign 40 (.load (.bin .add (.reg 31) (.const 1))))
  (.seq (.assign 41 (.load (.bin .add (.reg 31) (.const 2))))
  (.seq (.assign 42 (.load (.bin .add (.reg 28) (.reg 38))))
  (.seq (.assign 43 (.load (.bin .add (.reg 5) (.reg 42))))
  (.seq (.assign 44 (.load (.bin .add (.reg 28) (.reg 42))))
  (.seq (.assign 45 (.load (.bin .add (.reg 4) (.reg 38))))
  (.seq (.assign 46 (.load (.bin .add (.reg 5) (.reg 38))))
  (.seq (.call 36 bSum [.reg 45, .bin .sub (.reg 46) (.const 1), .reg 39, .reg 6, .reg 15, .reg 16,
    .reg 17, .reg 18, .reg 11, .reg 12, .reg 13, .reg 9, .reg 10, .reg 19])
  (.seq (.store (.bin .add (.reg 29) (.reg 40)) (.reg 38))
  (.seq (.store (.bin .add (.reg 31) (.const 1)) (.bin .add (.reg 40) (.const 1)))
  (.seq (.store (.bin .add (.reg 31) (.const 3)) (.reg 39))
  (.seq (.cond (.bin .eq (.reg 38) (.reg 41))
      (.seq (.store (.bin .add (.reg 31) (.const 2)) (.reg 42))
        (.cond (.bin .lt (.reg 42) (.reg 30))
          (.store (.bin .add (.reg 6) (.bin .sub (.reg 43) (.const 1))) (.reg 44)) .nop))
      .nop)
  (.ret (.const 1)))))))))))))))

/-- `pstep bStep bSum bTest`, with `dijStep`, `psum` and `ptest` at `bStep`, `bSum`, `bTest`. -/
def pstep (bStep bSum bTest : ℕ) : Stmt :=
  .seq (.assign 32 (.load (.reg 31)))
  (.seq (.assign 33 (.bin .div (.load (.bin .add (.reg 0) (.const 4))) (.reg 1)))
  (.seq (.cond (.bin .lt (.reg 32) (.bin .add (.reg 25) (.const 1)))
      (.cond (.bin .lt (.bin .add (.reg 23) (.bin .mul (.bin .sub (.reg 32) (.const 1)) (.reg 24)))
          (.reg 33))
        (.cond (.bin .lt (.load (.bin .add (.reg 31) (.const 3))) (.reg 33)) (ptestB bTest) .nop)
        .nop) .nop)
  (.seq (.call 37 bStep [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
    .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14])
  (.cond (.bin .eq (.reg 37) (.const 0)) (.ret (.const 0))
    (.cond (.bin .eq (.reg 37) (.const 2)) (psettleB bSum) (.ret (.const 1)))))))

theorem pstep_noRand (bStep bSum bTest : ℕ) : (pstep bStep bSum bTest).NoRand := by
  simp [pstep, ptestB, psettleB, Stmt.NoRand]

/-- The ghost values of `pstep`: those of `dijStep` and the other addresses. -/
structure PSG where
  G : StG
  ORD : ℕ
  AS : ℕ
  EXP : ℕ
  Es : ℕ
  SUM : ℕ
  M : ℕ
  κ : ℕ
  nact : ℕ
  lo : ℕ
  bw : ℕ
  Lb : ℕ
  SQ : ℕ
  P2 : ℕ
  NXT : ℕ
  SL : ℕ
  S : ℕ
  CTL : ℕ

namespace PSG

variable (X : PSG) (mem : ℕ → ℕ)

/-- The arguments of `pstep`. -/
def args : List ℕ :=
  X.G.L.argsR X.G.R ++ [X.ORD, X.AS, X.EXP, X.Es, X.SUM, X.M, X.κ, X.nact, X.lo, X.bw, X.Lb,
    X.SQ, X.P2, X.NXT, X.SL, X.S, X.CTL]

/-- The bucket pointer. -/
def qp : ℕ := mem X.CTL
/-- The least key of the queue. -/
def k : ℕ := mem (X.G.L.D + 4) / X.G.L.J
/-- The right end of bucket `qp`. -/
def bq : ℕ := X.lo + X.qp mem * X.bw
/-- The radius that is tested. -/
def rr : ℕ := if X.bq mem < X.k mem then X.bq mem else X.k mem - 1

theorem rr_of_lt (h : X.bq mem < X.k mem) : X.rr mem = X.bq mem := by
  unfold rr; simp only [h, ↓reduceIte]

theorem rr_of_ge (h : ¬ X.bq mem < X.k mem) : X.rr mem = X.k mem - 1 := by
  unfold rr; simp only [h, ↓reduceIte]

/-- The test is made. -/
def TB : Prop := X.qp mem < X.Lb + 1 ∧ X.lo + (X.qp mem - 1) * X.bw < X.k mem ∧
  mem (X.CTL + 3) < X.k mem
/-- The numbers of the test. -/
def pt : PT := ⟨X.rr mem, X.SUM, X.M, X.κ, mem (X.SQ + X.qp mem), mem (X.P2 + X.qp mem), X.nact⟩
/-- The settled node, after `dijStep`. -/
def u : ℕ := mem (X.G.R + 1)
/-- The numbers of `psum` for the settled node. -/
def ps : PS := ⟨mem (X.G.L.LO + X.u mem), mem (X.G.L.HI + X.u mem) - 1, mem X.G.R, X.G.L.HD,
  X.ORD, X.AS, X.EXP, X.Es, X.G.L.TS, X.G.L.NN, X.G.L.rs, X.G.L.OK, X.G.L.os, X.SUM⟩

/-- The memory after the settle phase, from the memory `mem2` after `psum`; `mem1` is the memory
after `dijStep`. -/
def setM (mem1 mem2 : ℕ → ℕ) : ℕ → ℕ :=
  let u := X.u mem1
  let ns := mem1 (X.CTL + 1)
  let h' := mem1 (X.NXT + u)
  let m3 := Function.update (Function.update (Function.update mem2 (X.SL + ns) u) (X.CTL + 1)
    (ns + 1)) (X.CTL + 3) (mem1 X.G.R)
  if u = mem1 (X.CTL + 2) then
    if h' < X.S then
      Function.update (Function.update m3 (X.CTL + 2) h')
        (X.G.L.HD + (mem1 (X.G.L.HI + h') - 1)) (mem1 (X.NXT + h'))
    else Function.update m3 (X.CTL + 2) h'
  else m3

/-- The precondition of `pstep`. -/
structure Pre (w : ℕ) : Prop where
  step : stepPre w X.G (X.G.L.argsR X.G.R) mem
  test : X.TB mem → (X.pt mem).Pre mem w
  sum : ∀ mem1, stepPost w X.G (X.G.L.argsR X.G.R) mem 2 mem1 → (X.ps mem1).Pre mem1 w
  q1 : 1 ≤ X.qp mem
  qL : X.qp mem ≤ X.Lb + 1
  wb : X.lo + (X.Lb + 1) * X.bw + 2 < 2 ^ w
  wL : X.Lb + 2 < 2 ^ w
  wSQ : X.SQ + X.Lb + 1 < 2 ^ w
  wP2 : X.P2 + X.Lb + 1 < 2 ^ w
  wCTL : X.CTL + 3 < 2 ^ w
  wSL : X.SL + mem (X.CTL + 1) + 1 < 2 ^ w
  wNXT : X.NXT + X.G.L.NN < 2 ^ w
  nxt : ∀ v < X.G.L.NN, mem (X.NXT + v) < X.G.L.NN
  wSQv : ∀ q ≤ X.Lb + 1, mem (X.SQ + q) < 2 ^ w ∧ mem (X.P2 + q) < 2 ^ w
  hiMM : ∀ v < X.G.L.NN, mem (X.G.L.HI + v) ≤ X.G.L.MM
  /-- The cells of `pstep` are kept by `dijStep` and are apart from each other. -/
  kSUM : ∀ t < 5, X.G.L.KeepS X.G.R (X.SUM + t)
  kSL : ∀ i ≤ mem (X.CTL + 1), X.G.L.KeepS X.G.R (X.SL + i)
  kCTL : ∀ i < 4, X.G.L.KeepS X.G.R (X.CTL + i)
  kNXT : ∀ v < X.G.L.NN, X.G.L.KeepS X.G.R (X.NXT + v)
  kSQ : ∀ q ≤ X.Lb + 1, X.G.L.KeepS X.G.R (X.SQ + q) ∧ X.G.L.KeepS X.G.R (X.P2 + q)
  dCTL : X.CTL + 4 ≤ X.SUM ∨ X.SUM + 5 ≤ X.CTL
  dSL : X.SL + mem (X.CTL + 1) < X.SUM ∨ X.SUM + 5 ≤ X.SL
  dSLC : X.SL + mem (X.CTL + 1) < X.CTL ∨ X.CTL + 4 ≤ X.SL
  dNXT : X.NXT + X.G.L.NN ≤ X.SUM ∨ X.SUM + 5 ≤ X.NXT

/-- The postcondition of `pstep`. -/
def Post (w : ℕ) (v : ℕ) (mem' : ℕ → ℕ) : Prop :=
  (2 ≤ v ∧ X.TB mem ∧ v = X.rr mem + 2 ∧ (X.pt mem).Pass mem ∧ mem' = mem) ∨
  (v = 1 ∧ X.TB mem ∧ ¬ (X.pt mem).Pass mem ∧ X.bq mem < X.k mem ∧
    mem' = Function.update mem X.CTL (X.qp mem + 1)) ∨
  ((X.TB mem → ¬ (X.pt mem).Pass mem ∧ X.k mem ≤ X.bq mem) ∧ ∃ mem1 v1,
    stepPost w X.G (X.G.L.argsR X.G.R) mem v1 mem1 ∧
    ((v1 = 0 ∧ v = 0 ∧ mem' = mem1) ∨ (v1 = 1 ∧ v = 1 ∧ mem' = mem1) ∨
     (v1 = 2 ∧ v = 1 ∧ ∃ mem2,
        (∀ t : Fin 5, mem2 (X.SUM + t) = mem1 (X.SUM + t) + (X.ps mem1).sm mem1 t (X.ps mem1).hi) ∧
        (∀ a, (a < X.SUM ∨ X.SUM + 5 ≤ a) → mem2 a = mem1 a) ∧ mem' = X.setM mem1 mem2)))

end PSG

/-- The numbers of the test of `pstep`, read from its arguments (as `PSG.pt`). -/
def ptA (args : List ℕ) (mem : ℕ → ℕ) : PT :=
  ⟨if args.getD 23 0 + mem (args.getD 31 0) * args.getD 24 0 <
      mem (args.getD 0 0 + 4) / args.getD 1 0 then
    args.getD 23 0 + mem (args.getD 31 0) * args.getD 24 0
  else mem (args.getD 0 0 + 4) / args.getD 1 0 - 1,
  args.getD 19 0, args.getD 20 0, args.getD 21 0, mem (args.getD 26 0 + mem (args.getD 31 0)),
  mem (args.getD 27 0 + mem (args.getD 31 0)), args.getD 22 0⟩

/-- The case of `pstep` that costs at most `400`: the test is made, and it passes or the bucket
ends below the least key. -/
def pcond (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  (mem (args.getD 31 0) < args.getD 25 0 + 1 ∧
      args.getD 23 0 + (mem (args.getD 31 0) - 1) * args.getD 24 0 <
        mem (args.getD 0 0 + 4) / args.getD 1 0 ∧
      mem (args.getD 31 0 + 3) < mem (args.getD 0 0 + 4) / args.getD 1 0) ∧
    (args.getD 23 0 + mem (args.getD 31 0) * args.getD 24 0 <
        mem (args.getD 0 0 + 4) / args.getD 1 0 ∨ (ptA args mem).Pass mem)

open Classical in
/-- The cost of `pstep`. -/
noncomputable def pstepCost (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  if pcond args mem then 400 else 2 * dijCost (args.take 15) mem + 600

theorem PSG.cost_ge (X : PSG) (mem : ℕ → ℕ) : 400 ≤ pstepCost X.args mem := by
  unfold pstepCost; split_ifs <;> omega

theorem PSG.pcond_iff (X : PSG) (mem : ℕ → ℕ) :
    pcond X.args mem ↔ X.TB mem ∧ (X.bq mem < X.k mem ∨ (X.pt mem).Pass mem) := by
  simp only [pcond, ptA, PSG.args, DL.argsR, List.cons_append, List.nil_append,
    List.getD_cons_succ, List.getD_cons_zero]
  rfl

theorem PSG.cost_dij (X : PSG) (mem : ℕ → ℕ)
    (h : ¬ (X.TB mem ∧ (X.bq mem < X.k mem ∨ (X.pt mem).Pass mem))) :
    pstepCost X.args mem = 2 * dijCost (X.G.L.argsR X.G.R) mem + 600 := by
  unfold pstepCost
  rw [if_neg (fun hc => h ((X.pcond_iff mem).mp hc))]
  rfl

theorem PSG.cost_400 (X : PSG) (mem : ℕ → ℕ)
    (h : X.TB mem ∧ (X.bq mem < X.k mem ∨ (X.pt mem).Pass mem)) :
    pstepCost X.args mem = 400 := by
  unfold pstepCost
  rw [if_pos ((X.pcond_iff mem).mpr h)]

/-- The contract of `pstep`. -/
noncomputable def pstepC (w : ℕ) : Contract :=
  ghostC (fun (X : PSG) args mem => args = X.args ∧ X.Pre mem w)
    (fun (X : PSG) _ mem v mem' => X.Post mem w v mem')
    pstepCost

theorem PSG.setM_1 {X : PSG} {mem1 mem2 : ℕ → ℕ} (e1 : X.u mem1 = mem1 (X.CTL + 2))
    (e2 : mem1 (X.NXT + X.u mem1) < X.S) :
    X.setM mem1 mem2 = Function.update (Function.update (Function.update (Function.update
      (Function.update mem2 (X.SL + mem1 (X.CTL + 1)) (X.u mem1)) (X.CTL + 1) (mem1 (X.CTL + 1) + 1))
      (X.CTL + 3) (mem1 X.G.R)) (X.CTL + 2) (mem1 (X.NXT + X.u mem1)))
      (X.G.L.HD + (mem1 (X.G.L.HI + mem1 (X.NXT + X.u mem1)) - 1))
      (mem1 (X.NXT + mem1 (X.NXT + X.u mem1))) := by
  unfold PSG.setM
  dsimp only
  rw [if_pos e1, if_pos e2]

theorem PSG.setM_2 {X : PSG} {mem1 mem2 : ℕ → ℕ} (e1 : X.u mem1 = mem1 (X.CTL + 2))
    (e2 : ¬ mem1 (X.NXT + X.u mem1) < X.S) :
    X.setM mem1 mem2 = Function.update (Function.update (Function.update (Function.update mem2
      (X.SL + mem1 (X.CTL + 1)) (X.u mem1)) (X.CTL + 1) (mem1 (X.CTL + 1) + 1))
      (X.CTL + 3) (mem1 X.G.R)) (X.CTL + 2) (mem1 (X.NXT + X.u mem1)) := by
  unfold PSG.setM
  dsimp only
  rw [if_pos e1, if_neg e2]

theorem PSG.setM_3 {X : PSG} {mem1 mem2 : ℕ → ℕ} (e1 : ¬ X.u mem1 = mem1 (X.CTL + 2)) :
    X.setM mem1 mem2 = Function.update (Function.update (Function.update mem2
      (X.SL + mem1 (X.CTL + 1)) (X.u mem1)) (X.CTL + 1) (mem1 (X.CTL + 1) + 1))
      (X.CTL + 3) (mem1 X.G.R) := by
  unfold PSG.setM
  dsimp only
  rw [if_neg e1]

/-- The bounds that the settle phase needs. -/
theorem PSG.raw {w : ℕ} {X : PSG} {mem mem1 : ℕ → ℕ} (h : X.Pre mem w)
    (hp : stepPost w X.G (X.G.L.argsR X.G.R) mem 2 mem1) :
    X.NXT + mem1 (X.G.R + 1) < 2 ^ w ∧
    X.G.L.HI + mem1 (X.NXT + mem1 (X.G.R + 1)) < 2 ^ w ∧
    X.NXT + mem1 (X.NXT + mem1 (X.G.R + 1)) < 2 ^ w ∧
    X.G.L.LO + mem1 (X.G.R + 1) < 2 ^ w ∧
    X.G.L.HI + mem1 (X.G.R + 1) < 2 ^ w ∧
    mem1 (X.G.L.LO + mem1 (X.G.R + 1)) < 2 ^ w ∧
    mem1 (X.G.L.HI + mem1 (X.G.R + 1)) < 2 ^ w ∧
    mem1 X.G.R < 2 ^ w ∧
    X.SL + mem1 (X.CTL + 1) < 2 ^ w ∧
    mem1 (X.CTL + 1) + 1 < 2 ^ w ∧
    mem1 (X.G.L.HI + mem1 (X.NXT + mem1 (X.G.R + 1))) < 2 ^ w ∧
    X.G.L.HD + (mem1 (X.G.L.HI + mem1 (X.NXT + mem1 (X.G.R + 1))) - 1) < 2 ^ w := by
  have hs0 := h.step
  obtain ⟨-, hR, hR2, hsh, -⟩ := hs0
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hsh.lay
  obtain ⟨hf1, -, -⟩ := hsh.fits
  rcases hp with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, d', qs', -, -, hdL, hsett, hs', hr', hinv', -, -, hk', -⟩
  · omega
  · omega
  have hu : mem1 (X.G.R + 1) ∈ X.G.Nodes := ((hr'.sett _).mp (by rw [hsett]; exact Or.inr rfl)).1
  have hun : mem1 (X.G.R + 1) < X.G.L.NN := ((hs'.ok_iff _).mpr hu).1
  have hkLO : mem1 (X.G.L.LO + mem1 (X.G.R + 1)) = mem (X.G.L.LO + mem1 (X.G.R + 1)) :=
    hk' _ (Or.inl (by omega))
  have hkHI : ∀ v < X.G.L.NN, mem1 (X.G.L.HI + v) = mem (X.G.L.HI + v) :=
    fun v hv => hk' _ (Or.inl (by omega))
  have hkN : ∀ v < X.G.L.NN, mem1 (X.NXT + v) = mem (X.NXT + v) := fun v hv => hk' _ (h.kNXT v hv)
  have hkC : mem1 (X.CTL + 1) = mem (X.CTL + 1) := hk' _ (h.kCTL 1 (by omega))
  have hn1 := hkN _ hun
  have hn2 := h.nxt _ hun
  rw [← hn1] at hn2
  have hn3 := hkN _ hn2
  have hh1 := h.hiMM _ hn2
  rw [← hkHI _ hn2] at hh1
  have har := hs'.arcs _ hu
  simp only [DL.g, if_pos hun] at har
  have hL := hinv'.L_lt
  have wSL := h.wSL
  have wNXT := h.wNXT
  have wCTL := h.wCTL
  have hfR : X.G.L.INF * X.G.L.J + X.G.L.J < 2 ^ w := hsh.fits.2.1
  have hJ1 := hr'.pq.J_pos
  have hINF : X.G.L.INF ≤ X.G.L.INF * X.G.L.J := Nat.le_mul_of_pos_right _ hJ1
  unfold pqSize at hf1
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

/-- `psum` on the settled node costs at most the step of Dijkstra. -/
theorem PSG.cost_settle {w : ℕ} {X : PSG} {mem mem1 : ℕ → ℕ} (h : X.Pre mem w)
    (hp : stepPost w X.G (X.G.L.argsR X.G.R) mem 2 mem1) :
    200 * (mem1 (X.G.L.HI + mem1 (X.G.R + 1)) - 1 - mem1 (X.G.L.LO + mem1 (X.G.R + 1))) + 30 ≤
      dijCost (X.G.L.argsR X.G.R) mem := by
  have hs0 := h.step
  obtain ⟨-, hR, hR2, hsh, -⟩ := hs0
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hsh.lay
  rcases hp with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, d', qs', -, -, -, hsett, hs', hr', -, -, -, hk', -, -, -, hc⟩
  · omega
  · omega
  have hu : mem1 (X.G.R + 1) ∈ X.G.Nodes := ((hr'.sett _).mp (by rw [hsett]; exact Or.inr rfl)).1
  have hun : mem1 (X.G.R + 1) < X.G.L.NN := ((hs'.ok_iff _).mpr hu).1
  have hkLO : mem1 (X.G.L.LO + mem1 (X.G.R + 1)) = mem (X.G.L.LO + mem1 (X.G.R + 1)) :=
    hk' _ (Or.inl (by omega))
  have hkHI : mem1 (X.G.L.HI + mem1 (X.G.R + 1)) = mem (X.G.L.HI + mem1 (X.G.R + 1)) :=
    hk' _ (Or.inl (by omega))
  have hdeg : X.G.L.deg mem (mem1 (X.G.R + 1)) =
      mem (X.G.L.HI + mem1 (X.G.R + 1)) - mem (X.G.L.LO + mem1 (X.G.R + 1)) := by
    simp [DL.deg, DL.g, hun]
  rw [hc, hdeg, hkLO, hkHI]
  have : 200 * (mem (X.G.L.HI + mem1 (X.G.R + 1)) - mem (X.G.L.LO + mem1 (X.G.R + 1)) + 1) ≤
      (mem (X.G.L.HI + mem1 (X.G.R + 1)) - mem (X.G.L.LO + mem1 (X.G.R + 1)) + 1) *
        (50 * (Nat.log 2 X.G.L.J + 2) + 300) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  unfold stCost
  omega

/-- A return at the start of a sequence. -/
theorem runs_seq_ret_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {t : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hq : Q (.returned v) st) (hc : k + (e.size + 1 + 1) ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.ret e) t) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  ⟨.returned v, st, e.size + 1 + 1,
    runs_seq_iff.mpr (Or.inl ⟨v, e.size + 1, runs_ret_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, rfl, rfl⟩),
    hq, hc⟩

/-- `wram_run`, which also steps over a return at the start of a sequence. -/
macro "pwram_run" : tactic => `(tactic|
  repeat (any_goals (first
    | wram_step
    | (wram_guard; with_reducible refine runs_seq_ret_le (by eval_expr) ?_ ?_))))

set_option hygiene false in
/-- The cost goals of `pstep_spec`. -/
macro "pcost_tac" : tactic => `(tactic| (
  simp only [dijStepC, psumC, ptestC, ghostC, PSG.args, DL.argsR,
    List.cons_append, List.nil_append, List.take, List.getD_cons_succ,
    List.getD_cons_zero, startState] at *
  wram_cost))

set_option hygiene false in
/-- `omega` with the least key as an atom. -/
macro "komega" : tactic => `(tactic| (
  try simp only [PSG.TB, PSG.qp, PSG.k, PSG.bq, PSG.rr] at *
  try simp only [startState] at *
  generalize mem (X.G.L.D + 4) / X.G.L.J = kk at *
  omega))

set_option hygiene false in
/-- The part of the proof of `pstep_spec` after the call of `dijStep`. -/
macro "pdij_tac" : tactic => `(tactic| (
  intro v1 mem1 pos1 hpost1
  have hp1 : stepPost w X.G (X.G.L.argsR X.G.R) mem v1 mem1 := hpost1 X.G h.step
  clear hpost1
  have hTF : X.TB mem → ¬ (X.pt mem).Pass mem ∧ X.k mem ≤ X.bq mem := by
    first
    | exact hTF0 (by omega) (by simp only [PSG.bq, PSG.k, PSG.qp]; omega)
    | (intro htb; simp only [PSG.TB, PSG.qp, PSG.k] at htb; komega)
  have hcD := PSG.cost_dij X mem (fun hh => by
    have := hTF hh.1
    rcases hh.2 with h' | h'
    · omega
    · exact this.1 h')
  rcases Classical.em (v1 = 2) with h2 | h2
  · subst h2
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := PSG.raw h hp1
    have wCTL := h.wCTL
    wram_run
    all_goals first
      | exact ⟨X.ps mem1, rfl, h.sum mem1 hp1⟩
      | (intro vs mem2 pos2 hps
         obtain ⟨hsum, hfr⟩ := hps (X.ps mem1) rfl
         clear hps
         have hcs := PSG.cost_settle h hp1
         wram_run
         all_goals first
           | pcost_tac
           | (refine Or.inr (Or.inr ⟨hTF, mem1, 2, hp1, Or.inr (Or.inr ⟨rfl, rfl, mem2, hsum, hfr, ?_⟩)⟩)
              dsimp only
              by_cases e1 : mem1 (X.G.R + 1) = mem1 (X.CTL + 2) <;>
                by_cases e2 : mem1 (X.NXT + mem1 (X.G.R + 1)) < X.S <;>
                first
                  | (exfalso; omega)
                  | (rw [PSG.setM_1 e1 e2]; rfl)
                  | (rw [PSG.setM_2 e1 e2]; rfl)
                  | (rw [PSG.setM_3 e1]; rfl)))
  · wram_run
    all_goals first
      | exact Or.inr (Or.inr ⟨hTF, mem1, v1, hp1, Or.inl ⟨‹v1 = 0›, rfl, rfl⟩⟩)
      | exact Or.inr (Or.inr ⟨hTF, mem1, v1, hp1, Or.inr (Or.inl
          ⟨by rcases hp1 with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ <;> omega, rfl, rfl⟩)⟩)
      | pcost_tac))

set_option maxHeartbeats 12000000 in
theorem pstep_spec {w : ℕ} {p : Program} {b bStep bSum bTest : ℕ}
    (hp : p.HasAt b [pstep bStep bSum bTest]) (hStep : MeetsContract w p bStep (dijStepC w))
    (hSum : MeetsContract w p bSum (psumC w)) (hTest : MeetsContract w p bTest (ptestC w)) :
    MeetsContract w p b (pstepC w) := by
  have hproc : p.procs[b]? = some (pstep bStep bSum bTest) := hp 0 (by simp)
  refine meets_of_ghost hproc ?_
  intro X args mem pos hwords hpre
  obtain ⟨rfl, h⟩ := hpre
  have hs := h.step
  obtain ⟨-, hR, hR2, hsh, hrep, hinv, hdone, hcap, hpar, hz, hS⟩ := hs
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hsh.lay
  obtain ⟨hf1, hf2, hf3⟩ := hsh.fits
  have hJ1 := hrep.pq.J_pos
  have hD : X.G.L.D + 4 < 2 ^ w := by unfold pqSize at hf1; omega
  have hrw : mem (X.G.L.D + 4) < 2 ^ w := by
    have e4 : X.G.L.D + 3 + 1 = X.G.L.D + 4 := rfl
    obtain ⟨c0, hc0, h0⟩ := hrep.pq.tt.root_mem hJ1
    rw [← e4, h0, hrep.pq.leaf c0 hc0]
    cases hq0 : X.G.qs c0 with
    | nil => simp only [leafv]; omega
    | cons f l =>
      simp only [leafv]
      have := hrep.pq.lt c0 f (by rw [hq0]; exact List.mem_cons_self)
      have : f.1 * X.G.L.J ≤ X.G.L.INF * X.G.L.J := Nat.mul_le_mul_right _ (by omega)
      omega
  have hq1 := h.q1
  have hqL := h.qL
  have wb := h.wb
  have wL := h.wL
  unfold PSG.qp at hq1 hqL
  have m1 : (mem X.CTL - 1) * X.bw ≤ (X.Lb + 1) * X.bw := Nat.mul_le_mul_right _ (by omega)
  have m2 : mem X.CTL * X.bw ≤ (X.Lb + 1) * X.bw := Nat.mul_le_mul_right _ hqL
  have hw15 : ∀ v ∈ [X.G.L.D, X.G.L.J, X.G.L.A, X.G.L.INF, X.G.L.LO, X.G.L.HI, X.G.L.HD,
      X.G.L.CS, X.G.L.CL, X.G.L.OK, X.G.L.os, X.G.L.TS, X.G.L.NN, X.G.L.rs, X.G.R], v < 2 ^ w :=
    fun v hv => hwords v (by
      simp only [PSG.args, DL.argsR, List.cons_append, List.nil_append, List.mem_cons] at hv ⊢
      rcases hv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h])
  have hrw' : (startState [X.G.L.D, X.G.L.J, X.G.L.A, X.G.L.INF, X.G.L.LO, X.G.L.HI, X.G.L.HD,
      X.G.L.CS, X.G.L.CL, X.G.L.OK, X.G.L.os, X.G.L.TS, X.G.L.NN, X.G.L.rs, X.G.R, X.ORD, X.AS,
      X.EXP, X.Es, X.SUM, X.M, X.κ, X.nact, X.lo, X.bw, X.Lb, X.SQ, X.P2, X.NXT, X.SL, X.S, X.CTL]
      mem pos).mem (X.G.L.D + 4) < 2 ^ w := hrw
  have hwX := hwords
  simp only [PSG.args, DL.argsR, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hwX
  obtain ⟨wD, wJ, wA, wINF, wLO, wHI, wHD, wCS, wCL, wOK, wos, wTS, wNN, wrs, wR, wORD, wAS, wEXP,
    wEs, wSUM, wM, wκ, wnact, wlo, wbw, wLb, wSQ, wP2, wNXT, wSL, wS, wCTL⟩ := hwX
  have vSQ := (h.wSQv _ hqL).1
  have vP2 := (h.wSQv _ hqL).2
  have fSQ : X.SQ + mem X.CTL < 2 ^ w := by have := h.wSQ; omega
  have fP2 : X.P2 + mem X.CTL < 2 ^ w := by have := h.wP2; omega
  have hc400 := PSG.cost_ge X mem
  have wCTL3 := h.wCTL
  wram_enter
  subst hpre
  dsimp only [pstep, ptestB, psettleB, PSG.args, DL.argsR, List.cons_append, List.nil_append]
  pwram_run
  all_goals first
    | exact hw15
    | exact ⟨X.G, h.step⟩
    | (simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        imp_false, not_false_eq_true, implies_true, and_true, startState]; omega)
    | (refine ⟨X.pt mem, ?_, h.test ?_⟩
       · simp only [PSG.pt, PT.args, PSG.rr, PSG.bq, PSG.k, PSG.qp, startState]
         simp only [hcond, ↓reduceIte]
       · simp only [PSG.TB, PSG.qp, PSG.k]; komega)
    | pdij_tac
    | (intro vt memt pt' hpt
       obtain ⟨hmt, hvt⟩ := hpt
       have hvt' : vt = @ite _ ((X.pt mem).Pass mem) (Classical.propDecidable _) 1 0 := hvt (X.pt mem) (by
         simp only [PSG.pt, PT.args, PSG.rr, PSG.bq, PSG.k, PSG.qp, startState]
         simp only [hcond, ↓reduceIte])
       clear hvt
       have hTF0 : vt = 0 → ¬ (X.bq mem < X.k mem) →
           (X.TB mem → ¬ (X.pt mem).Pass mem ∧ X.k mem ≤ X.bq mem) := by
         intro h0 hb _
         refine ⟨fun hP => ?_, by omega⟩
         simp only [hP, ↓reduceIte] at hvt'; omega
       subst memt
       pwram_run
       all_goals first
         | (simp only [Outcome.value, startState]
            refine Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩
            · omega
            · simp only [PSG.TB, PSG.qp, PSG.k]; komega
            · rcases Classical.em (X.bq mem < X.k mem) with hb | hb
              · rw [PSG.rr_of_lt X mem hb]; first | rfl | (exfalso; komega)
              · rw [PSG.rr_of_ge X mem hb]; first | rfl | (exfalso; komega)
            · by_contra hn; simp only [hn, ↓reduceIte] at hvt'; omega
            · rfl)
         | (simp only [Outcome.value, startState]
            refine Or.inr (Or.inl ⟨rfl, ?_, fun hP => ?_, ?_, ?_⟩)
            · simp only [PSG.TB, PSG.qp, PSG.k]; komega
            · simp only [hP, ↓reduceIte] at hvt'; omega
            · simp only [PSG.bq, PSG.k, PSG.qp]; omega
            · rfl)
         | exact ⟨X.G, h.step⟩
         | pcost_tac
         | pdij_tac)

end MinCostFlow.LowStretch
