module

public import MinCostFlow.LowStretch.ProgRecRootPre
public import MinCostFlow.LowStretch.ProgRecMx
public import MinCostFlow.LowStretch.ProgEntryMain

/-!
# The root procedure

The entry calls the procedure `rootP bRec bMx` with the arguments `E.args` of the first cluster
(`EA`). It finds the largest rounded weight `Mw` with `mxP` (at `bMx`), computes `J = pσ + pa + 4`
and `INF = 2 n Mw + 1`, writes the global block at the heap pointer `H` and the record block of
the first cluster at `H + 21` (`rootGlob`, `rootRecL`), and calls the cluster procedure (at
`bRec`) with `[H, H + 21, OUT, H + 30]`. It returns what that call returns.

`rootP_meets` shows that `rootP` meets the contract `clC` of the entry when the cluster procedure
meets `MeetsRec`. The precondition of the cluster procedure is `rootPre`. With the entry, this
gives the statement from `MeetsRec` (`lowStretchSpanningTree_of_rec`).

Two small tools come first: `stR`, which stores registers one after the other from the address
in a base register, and `runs_seq_call_spec`, which runs a call whose callee is described by a
statement about its runs (as `MeetsRec` is) and not by a `Contract`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-! ### Storing registers -/

/-- Store register `rs[j]` at `r_b + i + j`, then run `s`. -/
def stR (b : ℕ) : List ℕ → ℕ → Stmt → Stmt
  | [], _, s => s
  | r :: rs, i, s => .seq (.store (.bin .add (.reg b) (.const i)) (.reg r)) (stR b rs (i + 1) s)

theorem stR_noRand (b : ℕ) (s : Stmt) (hs : s.NoRand) :
    ∀ (rs : List ℕ) (i : ℕ), (stR b rs i s).NoRand
  | [], _ => hs
  | _ :: rs, i => by
    simp only [stR, Stmt.NoRand, true_and]
    exact stR_noRand b s hs rs (i + 1)

/-- **What `stR` leaves.** With `r_b = c` and `c + i + |rs| < 2^w`, the continuation `s` runs
from a memory that holds `st.regs rs[j]` at `c + i + j` and equals `st.mem` elsewhere, with the
same registers. Each store costs at most 6 steps. -/
theorem runs_stR {w : ℕ} {p : Program} {ω : ℕ → Bool} {Q : Outcome → State → Prop}
    {s : Stmt} {b c : ℕ} :
    ∀ (rs : List ℕ) (i : ℕ) (st : State) (k T : ℕ), st.regs b = c → c + i + rs.length < 2 ^ w →
      (∀ mem', (∀ j (hj : j < rs.length), mem' (c + i + j) = st.regs rs[j]) →
        (∀ y, (y < c + i ∨ c + i + rs.length ≤ y) → mem' y = st.mem y) →
        ∃ o st' c', Runs w p ω s { st with mem := mem' } o st' c' ∧ Q o st' ∧
          k + 6 * rs.length + c' ≤ T) →
      ∃ o st' c', Runs w p ω (stR b rs i s) st o st' c' ∧ Q o st' ∧ k + c' ≤ T := by
  intro rs
  induction rs with
  | nil =>
    intro i st k T _ _ hs
    obtain ⟨o, st', c', hr, hq, hc⟩ := hs st.mem (fun j hj => by simp at hj) (fun _ _ => rfl)
    exact ⟨o, st', c', hr, hq, by simpa using hc⟩
  | cons r rs ih =>
    intro i st k T hb hlt hs
    have hci : c + i < 2 ^ w := by simp at hlt; omega
    have hi : i < 2 ^ w := by omega
    unfold stR
    refine runs_seq_store_le (x := c + i) (v := st.regs r)
      (Expr.eval_add (Expr.eval_reg_of_eq hb) (Expr.eval_const hi) hci)
      (Expr.eval_reg_of_eq rfl) ?_
    refine ih (i + 1) { st with mem := Function.update st.mem (c + i) (st.regs r) } _ T hb
      (by simp at hlt; omega) ?_
    intro mem' hm hf
    obtain ⟨o, st', c', hr, hq, hc⟩ := hs mem' (fun j hj => by
        rcases j with _ | j
        · rw [Nat.add_zero, hf (c + i) (Or.inl (by omega))]
          simp
        · have := hm j (by simpa using hj)
          rw [show c + i + (j + 1) = c + (i + 1) + j by omega, this]
          simp)
      (fun y hy => by
        rw [hf y (by simp at hy; omega)]
        simp only
        rw [Function.update_of_ne (by simp at hy; omega)])
    refine ⟨o, st', c', hr, hq, ?_⟩
    simp only [Expr.size, List.length_cons] at hc ⊢
    omega

/-! ### Calls described by their runs -/

/-- **A call whose callee is described by its runs.** If every run of procedure `f` on the
arguments `vs` and the current memory ends with `Post` within `K` steps, the call runs as
`runs_seq_call_le` says. -/
theorem runs_seq_call_spec {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {s : Stmt} {st : State} {vs : List ℕ} {k T K : ℕ} {Q : Outcome → State → Prop}
    {Post : ℕ → (ℕ → ℕ) → Prop}
    (hf : ∀ pos ω, ∃ body, p.procs[f]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState vs st.mem pos) o st' c ∧ Post o.value st'.mem ∧ c ≤ K)
    (hargs : evalArgs w st args = some vs) (hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hrest : ∀ v mem' pos', Post v mem' →
      ∃ o st' c, Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' }
        o st' c ∧ Q o st' ∧ (k + argsSize args + K + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_call_le (C := ⟨fun a m => a = vs ∧ m = st.mem, fun _ _ v m' => Post v m',
      fun _ _ => K⟩)
    (fun _ _ pos ω _ h => by obtain ⟨rfl, rfl⟩ := h; exact hf pos ω) hargs hwords ⟨rfl, rfl⟩
    hrest

/-! ### The root procedure -/

/-- The registers that hold the global block and the first five words of the record block, in
order. The arguments `E.args` are in registers `0` to `28`; `Mw`, `B`, `J` and `INF` are in
registers `29` to `32`. -/
def rootRegs : List ℕ :=
  [0, 1, 5, 2, 3, 4, 18, 19, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 30, 31, 32, 23, 25, 26, 22, 24]

/-- **The root procedure**, called with `E.args`. -/
def rootP (bRec bMx : ℕ) : Stmt :=
  .seq (.call 29 bMx [.reg 1, .reg 3])
  (.seq (.assign 30 (.load (.bin .add (.reg 20) (.const 2))))
  (.seq (.assign 31 (.bin .add (.bin .add (.load (.bin .add (.reg 20) (.const 3)))
    (.load (.reg 20))) (.const 4)))
  (.seq (.assign 32 (.bin .add (.bin .mul (.bin .mul (.const 2) (.reg 0)) (.reg 29)) (.const 1)))
  (stR 28 rootRegs 0
    (.seq (.call 33 bRec [.reg 28, .bin .add (.reg 28) (.const 21), .reg 27,
      .bin .add (.reg 28) (.const 30)])
    (.ret (.reg 33)))))))

theorem rootP_noRand (bRec bMx : ℕ) : (rootP bRec bMx).NoRand := by
  simp only [rootP, Stmt.NoRand, true_and]
  exact stR_noRand _ _ (by simp [Stmt.NoRand]) _ _

variable {G : WGraph} {T : KT}

/-- **The root procedure meets the contract of the entry**, when the cluster procedure at
`bRec` meets `MeetsRec`. -/
theorem rootP_meets {w A : ℕ} {p : Program} {bRoot bRec bMx : ℕ}
    (hp : p.HasAt bRoot [rootP bRec bMx]) (hMx : p.HasAt bMx [mxP]) (hRec : MeetsRec w A p bRec) :
    MeetsContract w p bRoot (clC w A G T) := by
  intro args mem pos ω _ hpre
  obtain ⟨E, rfl, hE, hw⟩ := hpre
  have hproc : p.procs[bRoot]? = some (rootP bRec bMx) := hp 0 (by simp)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19,
    l20, l21⟩ := hE.lay
  have hn := hE.hn
  have hm := hE.hm
  have hN := hE.hN
  set X := E.H + (pgOf G).maxω + 2 with hX
  have hX1 : 1 ≤ X := by omega
  have hXw : 2 ^ 62 * X ^ 12 < 2 ^ w := by
    have : 2 ^ 62 * X ^ 12 ≤ 2 ^ 63 * X ^ 14 :=
      Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right hX1 (by norm_num))
    omega
  have hX12 : X ≤ X ^ 12 := Nat.le_self_pow (by norm_num) X
  have hXw' : 4 * (X * X) < 2 ^ w := by
    have : X * X ≤ X ^ 12 := by
      calc X * X = X ^ 2 := by ring
        _ ≤ X ^ 12 := Nat.pow_le_pow_right hX1 (by norm_num)
    omega
  have hpm : (pgOf G).m = G.m := pgOf_m
  refine ⟨rootP bRec bMx, hproc, ?_⟩
  refine runs_start_le ?_
  -- the largest rounded weight
  refine runs_seq_call_le (vs := [G.m, E.PW]) (mxP_spec hMx)
    (by simp [evalArgs, Expr.eval, startState, EA.args, hm]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      omega)
    ⟨G.m, E.PW, rfl, by omega, fun j hj => by
      show mem (E.PW + j) < 2 ^ w
      rw [hE.pw j hj]
      have := pω_le_maxω (G := G) hj
      omega⟩ ?_
  intro Mw mem1 pos1 hmx
  obtain ⟨hmem1, hle, hor⟩ := hmx
  subst mem1
  dsimp only [startState] at hle hor
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hle hor
  have hMw : ∀ p < G.m, (pgOf G).pω p ≤ Mw := fun p hp => by
    have := hle p hp; rwa [hE.pw p hp] at this
  have hMw' : Mw ≤ (pgOf G).maxω := by
    rcases hor with h | ⟨j, hj, h⟩
    · omega
    · rw [h, hE.pw j hj]; exact pω_le_maxω hj
  -- `B`, `J` and `INF`
  have hP : ∀ i < 6, mem (E.PAR + i) = parVal G.n G.m i := hE.prm
  have hJ2 : 2 ^ rootJ G.n < 2 ^ w := by
    have h1 := two_pow_J_le G.n
    have h2 : (G.n + 4) ^ 4 ≤ (2 * X) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h3 : (2 * X) ^ 4 = 16 * X ^ 4 := by ring
    have h4 : X ^ 4 ≤ X ^ 12 := Nat.pow_le_pow_right hX1 (by norm_num)
    omega
  have hJw : rootJ G.n < 2 ^ w := by
    have := Nat.lt_two_pow_self (n := rootJ G.n)
    omega
  have hBw : pB G.n < 2 ^ w := by
    have := lt_two_pow_J G.n
    have : pB G.n ≤ 128 * pB G.n * G.n ^ 2 := by
      have : 1 ≤ G.n ^ 2 := Nat.one_le_pow _ _ (by have := hE.two_le; omega)
      calc pB G.n = 1 * pB G.n * 1 := by ring
        _ ≤ 128 * pB G.n * G.n ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) this
    omega
  have hnM : G.n * Mw ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have hpa : pa G.n < 2 ^ w := by unfold rootJ at hJw; omega
  have hσ : pσ G.n < 2 ^ w := by unfold rootJ at hJw; omega
  refine runs_seq_assign_le (v := pB G.n) (Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq (v := E.PAR) (by simp [startState, EA.args]))
      (Expr.eval_const (by omega)) (by omega)) (hP 2 (by norm_num))) ?_
  refine runs_seq_assign_le (v := rootJ G.n) (Expr.eval_add (Expr.eval_add
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := E.PAR)
      (by simp [startState, EA.args])) (Expr.eval_const (by omega)) (by omega)) (hP 3 (by norm_num)))
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := E.PAR) (by simp [startState, EA.args]))
      (by exact hP 0 (by norm_num))) (by show pσ G.n + pa G.n < 2 ^ w; unfold rootJ at hJw; omega))
    (Expr.eval_const (by omega)) (by unfold rootJ at hJw; omega)) ?_
  refine runs_seq_assign_le (v := 2 * G.n * Mw + 1) (Expr.eval_add (Expr.eval_mul (Expr.eval_mul
    (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := G.n) (by simp [startState, EA.args, hn]))
      (by omega))
    (Expr.eval_reg_of_eq (v := Mw) (by simp [])) (by
      have e : 2 * G.n * Mw = 2 * (G.n * Mw) := by ring
      omega))
    (Expr.eval_const (by omega)) (by
      have e : 2 * G.n * Mw = 2 * (G.n * Mw) := by ring
      omega)) ?_
  -- the two blocks
  refine runs_stR (b := 28) (c := E.H) rootRegs 0 _ _ _
    (by simp [startState, EA.args])
    (by simp [rootRegs]; omega) ?_
  intro mem2 hst hfr
  simp only [rootRegs, List.length_cons, List.length_nil] at hst hfr
  have hfr' : ∀ a < E.H, mem2 a = mem a := fun a ha => hfr a (Or.inl (by omega))
  have hz : ZeroFrom mem2 (E.H + 30) := fun a ha => by
    rw [hfr a (Or.inr (by omega))]; exact hE.zero a (by omega)
  have hval : ∀ j (hj : j < 26), mem2 (E.H + j) = ([G.n, G.m, T.N, E.IN, E.PW, E.EXP, E.LAB,
      E.LOC, E.KPAR, E.KCH1, E.KCH2, E.KMW, E.KSZ, E.KLO, E.HEAD, E.ORDL, E.GOFF, E.GORD,
      pB G.n, rootJ G.n, 2 * G.n * Mw + 1, E.s, E.nS, E.SA, E.lθ, E.NODES] : List ℕ)[j] := by
    intro j hj
    have := hst j hj
    simp only [Nat.add_zero] at this
    rw [this]
    interval_cases j <;> simp [startState, EA.args, hn, hm, hN]
  have hgl : GlobL.read mem2 E.H = rootGlob E G T Mw := by
    simp only [GlobL.read, rootGlob, GlobL.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hval 0 (by norm_num)
    all_goals exact hval _ (by norm_num)
  have hrl : RecL.read mem2 (E.H + 21) = rootRecL E := by
    simp only [RecL.read, rootRecL, RecL.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hval 21 (by norm_num)
    · exact hval 22 (by norm_num)
    · exact hval 23 (by norm_num)
    · exact hval 24 (by norm_num)
    · exact hval 25 (by norm_num)
    all_goals exact (hfr _ (Or.inr (by omega))).trans (hE.zero _ (by omega))
  have hpre := rootPre (A := A) hE hw hMw hMw' hgl hrl hfr' hz
  -- the call of the cluster procedure
  refine runs_seq_call_spec (vs := [E.H, E.H + 21, E.OUT, E.H + 30])
    (K := recCost w A T (pgOf G) (par G.n G.m) (rootCl T G) (rootRec T G))
    (Post := RecPost w A T (pgOf G) (par G.n G.m) (rootCl T G) (rootRec T G)
      (GlobL.read mem2 E.H) E.OUT (E.H + 30) mem2)
    (fun pos ω => hRec T _ _ _ _ _ _ _ _ mem2 pos ω (pL_pos _) (fun _ => le_rfl)
      (by simp [pgOf]) hpre) ?_ ?_ ?_
  · have h21 : 21 < 2 ^ w := by omega
    have h30 : 30 < 2 ^ w := by omega
    have hH21 : E.H + 21 < 2 ^ w := by omega
    have hH30 : E.H + 30 < 2 ^ w := by omega
    simp [evalArgs, Expr.eval, startState, EA.args, h21, h30, hH21, hH30]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega
  intro v mem3 pos3 hpost
  refine runs_ret_le (Expr.eval_reg_of_eq (v := v) (by simp)) (fun E' hE' => ?_) ?_
  · rw [EA.eq_of_args hE']
    exact hpost.1
  · simp only [Expr.size, argsSize, clC, clCost, List.length_cons, List.length_nil, mxC,
      List.getD_cons_zero,
      rootRegs]
    omega

/-- **[AN19] Theorem 1** from a cluster procedure that meets `MeetsRec`. The program has the
entry at `0`, the preprocessing at `1` to `26`, the root procedure at `bRoot` and `mxP` at
`bMx`. -/
theorem lowStretchSpanningTree_of_rec
    (h : ∃ (p : Program) (A bRoot bRec bMx : ℕ), p.HasAt 0 (entryB bRoot :: preProcs 1) ∧
      p.HasAt bRoot [rootP bRec bMx] ∧ p.HasAt bMx [mxP] ∧ ∀ w, MeetsRec w A p bRec) :
    LowStretchSpanningTree := by
  obtain ⟨p, A, bRoot, bRec, bMx, hp, hR, hM, hRec⟩ := h
  exact lowStretchSpanningTree_of_cl
    ⟨p, A, bRoot, hp, fun w _ _ => rootP_meets hR hM (hRec w)⟩

end MinCostFlow.LowStretch
