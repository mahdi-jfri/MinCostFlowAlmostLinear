module

public import MinCostFlow.LowStretch.ProgRecLoop

/-!
# The cluster procedure

`recP bBody bRec bCopy`, called with `[GB, RB, OUT, h]`, runs the body (at `bBody`) with
`[GB, RB, h]`. If the body finds no children (a single vertex), it returns `0`: the tree is empty.
Otherwise it reads the number of children, the address of their record blocks, the end of the
heap of the body and the address of the portals at `h, …, h + 3`, runs the loop over the
children (`kidBody`, `ProgRecLoop.lean`), copies the `nch - 1` portals after the trees of the
children with `copyWords` (at `bCopy`), writes the end of the heap at `h + 2` and returns the
length of the tree.

`recP_meets` shows that `recP` meets `MeetsRec` when the body meets `MeetsBody` and
`A ≥ recK + 1`. The proof is by strong induction on `|X|`: the children are smaller
(`card_raw_lt`). One level is `recP_one`; its cost is `rec_node_cost` (or `rec_leaf_cost`),
where `recK` pays for the steps of `recP` itself, per child and once.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

variable {T : KT} {G : PG} {P : Par}

/-- **The cluster procedure.** -/
def recP (bBody bRec bCopy : ℕ) : Stmt :=
  .seq (.call 4 bBody [.reg 0, .reg 1, .reg 3])
  (.seq (.assign 5 (.load (.reg 3)))
  (.cond (.reg 5)
    (.seq (.assign 6 (.load (.bin .add (.reg 3) (.const 1))))
    (.seq (.assign 7 (.load (.bin .add (.reg 3) (.const 2))))
    (.seq (.assign 8 (.load (.bin .add (.reg 3) (.const 3))))
    (.seq (.assign 9 (.const 0))
    (.seq (forRange 10 (.const 0) (.reg 5) (kidBody bRec))
    (.seq (.call 12 bCopy [.reg 8, .bin .add (.reg 2) (.reg 9), .bin .sub (.reg 5) (.const 1)])
    (.seq (.store (.bin .add (.reg 3) (.const 2)) (.reg 7))
    (.ret (.bin .add (.reg 9) (.bin .sub (.reg 5) (.const 1)))))))))))
    (.ret (.const 0))))

theorem recP_noRand (bBody bRec bCopy : ℕ) : (recP bBody bRec bCopy).NoRand := by
  simp [recP, kidBody, forRange, forUp, Stmt.NoRand]

/-- The cost of the steps of `recP` itself, per child and once. -/
def recK : ℕ := 200

theorem heap_le {J X Z : ℕ} (h : X + 4 ≤ Z) : (J + 1) * X + 4 ≤ (J + 2) * Z := by nlinarith

theorem heap_le2 {J X Y Z : ℕ} (h : X + Y + 4 ≤ Z) :
    (J + 1) * X + 4 + (J + 2) * Y ≤ (J + 2) * Z := by nlinarith

/-- **The loop over the children**, from `LoopInv 0` to `LoopInv nch`. -/
theorem kids_loop {w A : ℕ} {p : Program} {bRec : ℕ} {c : Cl} {R : Rec} {D : Cl.Dec}
    {cs : ℕ → Cl} {Rs : ℕ → Rec} {GB RB OUT h : ℕ} {mem Mb : ℕ → ℕ}
    (hpre : RecPre w A T G P c R GB RB OUT h mem)
    (hfrb : ∀ a < h, ¬ ChildWr T G c (GlobL.read mem GB) a → Mb a = mem a)
    (hkids : BodyKids T G P c D cs Rs (GlobL.read mem GB) h Mb)
    (hcard : ∑ j ∈ Finset.range D.nch, (cs j).X.card = c.X.card)
    (hroom : Mb (h + 2) + ((GlobL.read mem GB).J + 2) *
      ∑ j ∈ Finset.range D.nch, recCost w A T G P (cs j) (Rs j) ≤
      h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R)
    (hword : h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R < 2 ^ w)
    (hIH : ∀ (c' : Cl) (R' : Rec) (RB' OUT' h' : ℕ) (M : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      c'.X.card < c.X.card → RecPre w A T G P c' R' GB RB' OUT' h' M →
      ∃ body, p.procs[bRec]? = some body ∧ ∃ o st' cost,
        Runs w p ω body (startState [GB, RB', OUT', h'] M pos) o st' cost ∧
        RecPost w A T G P c' R' (GlobL.read M GB) OUT' h' M o.value st'.mem ∧
        cost ≤ recCost w A T G P c' R')
    (hlt : ∀ j < D.nch, (cs j).X.card < c.X.card) (hw1 : 1 < 2 ^ w) (hnw : D.nch < 2 ^ w) :
    Triple w p (fun st => LoopInv w A T G P c D cs Rs (GlobL.read mem GB) GB OUT h Mb 0
        { st with regs := Function.update st.regs 10 0 })
      (forRange 10 (.const 0) (.reg 5) (kidBody bRec))
      (normalPost (LoopInv w A T G P c D cs Rs (GlobL.read mem GB) GB OUT h Mb D.nch))
      (fun _ => ∑ i ∈ Finset.range D.nch, recCost w A T G P (cs i) (Rs i) + 39 * D.nch + 7) := by
  refine (Triple.forRange_le (fun i => recCost w A T G P (cs i) (Rs i) + 30) 0 D.nch
    (Nat.zero_le _) hw1 (fun _ => hnw)
    (fun st hst => ⟨Expr.eval_const (by omega), hst⟩)
    (fun i st _ _ hI => hI.r10) (fun i st _ _ hI => Expr.eval_reg_of_eq hI.r5)
    (fun i _ hi => kid_step hpre hfrb hkids hcard hroom hword hIH hlt hi)).mono_cost ?_
  intro _ _
  rw [rangeCost_zero_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Expr.size]
  omega

/-- **One level of the cluster procedure**, when it meets its contract on smaller clusters. -/
theorem recP_one {w A : ℕ} {p : Program} {bBody bRec bCopy : ℕ}
    (hp : p.procs[bRec]? = some (recP bBody bRec bCopy)) (hBody : MeetsBody w A p bBody)
    (hCopy : p.HasAt bCopy [copyWords]) (hA : recK + 1 ≤ A)
    {c : Cl} {R : Rec} {GB RB OUT h : ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hL : 1 ≤ P.L) (hcw : ∀ q, 1 ≤ P.cw q) (hPp : P = par G.n G.m)
    (hIH : ∀ (c' : Cl) (R' : Rec) (RB' OUT' h' : ℕ) (M : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      c'.X.card < c.X.card → RecPre w A T G P c' R' GB RB' OUT' h' M →
      ∃ body, p.procs[bRec]? = some body ∧ ∃ o st' cost,
        Runs w p ω body (startState [GB, RB', OUT', h'] M pos) o st' cost ∧
        RecPost w A T G P c' R' (GlobL.read M GB) OUT' h' M o.value st'.mem ∧
        cost ≤ recCost w A T G P c' R')
    (hpre : RecPre w A T G P c R GB RB OUT h mem) :
    ∃ body, p.procs[bRec]? = some body ∧ ∃ o st' cost,
      Runs w p ω body (startState [GB, RB, OUT, h] mem pos) o st' cost ∧
      RecPost w A T G P c R (GlobL.read mem GB) OUT h mem o.value st'.mem ∧
      cost ≤ recCost w A T G P c R := by
  have hpar := hpre.toClPre
  have hT := hpar.glob.tree
  have hc := hpar.ok.inv
  obtain ⟨Mw, -, -, hroomw⟩ := hpar.room
  have hword : h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R < 2 ^ w := by omega
  have hX1 : 1 ≤ c.X.card := Finset.card_pos.mpr ⟨_, hc.good.conn.1⟩
  have hrc := recCost_ge (w := w) (A := A) (T := T) (G := G) (P := P) (R := R) hX1
  have hrcJ : recCost w A T G P c R ≤ ((GlobL.read mem GB).J + 2) * recCost w A T G P c R :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hw1 : 1 < 2 ^ w := by omega
  have hout := hpre.out_le
  refine ⟨_, hp, ?_⟩
  refine runs_start_le ?_
  unfold recP
  refine runs_seq_call_runs (vs := [GB, RB, h])
    (Post := fun cst _ M' => BodyPost w A T G P c R (GlobL.read mem GB) h mem M' cst)
    (hBody T G P c R GB RB h mem pos ω hpar hcw hPp) (by simp [evalArgs, Expr.eval, startState]) ?_
  intro cst v Mb pos1 hbody
  obtain ⟨hfrb, hlabb, hlocb, hhb, hzb, hcase⟩ := hbody
  refine runs_seq_assign_le (v := Mb h)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState]))
      rfl) ?_
  refine runs_cond_le (v := Mb h) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  swap
  · -- a single vertex
    intro h0
    rcases hcase with ⟨hX, -, hheapb, hcostb⟩ | ⟨D, cs, Rs, hX, hD, hkids, -⟩
    · obtain ⟨hlc, -⟩ := rec_leaf_cost (w := w) (T := T) (K0 := recK) (Nat.le_of_succ_le hA) hL
        hpar.ok.hGo (R := R) hc
      unfold recK at hlc
      refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ?_ ?_
      · refine ⟨⟨[], Run.leaf hX, rfl, fun i hi => by simp at hi⟩,
          fun a ha hnc _ => hfrb a ha hnc, hlabb, hlocb, hhb, hzb, ?_⟩
        have := heap_le (J := (GlobL.read mem GB).J)
          (show A * P.L * (R.S.length + 1) + 4 ≤ recCost w A T G P c R by omega)
        dsimp only
        omega
      · simp only [Expr.size, argsSize]
        omega
    · exfalso
      have := Cl.len_pos hpar.ok.hB hc hX hD
      have h1 := hkids.1
      unfold Cl.Dec.nch at h1
      omega
  -- a cluster with children
  intro hne
  rcases hcase with ⟨-, h0, -⟩ | ⟨D, cs, Rs, hX, hD, hkids, hS, hheapb, hcostb⟩
  · exact absurd h0 hne
  have hGo := hpar.ok.hGo
  have hB := hpar.ok.hB
  have hlen := Cl.len_pos hB hc hX hD
  have hnch : D.nch = D.ps.length + 1 := rfl
  have hn := fun k (hk : k < D.nch) => (hkids.2.1 k hk).1
  have hlt : ∀ j < D.nch, (cs j).X.card < c.X.card := fun j hj => by
    rw [(hn j hj).X_eq]
    exact Cl.card_raw_lt hc.good.conn hD (hc.Δ_pos hB hX) hlen hj
  have hcard : ∑ k ∈ Finset.range D.nch, (cs k).X.card = c.X.card := by
    rw [← Cl.sum_card_raw (G := G) (c := c) (D := D)]
    exact Finset.sum_congr rfl fun k hk => by rw [(hn k (Finset.mem_range.mp hk)).X_eq]
  have hnode := rec_node_cost (w := w) (K0 := recK) (by omega) hpar.ok hcw hL hX hD hn
    (fun k hk => (hkids.2.1 k hk).2.1) hS
  unfold recK at hnode
  have hroom : Mb (h + 2) + ((GlobL.read mem GB).J + 2) *
      ∑ j ∈ Finset.range D.nch, recCost w A T G P (cs j) (Rs j) ≤
      h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R := by
    have := heap_le2 (J := (GlobL.read mem GB).J)
      (show bodyShare A T G P c R D cs + D.nch * kidCost w G.n +
        ∑ j ∈ Finset.range D.nch, recCost w A T G P (cs j) (Rs j) + 4 ≤
        recCost w A T G P c R by omega)
    omega
  have hkid0 := hkids.2.2
  obtain ⟨hPT1, hPT2, hPT3⟩ := hkid0
  have hCB := (hkids.2.1 0 (by omega)).2.2.2.2.2.1
  have hMb2 : Mb (h + 2) ≤ h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R := by
    have := Nat.zero_le (((GlobL.read mem GB).J + 2) *
      ∑ j ∈ Finset.range D.nch, recCost w A T G P (cs j) (Rs j))
    omega
  have hh3 : h + 3 < 2 ^ w := by omega
  refine runs_seq_assign_le (v := Mb (h + 1))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
      (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) rfl) ?_
  refine runs_seq_assign_le (v := Mb (h + 2))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
      (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) rfl) ?_
  refine runs_seq_assign_le (v := Mb (h + 3))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
      (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) rfl) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hnw : D.nch < 2 ^ w := by
    have hge : ∑ k ∈ Finset.range D.nch, 1 ≤ ∑ k ∈ Finset.range D.nch, (cs k).X.card :=
      Finset.sum_le_sum fun k hk => Finset.card_pos.mpr
        ⟨_, ((hkids.2.1 k (Finset.mem_range.mp hk)).2.2.1).inv.good.conn.1⟩
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hge
    omega
  refine runs_seq_triple_le (kids_loop hpre hfrb hkids hcard hroom hword hIH hlt hw1 hnw) ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _, ⟨fun _ => [], fun j hj => by omega,
      ?_, ?_, fun i hi => by simp at hi⟩, fun _ _ _ _ => rfl, fun _ _ _ => rfl, hlabb, hlocb, ?_,
      ?_, ?_⟩ <;> simp [startState, hkids.1, hzb]
  intro st2 hI
  obtain ⟨Ts, hTs, h9, h9s, hlist⟩ := hI.trees
  rw [hcard] at h9s
  have hhe1 := hI.he1
  have hhe2 := hI.he2
  -- the portals
  have hcpre : (copyWordsContract w).pre [Mb (h + 3), OUT + st2.regs 9, D.nch - 1] st2.mem :=
    ⟨_, _, _, rfl, hw1, by omega, by omega, Or.inl (by omega)⟩
  refine runs_seq_call_le (copyWords_meetsContract hCopy) (vs := [Mb (h + 3), OUT + st2.regs 9,
      D.nch - 1]) (by simp [evalArgs, Expr.eval, hI.r8, hI.r2, hI.r5, BinOp.eval, hw1,
        show OUT + st2.regs 9 < 2 ^ w by omega,
        show D.nch - 1 < 2 ^ w by omega]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      omega) hcpre ?_
  intro u mem3 pos3 hcp
  obtain ⟨s', d', l', hargs', -, hcopy, hcfr⟩ := hcp
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl, rfl⟩ := hargs'
  refine runs_seq_store_le (x := h + 2) (v := st2.regs 7)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hI.r3])) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
  have hcount : st2.regs 9 + (D.nch - 1) < 2 ^ w := by omega
  refine runs_ret_le (v := st2.regs 9 + (D.nch - 1))
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp []))
      (Expr.eval_sub (Expr.eval_reg_of_eq (by simp [hI.r5]))
        (Expr.eval_const (by omega)) hnw) hcount) ?_ ?_
  · have hlabN : (GlobL.read mem GB).LAB + G.n ≤ h := hpar.lab_below
    have hol := hpre.out_lab
    unfold RegDisj at hol
    simp only at hol
    have hlocN : (GlobL.read mem GB).LOC + T.N ≤ h := hpar.loc_below
    have hoc := hpre.out_loc
    unfold RegDisj at hoc
    simp only at hoc
    refine ⟨⟨(List.range D.nch).flatMap Ts ++ D.portals, Run.node D cs Ts hX hD hn hTs, ?_, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Cl.Dec.portals, h9, hnch, Outcome.value]
    · refine listAt_append.mpr ⟨fun j hj => ?_, fun j hj => ?_⟩
      · show Function.update mem3 (h + 2) (st2.regs 7) (OUT + j) = _
        rw [Function.update_of_ne (by omega), hcfr _ (Or.inl (by omega))]
        exact hlist j hj
      · show Function.update mem3 (h + 2) (st2.regs 7) _ = _
        simp only [Cl.Dec.portals, List.length_map, List.length_range] at hj
        rw [Function.update_of_ne (by omega), ← h9, hcopy j (by omega),
          hI.heap _ (by omega) (by omega), hPT3 j hj]
        simp [Cl.Dec.portals]
    · intro a ha hnc hno
      show Function.update mem3 (h + 2) (st2.regs 7) a = mem a
      rw [Function.update_of_ne (by omega), hcfr _ (by omega)]
      rw [hI.fr a ha (fun j hj hw => hnc (childWr_mono hT (kid_facts (P := P) hT hkids hj).1
        hpar.ok.sub (kid_facts (P := P) hT hkids hj).2.1 (kid_facts (P := P) hT hkids hj).2.2.1
        hw)) hno]
      exact hfrb a ha hnc
    · intro x hx
      show Function.update mem3 (h + 2) (st2.regs 7) _ < T.N
      rw [Function.update_of_ne (by omega), hcfr _ (by omega)]
      exact hI.lab x hx
    · intro x hx
      show Function.update mem3 (h + 2) (st2.regs 7) _ < 2 ^ w
      rw [Function.update_of_ne (by omega), hcfr _ (by omega)]
      exact hI.loc x hx
    · show h + 4 ≤ Function.update mem3 (h + 2) (st2.regs 7) (h + 2)
      simp only [Function.update_self]
      omega
    · intro a ha
      show Function.update mem3 (h + 2) (st2.regs 7) a = 0
      simp only [Function.update_self] at ha
      rw [Function.update_of_ne (by omega), hcfr _ (Or.inr (by omega))]
      exact hI.zero a ha
    · show Function.update mem3 (h + 2) (st2.regs 7) (h + 2) ≤ _
      simp only [Function.update_self]
      omega
  · simp only [Expr.size, argsSize, copyWordsContract]
    omega

/-- **The cluster procedure meets its contract**, by strong induction on the size of the
cluster. -/
theorem recP_meets {w A : ℕ} {p : Program} {bBody bRec bCopy : ℕ}
    (hp : p.HasAt bRec [recP bBody bRec bCopy]) (hBody : MeetsBody w A p bBody)
    (hCopy : p.HasAt bCopy [copyWords]) (hA : recK + 1 ≤ A) : MeetsRec w A p bRec := by
  have hproc : p.procs[bRec]? = some (recP bBody bRec bCopy) := hp 0 (by simp)
  intro T G P c R GB RB OUT h mem pos ω hL hcw hPp hpre
  induction hn : c.X.card using Nat.strong_induction_on generalizing c R RB OUT h mem pos ω with
  | _ n ih =>
    exact recP_one hproc hBody hCopy hA hL hcw hPp
      (fun c' R' RB' OUT' h' M pos' ω' hlt hpre' =>
        ih c'.X.card (hn ▸ hlt) c' R' RB' OUT' h' M pos' ω' hpre' rfl) hpre

/-- `copyWords` is procedure `26` when the preprocessing is at `1`. -/
theorem copy_at_26 {p : Program} {bRoot : ℕ} (hp : p.HasAt 0 (entryB bRoot :: preProcs 1)) :
    p.HasAt 26 [copyWords] := by
  have := hasAt_sub hp 26 (by simp [preProcs_length])
  exact this

/-- **[AN19] Theorem 1** from a body that meets `MeetsBody`. The program has the entry at `0`,
the preprocessing at `1` to `26` (with `copyWords` at `26`), the root procedure at `bRoot`,
`mxP` at `bMx`, the cluster procedure `recP bBody bRec 26` at `bRec`, and the body at `bBody`,
with `A ≥ recK + 1`. -/
theorem lowStretchSpanningTree_of_body
    (h : ∃ (p : Program) (A bRoot bRec bMx bBody : ℕ), p.HasAt 0 (entryB bRoot :: preProcs 1) ∧
      p.HasAt bRoot [rootP bRec bMx] ∧ p.HasAt bMx [mxP] ∧
      p.HasAt bRec [recP bBody bRec 26] ∧ recK + 1 ≤ A ∧ ∀ w, MeetsBody w A p bBody) :
    LowStretchSpanningTree := by
  obtain ⟨p, A, bRoot, bRec, bMx, bBody, hp, hR, hM, hRec, hA, hBody⟩ := h
  exact lowStretchSpanningTree_of_rec ⟨p, A, bRoot, bRec, bMx, hp, hR, hM,
    fun w => recP_meets hRec (hBody w) (copy_at_26 hp) hA⟩

end MinCostFlow.LowStretch
