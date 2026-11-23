module

public import MinCostFlow.LowStretch.ProgRecKid
public import MinCostFlow.LowStretch.ProgRecCost
public import MinCostFlow.LowStretch.ProgRecRoot

/-!
# The loop over the children

After the body, the cluster procedure calls itself on the children `0, 1, …, nch - 1` in order
(`kidBody`, in a `forRange` over register `10`). Child `k` gets the record block at
`CB + 9k`, the part of the output that starts after the trees of the earlier children, and the
heap from the end `HE` of the heap used so far. After the call, the length of its tree is added
to the offset in register `9`, and the new end of the heap is read at `HE + 2`.

`LoopInv` is what holds before the call on child `i`: the trees of the earlier children are at
`OUT`, the memory below `h` differs from the memory after the body only at the cells of
`ChildWr` of the earlier children and at the output, the heap of the body is kept, the labels
stay below `N`, the memory is zero from `HE` on, and `HE` grew by at most `(J + 2) recCost` per
child. `kid_step` shows that one turn of the loop keeps it, when the procedure meets its contract
on smaller clusters. The precondition of the call is `kidPre`.

Some tools come first: `runs_seq_call_runs`, a call whose callee is described by one run (its
cost is then known only after the run), `rangeCost_zero_sum`, and `recCost_ge`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {T : KT} {G : PG} {P : Par}

/-! ### Tools -/

/-- **A call described by one run of the callee**, whose cost `c` the rest may use. -/
theorem runs_seq_call_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {s : Stmt} {st : State} {vs : List ℕ} {k K : ℕ} {Q : Outcome → State → Prop}
    {Post : ℕ → ℕ → (ℕ → ℕ) → Prop}
    (hf : ∃ body, p.procs[f]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState vs st.mem st.pos) o st' c ∧ Post c o.value st'.mem)
    (hargs : evalArgs w st args = some vs)
    (hrest : ∀ c v mem' pos', Post c v mem' →
      ∃ o st' c₂, Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' }
        o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c + 2) + c₂ ≤ K) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ K := by
  obtain ⟨body, hb, o₁, st₁, c₁, hr₁, hp⟩ := hf
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest c₁ o₁.value st₁.mem st₁.pos hp
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
      runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, hr₁, rfl, rfl, rfl⟩, hr₂, rfl⟩),
    hq, by omega⟩

theorem rangeCost_zero_sum (f : ℕ → ℕ) (n : ℕ) :
    rangeCost f 0 n = ∑ i ∈ Finset.range n, f i := by
  rw [rangeCost_zero_eq_range]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem flatMap_range_update (Ts : ℕ → List ℕ) (i : ℕ) (Tr : List ℕ) :
    (List.range (i + 1)).flatMap (Function.update Ts i Tr) = (List.range i).flatMap Ts ++ Tr := by
  rw [List.range_succ, List.flatMap_append]
  congr 1
  · exact List.flatMap_congr fun j hj => by
      rw [Function.update_of_ne (by have := List.mem_range.mp hj; omega)]
  · simp

theorem kidCost_ge (w n : ℕ) : 10000 ≤ kidCost w n := by unfold kidCost; omega

/-- The cost of a cluster is at least `20000`, from its term `2 kidCost (2|X| - 1)`. -/
theorem recCost_ge {w A : ℕ} {c : Cl} {R : Rec} (hc : 1 ≤ c.X.card) :
    20000 ≤ recCost w A T G P c R := by
  unfold recCost
  have := kidCost_ge w G.n
  have : 2 * kidCost w G.n * 1 ≤ 2 * kidCost w G.n * (2 * c.X.card - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The global block is kept** while the loop runs. -/
theorem kid_keep {w A : ℕ} {c : Cl} {R : Rec} {D : Cl.Dec} {cs : ℕ → Cl} {Rs : ℕ → Rec}
    {GB RB OUT h : ℕ} {mem Mb Mk : ℕ → ℕ} {k : ℕ}
    (hpre : RecPre w A T G P c R GB RB OUT h mem)
    (hfrb : ∀ a < h, ¬ ChildWr T G c (GlobL.read mem GB) a → Mb a = mem a)
    (hkids : BodyKids T G P c D cs Rs (GlobL.read mem GB) h Mb) (hk : k ≤ D.nch)
    (hfr : ∀ a < h, (∀ j < k, ¬ ChildWr T G (cs j) (GlobL.read mem GB) a) →
      ¬ (OUT ≤ a ∧ a < OUT + c.X.card) → Mk a = Mb a) :
    GlobL.read Mk GB = GlobL.read mem GB := by
  have hpar := hpre.toClPre
  have hT := hpar.glob.tree
  have hr : (GB, 21) ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB) := by simp [recRegs]
  refine GlobL.read_congr (fun i hi => ?_)
  have hb := hpar.below _ hr
  have hnc := not_childWr (r := (GB, 21)) (a := GB + i) hT hpar.ok.sub hpar.ok.inv.one_le
    (hpar.lab_disj _ hr) (hpar.loc_disj _ hr) (by simp) (by simp only; omega)
  have ho := hpre.out_disj _ hr
  unfold RegDisj at ho
  simp only at ho hb
  rw [hfr _ (by omega) (fun j hj hw => hnc (childWr_mono hT
    (kid_facts (P := P) hT hkids (show j < D.nch by omega)).1 hpar.ok.sub
    (kid_facts (P := P) hT hkids (show j < D.nch by omega)).2.1
    (kid_facts (P := P) hT hkids (show j < D.nch by omega)).2.2.1 hw)) (by omega)]
  exact hfrb _ (by omega) hnc

/-! ### The loop -/

/-- One turn of the loop: the call on child `r₁₀`, then the offset and the end of the heap. -/
def kidBody (bRec : ℕ) : Stmt :=
  .seq (.call 11 bRec [.reg 0, .bin .add (.reg 6) (.bin .mul (.const 9) (.reg 10)),
      .bin .add (.reg 2) (.reg 9), .reg 7])
  (.seq (.assign 9 (.bin .add (.reg 9) (.reg 11)))
  (.assign 7 (.load (.bin .add (.reg 7) (.const 2)))))

/-- **What holds before the call on child `i`**, with the memory `Mb` after the body and the
global block `E`. Register `9` is the offset of the output and register `7` the end `HE` of the
heap. -/
structure LoopInv (w A : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (D : Cl.Dec) (cs : ℕ → Cl)
    (Rs : ℕ → Rec) (E : GlobL) (GB OUT h : ℕ) (Mb : ℕ → ℕ) (i : ℕ) (st : State) : Prop where
  r0 : st.regs 0 = GB
  r2 : st.regs 2 = OUT
  r3 : st.regs 3 = h
  r5 : st.regs 5 = D.nch
  r6 : st.regs 6 = Mb (h + 1)
  r8 : st.regs 8 = Mb (h + 3)
  r10 : st.regs 10 = i
  le : i ≤ D.nch
  trees : ∃ Ts : ℕ → List ℕ, (∀ j < i, Run G P (cs j) (Ts j)) ∧
    st.regs 9 = ((List.range i).flatMap Ts).length ∧
    st.regs 9 + i = ∑ j ∈ Finset.range i, (cs j).X.card ∧
    ListAt st.mem OUT ((List.range i).flatMap Ts)
  fr : ∀ a < h, (∀ j < i, ¬ ChildWr T G (cs j) E a) → ¬ (OUT ≤ a ∧ a < OUT + c.X.card) →
    st.mem a = Mb a
  heap : ∀ a, h ≤ a → a < Mb (h + 2) → st.mem a = Mb a
  lab : ∀ u < G.n, st.mem (E.LAB + u) < T.N
  loc : ∀ x < T.N, st.mem (E.LOC + x) < 2 ^ w
  zero : ZeroFrom st.mem (st.regs 7)
  he1 : Mb (h + 2) ≤ st.regs 7
  he2 : st.regs 7 ≤ Mb (h + 2) + (E.J + 2) * ∑ j ∈ Finset.range i, recCost w A T G P (cs j) (Rs j)

/-- **One turn of the loop keeps `LoopInv`**, when the procedure at `bRec` meets its contract
on the clusters smaller than `c` (`hIH`). -/
theorem kid_step {w A : ℕ} {p : Program} {bRec : ℕ} {c : Cl} {R : Rec} {D : Cl.Dec}
    {cs : ℕ → Cl} {Rs : ℕ → Rec} {GB RB OUT h : ℕ} {mem Mb : ℕ → ℕ} {i : ℕ}
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
    (hlt : ∀ j < D.nch, (cs j).X.card < c.X.card) (hi : i < D.nch) :
    Triple w p (LoopInv w A T G P c D cs Rs (GlobL.read mem GB) GB OUT h Mb i) (kidBody bRec)
      (normalPost fun st₁ =>
        LoopInv w A T G P c D cs Rs (GlobL.read mem GB) GB OUT h Mb (i + 1)
          { st₁ with regs := Function.update st₁.regs 10 (i + 1) } ∧ st₁.regs 10 = i)
      (fun _ => recCost w A T G P (cs i) (Rs i) + 30) := by
  intro st ω hI
  have hpar := hpre.toClPre
  have hT := hpar.glob.tree
  obtain ⟨Ts, hTs, h9, h9s, hlist⟩ := hI.trees
  obtain ⟨hnk, hsatk, hokk, -, hb1, hb2, -⟩ := hkids.2.1 i hi
  have hfi := kid_facts (P := P) hT hkids hi
  -- the sums
  have hpart : ∑ j ∈ Finset.range (i + 1), (cs j).X.card ≤ c.X.card :=
    hcard ▸ Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  rw [Finset.sum_range_succ] at hpart
  have hpartR : ∑ j ∈ Finset.range (i + 1), recCost w A T G P (cs j) (Rs j) ≤
      ∑ j ∈ Finset.range D.nch, recCost w A T G P (cs j) (Rs j) :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  rw [Finset.sum_range_succ] at hpartR
  have hJmul := Nat.mul_le_mul_left ((GlobL.read mem GB).J + 2) hpartR
  rw [Nat.mul_add] at hJmul
  have hhe2 := hI.he2
  have hroomk : st.regs 7 + ((GlobL.read mem GB).J + 2) * recCost w A T G P (cs i) (Rs i) ≤
      h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R := by omega
  have hout := hpre.out_le
  have hKP := kidPre (k := i) (Mk := st.mem) (HEk := st.regs 7) (OUTk := OUT + st.regs 9)
    hpre hfrb hkids hi hI.fr hI.heap hI.lab hI.loc hI.zero hI.he1 hroomk (by omega) (by omega)
  have hEk := kid_keep hpre hfrb hkids hi.le hI.fr
  have hXi : 1 ≤ (cs i).X.card := Finset.card_pos.mpr ⟨_, hokk.inv.good.conn.1⟩
  have hrc := recCost_ge (w := w) (A := A) (T := T) (G := G) (P := P) (R := Rs i) hXi
  have hrcJ : recCost w A T G P (cs i) (Rs i) ≤
      ((GlobL.read mem GB).J + 2) * recCost w A T G P (cs i) (Rs i) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hGB : GB + 21 ≤ h := hpar.below (GB, 21) (by simp [recRegs])
  have hhe1 := hI.he1
  have hw7 : st.regs 7 + 2 < 2 ^ w := by omega
  have hw6 : Mb (h + 1) + 9 * i < 2 ^ w := by omega
  have hw9 : 9 * i < 2 ^ w := by omega
  have hw2 : OUT + st.regs 9 < 2 ^ w := by omega
  have hargs : evalArgs w st [.reg 0, .bin .add (.reg 6) (.bin .mul (.const 9) (.reg 10)),
      .bin .add (.reg 2) (.reg 9), .reg 7] =
      some [GB, Mb (h + 1) + 9 * i, OUT + st.regs 9, st.regs 7] := by
    have h9w : (9 : ℕ) < 2 ^ w := by omega
    simp [evalArgs, Expr.eval, hI.r0, hI.r6, hI.r10, hI.r2, BinOp.eval, h9w, hw9, hw6, hw2]
  unfold kidBody
  refine runs_start_le ?_
  refine runs_seq_call_runs (Post := fun cst v M' =>
      RecPost w A T G P (cs i) (Rs i) (GlobL.read st.mem GB) (OUT + st.regs 9) (st.regs 7) st.mem
        v M' ∧ cst ≤ recCost w A T G P (cs i) (Rs i)) ?_ hargs ?_
  · obtain ⟨body, hb, o, st', cst, hr, hpost, hc⟩ :=
      hIH (cs i) (Rs i) _ _ _ st.mem st.pos ω (hlt i hi) hKP
    exact ⟨body, hb, o, st', cst, hr, hpost, hc⟩
  intro cst v mem' pos' ⟨hpost, hc⟩
  rw [hEk] at hpost
  obtain ⟨⟨Tr, hrun, hv, hlist'⟩, hfr', hlab', hloc', hhe1', hz', hhe2'⟩ := hpost
  have htr := (Run.tree hpar.ok.hGo hpar.ok.hB hrun hokk.inv).2.2
  have hw9v : st.regs 9 + v < 2 ^ w := by omega
  refine runs_seq_assign_le (v := st.regs 9 + v)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp []))
      (Expr.eval_reg_of_eq (by simp)) hw9v) ?_
  refine runs_assign_le (v := mem' (st.regs 7 + 2))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp []))
      (Expr.eval_const (by omega)) hw7) rfl) ?_ ?_
  · -- the invariant for `i + 1`
    have hlabN : (GlobL.read mem GB).LAB + G.n ≤ h := hpar.lab_below
    have hlocN : (GlobL.read mem GB).LOC + T.N ≤ h := hpar.loc_below
    -- a cell of `ChildWr` of child `i` lies below `h` and outside the output
    have hcw : ∀ a, ChildWr T G (cs i) (GlobL.read mem GB) a → a < h ∧
        ¬ (OUT ≤ a ∧ a < OUT + c.X.card) := fun a hw => by
      have hol := hpre.out_lab
      have hoc := hpre.out_loc
      unfold RegDisj at hol hoc
      simp only at hol hoc
      rcases ChildWr.cell hT hfi.2.2.2.2 hfi.2.2.1 hw with ⟨u, hu, rfl⟩ | ⟨x, hx, rfl⟩
      · omega
      · omega
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hI.r0]
    · simp [hI.r2]
    · simp [hI.r3]
    · simp [hI.r5]
    · simp [hI.r6]
    · simp [hI.r8]
    · simp
    · show i + 1 ≤ D.nch; omega
    · refine ⟨Function.update Ts i Tr, fun j hj => ?_, ?_, ?_, ?_⟩
      · by_cases hji : j = i
        · subst hji; simpa using hrun
        · rw [Function.update_of_ne hji]; exact hTs j (by omega)
      · simp [flatMap_range_update, h9, hv]
      · simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
        rw [Finset.sum_range_succ]; omega
      · show ListAt mem' OUT _
        rw [flatMap_range_update]
        refine listAt_append.mpr ⟨fun j hj => ?_, ?_⟩
        · have hj' : j < st.regs 9 := by rw [h9]; exact hj
          rw [← hlist j hj]
          exact hfr' _ (by omega) (fun hw => (hcw _ hw).2 (by omega)) (by omega)
        · rw [← h9]; exact hlist'
    · show ∀ a < h, _ → _ → mem' a = Mb a
      intro a ha hnw hno
      rw [hfr' a (by omega) (hnw i (by omega)) (by omega)]
      exact hI.fr a ha (fun j hj => hnw j (by omega)) hno
    · show ∀ a, h ≤ a → a < Mb (h + 2) → mem' a = Mb a
      intro a ha1 ha2
      rw [hfr' a (by omega) (fun hw => by have := (hcw a hw).1; omega) (by omega)]
      exact hI.heap a ha1 ha2
    · exact hlab'
    · exact hloc'
    · simpa [Function.update_apply] using hz'
    · simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]; omega
    · simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
      rw [Finset.sum_range_succ, Nat.mul_add]; omega
    · simpa [Function.update_apply] using hI.r10
  · simp only [Expr.size, argsSize]
    omega

end MinCostFlow.LowStretch
