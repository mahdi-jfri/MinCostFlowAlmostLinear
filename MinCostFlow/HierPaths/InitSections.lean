module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.HierPaths.InitLayout
public import MinCostFlow.HierPaths.InitBlockLen

/-!
# Writing the sections of a block one after the other

The builder of the block of `Init` writes a `layoutList` of sections at `a`: the offset table
of `k + 1` words, then the sections. `writeSecs` does the bookkeeping. It keeps the arguments
`r0, …, r5` of the builder (`a` is `r5`) and the current end in `r6`. For each section it
stores the offset `r6 − (a + 25)` at `a + i`, then calls the writer of the section with
`[r0, …, r5, r6]`, which writes the section at `r6` and returns its end. At the end it stores
the last offset and returns `r6`. Each writer meets `SecContract`. `writeSecs_runs` gives what
the sequence leaves in memory: the offsets, the sections at their starts, zero memory after,
and memory below `a` unchanged.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- A writer of one section: the procedure, the section as a function of the six arguments, and
its cost. -/
structure SecProc where
  f : ℕ
  l : List ℕ → List ℕ
  cost : List ℕ → ℕ
  scratch : List ℕ → ℕ := fun _ => 0

/-- The contract of a writer: with the six arguments `base` meeting `Inv` and zero memory from
`c` on, it writes `l base` at `c`, returns its end, keeps memory below `c` and leaves zero memory
after the end. -/
def SecContract (w : ℕ) (Inv : List ℕ → (ℕ → ℕ) → Prop) (s : SecProc) : Contract where
  pre args mem := ∃ base c, args = base ++ [c] ∧ base.length = 6 ∧ Inv base mem ∧
    ZeroFrom mem c ∧ base.getD 5 0 + 25 ≤ c ∧ c + (s.l base).length + s.scratch base < 2 ^ w
  post args mem v mem' := ∃ base c, args = base ++ [c] ∧ v = c + (s.l base).length ∧
    ListAt mem' c (s.l base) ∧ ZeroFrom mem' v ∧ ∀ y < c, mem' y = mem y
  cost args _ := s.cost (args.take 6)

/-- The sum of the scratch space required by the remaining writers. -/
def secScratch (base : List ℕ) (ss : List SecProc) : ℕ :=
  (ss.map fun s => s.scratch base).sum

/-- The offset `r6 − (r5 + 25)`. -/
def offExpr : Expr := .bin .sub (.reg 6) (.bin .add (.reg 5) (.const 25))

/-- The arguments `r0, …, r6` of a writer. -/
def secArgs : List Expr := [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6]

/-- Store the offset of section `i`, call its writer; at the end store the last offset and
return the end. -/
def writeSecs : List SecProc → ℕ → Stmt
  | [], i => .seq (.store (.bin .add (.reg 5) (.const i)) offExpr) (.ret (.reg 6))
  | s :: ss, i => .seq (.store (.bin .add (.reg 5) (.const i)) offExpr)
      (.seq (.call 6 s.f secArgs) (writeSecs ss (i + 1)))

/-- The six arguments in the registers. -/
def regs6 (st : State) : List ℕ :=
  [st.regs 0, st.regs 1, st.regs 2, st.regs 3, st.regs 4, st.regs 5]

/-- The total length of the first `j` sections. -/
def secLen (base : List ℕ) (ss : List SecProc) (j : ℕ) : ℕ :=
  ((ss.take j).map fun s => (s.l base).length).sum

theorem secLen_cons_succ (base : List ℕ) (s : SecProc) (ss : List SecProc) (j : ℕ) :
    secLen base (s :: ss) (j + 1) = (s.l base).length + secLen base ss j := by
  simp [secLen]

theorem secLen_zero (base : List ℕ) (ss : List SecProc) : secLen base ss 0 = 0 := by
  simp [secLen]

theorem eval_offExpr {w a : ℕ} {st : State} (h5 : st.regs 5 = a) (hc : a + 25 ≤ st.regs 6)
    (h6 : st.regs 6 < 2 ^ w) : offExpr.eval w st = some (st.regs 6 - (a + 25)) := by
  have h25 : (25 : ℕ) < 2 ^ w := by omega
  have ha25 : a + 25 < 2 ^ w := by omega
  have hs : st.regs 6 - (a + 25) < 2 ^ w := by omega
  simp [offExpr, Expr.eval, h5, BinOp.eval, h25, ha25, hs]

theorem eval_addrExpr {w a i : ℕ} {st : State} (h5 : st.regs 5 = a) (hai : a + i < 2 ^ w) :
    (Expr.bin .add (.reg 5) (.const i)).eval w st = some (a + i) := by
  have hi : i < 2 ^ w := by omega
  simp [Expr.eval, h5, BinOp.eval, hi, hai]

theorem evalArgs_secArgs (w : ℕ) (st : State) :
    evalArgs w st secArgs = some (regs6 st ++ [st.regs 6]) := by
  simp [secArgs, evalArgs, Expr.eval, regs6]

/-- **What `writeSecs` leaves.** Started at section `i` with the arguments `base` in
`r0, …, r5` (`a = r5`), the end `c₀` in `r6`, `Inv` and zero memory from `c₀` on, it returns
`c₀` plus the total length `L` of the sections. Word `a + i + j` holds the offset of section `j`,
section `j` is at `c₀` plus the length before it, memory from `c₀ + L` on is zero, and memory
below `c₀` outside the words `a + i, …, a + i + |ss|` is unchanged. The proof is by induction
on the list of writers: a writer keeps memory below its start, which holds the offsets and the
earlier sections. -/
theorem writeSecs_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {Inv : List ℕ → (ℕ → ℕ) → Prop}
    (hInv : ∀ base mem mem', Inv base mem → (∀ y < base.getD 5 0, mem' y = mem y) →
      Inv base mem')
    (base : List ℕ) (hbase : base.length = 6) (hbw : ∀ v ∈ base, v < 2 ^ w) :
    ∀ (ss : List SecProc) (i : ℕ) (st : State) (k T : ℕ),
      (∀ s ∈ ss, MeetsContract w p s.f (SecContract w Inv s)) →
      regs6 st = base → Inv base st.mem → ZeroFrom st.mem (st.regs 6) →
      base.getD 5 0 + 25 ≤ st.regs 6 → i + ss.length < 25 →
      st.regs 6 + secLen base ss ss.length + secScratch base ss < 2 ^ w →
      k + ((ss.map fun s => s.cost base + 40).sum + 20) ≤ T →
      ∃ o st' c, Runs w p ω (writeSecs ss i) st o st' c ∧
        (o = .returned (st.regs 6 + secLen base ss ss.length) ∧
          (∀ j ≤ ss.length, st'.mem (base.getD 5 0 + i + j) =
            st.regs 6 - (base.getD 5 0 + 25) + secLen base ss j) ∧
          (∀ j (hj : j < ss.length), ListAt st'.mem (st.regs 6 + secLen base ss j)
            (ss[j].l base)) ∧
          ZeroFrom st'.mem (st.regs 6 + secLen base ss ss.length) ∧
          (∀ y < st.regs 6, (y < base.getD 5 0 + i ∨ base.getD 5 0 + i + ss.length < y) →
            st'.mem y = st.mem y)) ∧
        k + c ≤ T := by
  intro ss
  induction ss with
  | nil =>
    intro i st k T _ hr hI hz hc hi hb hT
    have h5 : st.regs 5 = base.getD 5 0 := by rw [← hr]; rfl
    generalize base.getD 5 0 = a at *
    have h6 : st.regs 6 < 2 ^ w := by simp [secLen] at hb; omega
    have hai : a + i < 2 ^ w := by omega
    have hi' : i < 2 ^ w := by omega
    have h25 : a + 25 < 2 ^ w := by omega
    have h25' : (25 : ℕ) < 2 ^ w := by omega
    unfold writeSecs
    refine runs_seq_store_le (x := a + i)
      (v := st.regs 6 - (a + 25)) (eval_addrExpr h5 hai)
      (eval_offExpr h5 hc (by omega)) ?_
    refine runs_ret_le (v := st.regs 6) (by simp [Expr.eval]) ⟨by simp [secLen], ?_, ?_, ?_, ?_⟩ ?_
    · intro j hj
      have : j = 0 := by simpa using hj
      subst this
      simp [secLen]
    · intro j hj; simp at hj
    · intro y hy
      simp only [secLen, List.take_nil, List.map_nil, List.sum_nil, Nat.add_zero] at hy
      dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hz y hy
    · intro y _ hy
      simp only [List.length_nil, Nat.add_zero] at hy
      dsimp only
      rw [Function.update_of_ne (by omega)]
    · simp [offExpr, Expr.size] at hT ⊢
      omega
  | cons s ss ih =>
    intro i st k T hf hr hI hz hc hi hb hT
    have h5 : st.regs 5 = base.getD 5 0 := by rw [← hr]; rfl
    generalize ha : base.getD 5 0 = a at *
    have hlen : secLen base (s :: ss) (s :: ss).length =
        (s.l base).length + secLen base ss ss.length := by
      rw [List.length_cons, secLen_cons_succ]
    simp only [secScratch, List.map_cons, List.sum_cons] at hb
    have h6 : st.regs 6 + (s.l base).length + s.scratch base < 2 ^ w := by omega
    have hai : a + i < 2 ^ w := by omega
    have hi' : i < 2 ^ w := by omega
    have h25 : a + 25 < 2 ^ w := by omega
    have h25' : (25 : ℕ) < 2 ^ w := by omega
    unfold writeSecs
    refine runs_seq_store_le (x := a + i)
      (v := st.regs 6 - (a + 25)) (eval_addrExpr h5 hai)
      (eval_offExpr h5 hc (by omega)) ?_
    set c₀ := st.regs 6 with hc₀
    set mem₁ := Function.update st.mem (a + i) (c₀ - (a + 25)) with hmem₁
    have hargs : evalArgs w { st with mem := mem₁ } secArgs = some (base ++ [c₀]) := by
      rw [evalArgs_secArgs, ← hr]; rfl
    have hwords : ∀ v ∈ base ++ [c₀], v < 2 ^ w := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hbw v hv
      · simp at hv; omega
    have hI₁ : Inv base mem₁ := hInv base st.mem mem₁ hI fun y hy => by
      rw [ha] at hy
      rw [hmem₁, Function.update_of_ne (by omega)]
    have hz₁ : ZeroFrom mem₁ c₀ := fun y hy => by
      rw [hmem₁, Function.update_of_ne (by omega)]; exact hz y hy
    refine runs_seq_call_le (hf s (by simp)) hargs hwords
      ⟨base, c₀, rfl, hbase, hI₁, hz₁, by rw [ha]; exact hc, h6⟩ ?_
    intro v mem₂ pos₂ hpost
    obtain ⟨base', c', hargs', hv, hlist, hz₂, hbelow⟩ := hpost
    have hbb : base = base' ∧ c₀ = c' := by
      have hl : base'.length = base.length := by
        have := congrArg List.length hargs'
        simp at this; omega
      have := List.append_inj hargs'.symm hl
      exact ⟨this.1.symm, by simpa using this.2.symm⟩
    obtain ⟨hb1, hc1⟩ := hbb
    subst hb1 hc1
    let st₂ : State := { mem := mem₂, regs := Function.update st.regs 6 v, pos := pos₂ }
    have hr₂ : regs6 st₂ = base := by
      rw [← hr]; simp [regs6, st₂, Function.update]
    have hI₂ : Inv base mem₂ := hInv base mem₁ mem₂ hI₁ fun y hy => hbelow y (by rw [ha] at hy; omega)
    have h6₂ : st₂.regs 6 = v := by simp [st₂]
    have hcostIH : (k + (Expr.bin .add (.reg 5) (.const i)).size + offExpr.size + 2 +
        argsSize secArgs + (SecContract w Inv s).cost (base ++ [c₀]) mem₁ + 2) +
        ((ss.map fun s => s.cost base + 40).sum + 20) ≤ T := by
      have hcost' : (SecContract w Inv s).cost (base ++ [c₀]) mem₁ = s.cost base := by
        simp [SecContract, hbase]
      rw [hcost']
      simp only [List.map_cons, List.sum_cons] at hT
      simp only [offExpr, secArgs, argsSize, Expr.size]
      omega
    obtain ⟨o, st', c, hrun, ⟨ho, hoff, hsec, hz', hfr⟩, hcost⟩ :=
      ih (i + 1) st₂ _ T (fun s' hs' => hf s' (by simp [hs'])) hr₂ hI₂
        (by rw [h6₂]; exact hz₂) (by rw [h6₂]; omega) (by simp at hi; omega)
        (by rw [h6₂, hv]; unfold secScratch; omega) hcostIH
    · rw [h6₂] at ho hoff hsec hz' hfr
      have hfr' : ∀ y < v, (y < a + (i + 1) ∨ a + (i + 1) + ss.length < y) → st'.mem y = mem₂ y :=
        hfr
      refine ⟨o, st', c, hrun, ⟨?_, ?_, ?_, ?_, ?_⟩, hcost⟩
      · rw [ho, hv, hlen, Nat.add_assoc]
      · intro j hj
        rcases j with _ | j
        · rw [secLen_zero, Nat.add_zero, Nat.add_zero, hfr' (a + i) (by omega) (by omega),
            hbelow (a + i) (by omega), hmem₁]
          simp
        · rw [show a + i + (j + 1) = a + (i + 1) + j by omega, hoff j (by simpa using hj),
            secLen_cons_succ, hv]
          omega
      · intro j hj
        rcases j with _ | j
        · intro t ht
          rw [secLen_zero, Nat.add_zero] at *
          rw [hfr' (c₀ + t) (by simp at ht; omega) (Or.inr (by simp at hi; omega))]
          exact hlist t ht
        · have := hsec j (by simpa using hj)
          rw [secLen_cons_succ, ← Nat.add_assoc, ← hv]
          simpa using this
      · rw [hlen, ← Nat.add_assoc, ← hv]; exact hz'
      · intro y hy hy'
        simp only [List.length_cons] at hy'
        have hne : y ≠ a + i := by omega
        rw [hfr' y (by omega) (by omega), hbelow y hy, hmem₁]
        simp [hne]

theorem secLen_succ (base : List ℕ) (ss : List SecProc) {j : ℕ} (hj : j < ss.length) :
    secLen base ss (j + 1) = secLen base ss j + (ss[j].l base).length := by
  unfold secLen
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.map_append, List.sum_append]
  simp

/-- **The block from the memory `writeSecs` leaves.** For 24 writers started at section 0 with
`r6 = a + 25`, the offsets and sections that `writeSecs_runs` gives form the block
`layoutList` of the 24 sections at `a` (by `listAt_layoutList_of_starts`). -/
theorem listAt_layoutList_of_writeSecs {mem : ℕ → ℕ} {a : ℕ} {base : List ℕ}
    {ss : List SecProc} (hlen : ss.length = 24)
    (hoff : ∀ j ≤ ss.length, mem (a + 0 + j) = a + 25 - (a + 25) + secLen base ss j)
    (hsec : ∀ j (hj : j < ss.length), ListAt mem (a + 25 + secLen base ss j) (ss[j].l base)) :
    ListAt mem a (layoutList (ss.map fun s => s.l base)) := by
  refine listAt_layoutList_of_starts (e := secLen base ss) (secLen_zero base ss) ?_ ?_ ?_
  · intro i hi
    rw [List.length_map] at hi
    rw [secLen_succ base ss hi]
    simp [List.getD_eq_getElem?_getD, hi]
  · intro i hi
    rw [List.length_map] at hi
    have := hoff i hi
    simpa using this
  · intro i hi
    rw [List.length_map] at hi
    have := hsec i hi
    rw [List.length_map, hlen]
    simpa [List.getD_eq_getElem?_getD, hi] using this

/-- The builder from the writers: `r6 := r5 + 25`, then `writeSecs ss 0`. -/
def secsEntry (ss : List SecProc) : Stmt :=
  .seq (.assign 6 (.bin .add (.reg 5) (.const 25))) (writeSecs ss 0)

/-- The contract of `secsEntry`: called with six arguments `base` meeting `Inv`, with zero
memory from `a = base[5]` on, it writes the block of the sections `s.l base` at `a`, returns its
end, keeps memory below `a`, and leaves zero memory after the end. -/
def SecsContract (w : ℕ) (Inv : List ℕ → (ℕ → ℕ) → Prop) (ss : List SecProc) : Contract where
  pre args mem := args.length = 6 ∧ Inv args mem ∧ ZeroFrom mem (args.getD 5 0) ∧
    args.getD 5 0 + 25 + secLen args ss ss.length + secScratch args ss < 2 ^ w
  post args mem v mem' := v = args.getD 5 0 + (layoutList (ss.map fun s => s.l args)).length ∧
    ListAt mem' (args.getD 5 0) (layoutList (ss.map fun s => s.l args)) ∧ ZeroFrom mem' v ∧
    ∀ y < args.getD 5 0, mem' y = mem y
  cost args _ := (ss.map fun s => s.cost args + 40).sum + 30

theorem length_layoutList_map (base : List ℕ) (ss : List SecProc) :
    (layoutList (ss.map fun s => s.l base)).length =
      ss.length + 1 + secLen base ss ss.length := by
  rw [length_layoutList]
  simp [secLen, List.map_map, Function.comp_def]

theorem regs6_startState {args : List ℕ} (hl : args.length = 6) (mem : ℕ → ℕ) (pos : ℕ) (v : ℕ) :
    regs6 { startState args mem pos with regs := Function.update (startState args mem pos).regs 6 v } =
      args := by
  match args, hl with
  | [a0, a1, a2, a3, a4, a5], _ => simp [regs6, startState, Function.update]

/-- **The builder from the writers meets `SecsContract`**, for 24 writers that meet
`SecContract` with an invariant `Inv` that depends only on memory below `a`. -/
theorem secsEntry_meetsContract {w : ℕ} {p : Program} {j : ℕ} {Inv : List ℕ → (ℕ → ℕ) → Prop}
    (hInv : ∀ base mem mem', Inv base mem → (∀ y < base.getD 5 0, mem' y = mem y) →
      Inv base mem')
    {ss : List SecProc} (hlen : ss.length = 24)
    (hf : ∀ s ∈ ss, MeetsContract w p s.f (SecContract w Inv s))
    (hp : p.procs[j]? = some (secsEntry ss)) :
    MeetsContract w p j (SecsContract w Inv ss) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨hl, hI, hz, hb⟩ := hpre
  refine runs_start_le ?_
  unfold secsEntry
  have h5 : (startState args mem pos).regs 5 = args.getD 5 0 := rfl
  have h25 : (25 : ℕ) < 2 ^ w := by omega
  have ha25 : args.getD 5 0 + 25 < 2 ^ w := by omega
  refine runs_seq_assign_le (v := args.getD 5 0 + 25)
    (eval_addrExpr h5 ha25) ?_
  set st₁ : State := { startState args mem pos with
    regs := Function.update (startState args mem pos).regs 6 (args.getD 5 0 + 25) } with hst₁
  have h6 : st₁.regs 6 = args.getD 5 0 + 25 := by simp [st₁]
  have hT : (0 + (Expr.bin .add (.reg 5) (.const 25)).size + 2) +
      ((ss.map fun s => s.cost args + 40).sum + 20) ≤ (SecsContract w Inv ss).cost args mem := by
    simp only [SecsContract, Expr.size]
    omega
  obtain ⟨o, st', c, hrun, ⟨ho, hoff, hsec, hz', hfr⟩, hcost⟩ :=
    writeSecs_runs (ω := ω) hInv args hl hw ss 0 st₁ _ _ hf (regs6_startState hl mem pos _)
      hI (by rw [h6]; exact fun y hy => hz y (by omega)) (by rw [h6]) (by omega)
      (by rw [h6]; omega) hT
  have hv : o.value = st₁.regs 6 + secLen args ss ss.length := by rw [ho]; rfl
  rw [h6] at hoff hsec hfr
  refine ⟨o, st', c, hrun, ?_, hcost⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hv, h6, length_layoutList_map, hlen]; omega
  · exact listAt_layoutList_of_writeSecs hlen hoff hsec
  · rw [hv]; exact hz'
  · intro y hy
    exact hfr y (by omega) (Or.inl (by omega))

end MinCostFlow.HierPaths
