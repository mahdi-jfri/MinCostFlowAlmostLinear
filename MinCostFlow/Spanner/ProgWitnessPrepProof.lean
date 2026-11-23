module

public import MinCostFlow.Spanner.ProgWitnessPrepBlockHelpers
import MinCostFlow.Spanner.ProgWitnessPrepPhaseA1
import MinCostFlow.Spanner.ProgWitnessPrepPhaseA2
import MinCostFlow.Spanner.ProgWitnessPrepUnmarkLoop

/-!
# Top-Level Contract Verification for `witnessPrepModule`

Composes the initialization, bucketing, level-0 extraction, header storage, component parsing,
and level-block loop triples into `witnessPrep_triple`, establishes memory uniqueness for
`DecomposeOutAt`, defines `witnessPrepContract`, and proves `witnessPrep_meetsContract`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

private lemma listAt_flatMap_compRecord_unique {mem : ℕ → ℕ} :
    ∀ (xs ys : List (ℕ × List ℕ)) (a : ℕ),
      xs.length = ys.length →
      ListAt mem a (xs.flatMap compRecord) →
      ListAt mem a (ys.flatMap compRecord) →
      xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, a, hlen, hx, hy => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    rcases x with ⟨lx, vx⟩
    rcases y with ⟨ly, vy⟩
    rw [List.flatMap_cons, listAt_append, compRecord, listAt_cons, listAt_cons] at hx hy
    have hl : lx = ly := hx.1.1.symm.trans hy.1.1
    have hvlen : vx.length = vy.length := hx.1.2.1.symm.trans hy.1.2.1
    have hv : vx = vy := listAt_eq_of_length_eq hvlen hx.1.2.2 hy.1.2.2
    have hx_tail : ListAt mem (a + 2 + vx.length) (xs.flatMap compRecord) := by
      simpa [compRecord, Nat.add_assoc, Nat.add_comm 2 vx.length] using hx.2
    have hy_tail : ListAt mem (a + 2 + vx.length) (ys.flatMap compRecord) := by
      simpa [compRecord, hvlen, Nat.add_assoc, Nat.add_comm 2 vy.length] using hy.2
    have htail : xs = ys := listAt_flatMap_compRecord_unique xs ys (a + 2 + vx.length) hlen hx_tail hy_tail
    simp [hl, hv, htail]

/-- Uniqueness of the fields stored in memory by `DecomposeOutAt` given the length of `level`. -/
theorem decomposeOutAt_unique {mem : ℕ → ℕ} {a m d₁ d₂ n₁ n₂ dn₁ dn₂ : ℕ}
    {lv₁ lv₂ : List ℕ} {rc₁ rc₂ : List (ℕ × List ℕ)}
    (h1 : DecomposeOutAt mem a d₁ n₁ dn₁ lv₁ rc₁)
    (h2 : DecomposeOutAt mem a d₂ n₂ dn₂ lv₂ rc₂)
    (hl1 : lv₁.length = m) (hl2 : lv₂.length = m) :
    d₁ = d₂ ∧ n₁ = n₂ ∧ dn₁ = dn₂ ∧ lv₁ = lv₂ ∧ rc₁ = rc₂ := by
  have f1 := decomposeOutAt_fields h1
  have f2 := decomposeOutAt_fields h2
  have hd : d₁ = d₂ := f1.1.symm.trans f2.1
  have hn : n₁ = n₂ := f1.2.1.symm.trans f2.2.1
  have hdn : dn₁ = dn₂ := f1.2.2.1.symm.trans f2.2.2.1
  have hlv : lv₁ = lv₂ := listAt_eq_of_length_eq (hl1.trans hl2.symm) f1.2.2.2.1 f2.2.2.2.1
  have hrc_len : rc₁.length = rc₂.length := by
    have ha1 := f1.2.2.2.2.1
    have ha2 := f2.2.2.2.2.1
    rw [hl1] at ha1
    rw [hl2] at ha2
    exact ha1.symm.trans ha2
  have hrc : rc₁ = rc₂ := listAt_flatMap_compRecord_unique rc₁ rc₂ (a + 4 + m) hrc_len
    (by simpa [hl1] using f1.2.2.2.2.2) (by simpa [hl2] using f2.2.2.2.2.2)
  exact ⟨hd, hn, hdn, hlv, hrc⟩

/-- End-to-end Hoare triple for `witnessPrepBody`: builds `j0Edges` and compiled block tables
(`J_sub`, `jSubOrigEdges`, `deg`) for every decomposition component, clears vertex scratch
marks, and returns `inp.hEnd` in time at most `1200 * inp.J0_strip.m + 500`. -/
theorem witnessPrep_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ) :
    Triple w p
      (fun st => st.mem = mem₀ ∧ inp.Valid mem₀ w ∧
        st.regs 0 = inp.jAddr ∧ st.regs 1 = inp.j0Addr ∧
        st.regs 2 = inp.nlAddr ∧ st.regs 3 = inp.decAddr ∧ st.regs 4 = inp.h)
      witnessPrepBody
      (fun o st => ∃ _ : o = .returned inp.hEnd,
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem inp.rawComps.length ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem inp.hEnd)
      (fun _ => 1200 * inp.J0_strip.m + 500) := by
  intro st ω hstart
  have hv : inp.Valid mem₀ w := hstart.2.1
  have hsz := inp.size_bounds hv
  have hwb : inp.h + 9 + inp.d_ℓ + 16 * inp.J0_strip.m + 2 * inp.J.n < 2 ^ w :=
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hRet : Triple w p
      (fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.hEnd ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem inp.rawComps.length ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem inp.hEnd)
      (Stmt.ret (.reg 16))
      (fun o st => ∃ _ : o = .returned inp.hEnd,
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem inp.rawComps.length ∧
        VertMarksZero inp st.mem ∧
        ZeroFrom st.mem inp.hEnd)
      (fun _ => (Expr.reg 16).size + 1) := by
    intro st' _ ⟨_, h16, hst, hdone, hvz, hzf⟩
    have hev : (Expr.reg 16).eval w st' = some inp.hEnd := ev_reg h16 (by omega)
    exact ⟨.returned inp.hEnd, st', (Expr.reg 16).size + 1,
      runs_ret_iff.mpr ⟨inp.hEnd, hev, rfl, rfl, rfl⟩, ⟨rfl, hst, hdone, hvz, hzf⟩, le_rfl⟩
  have h67 := Triple.seq_normal_const (prepBlockLoop_triple inp mem₀ hv) hRet
  have h57 := Triple.seq_normal_const
    ((prepParse_triple inp mem₀ hv).conseq (fun _ h => h)
      (fun o st' h => by
        cases o with
        | returned _ => exact h
        | normal =>
          rcases h with ⟨_, hst, hz, hf, h16, _, _, hrecs⟩
          have hvz : VertMarksZero inp st'.mem := by
            refine ⟨fun u hu => hz _ ?_, fun u hu => hz _ ?_⟩
            · simp only [PrepInput.aVComp]; omega
            · simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
          have hzf : ZeroFrom st'.mem inp.hBlocksStart := by
            intro x hx
            exact hz x (by
              have hbs := inp.hBlocksStart_eq
              simp only [PrepInput.aVLoc, PrepInput.aVComp] at hbs
              omega)
          exact ⟨hf, h16, hst, fun k _ hk => hrecs k hk, hvz, hzf⟩)
      (fun _ _ => le_rfl))
    h67
  have h47 := Triple.seq_normal_const (prepHdrStore_triple inp mem₀ hv) h57
  have h37 := Triple.seq_normal_const (prepJ0_triple inp mem₀ hv) h47
  have h27 := Triple.seq_normal_const (prepBucket_triple inp mem₀ hv) h37
  have h17 := Triple.seq_normal_const
    ((prepInit_triple inp mem₀).conseq (fun _ h => h)
      (fun o _ h => match o with
        | .normal => ⟨h.1, h.2.2⟩
        | .returned _ => h)
      (fun _ _ => le_rfl))
    h27
  exact (h17.conseq (T' := fun _ => 1200 * inp.J0_strip.m + 500)
    (fun _ h => h) (fun _ _ h => h)
    (fun _ _ => by norm_num [Expr.size]; omega)) st ω hstart

/-- Word-RAM `Contract` for `witnessPrepModule`. Arguments are `[jAddr, j0Addr, nlAddr, decAddr, h]`;
returns the next free heap address `inp.hEnd` with cost at most `1200 * J0_strip.m + 500`. -/
def witnessPrepContract (w : ℕ) : Contract where
  pre args mem :=
    args.length = 5 ∧
    ∃ inp : PrepInput,
      inp.jAddr = args.getD 0 0 ∧
      inp.j0Addr = args.getD 1 0 ∧
      inp.nlAddr = args.getD 2 0 ∧
      inp.decAddr = args.getD 3 0 ∧
      inp.h = args.getD 4 0 ∧
      inp.Valid mem w
  post args mem v mem' :=
    ∀ inp : PrepInput,
      inp.jAddr = args.getD 0 0 →
      inp.j0Addr = args.getD 1 0 →
      inp.nlAddr = args.getD 2 0 →
      inp.decAddr = args.getD 3 0 →
      inp.h = args.getD 4 0 →
      inp.Valid mem w →
      v = inp.hEnd ∧
      PrepStaticState inp mem mem' ∧
      CompsDoneUpTo inp mem' inp.rawComps.length ∧
      VertMarksZero inp mem' ∧
      ZeroFrom mem' inp.hEnd
  cost args mem := 1200 * mem (args.getD 1 0 + 1) + 500

private lemma prepInput_eq_withC {mem : ℕ → ℕ} {w : ℕ} {inp₁ inp₂ : PrepInput}
    (hv₁ : inp₁.Valid mem w) (hv₂ : inp₂.Valid mem w)
    (hjAddr : inp₁.jAddr = inp₂.jAddr)
    (hj0Addr : inp₁.j0Addr = inp₂.j0Addr)
    (hnlAddr : inp₁.nlAddr = inp₂.nlAddr)
    (hdecAddr : inp₁.decAddr = inp₂.decAddr)
    (hh : inp₁.h = inp₂.h) :
    inp₂ = { inp₁ with c_ℓ := inp₂.c_ℓ } := by
  rcases hv₁ with ⟨_, hgJ₁, hJ0₁, _, hnl₁, _, hdec₁, hllen₁, _⟩
  rcases hv₂ with ⟨_, hgJ₂, hJ0₂, _, hnl₂, _, hdec₂, hllen₂, _⟩
  have hJ : inp₁.J = inp₂.J := graphAt_unique hgJ₁ (hjAddr ▸ hgJ₂)
  have hJ0 : inp₁.J0_strip = inp₂.J0_strip := by rw [hJ0₁, hJ0₂, hJ]
  have hnl : inp₁.nlIdx = inp₂.nlIdx := by rw [hnl₁, hnl₂, hJ]
  have hdec := decomposeOutAt_unique hdec₁ (hdecAddr ▸ hdec₂) hllen₁ (hJ0 ▸ hllen₂)
  cases inp₁; cases inp₂
  dsimp only at hjAddr hj0Addr hnlAddr hdecAddr hh hJ hJ0 hnl hdec
  subst hjAddr hj0Addr hnlAddr hdecAddr hh hJ hJ0 hnl
  rcases hdec with ⟨hd, hn, hdn, hlv, hrc⟩
  subst hd hn hdn hlv hrc
  rfl

/-- `witnessPrepModule` at procedure index `base` deterministically satisfies
`witnessPrepContract w`. -/
theorem witnessPrep_meetsContract {w : ℕ} {p : Program} {base : ℕ}
    (hp : p.HasAt base witnessPrepModule) :
    MeetsContract w p base (witnessPrepContract w) := by
  intro args mem pos ω _ ⟨_, inp₀, hj0, hj00, hnl0, hdec0, hh0, hv₀⟩
  have hbody : p.procs[base]? = some witnessPrepBody := by
    simpa [witnessPrepModule] using hp 0 (by simp [witnessPrepModule])
  rcases witnessPrep_triple inp₀ mem (startState args mem pos) ω
      ⟨rfl, hv₀, hj0.symm, hj00.symm, hnl0.symm, hdec0.symm, hh0.symm⟩ with
    ⟨o, st', c, hruns, ⟨ho, hst, hdone, hvz, hzf⟩, hcost⟩
  refine ⟨witnessPrepBody, hbody, o, st', c, hruns, ?_, ?_⟩
  · intro inp' hj' hj0' hnl' hdec' hh' hv'
    have heq := prepInput_eq_withC hv₀ hv'
      (hj0.trans hj'.symm) (hj00.trans hj0'.symm) (hnl0.trans hnl'.symm)
      (hdec0.trans hdec'.symm) (hh0.trans hh'.symm)
    rw [heq]
    refine ⟨?_, hst, hdone, hvz, hzf⟩
    subst ho
    rfl
  · have hm : mem (args.getD 1 0 + 1) = inp₀.J0_strip.m := by
      rw [← hj00]
      exact graphAt_m hv₀.2.2.2.1
    dsimp only [witnessPrepContract]
    rw [hm]
    exact hcost

section StaticValid

/-- Static validity of `PrepInput` without the `ZeroFrom mem inp.h` scratch-tail requirement
(used after `witnessPrep` has populated `[inp.h, inp.hEnd)`). Preserves every tuple index of `PrepInput.Valid`. -/
def PrepInput.StaticValid (inp : PrepInput) (mem : ℕ → ℕ) (w : ℕ) : Prop :=
  inp.J.IsValid ∧
  GraphAt mem inp.jAddr inp.J ∧
  inp.J0_strip = stripLoops inp.J ∧
  GraphAt mem inp.j0Addr inp.J0_strip ∧
  inp.nlIdx = nonloopIndices inp.J ∧
  WordRAM.ListAt mem inp.nlAddr inp.nlIdx ∧
  DecomposeOutAt mem inp.decAddr inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps ∧
  inp.level.length = inp.J0_strip.m ∧
  1 ≤ inp.phiNum_dec ∧
  inp.phiNum_dec ≤ inp.phiDen_dec ∧
  List.Pairwise (fun a b => a.1 ≤ b.1) inp.rawComps ∧
  (∀ c ∈ inp.rawComps,
    1 ≤ c.1 ∧ c.1 ≤ inp.d_ℓ ∧ List.Pairwise (fun x1 x2 => x1 < x2) c.2 ∧ 2 ≤ c.2.length) ∧
  DecomposeProp inp.c_ℓ inp.J0_strip inp.decomp ((inp.phiNum_dec : ℝ) / inp.phiDen_dec) ∧
  inp.jAddr + inp.J.encode.length ≤ inp.h ∧
  inp.j0Addr + inp.J0_strip.encode.length ≤ inp.h ∧
  inp.nlAddr + inp.nlIdx.length ≤ inp.h ∧
  inp.decAddr +
    (Decompose.encode inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps).length ≤ inp.h ∧
  True ∧
  1 < 2 ^ w ∧
  inp.h + 9 + inp.d_ℓ + 16 * inp.J0_strip.m + 2 * inp.J.n < 2 ^ w

lemma PrepInput.Valid.toStatic {inp : PrepInput} {mem : ℕ → ℕ} {w : ℕ}
    (h : inp.Valid mem w) : inp.StaticValid mem w := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _, h19, h20⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, trivial, h19, h20⟩

lemma PrepInput.StaticValid.of_agree_below {inp : PrepInput} {mem mem' : ℕ → ℕ} {w : ℕ}
    (h : inp.StaticValid mem w) (hagree : ∀ x < inp.h, mem' x = mem x) :
    inp.StaticValid mem' w := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _, h19, h20⟩
  refine ⟨h1, GraphAt.of_agree_below h2 h14 hagree, h3, GraphAt.of_agree_below h4 h15 hagree,
    h5, fun i hi => by rw [hagree _ (by omega)]; exact h6 i hi,
    fun i hi => by rw [hagree _ (by omega)]; exact h7 i hi,
    h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, trivial, h19, h20⟩

lemma PrepInput.StaticValid.toValid_zeroTail {inp : PrepInput} {mem : ℕ → ℕ} {w : ℕ}
    (h : inp.StaticValid mem w) :
    inp.Valid (fun x => if x < inp.h then mem x else 0) w := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _, h19, h20⟩
  refine ⟨h1, GraphAt.of_agree_below h2 h14 (fun k hk => by simp [hk]), h3,
    GraphAt.of_agree_below h4 h15 (fun k hk => by simp [hk]), h5,
    fun i hi => by dsimp only; split_ifs with hc; exact h6 i hi; omega,
    fun i hi => by dsimp only; split_ifs with hc; exact h7 i hi; omega,
    h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    fun a ha => by dsimp only; split_ifs with hc; omega; rfl, h19, h20⟩

lemma PrepInput.StaticValid.size_bounds {inp : PrepInput} {mem : ℕ → ℕ} {w : ℕ}
    (h : inp.StaticValid mem w) :
    inp.j0Edges.length ≤ inp.J0_strip.m ∧
      inp.rawComps.length ≤ inp.J0_strip.m ∧
      (List.map (fun c => 2 + c.2.length) inp.rawComps).sum ≤ 4 * inp.J0_strip.m ∧
      inp.j0Edges.length + (List.map (fun c => (inp.cJSub c).m) inp.rawComps).sum ≤ inp.J0_strip.m ∧
      inp.hEnd ≤ inp.h + 9 + inp.d_ℓ + 16 * inp.J0_strip.m + 2 * inp.J.n ∧
      inp.J0_strip.m ≤ inp.J.m :=
  PrepInput.size_bounds h.toValid_zeroTail

end StaticValid

end MinCostFlow.Spanner
