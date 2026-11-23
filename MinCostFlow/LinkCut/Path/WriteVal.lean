module

public import MinCostFlow.LinkCut.Path.ReadVal
public import MinCostFlow.LinkCut.Path.Block
public import MinCostFlow.Num.SignExtend

/-!
# Copying an edge value in, widening its numbers

A point write receives an edge value in the interface width `L` and stores it in a node record
in `K ≥ L` limbs. `widenBody` sign-extends one number into scratch memory, copies it into place,
and clears the scratch. `writeValBody` copies the header and direction words and widens the four
numbers.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen

/-- `widen [src, dst, L, K, heap]`: the `L`-limb number at `src` becomes a `K`-limb one at
`dst`. -/
def widenBody (extProc copyProc : ℕ) : Stmt :=
  .call 5 extProc [.reg 0, .reg 2, .reg 3, .reg 4] ;;
  .call 5 copyProc [.reg 4, .reg 1, .reg 3] ;;
  .call 5 copyProc [.bin .add (.reg 4) (.reg 3), .reg 4, .reg 3] ;;
  .ret (.const 0)

theorem widenBody_noRand (a b : ℕ) : (widenBody a b).NoRand := by
  simp [widenBody, Stmt.NoRand]

/-- The contract of `widenBody`. -/
def widenContract (w h L K : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ src dst heap, args = [src, dst, L, K, heap] ∧ 1 < 2 ^ w ∧ L ≤ K ∧
      src + L ≤ heap ∧ dst + K ≤ heap ∧ Valid mem src h L)
    (fun args y => args.getD 1 0 ≤ y ∧ y < args.getD 1 0 + K)
    (fun args mem _ mem' => Valid mem' (args.getD 1 0) h K ∧
      intVal mem' (args.getD 1 0) h K = intVal mem (args.getD 0 0) h L)
    (70 * K + 100) (2 * K)

theorem widen_meetsContract {w h L K f extProc copyProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (widenBody extProc copyProc))
    (hext : MeetsContract w p extProc (signExtendContract w h))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p f (widenContract w h L K) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨src, dst, heap, rfl, hw, hLK, hsh, hdh, hv⟩, hz, hroom⟩
  change ZeroFrom mem heap at hz
  change heap + 2 * K < 2 ^ w at hroom
  have hLw := hwords L (by simp)
  have hKw := hwords K (by simp)
  apply runs_start_le
  unfold widenBody
  refine runs_seq_call_le hext (vs := [src, L, K, heap]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨⟨_, _, _, _, rfl, hLK, hsh, hv⟩, hz, show heap + K < 2 ^ w by omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨hv₁, -, -, hf₁, hz₁, hvk₁, hval₁⟩
  change v₁ = heap + K at hv₁
  subst hv₁
  change ∀ y < heap, m₁ y = mem y at hf₁
  change Valid m₁ heap h K at hvk₁
  change intVal m₁ heap h K = intVal mem src h L at hval₁
  refine runs_seq_call_le hcopy (vs := [heap, dst, K]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, Or.inl hdh⟩ ?_
  rintro v₂ m₂ pos₂ ⟨s₂, d₂, l₂, heq₂, -, hc₂, ho₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  refine runs_seq_call_le hcopy (vs := [heap + K, heap, K]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, Or.inl le_rfl⟩ ?_
  rintro v₃ m₃ pos₃ ⟨s₃, d₃, l₃, heq₃, -, hc₃, ho₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl⟩ := heq₃
  obtain ⟨hz₃, hx₃, hk₃⟩ := storeBack_facts hdh hz₁ hc₂ ho₂ hc₃ ho₃
  refine runs_ret_le (by eval_expr) ?_ ?_
  · show ZeroFrom m₃ heap ∧ (∀ y < heap, ¬ (dst ≤ y ∧ y < dst + K) → m₃ y = mem y) ∧
      Valid m₃ dst h K ∧ intVal m₃ dst h K = intVal mem src h L
    refine ⟨hz₃, fun y hy hn => (hk₃ y hy hn).trans (hf₁ y hy), ?_, ?_⟩
    · intro i hi; rw [hx₃ i hi]; exact hvk₁ i hi
    · rw [intVal_congr (fun i hi => hx₃ i hi), hval₁]
  · simp only [widenContract, payloadContract, signExtendContract, heapContract, copyWordsContract,
      Expr.size_reg, Expr.size_const, Expr.size_bin, argsSize_cons, argsSize_nil,
      List.getD_cons_zero, List.getD_cons_succ]
    omega

/-- A call of `widen`, followed by `s`. -/
theorem runs_seq_widen {w h L K f r : ℕ} {p : Program} {ω : ℕ → Bool} {es ed el ek eh : Expr}
    {s : Stmt} {st : State} {src dst heap k T : ℕ} {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f (widenContract w h L K))
    (hargs : evalArgs w st [es, ed, el, ek, eh] = some [src, dst, L, K, heap]) (hsw : src < 2 ^ w)
    (hdw : dst < 2 ^ w) (hhw : heap < 2 ^ w) (hw : 1 < 2 ^ w) (hLK : L ≤ K)
    (hsh : src + L ≤ heap) (hdh : dst + K ≤ heap) (hv : Valid st.mem src h L)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 2 * K < 2 ^ w)
    (hrest : ∀ mem', ZeroFrom mem' heap →
      (∀ y < heap, ¬ (dst ≤ y ∧ y < dst + K) → mem' y = st.mem y) → Valid mem' dst h K →
      intVal mem' dst h K = intVal st.mem src h L → ∀ v pos', ∃ o st' c,
        Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' } o st' c ∧
        Q o st' ∧ (k + argsSize [es, ed, el, ek, eh] + (70 * K + 100) + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f [es, ed, el, ek, eh]) s) st o st' c ∧ Q o st' ∧
      k + c ≤ T := by
  refine runs_seq_call_le hf hargs (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega)
    ⟨⟨src, dst, heap, rfl, hw, hLK, hsh, hdh, hv⟩, hz, hroom⟩ ?_
  rintro v mem' pos' ⟨hz', hfr, hv', hval⟩
  exact hrest mem' hz' hfr hv' hval v pos'

/-- `writeVal [src, dst, L, K, heap]`: copy the `L`-limb edge value at `src` to a `K`-limb one
at `dst`. -/
def writeValBody (widenProc copyProc : ℕ) : Stmt :=
  .call 5 copyProc [.reg 0, .reg 1, .const 2] ;;
  .call 5 widenProc [.bin .add (.reg 0) (.const 2), .bin .add (.reg 1) (.const 2), .reg 2, .reg 3,
    .reg 4] ;;
  .call 5 widenProc [.bin .add (.reg 0) (.bin .add (.const 2) (.reg 2)),
    .bin .add (.reg 1) (.bin .add (.const 2) (.reg 3)), .reg 2, .reg 3, .reg 4] ;;
  .call 5 widenProc [atR 0 2 2 2, atR 1 3 2 2, .reg 2, .reg 3, .reg 4] ;;
  .call 5 widenProc [atR 0 2 2 3, atR 1 3 2 3, .reg 2, .reg 3, .reg 4] ;;
  .ret (.const 0)

theorem writeValBody_noRand (a b : ℕ) : (writeValBody a b).NoRand := by
  simp [writeValBody, Stmt.NoRand]

/-- The contract of `writeValBody`. The value is an edge; the two blocks do not overlap. -/
def writeValContract (w h L K : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ src dst heap, args = [src, dst, L, K, heap] ∧ 1 < 2 ^ w ∧ L ≤ K ∧
      src + (2 + 4 * L) ≤ heap ∧ dst + (2 + 4 * K) ≤ heap ∧
      (src + (2 + 4 * L) ≤ dst ∨ dst + (2 + 4 * K) ≤ src) ∧
      ∃ e, PathEdgeAt mem src h L (some e))
    (fun args y => args.getD 1 0 ≤ y ∧ y < args.getD 1 0 + (2 + 4 * K))
    (fun args mem _ mem' => ∀ e, PathEdgeAt mem (args.getD 0 0) h L (some e) →
      PathEdgeAt mem' (args.getD 1 0) h K (some e))
    (300 * K + 600) (2 * K)

theorem writeVal_meetsContract {w h L K f widenProc copyProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (writeValBody widenProc copyProc))
    (hwiden : MeetsContract w p widenProc (widenContract w h L K))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p f (writeValContract w h L K) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨src, dst, heap, rfl, hw, hLK, hsh, hdh, hdis, e, hv⟩, hz, hroom⟩
  change ZeroFrom mem heap at hz
  change heap + 2 * K < 2 ^ w at hroom
  have hv0 := hv
  obtain ⟨hh, hd, hg, hl, hfl, hdt⟩ := hv
  apply runs_start_le
  unfold writeValBody
  refine runs_seq_call_le hcopy (vs := [src, dst, 2]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨s₁, d₁, l₁, heq₁, -, hc₁, ho₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  change ∀ i < 2, m₁ (dst + i) = mem (src + i) at hc₁
  change ∀ y, y < dst ∨ dst + 2 ≤ y → m₁ y = mem y at ho₁
  have hz₁ : ZeroFrom m₁ heap := fun y hy => by rw [ho₁ y (by omega)]; exact hz y hy
  refine runs_seq_widen (src := src + 2) (dst := dst + 2) (heap := heap) hwiden (by eval_expr)
    (by omega) (by omega) (by omega) hw hLK (by omega) (by omega)
    (hg.congr fun i hi => ho₁ _ (by omega)).1 hz₁ hroom ?_
  intro m₂ hz₂ hf₂ hv₂ hval₂ v₂ pos₂
  dsimp only at hf₂ hval₂
  rw [show src + 2 + L = src + (2 + L) by omega] at hl
  refine runs_seq_widen (src := src + (2 + L)) (dst := dst + (2 + K)) (heap := heap) hwiden
    (by eval_expr) (by omega) (by omega) (by omega) hw hLK (by omega) (by omega)
    (hl.congr fun i hi => by
      show m₂ _ = _
      rw [hf₂ _ (by omega) (by omega), ho₁ _ (by omega)]).1 hz₂ hroom ?_
  intro m₃ hz₃ hf₃ hv₃ hval₃ v₃ pos₃
  dsimp only at hf₃ hval₃
  rw [show src + 2 + 2 * L = src + (2 + 2 * L) by omega] at hfl
  refine runs_seq_widen (src := src + (2 + 2 * L)) (dst := dst + (2 + 2 * K)) (heap := heap)
    hwiden (by eval_expr) (by omega) (by omega) (by omega) hw hLK (by omega) (by omega)
    (hfl.congr fun i hi => by
      show m₃ _ = _
      rw [hf₃ _ (by omega) (by omega), hf₂ _ (by omega) (by omega), ho₁ _ (by omega)]).1
    hz₃ hroom ?_
  intro m₄ hz₄ hf₄ hv₄ hval₄ v₄ pos₄
  dsimp only at hf₄ hval₄
  rw [show src + 2 + 3 * L = src + (2 + 3 * L) by omega] at hdt
  refine runs_seq_widen (src := src + (2 + 3 * L)) (dst := dst + (2 + 3 * K)) (heap := heap)
    hwiden (by eval_expr) (by omega) (by omega) (by omega) hw hLK (by omega) (by omega)
    (hdt.congr fun i hi => by
      show m₄ _ = _
      rw [hf₄ _ (by omega) (by omega), hf₃ _ (by omega) (by omega),
        hf₂ _ (by omega) (by omega), ho₁ _ (by omega)]).1
    hz₄ hroom ?_
  intro m₅ hz₅ hf₅ hv₅ hval₅ v₅ pos₅
  dsimp only at hf₅ hval₅
  -- Source cells below the heap pointer are unchanged at each step.
  have hsrc₂ : ∀ y, src ≤ y → y < src + (2 + 4 * L) → m₂ y = mem y := fun y h1 h2 => by
    rw [hf₂ _ (by omega) (by omega), ho₁ _ (by omega)]
  have hsrc₃ : ∀ y, src ≤ y → y < src + (2 + 4 * L) → m₃ y = mem y := fun y h1 h2 => by
    rw [hf₃ _ (by omega) (by omega), hsrc₂ y h1 h2]
  have hsrc₄ : ∀ y, src ≤ y → y < src + (2 + 4 * L) → m₄ y = mem y := fun y h1 h2 => by
    rw [hf₄ _ (by omega) (by omega), hsrc₃ y h1 h2]
  refine runs_ret_le (by eval_expr) ⟨hz₅, fun y hy hn => ?_, fun e' he' => ?_⟩
    (by simp only [writeValContract, widenContract, payloadContract, copyWordsContract,
      Expr.size_reg, Expr.size_const, Expr.size_bin, argsSize_cons, argsSize_nil, atR]; omega)
  · change y < heap at hy
    change ¬ (dst ≤ y ∧ y < dst + (2 + 4 * K)) at hn
    show m₅ y = mem y
    rw [hf₅ _ hy (by omega), hf₄ _ hy (by omega), hf₃ _ hy (by omega), hf₂ _ hy (by omega),
      ho₁ _ (by omega)]
  · change PathEdgeAt mem src h L (some e') at he'
    obtain rfl : e = e' := Option.some.inj (pathEdgeAt_unique hv0 he')
    show PathEdgeAt m₅ dst h K (some e)
    have hlate : ∀ y < heap, ¬ (dst + 2 ≤ y ∧ y < dst + (2 + 4 * K)) → m₅ y = m₁ y :=
      fun y hy hn => by
        rw [hf₅ _ hy (by omega), hf₄ _ hy (by omega), hf₃ _ hy (by omega),
          hf₂ _ hy (by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlate dst (by omega) (by omega)]
      have := hc₁ 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact hh
    · rw [hlate (dst + 1) (by omega) (by omega), hc₁ 1 (by omega)]; exact hd
    · refine ⟨fun i hi => ?_, ?_⟩
      · rw [hf₅ _ (by omega) (by omega), hf₄ _ (by omega) (by omega),
          hf₃ _ (by omega) (by omega)]
        exact hv₂ i hi
      · rw [intVal_congr (fun i hi => by
          rw [hf₅ _ (by omega) (by omega), hf₄ _ (by omega) (by omega),
            hf₃ _ (by omega) (by omega)]), hval₂,
          intVal_congr (fun i hi => ho₁ _ (by omega)), hg.2]
    · rw [show dst + 2 + K = dst + (2 + K) by omega]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [hf₅ _ (by omega) (by omega), hf₄ _ (by omega) (by omega)]
        exact hv₃ i hi
      · rw [intVal_congr (fun i hi => by
          rw [hf₅ _ (by omega) (by omega), hf₄ _ (by omega) (by omega)]), hval₃,
          intVal_congr (fun i hi => hsrc₂ _ (by omega) (by omega)), hl.2]
    · rw [show dst + 2 + 2 * K = dst + (2 + 2 * K) by omega]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [hf₅ _ (by omega) (by omega)]
        exact hv₄ i hi
      · rw [intVal_congr (fun i hi => by rw [hf₅ _ (by omega) (by omega)]), hval₄,
          intVal_congr (fun i hi => hsrc₃ _ (by omega) (by omega)), hfl.2]
    · rw [show dst + 2 + 3 * K = dst + (2 + 3 * K) by omega]
      refine ⟨hv₅, ?_⟩
      rw [hval₅, intVal_congr (fun i hi => hsrc₄ _ (by omega) (by omega)), hdt.2]

end MinCostFlow.LinkCut.Path
