module

public import MinCostFlow.MinRatio.ExplicitEdgeAddresses
public import MinCostFlow.MinRatio.ExplicitEdgeLoopMemory
public import MinCostFlow.Basic.Forest
import MinCostFlow.MinRatio.CycleDetectorAccounting
import MinCostFlow.Num.IPM.FixedPointFacts
public import MinCostFlow.MinRatio.DetectorThreshold
public import MinCostFlow.IPM.Machine.MinRatioContract
import WordRAM.Tactic

/-!
# Updating all explicit edges of a route

Algorithm 2 (page 29) applies the normalized circulation and records
its absolute value. Resolve the record addresses into fresh memory,
then update exactly the first occurrence of each explicit name.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Arguments are the route base and length, live address table,
incoming heap, multiplier address, and limb count. -/
@[expose] def explicitEdgeRouteUpdateBody (resolve visit : ℕ) : Stmt :=
  .call 7 resolve [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .assign 2 (.reg 3) ;;
  .assign 3 (.reg 4) ;;
  .assign 4 (.reg 5) ;;
  .assign 5 (.reg 7) ;;
  explicitEdgeLoop visit ;;
  .ret (.reg 5)

/-- Resolving addresses and applying explicit edge updates uses no random statements. -/
theorem explicitEdgeRouteUpdateBody_noRand (resolve visit : ℕ) :
    (explicitEdgeRouteUpdateBody resolve visit).NoRand := by
  simp [explicitEdgeRouteUpdateBody, explicitEdgeLoop_noRand, Stmt.NoRand]

/-- The route update uses one address word per row and the verified
per-row workspace budget. -/
@[expose] def explicitEdgeRouteUpdateContract (w h L base table dst a : ℕ)
    (edges : List (ℕ × Bool)) (address : ℕ → ℕ) (old : ℕ → PathEdgeValue) (num : ℤ) :
    Contract where
  pre args mem :=
    args = [base, edges.length, table, dst, a, L] ∧
    (explicitEdgeAddressContract w edges address).pre [base, edges.length, table, dst] mem ∧
    PathIntAt mem a h L num ∧ ZeroFrom mem dst ∧
    (∀ e ∈ edges.map Prod.fst, PathEdgeAt mem (address e) h L (some (old e))) ∧
    dst + edges.length + edges.length * (17 * L + 3) < 2 ^ w
  post _ mem ret mem' :=
    dst + edges.length ≤ ret ∧ ZeroFrom mem' ret ∧
    ExplicitEdgePrefixAt mem' h L edges address old num edges.length ∧
    ret ≤ dst + edges.length + edges.length * (17 * L + 3) ∧
    ∀ x < dst, (∀ e ∈ edges.map Prod.fst, x < address e + 2 + 2 * L ∨
      address e + 2 + 4 * L ≤ x) → mem' x = mem x
  cost _ _ := edges.length * (136 * edges.length + 152 * L^2 + 561 * L + 825) + 40

/-- The address resolver initializes the concrete invariant of the update
loop. The final records contain the exact grouped increments. -/
theorem explicitEdgeRouteUpdate_meetsContract {w h entry resolve visit L base table dst a : ℕ}
    {p : Program} (edges : List (ℕ × Bool)) (address : ℕ → ℕ)
    (old : ℕ → PathEdgeValue) (num : ℤ)
    (ha : a + L ≤ dst) (hroom : dst + edges.length + 2 < 2 ^ w)
    (hname : ∀ e ∈ edges.map Prod.fst, e < 2 ^ w)
    (hbelow : ∀ e ∈ edges.map Prod.fst, address e + 2 + 4 * L ≤ min base (min dst a))
    (hdisj : ∀ e ∈ edges.map Prod.fst, ∀ f ∈ edges.map Prod.fst, e ≠ f →
      address e + 2 + 4 * L ≤ address f ∨ address f + 2 + 4 * L ≤ address e)
    (hfit : ∀ e ∈ edges.map Prod.fst,
      let n := (edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)
      Num.Fits h L n ∧ Num.Fits h L (num * n) ∧ Num.Fits h L |num * n| ∧
        Num.Fits h L ((old e).flow + num * n) ∧ Num.Fits h L ((old e).detector + |num * n|))
    (hp : p.HasAt entry [explicitEdgeRouteUpdateBody resolve visit])
    (hr : MeetsContract w p resolve (explicitEdgeAddressContract w edges address))
    (hv : ∀ i, MeetsContract w p visit
      (explicitEdgeVisitContract w h edges i (old ((edges[i]?.getD (0, false)).1)) num)) :
    MeetsContract w p entry
      (explicitEdgeRouteUpdateContract w h L base table dst a edges address old num) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hresolve, hn, hz, hold, hreserve⟩ := hpre
  have hroute : ExplicitEdgesAt mem base edges ∧ base + 2 * edges.length ≤ dst := by
    obtain ⟨_, _, _, heq, hl, hb, _, _⟩ := hresolve
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, _, rfl, rfl⟩ := heq
    exact ⟨hl, hb⟩
  have htable := hwords table (by simp)
  apply runs_start_le
  unfold explicitEdgeRouteUpdateBody
  refine runs_seq_call_le hr (vs := [base, edges.length, table, dst]) (by eval_expr)
    (by wram_words) hresolve ?_
  intro ptr mem₁ pos₁ hpost
  have hptr : ptr = dst + edges.length := hpost.1
  have hpw : ptr < 2 ^ w := by omega
  have hframe : ∀ x, x < dst ∨ ptr ≤ x → mem₁ x = mem x := hpost.2.2
  have hpacked := hroute.1.congr (mem' := mem₁) (fun x _ hx => hframe x (Or.inl (by omega)))
  have hn₁ := hn.congr (mem' := mem₁) (fun i hi => hframe _ (Or.inl (by omega)))
  have hz₁ : ZeroFrom mem₁ ptr := fun x hx => (hframe x (Or.inr hx)).trans (hz x (by omega))
  have hold₁ : ∀ e ∈ edges.map Prod.fst, PathEdgeAt mem₁ (address e) h L (some (old e)) := by
    intro e he
    have hbound := hbelow e he
    exact (hold e he).congr (fun x _ hx => hframe x (Or.inl (by omega)))
  have hinit := explicitEdgeLoopMemory_zero (w := w) (start := ptr) (by omega) hpacked hn₁ hz₁ hold₁
  have hloop := explicitEdgeLoop_memory (p := p) (visit := visit) edges address old num mem₁
    (start := ptr) (base := base) (addrBase := dst) (a := a)
    ⟨by omega, by omega, by omega⟩ (by omega) hname hbelow hdisj hfit hv
  refine runs_seq_assign_le (v := dst) (by eval_expr) ?_
  refine runs_seq_assign_le (v := a) (by eval_expr) ?_
  refine runs_seq_assign_le (v := L) (by eval_expr) ?_
  refine runs_seq_assign_le (v := ptr) (by eval_expr) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨rfl, (List.length_map _).symm, rfl, rfl, rfl, rfl, hpost.2.1, hinit⟩
  · intro st hout
    have hf := hout.2.2.2.2.2.2.2
    refine runs_ret_le (v := st.regs 5) (by simp [Expr.eval]) ?_ ?_
    · exact ⟨hptr ▸ hf.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hptr ▸ hf.2.2.2.2.2.2.1,
        fun x hx houtside => (hf.2.2.2.2.2.2.2 x (by omega) houtside).trans (hframe x (Or.inl hx))⟩
    · simp [explicitEdgeRouteUpdateContract, explicitEdgeAddressContract, argsSize, Expr.size]
      simp only [Nat.mul_add]
      omega

/-- The grouped signed count fits whenever the entire route length
fits strictly inside the positive half of the limb range. -/
theorem explicitEdge_signed_count_fits {h L : ℕ} (edges : List (ℕ × Bool)) (e : ℕ)
    (hlen : 2 * (edges.length : ℤ) < (Num.capacity h L : ℤ)) :
    Num.Fits h L ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)) := by
  have hb := abs_le.mp (explicitEdge_signed_count_bound edges e)
  unfold Num.Fits
  omega

/-- A common decoded magnitude bound on the old accounts and the net
increment supplies the limb ranges for the explicit record update.
One extra bit accounts for adding a change to an old account. -/
theorem explicitEdge_increment_fits {h L P B : ℕ} (old : PathEdgeValue) (change : ℤ)
    (hwidth : P + B + 3 ≤ h * L)
    (hf : |(old.flow : ℝ) / (2 : ℝ)^P| ≤ (2 : ℝ)^B)
    (hd : |(old.detector : ℝ) / (2 : ℝ)^P| ≤ (2 : ℝ)^B)
    (hc : |(change : ℝ) / (2 : ℝ)^P| ≤ (2 : ℝ)^B) :
    Num.Fits h L change ∧ Num.Fits h L |change| ∧
      Num.Fits h L (old.flow + change) ∧ Num.Fits h L (old.detector + |change|) := by
  have hpow : 0 < (2 : ℝ)^P := pow_pos zero_lt_two _
  have hca : |((|change| : ℤ) : ℝ) / (2 : ℝ)^P| ≤ (2 : ℝ)^B := by
    simpa only [Int.cast_abs, abs_div, abs_of_pos hpow, abs_abs] using hc
  have hadd (x y : ℤ) (hx : |(x : ℝ) / (2 : ℝ)^P| ≤ (2 : ℝ)^B)
      (hy : |(y : ℝ) / (2 : ℝ)^P| ≤ (2 : ℝ)^B) : Num.Fits h L (x + y) := by
    apply Num.IPM.fits_of_scaled_bound (P := P) (E := B + 1) (by omega)
    rw [Int.cast_add, add_div]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hx hy
      _ = (2 : ℝ)^(B + 1) := by rw [pow_succ, mul_two]
  exact ⟨Num.IPM.fits_of_scaled_bound (by omega) hc,
    Num.IPM.fits_of_scaled_bound (by omega) hca, hadd _ _ hf hc, hadd _ _ hd hca⟩

/-- After Detect and length refresh, an increment bounded by
`2^(3E+1)` and an old flow bounded by `2^E` fit the IPM format,
including the new detector residual. -/
theorem explicitEdge_increment_fits_after_detect {w : ℕ} (F : IPM.Machine.MinRatioFormat w)
    (old : PathEdgeValue) (change account : ℤ) (epsilon oldLength newLength : ℝ)
    (he : 0 < epsilon) (heU : epsilon ≤ (2 : ℝ)^F.rangeExponent)
    (ho : 1 / (2 : ℝ)^F.rangeExponent ≤ oldLength)
    (hn : 1 / (2 : ℝ)^F.rangeExponent ≤ newLength) (ha : 0 ≤ account)
    (hres : old.detector =
      (if detectorThreshold F.fmt.precision epsilon oldLength ≤ account then 0 else account) -
        detectorThreshold F.fmt.precision epsilon newLength)
    (hf : |(old.flow : ℝ) / (2 : ℝ)^F.fmt.precision| ≤ (2 : ℝ)^F.rangeExponent)
    (hc : |(change : ℝ) / (2 : ℝ)^F.fmt.precision| ≤ (2 : ℝ)^(3 * F.rangeExponent + 1)) :
    Num.Fits F.fmt.limbBits F.limbs change ∧ Num.Fits F.fmt.limbBits F.limbs |change| ∧
      Num.Fits F.fmt.limbBits F.limbs (old.flow + change) ∧
      Num.Fits F.fmt.limbBits F.limbs (old.detector + |change|) := by
  have hw := F.width
  have hpow (n : ℕ) (hn : n ≤ 3 * F.rangeExponent + 1) :
      (2 : ℝ)^n ≤ (2 : ℝ)^(3 * F.rangeExponent + 1) :=
    pow_le_pow_right₀ one_le_two hn
  refine explicitEdge_increment_fits (P := F.fmt.precision) (B := 3 * F.rangeExponent + 1)
    old change (by omega) (hf.trans (hpow _ (by omega))) ?_ hc
  rw [hres]
  exact (detectorThreshold_refresh_scaled_bound F.fmt.precision F.rangeExponent epsilon
    oldLength newLength account he heU ho hn ha).trans (hpow _ (by omega))

/-- At the original precision, the updated record contains the old
signed flow plus the scaled count, and the old detector plus its
absolute value. -/
theorem explicitEdgeRouteUpdate_fixVal {w h L P base table dst a e ret : ℕ}
    {mem mem' : ℕ → ℕ} {edges : List (ℕ × Bool)} {address : ℕ → ℕ}
    {old : ℕ → PathEdgeValue} {num : ℤ}
    (he : e ∈ edges.map Prod.fst) (hn : PathIntAt mem a h L num)
    (hold : PathEdgeAt mem (address e) h L (some (old e)))
    (hp : (explicitEdgeRouteUpdateContract w h L base table dst a edges address old num).post
      [base, edges.length, table, dst, a, L] mem ret mem') :
    let flow := address e + 2 + 2 * L
    let det := address e + 2 + 3 * L
    let delta := Num.fixVal mem a h L P *
      (((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ) : ℤ) : ℝ)
    Num.fixVal mem' flow h L P = Num.fixVal mem flow h L P + delta ∧
    Num.fixVal mem' det h L P = Num.fixVal mem det h L P + |delta| := by
  dsimp only
  have updated := explicitEdgePrefixAt_done hp.2.2.1 e he
  have hf := hold.2.2.2.2.1.2
  have hd := hold.2.2.2.2.2.2
  have hf' := updated.2.2.2.2.1.2
  have hd' := updated.2.2.2.2.2.2
  simp only [Num.fixVal, hf, hd, hf', hd', hn.2, PathEdgeValue.shift, PathTag.ofFlow,
    Int.cast_add, Int.cast_abs, Int.cast_mul, add_div, abs_mul, abs_div,
    abs_of_nonneg (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) P),
    div_mul_eq_mul_div, and_self]

/-- For an explicit off-tree edge the decoded update is precisely the
normalized cycle coordinate and its absolute value in Algorithm 2 (page 29). -/
theorem explicitEdgeRouteUpdate_cycle {w h L P base table dst a e ret : ℕ}
    {mem mem' : ℕ → ℕ} {edges : List (ℕ × Bool)} {address : ℕ → ℕ}
    {old : ℕ → PathEdgeValue} {num : ℤ} {F : MGraph}
    (he : e ∈ edges.map Prod.fst) (hoff : e ∉ F.E)
    (paths : List (ℕ × ℕ)) (hc : ∀ p ∈ paths, F.Connected p.1 p.2)
    (C : ℕ → ℝ)
    (hC : C e = (edges.map (fun x => walkFlow [x] e)).sum +
      (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum)
    (hn : PathIntAt mem a h L num)
    (hold : PathEdgeAt mem (address e) h L (some (old e)))
    (hp : (explicitEdgeRouteUpdateContract w h L base table dst a edges address old num).post
      [base, edges.length, table, dst, a, L] mem ret mem') :
    let flow := address e + 2 + 2 * L
    let det := address e + 2 + 3 * L
    let delta := Num.fixVal mem a h L P * C e
    Num.fixVal mem' flow h L P = Num.fixVal mem flow h L P + delta ∧
    Num.fixVal mem' det h L P = Num.fixVal mem det h L P + |delta| := by
  dsimp only
  have ⟨hs, _⟩ := offTree_cycle_increment_of_signed_count hoff edges paths hc C hC
    (Num.fixVal mem a h L P)
  rw [hs]
  exact explicitEdgeRouteUpdate_fixVal he hn hold hp

/-- An off-tree edge absent from the explicit route has zero
cycle coordinate, and its disjoint record is preserved. -/
theorem explicitEdgeRouteUpdate_absent {w h L base table dst a e ret : ℕ}
    {mem mem' : ℕ → ℕ} {edges : List (ℕ × Bool)} {address : ℕ → ℕ}
    {old : ℕ → PathEdgeValue} {num : ℤ} {F : MGraph}
    (he : e ∉ edges.map Prod.fst) (hoff : e ∉ F.E)
    (paths : List (ℕ × ℕ)) (hc : ∀ p ∈ paths, F.Connected p.1 p.2)
    (C : ℕ → ℝ)
    (hC : C e = (edges.map (fun x => walkFlow [x] e)).sum +
      (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum)
    (hold : PathEdgeAt mem (address e) h L (some (old e)))
    (hbelow : address e + 2 + 4 * L ≤ dst)
    (hdisj : ∀ f ∈ edges.map Prod.fst,
      address e + 2 + 4 * L ≤ address f ∨ address f + 2 + 4 * L ≤ address e)
    (hp : (explicitEdgeRouteUpdateContract w h L base table dst a edges address old num).post
      [base, edges.length, table, dst, a, L] mem ret mem') :
    C e = 0 ∧ PathEdgeAt mem' (address e) h L (some (old e)) := by
  obtain ⟨ht, hf⟩ := (explicitEdge_counts_zero_iff edges e).2 he
  have ⟨hs, _⟩ := offTree_cycle_increment_of_signed_count hoff edges paths hc C hC 1
  refine ⟨by simpa [ht, hf] using hs, hold.congr ?_⟩
  intro x hx₀ hx₁
  apply hp.2.2.2.2 x (lt_of_lt_of_le hx₁ hbelow)
  intro f hf
  rcases hdisj f hf with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (h.trans hx₀)

end MinCostFlow.MinRatio
