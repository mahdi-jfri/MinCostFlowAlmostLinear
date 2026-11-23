module

public import MinCostFlow.DynSpanner.Program.DynSpannerClearBuckets
public import MinCostFlow.DynSpanner.Program.DynSpannerFillLevel
public import MinCostFlow.DynSpanner.Program.DynSpannerStepMinH
public import MinCostFlow.DynSpanner.Program.DynSpannerLevelsDelete
import WordRAM.Tactic

/-!
# The buckets after a rebuild of level `j`

After a rebuild of level `j`, the levels `j..L` change: level `j` becomes `H_j` with the edges of
`J̃`, and the levels above `j` become empty. In memory, the levels are kept through the words
`minH` and the buckets. `dsRebuildBucketsStmt` updates them in two passes:
1. `dsClearBucketsStmt` empties the buckets of the levels `j..L` and sets `minH[e] := 0` for
   their edges;
2. `dsFillLevelStmt` puts each edge of `J̃` whose word is now `0` into bucket `j`.

`dsRebuildBuckets_meetsContract` proves that afterwards the buckets are `rebuildBuckets` (the old
buckets below `j`, the new edges in bucket `j`, empty buckets above `j`) and the words are
`minHRebuild` (`minH_after_passes`). With `bucketRebuild_spec` and `minHRebuild_spec`, these are
the bucket facts of `DynSpannerStateAt` for the new levels.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [nextBase, headBase, degBase, j, L + 1, minHBase, b, esPtr, esLen]`. -/
def dsRebuildBucketsStmt (bC bF : ℕ) : Stmt :=
  .call 9 (bC + clearBucketsIdx) [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5] ;;
  .call 9 (bF + fillLevelIdx) [.reg 6, .reg 3, .reg 7, .reg 8, .reg 5] ;;
  .ret (.const 0)

def rebuildBucketsProcs (bC bF : ℕ) : List Stmt := [dsRebuildBucketsStmt bC bF]

def rebuildBucketsIdx : ℕ := 0

lemma rebuildBucketsProcs_noRand (bC bF : ℕ) : ∀ s ∈ rebuildBucketsProcs bC bF, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The data and the precondition of `dsRebuildBucketsStmt`: the state block at `b`, the level
`j`, the list `es` of the edges of `J̃`, and the buckets `B` (bucket `i` holds the edges with
`minH[e] = i + 1`). -/
structure RBCtx where
  w : ℕ
  L : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  j : ℕ
  es : List ℕ
  esPtr : ℕ
  B : ℕ → List ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hbound : b + dsFixedSize L vCap eCap < 2 ^ w
  hjL : j ≤ L
  hLw : mem0 (b + dsLOff) = L
  hvw : mem0 (b + dsVCapOff) = vCap
  hew : mem0 (b + dsECapOff) = eCap
  hesB : esPtr + es.length < 2 ^ w
  dEB : IvlDisj esPtr es.length b (dsFixedSize L vCap eCap)
  hes : ListAt mem0 esPtr es
  hnd : es.Nodup
  hesC : ∀ e ∈ es, e < eCap
  hBk : BucketsAt mem0 L vCap eCap b B
  hBiff : ∀ i e, i ≤ L → (e ∈ B i ↔ e < eCap ∧ mem0 (dsMinHBase b vCap eCap + e) = i + 1)
  hbig : ∀ e < eCap, mem0 (dsMinHBase b vCap eCap + e) ≤ L + 1

/-- The old words `minH`. -/
def RBCtx.m0 (c : RBCtx) (e : ℕ) : ℕ := c.mem0 (dsMinHBase c.b c.vCap c.eCap + e)

/-- The buckets after the rebuild. -/
def RBCtx.newB (c : RBCtx) (i : ℕ) : List ℕ :=
  if i < c.j then c.B i
  else if i = c.j then (c.es.filter fun e => decide (minHClear c.j c.m0 e = 0)).reverse
  else []

/-- Contract of `dsRebuildBucketsStmt`. -/
def dsRebuildBucketsContract (c : RBCtx) : Contract where
  pre args mem :=
    args = [dsHNextBase c.b c.vCap c.eCap, dsHHeadBase c.b c.vCap c.eCap,
      dsHDegDummyBase c.b c.L c.vCap c.eCap, c.j, c.L + 1, dsMinHBase c.b c.vCap c.eCap, c.b,
      c.esPtr, c.es.length] ∧ mem = c.mem0
  post _ mem _ mem' :=
    BucketsAt mem' c.L c.vCap c.eCap c.b c.newB ∧
    (∀ e < c.eCap, mem' (dsMinHBase c.b c.vCap c.eCap + e) = minHRebuild c.j c.es.toFinset c.m0 e) ∧
    ∀ addr, (addr < dsMinHBase c.b c.vCap c.eCap ∨ dsDomGenBase c.b c.L c.vCap c.eCap ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 40 * (bucketsCat c.B c.j (c.L + 1 - c.j)).length + 60 * (c.L + 1 - c.j) +
    210 * c.es.length + 100

end

private lemma domGen_le₃ (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
    dsEdgeDomGenBase]
  omega

public section

/-- After the clearing pass, the words are `minHClear`. -/
theorem minH_after_clear {eCap j L minH : ℕ} {mem₀ mem₁ : ℕ → ℕ} (B : ℕ → List ℕ)
    (hB : ∀ i e, j ≤ i → i ≤ L → (e ∈ B i ↔ e < eCap ∧ mem₀ (minH + e) = i + 1))
    (hbig : ∀ e < eCap, mem₀ (minH + e) ≤ L + 1)
    (h1z : ∀ x ∈ bucketsCat B j (L + 1 - j), mem₁ (minH + x) = 0)
    (h1fr : ∀ e < eCap, e ∉ bucketsCat B j (L + 1 - j) → mem₁ (minH + e) = mem₀ (minH + e)) :
    ∀ e < eCap, mem₁ (minH + e) = minHClear j (fun e => mem₀ (minH + e)) e := by
  intro e heC
  have hcat : e ∈ bucketsCat B j (L + 1 - j) ↔ j + 1 ≤ mem₀ (minH + e) := by
    simp only [bucketsCat, List.mem_flatMap, List.mem_range']
    constructor
    · rintro ⟨i, ⟨k, hk, rfl⟩, hi⟩
      have := ((hB (j + 1 * k) e (by omega) (by omega)).mp hi).2
      omega
    · intro h
      have := hbig e heC
      refine ⟨mem₀ (minH + e) - 1, ⟨mem₀ (minH + e) - 1 - j, by omega, by omega⟩, ?_⟩
      exact (hB _ e (by omega) (by omega)).mpr ⟨heC, by omega⟩
  simp only [minHClear]
  split_ifs with h
  · exact h1z e (hcat.mpr h)
  · exact h1fr e heC (fun h' => h (hcat.mp h'))

/-- `dsRebuildBucketsStmt` meets `dsRebuildBucketsContract`. -/
theorem dsRebuildBuckets_meetsContract (c : RBCtx) {p : Program}
    {bRB bC bF bPhase bOps bEdge : ℕ}
    (hpC : p.HasAt bC clearBucketsProcs)
    (hpP : p.HasAt bPhase (phaseProcs bOps bEdge)) (hpOps : p.HasAt bOps dgOpsProcs)
    (hpF : p.HasAt bF (fillLevelProcs bPhase))
    (hpRB : p.HasAt bRB (rebuildBucketsProcs bC bF)) :
    MeetsContract c.w p (bRB + rebuildBucketsIdx) (dsRebuildBucketsContract c) := by
  refine meetsContract_of_runs
    (hpRB.get (i := rebuildBucketsIdx) (by simp [rebuildBucketsProcs, rebuildBucketsIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, rfl⟩
  simp only [rebuildBucketsProcs, rebuildBucketsIdx, List.getElem_cons_zero]
  dsimp only [dsRebuildBucketsStmt]
  have hw16 := c.hw16
  have hbound := c.hbound
  have hjL := c.hjL
  have hdom := domGen_le₃ c.b c.L c.vCap c.eCap
  have hdom_eq := dsDomGenBase_eq c.b c.L c.vCap c.eCap
  have hn : dsHNextBase c.b c.vCap c.eCap = dsMinHBase c.b c.vCap c.eCap + c.eCap := rfl
  have hp : dsHPrevBase c.b c.vCap c.eCap = dsHNextBase c.b c.vCap c.eCap + c.eCap := rfl
  have hh : dsHHeadBase c.b c.vCap c.eCap = dsHPrevBase c.b c.vCap c.eCap + c.eCap := rfl
  have hd : dsHDegDummyBase c.b c.L c.vCap c.eCap =
    dsHHeadBase c.b c.vCap c.eCap + (c.L + 1) := rfl
  have hMb : c.b + dsHdrSize ≤ dsMinHBase c.b c.vCap c.eCap := by
    simp only [dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
  have dEB := c.dEB
  have hesB := c.hesB
  unfold IvlDisj at dEB
  set minH := dsMinHBase c.b c.vCap c.eCap with hminH
  set cat := bucketsCat c.B c.j (c.L + 1 - c.j) with hcat
  have hcatC : ∀ x ∈ cat, x < c.eCap := by
    intro x hx
    simp only [hcat, bucketsCat, List.mem_flatMap, List.mem_range'] at hx
    obtain ⟨i, ⟨k, hk, rfl⟩, hi⟩ := hx
    exact ((c.hBiff _ x (by omega)).mp hi).1
  -- Pass 1: clear the buckets of the levels `j..L`.
  let cc : CBCtx :=
    { w := c.w, eCap := c.eCap, B := c.B, lo := c.j, hi := c.L + 1,
      prevBase := dsHPrevBase c.b c.vCap c.eCap, nextBase := dsHNextBase c.b c.vCap c.eCap,
      headBase := dsHHeadBase c.b c.vCap c.eCap, degBase := dsHDegDummyBase c.b c.L c.vCap c.eCap,
      minH := minH, mem0 := c.mem0, hle := by omega, hw16 := hw16,
      hnB := by omega, hmB := by omega, hhB := by omega, hdB := by omega,
      dMN := by unfold IvlDisj; omega, dMH := by unfold IvlDisj; omega,
      dMD := by unfold IvlDisj; omega, dNH := by unfold IvlDisj; omega,
      dND := by unfold IvlDisj; omega, dHD := by unfold IvlDisj; omega,
      hB := fun i _ h2 => c.hBk i (by omega) }
  refine runs_start_le ?_
  refine runs_seq_call_le (vs := [dsHNextBase c.b c.vCap c.eCap, dsHHeadBase c.b c.vCap c.eCap,
      dsHDegDummyBase c.b c.L c.vCap c.eCap, c.j, c.L + 1, minH])
    (dsClearBuckets_meetsContract cc hpC) (by eval_expr)
    (fun v hv => hW v (by simp only [List.mem_cons] at hv ⊢; tauto)) ⟨rfl, rfl⟩ ?_
  rintro r₁ mem₁ pos₁ ⟨hz, hhd, hfr⟩
  simp only [cc] at hz hhd hfr
  have hfr1 : ∀ addr, (addr < minH ∨ dsDomGenBase c.b c.L c.vCap c.eCap ≤ addr) →
      mem₁ addr = c.mem0 addr := fun addr h =>
    hfr addr (fun x hx => by have := hcatC x hx; omega)
      (fun i' _ h2 => ⟨by show addr ≠ dsHHeadBase c.b c.vCap c.eCap + i'; omega,
        by show addr ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + i'; omega⟩)
  have h1fr : ∀ e < c.eCap, e ∉ cat → mem₁ (minH + e) = c.mem0 (minH + e) := fun e he hnc =>
    hfr _ (fun x hx h => hnc (by
      have : x = e := by omega
      exact this ▸ hx))
      (fun i' _ h2 => ⟨by show minH + e ≠ dsHHeadBase c.b c.vCap c.eCap + i'; omega,
        by show minH + e ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + i'; omega⟩)
  have hclr : ∀ e < c.eCap, mem₁ (minH + e) = minHClear c.j c.m0 e :=
    minH_after_clear (L := c.L) c.B (fun i e _ h2 => c.hBiff i e h2) c.hbig hz h1fr
  -- Pass 2: fill bucket `j`.
  let cf : FLCtx :=
    { w := c.w, L := c.L, vCap := c.vCap, eCap := c.eCap, b := c.b, j := c.j, es := c.es,
      esPtr := c.esPtr, B₀ := [], mem0 := mem₁, hw16 := hw16, hbound := hbound, hjL := hjL,
      hLw := (hfr1 _ (Or.inl (by simp only [dsLOff, dsHdrSize] at hMb ⊢; omega))).trans c.hLw,
      hvw := (hfr1 _ (Or.inl (by simp only [dsVCapOff, dsHdrSize] at hMb ⊢; omega))).trans c.hvw,
      hew := (hfr1 _ (Or.inl (by simp only [dsECapOff, dsHdrSize] at hMb ⊢; omega))).trans c.hew,
      hesB := hesB, dEB := c.dEB,
      hes := c.hes.congr fun k h1 h2 => hfr1 k (by omega),
      hnd := c.hnd, hesC := c.hesC,
      hdll := ⟨List.nodup_nil, by simp, by simpa using (hhd c.j le_rfl (by omega)).1, by simp⟩,
      hdeg := by simpa using (hhd c.j le_rfl (by omega)).2,
      hB₀ := by simp }
  refine runs_seq_call_le (vs := [c.b, c.j, c.esPtr, c.es.length, minH])
    (dsFillLevel_meetsContract cf hpP hpOps hpF) (by eval_expr)
    (fun v hv => hW v (by simp only [List.mem_cons] at hv ⊢; tauto)) ⟨rfl, rfl⟩ ?_
  rintro r₂ mem₂ pos₂ ⟨hdllj, hdegj, hset, hfr2⟩
  simp only [cf, List.append_nil] at hdllj hdegj hset hfr2
  set A := cf.added c.es with hAdef
  have hA : A = c.es.filter fun e => decide (minHClear c.j c.m0 e = 0) := by
    simp only [hAdef, FLCtx.added, cf]
    exact List.filter_congr fun e he => by
      simp only [decide_eq_decide]
      exact Iff.of_eq (congrArg (· = 0) (hclr e (c.hesC e he)))
  have hAC : ∀ x ∈ A, x < c.eCap := fun x hx => c.hesC x (List.mem_filter.mp hx).1
  have hA0 : ∀ x ∈ A, mem₁ (minH + x) = 0 := fun x hx => by
    have := (List.mem_filter.mp hx).2
    simpa [FLCtx.added, cf] using this
  -- The frame of pass 2, for the cells outside the bucket arrays of the new edges.
  have hfr2' : ∀ addr, (addr < minH ∨ dsDomGenBase c.b c.L c.vCap c.eCap ≤ addr) →
      mem₂ addr = mem₁ addr := fun addr h =>
    hfr2 addr (fun e he => by have := hAC e he; omega)
      (by show addr ≠ dsHHeadBase c.b c.vCap c.eCap + c.j; omega)
      (by show addr ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + c.j; omega)
      (fun x hx hxA => by
        have := hAC x (by simpa using hxA)
        omega)
      (fun x hx hxA => by
        have := hAC x (by simpa using hxA)
        omega)
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ⟨fun i hi => ?_, fun e he => ?_,
    fun addr h => (hfr2' addr h).trans (hfr1 addr h)⟩ ?_
  · -- The buckets.
    by_cases hij : i < c.j
    · -- A bucket below `j` keeps its cells.
      simp only [RBCtx.newB, hij, ite_true]
      obtain ⟨hdll0, hdeg0⟩ := c.hBk i hi
      have hBC : ∀ h ∈ c.B i, h < c.eCap := fun h hh => hdll0.2.1 h hh
      have hnotA : ∀ h ∈ c.B i, h ∉ A := fun h hhB hhA => by
        have hv := ((c.hBiff i h hi).mp hhB).2
        have h0 := hA0 h hhA
        rw [hclr h (hBC h hhB)] at h0
        simp only [minHClear, RBCtx.m0, hv] at h0
        split_ifs at h0 with h'; omega
      -- Agreement of pass 1 on the cells of the bucket.
      have hag1 : ∀ addr, minH + c.eCap ≤ addr →
          (∀ i', c.j ≤ i' → i' < c.L + 1 →
            addr ≠ dsHHeadBase c.b c.vCap c.eCap + i' ∧
            addr ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + i') →
          mem₁ addr = c.mem0 addr := fun addr h1 h2 =>
        hfr addr (fun x hx => by have := hcatC x hx; omega) h2
      have hag2 : ∀ addr, minH + c.eCap ≤ addr →
          addr ≠ dsHHeadBase c.b c.vCap c.eCap + c.j →
          addr ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + c.j →
          (∀ x, addr = dsHPrevBase c.b c.vCap c.eCap + x → x ∉ A) →
          (∀ x, addr = dsHNextBase c.b c.vCap c.eCap + x → x ∉ A) →
          mem₂ addr = mem₁ addr := fun addr h1 h2 h3 h4 h5 =>
        hfr2 addr (fun e he => by have := hAC e he; omega) h2 h3
          (fun x hx hxA => h4 x hx (by simpa using hxA))
          (fun x hx hxA => h5 x hx (by simpa using hxA))
      refine ⟨hdll0.of_agree ?_ (fun h hh => ?_) (fun h hh => ?_), ?_⟩
      · rw [hag2 _ (by omega) (by omega) (by omega)
          (fun x hx hxA => by have := hAC x hxA; omega)
          (fun x hx hxA => by have := hAC x hxA; omega)]
        exact hag1 _ (by omega) (fun i' h1 h2 => ⟨by omega, by omega⟩)
      · have := hBC h hh
        rw [hag2 _ (by omega) (by omega) (by omega)
          (fun x hx hxA => by
            have : x = h := by omega
            exact hnotA h hh (this ▸ hxA))
          (fun x hx hxA => by have := hAC x hxA; omega)]
        exact hag1 _ (by omega) (fun i' h1 h2 => ⟨by omega, by omega⟩)
      · have := hBC h hh
        rw [hag2 _ (by omega) (by omega) (by omega)
          (fun x hx hxA => by have := hAC x hxA; omega)
          (fun x hx hxA => by
            have : x = h := by omega
            exact hnotA h hh (this ▸ hxA))]
        exact hag1 _ (by omega) (fun i' h1 h2 => ⟨by omega, by omega⟩)
      · rw [hag2 _ (by omega) (by omega) (by omega)
          (fun x hx hxA => by have := hAC x hxA; omega)
          (fun x hx hxA => by have := hAC x hxA; omega)]
        rw [hag1 _ (by omega) (fun i' h1 h2 => ⟨by omega, by omega⟩)]
        exact hdeg0
    · by_cases hji : i = c.j
      · -- Bucket `j` holds the new edges.
        subst hji
        simp only [RBCtx.newB, lt_irrefl, ite_false, ite_true]
        rw [← hA]
        refine ⟨by simpa using hdllj, ?_⟩
        have := hdegj
        simp only [List.length_nil, Nat.add_zero] at this
        rw [List.length_reverse]
        exact this
      · -- A bucket above `j` is empty.
        simp only [RBCtx.newB, hij, hji, ite_false]
        obtain ⟨hh0, hd0⟩ := hhd i (by omega) (by omega)
        have hhead : mem₂ (dsHHeadBase c.b c.vCap c.eCap + i) = 0 := by
          rw [hfr2 _ (fun e he => by have := hAC e he; omega)
            (by show _ ≠ dsHHeadBase c.b c.vCap c.eCap + c.j; omega)
            (by show _ ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + c.j; omega)
            (fun x hx hxA => by have := hAC x (by simpa using hxA); omega)
            (fun x hx hxA => by have := hAC x (by simpa using hxA); omega)]
          exact hh0
        have hdeg : mem₂ (dsHDegDummyBase c.b c.L c.vCap c.eCap + i) = 0 := by
          rw [hfr2 _ (fun e he => by have := hAC e he; omega)
            (by show _ ≠ dsHHeadBase c.b c.vCap c.eCap + c.j; omega)
            (by show _ ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + c.j; omega)
            (fun x hx hxA => by have := hAC x (by simpa using hxA); omega)
            (fun x hx hxA => by have := hAC x (by simpa using hxA); omega)]
          exact hd0
        exact ⟨⟨List.nodup_nil, by simp, by simpa using hhead, by simp⟩, by simpa using hdeg⟩
  · -- The words.
    have h2set : ∀ e ∈ c.es.filter (fun e => decide (mem₁ (minH + e) = 0)),
        mem₂ (minH + e) = c.j + 1 := fun e he => hset e he
    have h2fr : ∀ e < c.eCap, e ∉ c.es.filter (fun e => decide (mem₁ (minH + e) = 0)) →
        mem₂ (minH + e) = mem₁ (minH + e) := fun e he hnA =>
      hfr2 _ (fun e' he' h => hnA (by
          have : e' = e := by have := hAC e' he'; omega
          exact this ▸ he'))
        (by show _ ≠ dsHHeadBase c.b c.vCap c.eCap + c.j; omega)
        (by show _ ≠ dsHDegDummyBase c.b c.L c.vCap c.eCap + c.j; omega)
        (fun x hx hxA => by omega)
        (fun x hx hxA => by omega)
    exact minH_after_passes (L := c.L) c.B c.es (fun i e _ h2 => c.hBiff i e h2) c.hbig hz h1fr
      h2set h2fr e he
  · simp only [Expr.size, argsSize, dsRebuildBucketsContract, dsClearBucketsContract,
      dsFillLevelContract, cc, cf]
    omega

/-- The membership clause of the buckets in `DynSpannerStateAt` after the rebuild: bucket `i` of
`RBCtx.newB` holds the edges of the new `H` (the levels below `j` and `E(J̃)`) whose new word is
`i + 1`. The words come from `dsRebuildBuckets_meetsContract`; the logic is
`bucketRebuild_spec`. Edges at or above `eCap` are in no bucket and in no level. -/
theorem newB_mem_iff (c : RBCtx) {H_mid : Fin (c.L + 1) → MGraph} {E : Finset ℕ} {m : ℕ → ℕ}
    {mem' : ℕ → ℕ}
    (hm : ∀ e < c.eCap, m e = c.m0 e) (hm0 : ∀ e, m e = 0 ↔ e ∉ E)
    (hmin : ∀ e ∈ E, ∃ i : Fin (c.L + 1), m e = i.1 + 1 ∧ e ∈ (H_mid i).E ∧
      ∀ k : Fin (c.L + 1), k.1 < i.1 → e ∉ (H_mid k).E)
    (hsub : unionEdgesLt H_mid c.j ⊆ E)
    (hEC : ∀ e ∈ E, e < c.eCap)
    (hw : ∀ e < c.eCap, mem' (dsMinHBase c.b c.vCap c.eCap + e) =
      minHRebuild c.j c.es.toFinset c.m0 e) :
    ∀ i ≤ c.L, ∀ e, e ∈ c.newB i ↔ e ∈ unionEdgesLt H_mid c.j ∪ c.es.toFinset ∧
      mem' (dsMinHBase c.b c.vCap c.eCap + e) = i + 1 := by
  -- The old buckets in terms of `m`.
  have hB : ∀ i ≤ c.L, ∀ e, e ∈ c.B i ↔ e ∈ E ∧ m e = i + 1 := by
    intro i hi e
    rw [c.hBiff i e hi]
    constructor
    · rintro ⟨heC, hv⟩
      have hm' : m e = i + 1 := by rw [hm e heC]; exact hv
      exact ⟨by by_contra h; have := (hm0 e).mpr h; omega, hm'⟩
    · rintro ⟨hE, hv⟩
      have heC := hEC e hE
      exact ⟨heC, (hm e heC).symm.trans hv⟩
  have hspec := bucketRebuild_spec c.hjL H_mid E m hm0 hmin hsub c.B hB c.es
  intro i hi e
  by_cases heC : e < c.eCap
  · -- Below `eCap` the words and the filter agree with those of `m`.
    have hcl : ∀ x ∈ c.es, minHClear c.j m x = minHClear c.j c.m0 x := fun x hx => by
      unfold minHClear; rw [hm x (c.hesC x hx)]
    have hfil : (c.es.filter fun e => decide (minHClear c.j c.m0 e = 0)) =
        c.es.filter fun e => decide (minHClear c.j m e = 0) :=
      List.filter_congr fun x hx => by rw [hcl x hx]
    have hreb : minHRebuild c.j c.es.toFinset c.m0 e = minHRebuild c.j c.es.toFinset m e := by
      unfold minHRebuild minHClear; rw [hm e heC]
    have := hspec i hi e
    simp only [RBCtx.newB, hfil] at this ⊢
    rw [hw e heC, hreb]
    exact this
  · -- At or above `eCap`: in no bucket, and not an edge.
    have hnot : e ∉ c.newB i := by
      intro h
      simp only [RBCtx.newB] at h
      split_ifs at h with h1 h2
      · exact heC ((c.hBiff i e hi).mp h).1
      · exact heC (c.hesC e (List.mem_filter.mp (List.mem_reverse.mp h)).1)
      · simp at h
    have hnE : e ∉ unionEdgesLt H_mid c.j ∪ c.es.toFinset := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact heC (hEC e (hsub h))
      · exact heC (c.hesC e (List.mem_toFinset.mp h))
    simp [hnot, hnE]

/-- The `minH` clause of `DynSpannerStateAt` after the rebuild, for the levels
`rebuildLevels H_mid Hj G' j` with `E(Hj)` the edges of the list `es`. The words come from
`dsRebuildBuckets_meetsContract`; the logic is `minHRebuild_spec`. -/
theorem minH_clause_new (c : RBCtx) {H_mid : Fin (c.L + 1) → MGraph} {Hj G' : MGraph}
    {E : Finset ℕ} {m : ℕ → ℕ} {mem' : ℕ → ℕ}
    (hm : ∀ e < c.eCap, m e = c.m0 e) (hm0 : ∀ e, m e = 0 ↔ e ∉ E)
    (hmin : ∀ e ∈ E, ∃ i : Fin (c.L + 1), m e = i.1 + 1 ∧ e ∈ (H_mid i).E ∧
      ∀ k : Fin (c.L + 1), k.1 < i.1 → e ∉ (H_mid k).E)
    (hsub : unionEdgesLt H_mid c.j ⊆ E) (hHj : Hj.E = c.es.toFinset)
    (hw : ∀ e < c.eCap, mem' (dsMinHBase c.b c.vCap c.eCap + e) =
      minHRebuild c.j c.es.toFinset c.m0 e) :
    ∀ e < c.eCap,
      (mem' (dsMinHBase c.b c.vCap c.eCap + e) = 0 ↔ e ∉ unionEdgesLt H_mid c.j ∪ Hj.E) ∧
      (e ∈ unionEdgesLt H_mid c.j ∪ Hj.E → ∃ i : Fin (c.L + 1),
        mem' (dsMinHBase c.b c.vCap c.eCap + e) = i.1 + 1 ∧
        e ∈ (rebuildLevels H_mid Hj G' c.j i).E ∧
        ∀ k : Fin (c.L + 1), k.1 < i.1 → e ∉ (rebuildLevels H_mid Hj G' c.j k).E) := by
  obtain ⟨h0, h1⟩ := minHRebuild_spec c.hjL H_mid Hj G' E m hm0 hmin hsub
  intro e heC
  -- Below `eCap` the new word is `minHRebuild` of `m`.
  have hreb : mem' (dsMinHBase c.b c.vCap c.eCap + e) = minHRebuild c.j Hj.E m e := by
    rw [hw e heC, hHj]
    unfold minHRebuild minHClear
    rw [hm e heC]
  rw [hreb]
  exact ⟨h0 e, h1 e⟩

/-- The buckets depend only on the words in `[minH, domGen)`. -/
lemma BucketsAt.of_agree_range {mem mem' : ℕ → ℕ} {L vCap eCap b : ℕ} {B : ℕ → List ℕ}
    (hB : BucketsAt mem L vCap eCap b B)
    (hagree : ∀ addr, dsMinHBase b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      mem' addr = mem addr) :
    BucketsAt mem' L vCap eCap b B := by
  intro i hi
  obtain ⟨hdll, hdeg⟩ := hB i hi
  have hn : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hp : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hh : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hd : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have hg : dsDomGenBase b L vCap eCap = dsHDegDummyBase b L vCap eCap + (L + 1) := rfl
  refine ⟨hdll.of_agree (hagree _ (by omega) (by omega))
    (fun x hx => by have := hdll.2.1 x hx; exact hagree _ (by omega) (by omega))
    (fun x hx => by have := hdll.2.1 x hx; exact hagree _ (by omega) (by omega)), ?_⟩
  rw [hagree _ (by omega) (by omega)]
  exact hdeg

/-- A context `RBCtx` moves to a memory that agrees with its memory on the header words
`[b, b + dsHdrSize)`, on `[minH, domGen)` and on the list `es`. -/
@[expose] def RBCtx.ofAgree (c : RBCtx) (mem : ℕ → ℕ)
    (hagree : ∀ addr, ((c.b ≤ addr ∧ addr < dsGPtr c.b) ∨
      (dsMinHBase c.b c.vCap c.eCap ≤ addr ∧ addr < dsDomGenBase c.b c.L c.vCap c.eCap) ∨
      (c.esPtr ≤ addr ∧ addr < c.esPtr + c.es.length)) → mem addr = c.mem0 addr) : RBCtx :=
  { c with
    mem0 := mem
    hLw := by
      rw [hagree _ (Or.inl ⟨by omega, by simp [dsGPtr, dsHdrSize, dsLOff]⟩)]; exact c.hLw
    hvw := by
      rw [hagree _ (Or.inl ⟨by omega, by simp [dsGPtr, dsHdrSize, dsVCapOff]⟩)]; exact c.hvw
    hew := by
      rw [hagree _ (Or.inl ⟨by omega, by simp [dsGPtr, dsHdrSize, dsECapOff]⟩)]; exact c.hew
    hes := c.hes.congr fun k h1 h2 => hagree _ (Or.inr (Or.inr ⟨h1, h2⟩))
    hBk := c.hBk.of_agree_range fun addr h1 h2 => hagree _ (Or.inr (Or.inl ⟨h1, h2⟩))
    hBiff := fun i e hi => by
      rw [c.hBiff i e hi]
      constructor
      · rintro ⟨heC, hv⟩
        refine ⟨heC, ?_⟩
        rw [hagree _ (Or.inr (Or.inl ⟨by omega, ?_⟩))]; · exact hv
        simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
        omega
      · rintro ⟨heC, hv⟩
        refine ⟨heC, ?_⟩
        rw [← hagree _ (Or.inr (Or.inl ⟨by omega, ?_⟩))]; · exact hv
        simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
        omega
    hbig := fun e he => by
      rw [hagree _ (Or.inr (Or.inl ⟨by omega, ?_⟩))]; · exact c.hbig e he
      simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
      omega }

end

end MinCostFlow.DynSpanner.Program
