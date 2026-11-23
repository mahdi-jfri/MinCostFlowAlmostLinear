module

public import MinCostFlow.HierPaths.QueryProgBegin
public import MinCostFlow.HierPaths.QueryProgFill
public import MinCostFlow.HierPaths.QueryProgFinish

/-!
# The GetPath procedure contract

The input buffers hold the two attachments and the route. Loop erasure restores the
position table and leaves the model's simple walk at the heap pointer. The returned
pointer marks the end of the output, after which memory is zero.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM Spanner

private theorem zip_steps_parts (ss : List (ℕ × ℕ)) :
    (ss.map Prod.fst).zip (ss.map Prod.snd) = ss := by
  induction ss with
  | nil => rfl
  | cons p ss ih => cases p; simp [ih]

private theorem queryHelperAt {p : Program} {j f : ℕ} (hp : hierQueryProc.At p j f) :
    p.procs[f]? = some (attachProc (f + 1) (f + 2)) ∧
    p.procs[f + 1]? = some entryWordProc ∧ p.procs[f + 2]? = some copyProc ∧
    p.procs[f + 3]? = some (routeProc (f + 3) (f + 4) (f + 2)) ∧
    p.procs[f + 4]? = some pickProc ∧ p.procs[f + 5]? = some eraseProc ∧
    p.procs[f + 6]? = some (writeWalkProc (f + 7)) ∧
    p.procs[f + 7]? = some copyListBody ∧ p.procs[f + 8]? = some zeroProc := by
  have h := hp.2
  have hlen : (hierQueryProc.helpers f).length = 9 := rfl
  exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega), h 8 (by omega)⟩

private theorem querySupport_length_le {a v : ℕ} (X : HierConcrete) (h : X.H.Rel a X.ms)
    (hG : X.ms.abs.G.IsValid) (hv : v ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) :
    attachmentLength (X.H.entryAt X.ms.st v) ≤ X.H.lam := by
  have he := (X.query_support h hG hv).2.1
  cases hEntry : X.H.entryAt X.ms.st v with
  | term t => exact Nat.zero_le _
  | onWalk c k =>
    have he' : SupportEntry.onWalk c k ∈ X.H.A.C.supportArray v := hEntry ▸ he
    obtain ⟨hc, _, hk⟩ := support_onWalk_bounds X.H.A.C h.spec.arrays.fits he'
    exact hk.trans (h.spec.walkLen c hc)

private theorem heap_above_layout {X : HierConcrete} {b out : ℕ}
    (h : ∀ z, b ≤ z ∧ z < b + X.encode.length → z < out) : b + X.encode.length ≤ out := by
  have hlen : 25 ≤ X.encode.length := by simp [HierConcrete.encode, layoutList, csrList, csrOffsets]
  have h' := h (b + X.encode.length - 1) ⟨by omega, by omega⟩
  omega

set_option maxHeartbeats 4000000 in
/-- A run of the complete query body produces the model's walk and restores the heap. -/
theorem queryEntry_runs {w a : ℕ} {p : Program} {j f : ℕ} (hp : hierQueryProc.At p j f)
    (X : HierConcrete) (hrel : X.H.Rel a X.ms) (hG : X.ms.abs.G.IsValid)
    {u v b out pos : ℕ} {mem : ℕ → ℕ} (ω : ℕ → Bool)
    (hu : u ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) (hv : v ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat)
    (hL : ListAt mem b X.encode) (hblock : b + X.encode.length ≤ out)
    (hzero : ZeroFrom mem out)
    (hm : X.m ≤ X.ms.abs.M)
    (hw : out + 6 * gammaHP a (Nat.ceil (1 / X.ms.abs.φ_in)) X.ms.abs.M + 3 < 2 ^ w) :
    ∃ out' st' cost,
      Runs w p ω (queryEntryProc f) (startState [b, u, v, out] mem pos) (.returned out') st' cost ∧
      WalkAt st'.mem out (X.H.getPath X.ms u v) ∧ (∀ z < out, st'.mem z = mem z) ∧
      ZeroFrom st'.mem out' ∧ out ≤ out' ∧
      out' ≤ out + 6 * gammaHP a (Nat.ceil (1 / X.ms.abs.φ_in)) X.ms.abs.M + 3 ∧
      cost ≤ 10000 * gammaHP a (Nat.ceil (1 / X.ms.abs.φ_in)) X.ms.abs.M := by
  obtain ⟨hA, hE, hC, hR, hP, hErase, hWrite, hList, hZero⟩ := queryHelperAt hp
  let cap := X.queryCapacity
  let d := Nat.ceil (1 / X.ms.abs.φ_in)
  let Γ := gammaHP a d X.ms.abs.M
  let inE := out + (2 * cap + 3)
  let inY := inE + cap
  let stE := inY + cap
  let stY := stE + cap
  let ss := Walk.steps (X.queryInputWalk u v)
  let E := ss.map Prod.fst
  let Y := ss.map Prod.snd
  let res := arrFrom u [] (E.zip Y)
  let out' := out + 2 * res.length + 3
  have hcalc : 2 ^ X.depth ≤ Γ := by
    apply le_trans _ (queryFactor_le_gamma a d hm)
    unfold queryFactor
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hrel.fits.depth).trans
      (Nat.le_mul_of_pos_right _ (by omega))
  have hcap := X.queryCapacity_le_gamma hrel.fits hm
  have hdepthW : 2 ^ X.depth + 1 < 2 ^ w := by change out + 6 * Γ + 3 < 2 ^ w at hw; omega
  have hwEnd : out + 6 * cap + 3 < 2 ^ w := by
    change cap ≤ Γ at hcap
    change out + 6 * Γ + 3 < 2 ^ w at hw
    omega
  have hwScratch : inE + 4 * cap < 2 ^ w := by dsimp [inE]; omega
  have hBelowE : b + X.encode.length ≤ inE := by dsimp [inE]; omega
  have hBelowW : b + X.encode.length < 2 ^ w := by omega
  have huN := (X.query_support hrel hG hu).1
  have hlen : E.length = ss.length := List.length_map _
  have hlenY : Y.length = E.length := by simp [E, Y]
  have hK : E.length ≤ cap := by
    rw [hlen]
    exact (X.queryInputWalk_stepBounds hrel hG hu hv).1
  have hRes : res.length ≤ E.length := by
    simpa [res, List.length_zip, hlenY] using length_arrFrom_le u [] (E.zip Y)
  have hPath : ofSteps u res = X.H.getPath X.ms u v := by
    dsimp only [res, E, Y]
    rw [zip_steps_parts]
    exact X.queryInputWalk_erase hrel hG hu hv
  have hlenBlock : 25 ≤ X.encode.length := by simp [HierConcrete.encode, layoutList, csrList, csrOffsets]
  have h4 : 4 < 2 ^ w := by omega
  obtain ⟨hPos, hPosEnd⟩ := block_sec hL (i := 22) (by decide)
  let posA := b + 25 + mem (b + 22)
  change ListAt mem posA (List.replicate X.n 0) at hPos
  change posA + (List.replicate X.n 0).length ≤ _ at hPosEnd
  rw [List.length_replicate] at hPosEnd
  have hpEnd : posA + X.n ≤ out := hPosEnd.trans hblock
  have hNear := queryBegin_triple (p := p) (u := u) (v := v) (pos := pos) hL hblock hdepthW hwEnd
  suffices hrun : ∃ o st' cost,
      Runs w p ω (queryEntryProc f) (startState [b, u, v, out] mem pos) o st' cost ∧
      (o = .returned out' ∧ WalkAt st'.mem out (X.H.getPath X.ms u v) ∧
        (∀ z < out, st'.mem z = mem z) ∧ ZeroFrom st'.mem out') ∧
      0 + cost ≤ 10000 * Γ by
    obtain ⟨o, st', cost, hrun, ⟨rfl, hWalk, hf, hz⟩, hc⟩ := hrun
    refine ⟨out', st', cost, hrun, hWalk, hf, hz, ?_, ?_, by rw [Nat.zero_add] at hc; exact hc⟩
    · dsimp [out']; omega
    · change out + 2 * res.length + 3 ≤ out + 6 * Γ + 3
      change cap ≤ Γ at hcap
      omega
  unfold queryEntryProc
  refine runs_seq_triple_le hNear rfl ?_
  intro st₁ hreg
  obtain ⟨hm₁, h0, h1, h2, h3, h4D, h5, h6, h7, h8, h9, h10⟩ := hreg
  have hFill := queryFill_triple (p := p) hA hE hC hR hP hrel hG hu hv
    hBelowE (inY := inY) le_rfl (show inY + cap < 2 ^ w by dsimp [inY]; omega)
    (mem := mem) (regs := st₁.regs)
  refine runs_seq_triple_le hFill ⟨hm₁, rfl, hL, ⟨h0, h1, h2, h4D, h7, h8⟩⟩ ?_
  intro st₂ ⟨hEA, hYA, h18, hregs, hf₂⟩
  have h0' : st₂.regs 0 = b := (hregs 0 (by decide)).trans h0
  have hL₂ : ListAt st₂.mem b X.encode := hL.congr fun z _ hz =>
    hf₂ z (Or.inl (hz.trans_le hBelowE))
  have hposEval : (secExpr 22).eval w st₂ = some posA := by
    rw [eval_querySection hL₂ h0' (by decide) hBelowW, hf₂ (b + 22) (Or.inl (by omega))]
  have hPos₂ : ∀ x < X.n, st₂.mem (posA + x) = 0 := by
    intro x hx
    rw [hf₂ _ (Or.inl (by dsimp [inE]; omega))]
    exact (listAt_replicate.mp hPos) x hx
  have hM : EraseMem inE inY u posA stE stY X.n E Y st₂.mem := by
    refine ⟨hlenY, hEA, hYA, ?_, huN, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
      exact (X.queryInputWalk_stepBounds hrel hG hu hv).2 q hq
    all_goals
      (try (intro i hi; unfold EraseOutside))
      dsimp [inE, inY, stE, stY] at *
      omega
  have hsR : QueryFinishRegs st₂ u out cap inE inY stE stY E.length :=
    ⟨(hregs 1 (by decide)).trans h1, (hregs 3 (by decide)).trans h3,
      (hregs 6 (by decide)).trans h6, (hregs 7 (by decide)).trans h7,
      (hregs 8 (by decide)).trans h8, (hregs 9 (by decide)).trans h9,
      (hregs 10 (by decide)).trans h10, h18.trans hlen.symm⟩
  obtain ⟨st₃, cc, hrun, hWalk, hbelow, hz, hcost⟩ := queryFinish_runs hErase hWrite hList hZero ω
    hsR hposEval hM hPos₂ (fun z hz hi => (hf₂ z (Or.inl hi)).trans (hzero z hz))
    (fun z hz => (hf₂ z (Or.inr (by dsimp [inY]; omega))).trans
      (hzero z (by dsimp [inE] at hz; omega)))
    hK hpEnd (by dsimp [inE]; omega) rfl rfl rfl hwScratch h4
  refine ⟨.returned out', st₃, cc, hrun, ⟨rfl, hPath ▸ hWalk, ?_, hz⟩, ?_⟩
  · intro z hz
    exact (hbelow z hz).trans (hf₂ z (Or.inl (by dsimp [inE]; omega)))
  · have hChoice := X.tablePick_isConnectorChoice hrel.spec.arrays hrel.spec.pairs hrel.inv
    have ht := (X.query_support hrel hG hu).2.2.2.1
    have ht' := (X.query_support hrel hG hv).2.2.2.1
    have hr := X.H.A.C.routeOps_le _ _ hrel.spec.arrays.fits hChoice hrel.spec.walkLen
      X.depth 0 _ _ ht ht' (X.query_same_root hrel ht ht')
    have hc := queryHelper_cost_le (a := a) (d := d) hm hrel.fits.depth hrel.fits.lam
      (le_rfl : cap ≤ (2 ^ X.depth + 1) * X.H.lam)
      (Nat.le_trans (Nat.le_add_right _ _) hr) hK
      (querySupport_length_le X hrel hG hu) (querySupport_length_le X hrel hG hv)
    change _ + cc ≤ 10000 * Γ
    omega

/-- The deterministic GetPath procedure meets operation 1 of the path data structure. -/
theorem hierQueryProc_spec (a : ℕ) : QueryProcSpec a hierQueryProc 10000 (hierQuerySpace a) 9 1 1 := by
  refine ⟨hierQueryProc_noRand, by norm_num, hierQuerySpace_form a, ?_⟩
  intro hc hcost hspace _ w p j f hp
  intro b s X args mem pos ω _ hhead hrep hpre hfoot hzero hroom
  obtain ⟨b', u, v, out, rfl, hValid, hu, hv, _⟩ := hpre
  have hbb : b' = b := Option.some.inj hhead
  subst b'
  obtain ⟨hs, hrel, hL⟩ := hrep
  subst s
  have hValidFacts := hValid
  obtain ⟨hφ₁, hφ₂, hG, _, hm, _⟩ := hValidFacts
  have hheap : heapArg [b, u, v, out] = out := rfl
  have hSize : (pathDSDataStructure hc.params w).space 1 X.ms.abs [b, u, v, out] mem =
      6 * gammaHP a (Nat.ceil (1 / X.ms.abs.φ_in)) X.ms.abs.M + 3 := by
    change hc.querySpace X.ms.abs.phiNum X.ms.abs.phiDen X.n X.m X.ms.abs.M = _
    rw [hspace, hierQuerySpace]
    rw [PathDSAbsState.φ_in, nat_ceil_div_eq hφ₁ hφ₂]
  rw [hheap, hSize] at hroom
  rw [hheap] at hzero
  have hblock := heap_above_layout (X := X) (b := b) (out := out) hfoot
  obtain ⟨out', st', c, hRun, hWalk, hBelow, hZero, hOut, hBound, hcRun⟩ :=
    queryEntry_runs hp X hrel hG ω hu hv hL hblock hzero hm hroom
  have hParams : IsHierParams a hc.params := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩
  obtain ⟨hIsWalk, hNoDup, hNoDel, hLive, hLen, _⟩ :=
    X.H.model_getPath hParams hrel hValid hu hv
  have hL' : ListAt st'.mem b X.encode := hL.congr fun z _ hz =>
    hBelow z (hz.trans_le hblock)
  refine ⟨queryEntryProc f, hp.1, .returned out', st', c, hRun, X.ms.abs, X,
    ⟨rfl, hrel, hL'⟩, ?_, ?_, ?_⟩
  · exact ⟨b, u, v, out, rfl, rfl, X.H.getPath X.ms u v, hWalk,
      hIsWalk, hNoDup, hNoDel, hLive, hLen⟩
  · rw [hheap, hSize]
    exact ⟨hOut, hBound, hZero, fun z hz _ => hBelow z hz, fun _ hz => Or.inl hz⟩
  · change c + hierPhiScale * X.potential ≤
      Nat.ceil (hc.K_query * (gammaHP a (Nat.ceil (1 / X.ms.abs.φ_in)) X.ms.abs.M : ℝ)) +
      hierPhiScale * X.potential
    rw [hcost]
    apply Nat.add_le_add_right
    have hcast : (10000 : ℝ) * (gammaHP a (Nat.ceil (1 / X.ms.abs.φ_in)) X.ms.abs.M : ℝ) =
        ((10000 * gammaHP a (Nat.ceil (1 / X.ms.abs.φ_in)) X.ms.abs.M : ℕ) : ℝ) := by norm_cast
    rw [hcast, Nat.ceil_natCast]
    exact hcRun

end MinCostFlow.HierPaths
