module

public import MinCostFlow.SparseCore.Program.OutResetIns
public import MinCostFlow.DynSpanner.Program.DynGraphBatch

/-!
# The reset `outReset` meets its statement

This file puts the setup and the two loops of the reset together (`outReset_body_runs`). After
the first loop the stored graph has no edge and no end is marked. After the second loop the
stored graph has the edges of `Snew` with the ends they have in `Snew`, so it stores `Snew`
(`DynGraphAt.congr_ends`), and the marked ends are the ends of these edges. Each loop round costs
two tour calls and a constant, so the cost is the number of edges of both graphs times the log
factor. Each round takes at most two query spaces of new memory, and both graphs have at most
`eCap` edges, so the space is at most `4 eCap` query spaces. The statement of piece P7 follows for
every program that holds the reset and the graph edge procedures (`sig_outReset_runs_of`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- A graph stored with edges below `eCap` has at most `eCap` edges. -/
theorem MGraph.m_le_of_dynGraphAt {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) : G.m ≤ eCap :=
  calc G.m = G.E.card := rfl
    _ ≤ (Finset.range eCap).card :=
      Finset.card_le_card fun x hx => Finset.mem_range.mpr (hG.2.2.1 x hx)
    _ = eCap := Finset.card_range _

section Main

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- **The reset `outReset`.** -/
theorem outReset_body_runs (T : OutTourAt S w vCap eCap p nm sm fm lm)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) {f dgb bOps : ℕ}
    (hproc : p.procs[f]? = some (outResetBody sm dgb)) (hp : p.HasAt dgb (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) (Sold Snew : MGraph) (outH tourH g₂ h g : ℕ)
    (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hargs : ∀ a ∈ [outH, tourH, g₂, h], a < 2 ^ w)
    (hrepO : (outGraphRep vCap eCap).rep outH Sold g mem) (hrep : T.rep.rep tourH s tx mem)
    (hmarks : OutMarksOf s s.cord Sold.E) (hS₂ : DynGraphAt mem g₂ vCap eCap Snew)
    (hVeq : Snew.V = Sold.V)
    (hends : ∀ e ∈ Sold.E ∪ Snew.E, ∀ t : Bool, ∃ v < vCap, (e, t) ∈ s.cord v)
    (hfootO : ∀ a, (outGraphRep vCap eCap).foot outH g a → a < h)
    (hfoot : ∀ a, T.rep.foot tourH tx a → a < h) (hg₂h : g₂ + dynGraphSize vCap eCap ≤ h)
    (hdisjO : ∀ a, (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a)
    (hblk₂ : ∀ a, g₂ ≤ a → a < g₂ + dynGraphSize vCap eCap →
      ¬ (outGraphRep vCap eCap).foot outH g a ∧ ¬ T.rep.foot tourH tx a)
    (hz : ZeroFrom mem h) (hsp : h + outResetSpace S (2 * eCap) < 2 ^ w) :
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c tx' s',
      Runs w p ω body (startState [outH, tourH, g₂, h] mem pos) o st' c ∧
      (outGraphRep vCap eCap).rep outH Snew g st'.mem ∧
      T.rep.rep tourH s' tx' st'.mem ∧ OutMarksOf s' s.cord Snew.E ∧
      h ≤ o.value ∧ o.value ≤ h + outResetSpace S (2 * eCap) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a →
        st'.mem a = mem a) ∧
      (∀ a, T.rep.foot tourH tx' a → T.rep.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
      c + T.rep.phi tourH tx' st'.mem ≤
        1000 * (S.mul + 1) * (Sold.m + Snew.m + 1) * ordStoreLog eCap +
          T.rep.phi tourH tx mem := by
  obtain ⟨hgo, hsep, hG⟩ := hrepO
  have hhw := hargs h (by simp)
  have htour := hargs tourH (by simp)
  have hq := S.querySpace_ge
  -- the stored graph lies below `h`
  have hsize : 4 ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
  have hgh : g + dynGraphSize vCap eCap ≤ h := by
    have := hfootO (g + dynGraphSize vCap eCap - 1) (Or.inr ⟨by omega, by omega⟩)
    omega
  have hoh : outH < h := hfootO outH (Or.inl rfl)
  have hgw : g + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hg₂w : g₂ + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx a :=
    fun a h1 h2 => hdisjO a (Or.inr ⟨h1, h2⟩)
  have hw4 : 4 ≤ (vCap + eCap + 2) ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (vCap + eCap + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hw8 := rs_eight_le (w := w) (by omega)
  have hmO := MGraph.m_le_of_dynGraphAt hG
  have hmN := MGraph.m_le_of_dynGraphAt hS₂
  unfold outResetSpace at hsp ⊢
  have hsp1 : 2 * Sold.m * S.querySpace ≤ 2 * eCap * S.querySpace :=
    Nat.mul_le_mul_right _ (by omega)
  have hsp2 : 2 * Snew.m * S.querySpace ≤ 2 * eCap * S.querySpace :=
    Nat.mul_le_mul_right _ (by omega)
  have hsp3 : 2 * (2 * eCap) * S.querySpace = 2 * eCap * S.querySpace + 2 * eCap * S.querySpace :=
    by ring
  have hspace : h + 2 * Sold.m * S.querySpace + 2 * Snew.m * S.querySpace < 2 ^ w := by omega
  -- the setup
  have hv0 : mem g = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have he0 : mem (g + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  obtain ⟨st0, c0, hr0, hmem0, -, hR0, h70, hc0⟩ :=
    rsSetup_runs (p := p) (ω := ω) (tourH := tourH) (g₂ := g₂) (h := h) mem pos hgo hv0 he0 hw8
      hgw hg₂w
  -- the first loop
  have hI1 : RS1Inv T tourH g₂ g h tx mem s Sold (Sold.m, T.rep.phi tourH tx mem) st0 := by
    refine ⟨Sold, s, tx, ⟨by rw [hmem0]; exact hrep, by rw [hmem0, h70]; exact hz,
      by rw [h70], fun a ha => Or.inl ha, fun a _ _ _ => by rw [hmem0]⟩, by rw [hmem0], by
      rw [hmem0]; exact hG, rfl, subset_rfl, rfl, rfl, hmarks.2, hR0, by rw [h70]⟩
  obtain ⟨o1, st1, c1, hr1, r1, ⟨rfl, hI1'⟩, hc1⟩ :=
    rsDelLoop_runs T ω hp hpOps hfoot hgh hdisj
      (fun e he t => hends e (Finset.mem_union_left _ he) t) hw htour hgw (by omega) _ st0 hI1
  obtain ⟨G₁, s₁, tx₁, hF₁, hphi₁, hG₁, hV₁, -, hm₁, hcord₁, hmarks₁, hR₁, hcur₁⟩ := hI1'
  dsimp only at hphi₁ hm₁ hcur₁
  -- the count of the new graph
  have hg₂blk : ∀ a, g₂ ≤ a → a < g₂ + dynGraphSize vCap eCap →
      a < h ∧ ¬ (g ≤ a ∧ a < g + dynGraphSize vCap eCap) ∧ ¬ T.rep.foot tourH tx a := by
    intro a h1 h2
    obtain ⟨hn1, hn2⟩ := hblk₂ a h1 h2
    exact ⟨by omega, fun hh => hn1 (Or.inr hh), hn2⟩
  have hm₂ : st1.mem (g₂ + 3) = Snew.m := by
    obtain ⟨hah, hag, haf⟩ := hg₂blk (g₂ + 3) (by omega) (by omega)
    rw [hF₁.2.2.2.2 _ hah hag haf]
    simpa [dgMOff] using hS₂.2.2.2.2.2.2.1
  have ha13 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 13) (st := st1)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hR₁.2.1)
      (Expr.eval_const (k := 3) (by omega)) (by omega)) hm₂)
  set st2 : State := { st1 with regs := Function.update st1.regs 13 Snew.m } with hst2
  -- the second loop
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨eL₂, heL_len, heL_nd, heL_mem, heL_at, -⟩, -, -⟩ :=
    id hS₂
  have hE₁ : G₁.E = ∅ := Finset.card_eq_zero.mp hm₁
  have hI2 : RS2Inv T tourH g₂ g h tx mem s Sold Snew eL₂ (Snew.m, r1) st2 := by
    refine ⟨G₁, s₁, tx₁, hF₁, hphi₁, hG₁, hV₁, ?_, ?_, hcord₁, hmarks₁, ?_, by simp [hst2],
      by dsimp only; omega, ?_⟩
    · intro e
      rw [hE₁, ← heL_len, List.drop_length]
      simp
    · intro e he; rw [hE₁] at he; simp at he
    · exact hR₁.of_regs fun r _ _ _ _ h13 _ _ => by simp [hst2, Function.update_of_ne h13]
    · dsimp only
      show st1.regs 7 + _ ≤ _
      omega
  obtain ⟨o3, st3, c3, hr3, r3, ⟨rfl, hI3⟩, hc3⟩ :=
    rsInsLoop_runs T ω hp hpOps hfoot hgh hdisj hS₂ hVeq heL_len heL_nd heL_mem heL_at hg₂blk
      (fun e he t => hends e (Finset.mem_union_right _ he) t) hw htour hgw hg₂w hspace _ st2 hI2
  obtain ⟨G₃, s₃, tx₃, hF₃, hphi₃, hG₃, hV₃, hGE₃, hGends₃, hcord₃, hmarks₃, -, -, -, hcur₃⟩ :=
    hI3
  dsimp only at hphi₃ hGE₃ hcur₃
  -- the return
  have hret : Runs w p ω (.ret (.reg 7)) st3 (.returned (st3.regs 7)) st3 2 :=
    runs_ret_iff.mpr ⟨st3.regs 7, Expr.eval_reg w 7 st3, rfl, rfl, rfl⟩
  have hrun := runs_seq_normal hr0 (runs_seq_normal hr1 (runs_seq_normal ha13
    (runs_seq_normal hr3 hret)))
  -- the stored graph is `Snew`
  have hE₃ : G₃.E = Snew.E := by
    ext e; rw [hGE₃ e, List.drop_zero, heL_mem]
  have hGS : DynGraphAt st3.mem g vCap eCap Snew :=
    DynGraphAt.congr_ends (by rw [hV₃, hVeq]) hE₃ hGends₃ hG₃
  obtain ⟨hrep₃, hz₃, hcurh, hft₃, hfr₃⟩ := hF₃
  have hframe : ∀ a < h, ¬ (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a →
      st3.mem a = mem a := fun a ha hn hn' => hfr₃ a ha (fun hh => hn (Or.inr hh)) hn'
  have hgo₃ : st3.mem outH = g := by
    rw [hfr₃ outH hoh (fun ⟨h1, h2⟩ => by rcases hsep with hs | hs <;> omega)
      (hdisjO outH (Or.inl rfl))]
    exact hgo
  refine ⟨_, hproc, _, st3, _, tx₃, s₃, hrun, ⟨hgo₃, hsep, hGS⟩, hrep₃,
    ⟨hcord₃, fun z => by rw [hmarks₃ z, hE₃]⟩, hcurh, ?_, hz₃, hframe, hft₃, ?_⟩
  · show st3.regs 7 ≤ _
    omega
  · -- the cost
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at hc1 hc3 ⊢
    rw [hphi₃]
    have hL : 1 ≤ ordStoreLog eCap := by unfold ordStoreLog; omega
    set X := S.mul * ordStoreLog eCap with hX
    have f1 : (2 * X + 500) * Sold.m ≤ 2 * (X * Sold.m) + 520 * Sold.m := by
      rw [add_mul, mul_assoc]; omega
    have f2 : (2 * X + 520) * Snew.m = 2 * (X * Snew.m) + 520 * Snew.m := by ring
    have f3 : 1000 * (S.mul + 1) * (Sold.m + Snew.m + 1) * ordStoreLog eCap =
        1000 * (X * Sold.m) + 1000 * (X * Snew.m) + 1000 * X +
          1000 * ((Sold.m + Snew.m + 1) * ordStoreLog eCap) := by
      rw [hX]; ring
    have f4 : Sold.m + Snew.m + 1 ≤ (Sold.m + Snew.m + 1) * ordStoreLog eCap :=
      Nat.le_mul_of_pos_right _ hL
    omega

end Main

/-- **The statement of the reset**, for every program whose procedure `idx b` is the reset with
the tour procedure `sm` and the graph edge procedures at `dgb b` (which call the graph
procedures at `ops b`). -/
theorem sig_outReset_runs_of (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (idx dgb ops : ℕ → ℕ)
    (hH : ∀ p b nm sm fm lm, HasOutProcs p b nm sm fm lm →
      p.procs[idx b]? = some (outResetBody sm (dgb b)) ∧ p.HasAt (dgb b) (dgEdgeProcs (ops b)) ∧
        p.HasAt (ops b) dgOpsProcs) :
    sig_outReset_runs HasOutProcs idx := by
  refine ⟨1000, ?_⟩
  intro S w vCap eCap p b nm sm fm lm hP hw T Sold Snew outH tourH g₂ h g s tx mem pos ω
  obtain ⟨hproc, hp, hpOps⟩ := hH p b nm sm fm lm hP
  exact outReset_body_runs T hw hproc hp hpOps Sold Snew outH tourH g₂ h g s tx mem pos ω

end MinCostFlow.SparseCore.Program
