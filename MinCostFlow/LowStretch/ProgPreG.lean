module

public import MinCostFlow.LowStretch.ProgPreK
public import MinCostFlow.LowStretch.ProgKOrder
public import MinCostFlow.LowStretch.ProgLca

/-!
# The preprocessing, part 3: heavy paths and the lowest common nodes

`gP` takes the merge tree `T` that `kP` wrote. It computes the sizes, the leaf order and the
heavy-path heads of the nodes (`koP`), the lowest common node of the two ends of every pair
(`lcaAll`), and groups the pairs by this node (`csrB`) (`gP_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- `gP` with `args = [n, m, N]`; `koP`, `lcaAll` and `csrB` sit at `bKo`, `bLca` and `bCsr`. -/
def gP (bKo bLca bCsr : ℕ) : Stmt :=
  .seq (.call 4 bKo [.reg 0, .reg 2, lin 9 9 7, lin 9 9 9, lin 9 9 11, lin 9 9 17, lin 9 9 19,
    lin 9 9 21, lin 9 9 23])
  (.seq (.call 4 bLca [.reg 1, .const 2, lin 9 9 7, lin 9 9 21, lin 9 9 24, .reg 0])
  (.seq (.call 4 bCsr [lin 9 9 24, .reg 1, .reg 2, lin 9 10 24, lin 10 10 26, lin 10 10 28])
  (.ret (.const 0))))

theorem gP_noRand (bKo bLca bCsr : ℕ) : (gP bKo bLca bCsr).NoRand := by
  simp [gP, lin, Stmt.NoRand]

/-- The cost of `gP`. -/
def gCost (G : WGraph) : ℕ := 1000 * (G.m + G.n + 1) + G.m * (80 * Nat.log 2 G.n + 200)

/-- The merge tree `T` of `G` is in memory, as `kP` leaves it. -/
structure TreeIn (w : ℕ) (G : WGraph) (T : KT) (mem : ℕ → ℕ) : Prop where
  input : InG w G mem
  ok : T.Ok (pgOf G)
  N_le : T.N ≤ 2 * G.n
  par : ∀ k < T.N, mem (aKPAR G.n G.m + k) = T.par k ∧ mem (aKMW G.n G.m + k) = T.mw k
  ch : ∀ k, G.n ≤ k → k < T.N → mem (aKCH1 G.n G.m + k) = T.ch1 k ∧
    mem (aKCH2 G.n G.m + k) = T.ch2 k ∧ mem (aKMP G.n G.m + k) = T.mp k

/-- The contract of `gP` for the graph `G` and its merge tree `T`. -/
def gC (w : ℕ) (G : WGraph) (T : KT) : Contract where
  pre args mem := args = [G.n, G.m, T.N] ∧ TreeIn w G T mem
  post _ mem _ mem' :=
    (∀ k < T.N, mem' (aKSZ G.n G.m + k) = T.sz (pgOf G) k ∧
      mem' (aKLO G.n G.m + k) = T.lo (pgOf G) k ∧ mem' (aHEAD G.n G.m + k) = T.hd (pgOf G) k) ∧
    (∀ v < G.n, mem' (aORDL G.n G.m + T.lo (pgOf G) v) = v) ∧
    (∀ q < G.m, T.IsLca ((pgOf G).pu q) ((pgOf G).pv q) (mem' (aLCA G.n G.m + q))) ∧
    (∀ u ≤ T.N, mem' (aGOFF G.n G.m + u) = offOf (fun q => mem' (aLCA G.n G.m + q)) G.m u) ∧
    (∀ u < T.N, ∀ j < (grp (fun q => mem' (aLCA G.n G.m + q)) G.m u).length,
      mem' (aGORD G.n G.m + offOf (fun q => mem' (aLCA G.n G.m + q)) G.m u + j) =
        (grp (fun q => mem' (aLCA G.n G.m + q)) G.m u).getD j 0) ∧
    ∀ a, (a < aKSZ G.n G.m ∨ aCTL G.n G.m ≤ a) → mem' a = mem a
  cost _ _ := gCost G

theorem gP_spec {w : ℕ} {p : Program} {b bKo bLca bCsr : ℕ} {G : WGraph} {T : KT}
    (hp : p.HasAt b [gP bKo bLca bCsr]) (hKo : MeetsContract w p bKo (koC w T (pgOf G)))
    (hLca : MeetsContract w p bLca (lcaAC w T (pgOf G))) (hCsr : MeetsContract w p bCsr (csrC w)) :
    MeetsContract w p b (gC w G T) := by
  intro args mem pos ω _ hpre
  obtain ⟨rfl, hT⟩ := hpre
  have hproc : p.procs[b]? = some (gP bKo bLca bCsr) := hp 0 (by simp)
  refine ⟨_, hproc, ?_⟩
  have hG := hT.input
  have hw := hG.add_lt
  have hn1 := hG.one_le
  have hN := hT.N_le
  have hnN : G.n < T.N := hT.ok.n_lt
  simp only [aH] at hw
  have hends := hG.ends
  have hpG : ∀ q < G.m, (pgOf G).pu q < G.n ∧ (pgOf G).pv q < G.n := fun q hq =>
    ⟨(hG.allowed.fit.ok q (by rw [pgOf_m]; exact hq)).1,
      (hG.allowed.fit.ok q (by rw [pgOf_m]; exact hq)).2.1⟩
  dsimp only [gP, lin]
  refine runs_start_le ?_
  -- sizes, leaf order and heads
  wram_step
  · exact ⟨⟨G.n, T.N, _, _, _, _, _, _, _⟩, rfl, ⟨hT.ok, rfl, rfl,
      fun k hk => by simp only [startState]; have := (hT.par k hk).1; unfold aKPAR at this; simpa using this,
      fun k h1 h2 => by
        simp only [startState]; have := hT.ch k h1 h2; unfold aKCH1 aKCH2 at this; simpa using And.intro this.1 this.2.1,
      by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega,
      by simp only; omega⟩⟩
  intro v1 mem1 pos1 h1
  obtain ⟨h1a, h1b, h1c⟩ := h1 ⟨G.n, T.N, _, _, _, _, _, _, _⟩ rfl
  simp only [startState] at h1a h1b h1c
  have hin1 : ∀ a < 9 + 9 * G.m + 17 * G.n, mem1 a = mem a := fun a ha => h1c a (Or.inl ha)
  -- the lowest common nodes
  wram_step
  · refine ⟨2, 9 + 9 * G.m + 7 * G.n, 9 + 9 * G.m + 21 * G.n, 9 + 9 * G.m + 24 * G.n,
      by simp [pgOf_m]; rfl, ⟨hT.ok, fun k hk => ⟨?_, ?_⟩, by omega, by omega⟩,
      fun q hq => ?_, fun q hq => ?_, by simp [pgOf_m]; omega, by omega, by omega,
      by simp [pgOf_m]; omega⟩
    · show mem1 _ = _; rw [hin1 _ (by omega)]
      have := (hT.par k hk).1; unfold aKPAR at this; simpa using this
    · show mem1 _ = _; have := (h1a k hk).2.2; simpa using this
    · rw [pgOf_m] at hq
      show mem1 _ = _ ∧ mem1 _ = _
      rw [hin1 _ (by omega), hin1 _ (by omega)]; exact hends q hq
    · rw [pgOf_m] at hq; exact hpG q hq
  intro v2 mem2 pos2 h2
  obtain ⟨h2a, h2b⟩ := h2 2 (9 + 9 * G.m + 7 * G.n) (9 + 9 * G.m + 21 * G.n)
    (9 + 9 * G.m + 24 * G.n) (by simp [pgOf_m]; rfl)
  rw [pgOf_m] at h2a h2b
  have hlt : ∀ q < G.m, mem2 (9 + 9 * G.m + 24 * G.n + q) < T.N := fun q hq =>
    (h2a q hq).1.lt_N hT.ok (by have := (hpG q hq).1; omega)
  -- the groups by the lowest common node
  wram_step
  · exact ⟨_, _, _, _, _, _, rfl, fun i hi => hlt i hi, by omega, by omega, by omega, by omega⟩
  intro v3 mem3 pos3 h3
  obtain ⟨h3a, h3b, h3c⟩ := h3
  simp only [List.getD_cons_zero, List.getD_cons_succ, csrOut] at h3a h3b h3c
  have e32 : ∀ a < 9 + 10 * G.m + 24 * G.n, mem3 a = mem2 a := fun a ha => h3c a (by omega)
  have e21 : ∀ a < 9 + 9 * G.m + 24 * G.n, mem2 a = mem1 a := fun a ha => h2b a (Or.inl ha)
  have hf : ∀ q < G.m, (fun i => mem2 (9 + 9 * G.m + 24 * G.n + i)) q =
      (fun q => mem3 (aLCA G.n G.m + q)) q := fun q hq => by
    simp only; unfold aLCA; rw [e32 _ (by omega)]
  wram_step
  · dsimp only
    refine ⟨fun k hk => ?_, fun v hv => ?_, fun q hq => ?_, fun u hu => ?_, fun u hu j hj => ?_,
      fun a ha => ?_⟩
    · obtain ⟨a1, a2, a3⟩ := h1a k hk
      unfold aKSZ aKLO aHEAD
      rw [e32 _ (by omega), e32 _ (by omega), e32 _ (by omega), e21 _ (by omega),
        e21 _ (by omega), e21 _ (by omega)]
      exact ⟨a1, a2, a3⟩
    · have hlo : T.lo (pgOf G) v < G.n := KT.lo_lt hT.ok hv
      unfold aORDL
      rw [e32 _ (by omega), e21 _ (by omega)]
      exact h1b v hv
    · unfold aLCA; rw [e32 _ (by omega)]; exact h2a q hq
    · rw [← offOf_congr hf]; unfold aGOFF; exact h3a u hu
    · rw [← grp_congr hf] at hj ⊢; rw [← offOf_congr hf]; unfold aGORD; exact h3b u hu j hj
    · unfold aKSZ aCTL at ha
      show mem3 a = mem a
      rw [h3c a (by omega), h2b a (by omega)]; exact h1c a (by omega)
  · simp only [gC, gCost, koC, lcaAC, csrC, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil,
      pgOf_m]
    nlinarith

end MinCostFlow.LowStretch
