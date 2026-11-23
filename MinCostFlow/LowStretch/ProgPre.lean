module

public import MinCostFlow.LowStretch.ProgPreR

/-!
# The preprocessing

`preP` runs the four parts `wP`, `kP`, `gP` and `rP` in this order and returns the number of
nodes of the merge tree. Afterwards the memory meets the precondition `EA.Pre` of the cluster
procedure on the first cluster, for the arguments `eaOf G T` (`preP_spec`), and the five cells at
`CTL` hold the arguments that depend on the tree.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- `preP` with `args = [n, m]`; the four parts sit at `bW`, `bK`, `bG` and `bR`. -/
def preP (bW bK bG bR : ℕ) : Stmt :=
  .seq (.call 2 bW [.reg 0, .reg 1])
  (.seq (.call 2 bK [.reg 0, .reg 1])
  (.seq (.call 3 bG [.reg 0, .reg 1, .reg 2])
  (.seq (.call 3 bR [.reg 0, .reg 1, .reg 2])
  (.ret (.reg 2)))))

theorem preP_noRand (bW bK bG bR : ℕ) : (preP bW bK bG bR).NoRand := by
  simp [preP, Stmt.NoRand]

/-- The arguments of the cluster procedure for the graph `G` and its merge tree `T`. -/
noncomputable def eaOf (G : WGraph) (T : KT) : EA :=
  ⟨G.n, G.m, 2, aPW G.n G.m, aEXP G.n G.m, T.N, aKPAR G.n G.m, aKCH1 G.n G.m, aKCH2 G.n G.m,
    aKMW G.n G.m, aKMP G.n G.m, aKSZ G.n G.m, aKLO G.n G.m, aHEAD G.n G.m, aORDL G.n G.m,
    aLCA G.n G.m, aGOFF G.n G.m, aGORD G.n G.m, aLAB G.n G.m, aLOC G.n G.m, aPAR G.n G.m,
    rootθ T G, Nat.log 2 (rootθ T G), (rootRec T G).nodes.length, aNODES G.n G.m,
    (rootRec T G).S.length, aSA G.n G.m, aOUT G.n G.m, aH G.n G.m⟩

/-- The cost of `preP`. -/
def preCost (G : WGraph) : ℕ := wCost G + kCost G + gCost G + 300 * (G.m + 2 * G.n + 1) +
  log2Cost ((pgOf G).maxω + 4 * pB G.n * G.n) + 50

theorem rCost_le {G : WGraph} {T : KT} (h : T.Ok (pgOf G)) :
    rCost G T ≤ 300 * (G.m + 2 * G.n + 1) + log2Cost ((pgOf G).maxω + 4 * pB G.n * G.n) := by
  unfold rCost
  have h1 : rootS T G ≤ (pgOf G).maxω + 4 * pB G.n * G.n := by
    unfold rootS
    have : T.mw (T.N - 1) ≤ (pgOf G).maxω := KT.mw_le_maxω h (by have := h.n_lt; omega)
    omega
  have := log2Cost_mono ((Nat.div_le_self (rootS T G) (4 * pB G.n * G.n)).trans h1)
  omega

/-- The contract of `preP` for the graph `G`: it returns the number of nodes of a merge tree `T`
and leaves the memory that the cluster procedure needs. -/
noncomputable def preC (w : ℕ) (G : WGraph) : Contract where
  pre args mem := args = [G.n, G.m] ∧ InG w G mem ∧ ZeroFrom mem (aPAR G.n G.m)
  post _ _ v mem' := ∃ T : KT, v = T.N ∧ (eaOf G T).Pre w G T mem' ∧
    mem' (aCTL G.n G.m) = T.N ∧ mem' (aCTL G.n G.m + 1) = rootθ T G ∧
    mem' (aCTL G.n G.m + 2) = Nat.log 2 (rootθ T G) ∧
    mem' (aCTL G.n G.m + 3) = (rootRec T G).nodes.length ∧
    mem' (aCTL G.n G.m + 4) = (rootRec T G).S.length
  cost _ _ := preCost G

theorem preP_spec {w : ℕ} {p : Program} {b bW bK bG bR : ℕ} {G : WGraph}
    (hp : p.HasAt b [preP bW bK bG bR]) (hW : MeetsContract w p bW (wC w G))
    (hK : MeetsContract w p bK (kC w G)) (hG : ∀ T, MeetsContract w p bG (gC w G T))
    (hR : ∀ T, MeetsContract w p bR (rC w G T)) : MeetsContract w p b (preC w G) := by
  intro args mem pos ω _ hpre
  obtain ⟨rfl, hI, hZ⟩ := hpre
  have hproc : p.procs[b]? = some (preP bW bK bG bR) := hp 0 (by simp)
  refine ⟨_, hproc, ?_⟩
  have hw := hI.add_lt
  simp only [aH] at hw
  dsimp only [preP]
  refine runs_start_le ?_
  wram_step
  · exact ⟨rfl, hI⟩
  intro v1 mem1 pos1 h1
  obtain ⟨h1p, h1e, h1f⟩ := h1
  dsimp only [startState] at h1p h1e h1f
  have hI1 : InG w G mem1 := hI.frame fun a ha => h1f a (Or.inl (by unfold aPAR; omega))
  wram_step
  · refine ⟨rfl, hI1, fun q hq => ⟨(h1e q hq).2, ?_⟩⟩
    show (pgOf G).pω q = 2 ^ mem1 (aEXP G.n G.m + q)
    rw [(h1e q hq).1, pω_wtOf hq]
  intro N mem2 pos2 h2
  obtain ⟨T, hT, rfl, hN, h2p, h2c, h2f⟩ := h2
  dsimp only at h2p h2c h2f
  have hI2 : InG w G mem2 := hI1.frame fun a ha => h2f a (Or.inl (by unfold aTLK; omega))
  have hTI : TreeIn w G T mem2 := ⟨hI2, hT, hN, h2p, h2c⟩
  have hNw : T.N < 2 ^ w := by omega
  have hGT := hG T
  have hRT := hR T
  wram_step
  · exact ⟨rfl, hTI⟩
  intro v3 mem3 pos3 h3
  obtain ⟨h3k, h3o, h3l, h3g, h3r, h3f⟩ := h3
  dsimp only at h3k h3o h3l h3g h3r h3f
  have hlow3 : ∀ a < aKSZ G.n G.m, mem3 a = mem2 a := fun a ha => h3f a (Or.inl ha)
  have hTI3 : TreeIn w G T mem3 := by
    refine ⟨hI2.frame fun a ha => hlow3 a (by unfold aKSZ; omega), hT, hN, fun k hk => ?_,
      fun k h1 h2 => ?_⟩
    · rw [hlow3 _ (by unfold aKPAR aKSZ; omega), hlow3 _ (by unfold aKMW aKSZ; omega)]
      exact h2p k hk
    · rw [hlow3 _ (by unfold aKCH1 aKSZ; omega), hlow3 _ (by unfold aKCH2 aKSZ; omega),
        hlow3 _ (by unfold aKMP aKSZ; omega)]
      exact h2c k h1 h2
  have hZ3 : ZeroFrom mem3 (aCTL G.n G.m) := fun a ha => by
    rw [h3f a (Or.inr ha), h2f a (Or.inr (by unfold aCTL aKSZ at *; omega)),
      h1f a (Or.inr (by unfold aCTL aTLK at *; omega))]
    exact hZ a (by unfold aCTL aPAR at *; omega)
  wram_step
  · dsimp only
    refine ⟨rfl, hTI3, fun k hk => (h3k k hk).2.2, ?_, hZ3⟩
    rw [hlow3 _ (by unfold aPAR aKSZ; omega), h2f _ (Or.inl (by unfold aPAR aTLK; omega))]
    exact h1p 2 (by norm_num)
  intro v4 mem4 pos4 h4
  obtain ⟨c0, c1, c2, c3, c4, hlab, hloc, hlocw, hnodes, hsa, hZ4, h4f⟩ := h4
  dsimp only at h4f
  have h43 : ∀ a < aCTL G.n G.m, mem4 a = mem3 a := h4f
  have h42 : ∀ a < aKSZ G.n G.m, mem4 a = mem2 a := fun a ha => by
    rw [h43 a (by unfold aCTL aKSZ at *; omega), hlow3 a ha]
  have h41 : ∀ a < aTLK G.n G.m, mem4 a = mem1 a := fun a ha => by
    rw [h42 a (by unfold aKSZ aTLK at *; omega), h2f a (Or.inl ha)]
  have hsN : (rootRec T G).nodes.length ≤ T.N := by
    unfold rootRec; simp only
    exact (List.length_filter_le _ _).trans (by simp)
  have hSm : (rootRec T G).S.length ≤ G.m := by
    unfold rootRec; simp only [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  wram_step
  · dsimp only
    refine ⟨T, rfl, ⟨hI.allowed, hI.two_le, rfl, rfl, rfl, hN, rootRec_ok hI.allowed hI.two_le hT,
      rfl, ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun k hk => ?_, fun k h1 h2 => ?_,
      fun k hk => ?_, fun v hv => ?_, fun q hq => ?_, fun u hu => ?_, fun u hu j hj => ?_, hlab,
      hloc, hlocw, fun i hi => ?_, rfl, hnodes, rfl, hsa, ?_, hZ4, hI.word⟩, c0, c1, ?_, c3, c4⟩
    · show rootθ T G = 2 ^ Nat.log 2 (rootθ T G)
      rw [c2, Nat.log_pow (by norm_num)]
    · show mem4 (2 + 3 * q) = _ ∧ mem4 (2 + 3 * q + 1) = _
      rw [h41 _ (by unfold aTLK; omega), h41 _ (by unfold aTLK; omega),
        h1f _ (Or.inl (by unfold aPAR; omega)), h1f _ (Or.inl (by unfold aPAR; omega))]
      exact hI.ends q hq
    · show mem4 (aPW G.n G.m + q) = _
      rw [h41 _ (by unfold aPW aTLK; omega)]; exact (h1e q hq).2
    · show (pgOf G).pω q = 2 ^ mem4 (aEXP G.n G.m + q)
      rw [h41 _ (by unfold aEXP aTLK; omega), (h1e q hq).1, pω_wtOf hq]
    · show mem4 (aKPAR G.n G.m + k) = _ ∧ mem4 (aKMW G.n G.m + k) = _
      rw [h42 _ (by unfold aKPAR aKSZ; omega), h42 _ (by unfold aKMW aKSZ; omega)]; exact h2p k hk
    · show mem4 (aKCH1 G.n G.m + k) = _ ∧ mem4 (aKCH2 G.n G.m + k) = _ ∧ mem4 (aKMP G.n G.m + k) = _
      rw [h42 _ (by unfold aKCH1 aKSZ; omega), h42 _ (by unfold aKCH2 aKSZ; omega),
        h42 _ (by unfold aKMP aKSZ; omega)]
      exact h2c k h1 h2
    · show mem4 (aKSZ G.n G.m + k) = _ ∧ mem4 (aKLO G.n G.m + k) = _ ∧ mem4 (aHEAD G.n G.m + k) = _
      rw [h43 _ (by unfold aKSZ aCTL; omega), h43 _ (by unfold aKLO aCTL; omega),
        h43 _ (by unfold aHEAD aCTL; omega)]
      exact h3k k hk
    · show mem4 (aORDL G.n G.m + T.lo (pgOf G) v) = v
      have hlo : T.lo (pgOf G) v < G.n := KT.lo_lt hT hv
      rw [h43 _ (by unfold aORDL aCTL; omega)]; exact h3o v hv
    · show T.IsLca _ _ (mem4 (aLCA G.n G.m + q))
      rw [h43 _ (by unfold aLCA aCTL; omega)]; exact h3l q hq
    · have hf : ∀ q < G.m, (fun q => mem3 (aLCA G.n G.m + q)) q = (fun q => mem4 (aLCA G.n G.m + q)) q :=
        fun q hq => (h43 _ (by unfold aLCA aCTL; omega)).symm
      show mem4 (aGOFF G.n G.m + u) = offOf (fun q => mem4 (aLCA G.n G.m + q)) G.m u
      rw [h43 _ (by unfold aGOFF aCTL; omega), ← offOf_congr hf]; exact h3g u hu
    · have hf : ∀ q < G.m, (fun q => mem3 (aLCA G.n G.m + q)) q = (fun q => mem4 (aLCA G.n G.m + q)) q :=
        fun q hq => (h43 _ (by unfold aLCA aCTL; omega)).symm
      change j < (grp (fun q => mem4 (aLCA G.n G.m + q)) G.m u).length at hj
      show mem4 (aGORD G.n G.m + offOf (fun q => mem4 (aLCA G.n G.m + q)) G.m u + j) =
        (grp (fun q => mem4 (aLCA G.n G.m + q)) G.m u).getD j 0
      rw [← grp_congr hf] at hj ⊢
      rw [← offOf_congr hf]
      have hle : offOf (fun q => mem3 (aLCA G.n G.m + q)) G.m u + j < G.m := by
        have h1 := offOf_succ (fun q => mem3 (aLCA G.n G.m + q)) G.m u
        have h2 : offOf (fun q => mem3 (aLCA G.n G.m + q)) G.m (u + 1) ≤ G.m :=
          (List.length_filter_le _ _).trans (by simp)
        omega
      rw [h43 _ (by unfold aGORD aCTL; omega)]; exact h3r u hu j hj
    · show mem4 (aPAR G.n G.m + i) = _
      rw [h41 _ (by unfold aPAR aTLK; omega), h1p i hi]
    · constructor <;> simp only [eaOf, aPAR, aEXP, aPW, aKPAR, aKCH1, aKCH2, aKMW, aKMP, aKSZ, aKLO,
        aHEAD, aORDL, aLCA, aGOFF, aGORD, aNODES, aLAB, aLOC, aSA, aOUT, aH] <;> omega
    · rw [c2, Nat.log_pow (by norm_num)]
  · simp only [preC, preCost, wC, kC, gC, rC, Expr.size_reg, argsSize_cons, argsSize_nil]
    have := rCost_le hT
    omega

end MinCostFlow.LowStretch
