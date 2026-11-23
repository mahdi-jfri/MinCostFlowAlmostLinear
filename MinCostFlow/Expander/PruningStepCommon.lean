module

public import MinCostFlow.Expander.PruningRemoveOneProg

/-!
# Shared Invariant, Volume, Bucket Preservation, and mkPruneMemInv Helpers
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

/-! ## 2b. Shared Invariant, Volume, and Bucket Preservation Helpers -/

lemma foldl_removeEdgeStep_ex_of_not_inR (cfg : PruneCfg) (flow : ℕ → ℤ)
    (inR' : ℕ → Bool) {x : ℕ} (hx : inR' x = false) :
    ∀ (L : List (ℕ × Bool × ℕ)) (st : PruneState),
      (L.foldl (removeEdgeStep cfg flow inR') st).ex x = st.ex x
  | [], st => rfl
  | p :: ps, st => by
      dsimp only [List.foldl_cons]
      rw [foldl_removeEdgeStep_ex_of_not_inR cfg flow inR' hx ps]
      unfold removeEdgeStep
      by_cases hp : inR' p.2.2 = true
      · have hne : x ≠ p.2.2 := fun h => by subst h; simp [hx] at hp
        simp [hp, hne]
      · simp [hp]

lemma ex_bound_of_sweep_after_removeOne {cfg : PruneCfg} {A : Finset ℕ}
    {s : PruneState} {a : ℕ}
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hGv : cfg.G.IsValid)
    (hpre : ∀ u < cfg.G.n, s.ex u ≤ 4 * cfg.C_cap * cfg.G.m)
    (hsw' : SweepInv cfg A (removeOneFromR cfg a s)) :
    ∀ u < cfg.G.n, (removeOneFromR cfg a s).ex u ≤ 4 * cfg.C_cap * cfg.G.m := by
  intro u hu
  by_cases huR : (removeOneFromR cfg a s).inR u = true
  · exact ex_le_bound_of_flow_balance hcfgX hGv hsw'.flow_cap hsw'.flow_balance hsw'.inR_sub huR
  · have huF : (removeOneFromR cfg a s).inR u = false := Bool.eq_false_of_not_eq_true huR
    have hinR_eq : (removeOneFromR cfg a s).inR u = (if u = a then false else s.inR u) :=
      removeOneFromR_inR cfg a s u
    have huF' : (if u = a then false else s.inR u) = false := hinR_eq ▸ huF
    have hex_eq := foldl_removeEdgeStep_ex_of_not_inR cfg s.flow
      (fun x => if x = a then false else s.inR x) huF' (cfg.incEdges a)
      { s with inR := fun x => if x = a then false else s.inR x }
    change (removeOneFromR cfg a s).ex u = s.ex u at hex_eq
    rw [hex_eq]
    exact hpre u hu

lemma volAtLevel_erase {cfg : PruneCfg} {inR : ℕ → Bool} {h : ℕ → ℕ} {a ℓ : ℕ}
    (haX : a ∈ cfg.X) (haR : inR a = true) :
    volAtLevel cfg (fun x => if x = a then false else inR x) h ℓ =
      if h a = ℓ then volAtLevel cfg inR h ℓ - cfg.degX a else volAtLevel cfg inR h ℓ := by
  unfold volAtLevel
  rw [← Finset.add_sum_erase cfg.X _ haX, ← Finset.add_sum_erase cfg.X _ haX]
  have hsum :
      ∑ x ∈ cfg.X.erase a,
          (if (if x = a then false else inR x) && decide (h x = ℓ) then cfg.degX x else 0) =
      ∑ x ∈ cfg.X.erase a, (if inR x && decide (h x = ℓ) then cfg.degX x else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ a := (Finset.mem_erase.mp hx).1
    simp [hne]
  rw [hsum]
  by_cases haℓ : h a = ℓ <;> simp [haR, haℓ]

lemma volAtLevel_relabel {cfg : PruneCfg} {inR : ℕ → Bool} {h : ℕ → ℕ}
    {u oldL newL ℓ : ℕ}
    (huX : u ∈ cfg.X) (huR : inR u = true) (hold : h u = oldL) (hne : oldL ≠ newL) :
    volAtLevel cfg inR (fun x => if x = u then newL else h x) ℓ =
      if ℓ = newL then volAtLevel cfg inR h ℓ + cfg.degX u
      else if ℓ = oldL then volAtLevel cfg inR h ℓ - cfg.degX u
      else volAtLevel cfg inR h ℓ := by
  unfold volAtLevel
  rw [← Finset.add_sum_erase cfg.X _ huX, ← Finset.add_sum_erase cfg.X _ huX]
  have hsum :
      ∑ x ∈ cfg.X.erase u,
          (if inR x && decide ((if x = u then newL else h x) = ℓ) then cfg.degX x else 0) =
      ∑ x ∈ cfg.X.erase u, (if inR x && decide (h x = ℓ) then cfg.degX x else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
    simp [hxu]
  rw [hsum]
  by_cases hn : ℓ = newL
  · subst hn
    simp [huR, hold, hne]
    omega
  · by_cases ho : ℓ = oldL
    · subst ho
      simp [huR, hold, Ne.symm hne]
      omega
    · simp [huR, hold, hn, ho, Ne.symm hn, Ne.symm ho]

lemma static_of_preserved2 {cfg : PruneCfg}
    {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st₀ st' : State}
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hpr : PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
      (wHArr workAddr cfg.G.n cfg.G.m cfg.H)
      (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H)) :
    Spanner.GraphAt st'.mem gAddr cfg.G ∧
    HasCsrAt st'.mem csrAddr cfg.G ∧
    (∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ st'.mem (inBAddr + b) ≠ 0) ∧
    (∀ u < cfg.G.n, st'.mem (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) = cfg.degX u) := by
  set n := cfg.G.n
  set m := cfg.G.m
  set H := cfg.H
  have hdisj_g_outR := hdisj.1
  have hdisj_g_work := hdisj.2.2.2.1
  have hdisj_csr_outR := hdisj.2.1
  have hdisj_csr_work := hdisj.2.2.2.2.1
  have hdisj_inB_outR := hdisj.2.2.1
  have hdisj_inB_work := hdisj.2.2.2.2.2.1
  have hdisj_outR_work := hdisj.2.2.2.2.2.2
  have hG' : Spanner.GraphAt st'.mem gAddr cfg.G := fun i hi => by
    rw [hpr (gAddr + i)
      (by dsimp only [n] at *; rcases hdisj_g_outR with h | h <;> omega)
      (by dsimp only [n, m, H] at *; dsimp [wHArr]
          rcases hdisj_g_work with h | h <;> omega)]
    exact hinv.graph_at i hi
  have hCsr' : HasCsrAt st'.mem csrAddr cfg.G := by
    refine ⟨fun u hu => ?_, fun u hu j hj => ?_⟩
    · rw [hpr (csrAddr + u)
        (by dsimp only [n] at *; rcases hdisj_csr_outR with h | h <;> omega)
        (by dsimp only [n, m, H] at *; dsimp [wHArr]
            rcases hdisj_csr_work with h | h <;> omega)]
      exact hinv.csr_at.1 u hu
    · have hj_lt : csrOff cfg.G u + j < 2 * m := by
        have hs := csrOff_succ cfg.G u
        have hle := csrOff_le_two_mul_m cfg.G (u + 1)
        dsimp [m, Cited.Graph.m] at *
        omega
      refine ⟨?_, ?_⟩
      · rw [hpr (csrAddr + 2 * n + 1 + csrOff cfg.G u + j)
          (by dsimp only [n, m] at *; rcases hdisj_csr_outR with h | h <;> omega)
          (by dsimp only [n, m, H] at *; dsimp [wHArr]
              rcases hdisj_csr_work with h | h <;> omega)]
        exact (hinv.csr_at.2 u hu j hj).1
      · rw [hpr (csrAddr + 2 * n + 1 + 2 * m + csrOff cfg.G u + j)
          (by dsimp only [n, m] at *; rcases hdisj_csr_outR with h | h <;> omega)
          (by dsimp only [n, m, H] at *; dsimp [wHArr]
              rcases hdisj_csr_work with h | h <;> omega)]
        exact (hinv.csr_at.2 u hu j hj).2
  have hinB' : ∀ b, b ∈ cfg.B ↔ b < n ∧ st'.mem (inBAddr + b) ≠ 0 := by
    intro b
    constructor
    · intro hb
      obtain ⟨hbn, hm⟩ := (hinv.inB_eq b).mp hb
      refine ⟨hbn, ?_⟩
      rw [hpr (inBAddr + b)
        (by dsimp only [n] at *; rcases hdisj_inB_outR with h | h <;> omega)
        (by dsimp only [n, m, H] at *; dsimp [wHArr]
            rcases hdisj_inB_work with h | h <;> omega)]
      exact hm
    · rintro ⟨hbn, hm⟩
      refine (hinv.inB_eq b).mpr ⟨hbn, ?_⟩
      rwa [← hpr (inBAddr + b)
        (by dsimp only [n] at *; rcases hdisj_inB_outR with h | h <;> omega)
        (by dsimp only [n, m, H] at *; dsimp [wHArr]
            rcases hdisj_inB_work with h | h <;> omega)]
  have hdegX' : ∀ u < n, st'.mem (wDegX workAddr n m H + u) = cfg.degX u := by
    intro u hu
    rw [hpr (wDegX workAddr n m H + u)
      (by dsimp only [n, m, H] at *; dsimp [wDegX]
          unfold pruneWorkSpace at hdisj_outR_work
          rcases hdisj_outR_work with h | h <;> omega)
      (by dsimp [wDegX, wHArr]; omega)]
    exact hinv.degX_eq u hu
  exact ⟨hG', hCsr', hinB', hdegX'⟩

lemma buckets_preserved_of_mem_agree {cfg : PruneCfg}
    {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} (s' : PruneState) {buckets : ℕ → List ℕ} {st₀ : State} (st' : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hinR : s'.inR = s.inR) (hh : s'.h = s.h)
    (hagree : ∀ k, wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ k →
      k < wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + cfg.H + 1 → st'.mem k = st₀.mem k) :
    st'.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) = 0 ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
      st'.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = volAtLevel cfg s'.inR s'.h ℓ) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → (buckets ℓ).Nodup) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → ∀ x, x ∈ buckets ℓ ↔ x < cfg.G.n ∧ s'.inR x = true ∧ s'.h x = ℓ) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
      DoublyLinked st'.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H)
        (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n (buckets ℓ) cfg.G.n
        (st'.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ))) := by
  set n := cfg.G.n; set m := cfg.G.m; set H := cfg.H
  have hvolH : st'.mem (wLvlVol workAddr n m H + H) = 0 := by
    rw [hagree (wLvlVol workAddr n m H + H)
      (by dsimp [wLvlNext, wLvlVol]; omega)
      (by dsimp [wLvlVol, wLvlHead]; omega)]
    exact hinv.lvlVol_H
  have hvol : ∀ ℓ, 1 ≤ ℓ → ℓ < H →
      st'.mem (wLvlVol workAddr n m H + ℓ) = volAtLevel cfg s'.inR s'.h ℓ := by
    intro ℓ hℓ1 hℓH
    rw [hagree (wLvlVol workAddr n m H + ℓ)
      (by dsimp [wLvlNext, wLvlVol]; omega)
      (by dsimp [wLvlVol, wLvlHead]; omega), hinR, hh]
    exact hinv.lvlVol_eq ℓ hℓ1 hℓH
  have hdl : ∀ ℓ, 1 ≤ ℓ → ℓ < H →
      DoublyLinked st'.mem (wLvlNext workAddr n m H) (wLvlPrev workAddr n m H) n
        (buckets ℓ) n (st'.mem (wLvlHead workAddr n m H + ℓ)) := by
    intro ℓ hℓ1 hℓH
    rw [hagree (wLvlHead workAddr n m H + ℓ)
      (by dsimp [wLvlNext, wLvlHead]; omega)
      (by dsimp [wHArr, wLvlHead]; omega)]
    refine doublyLinked_congr_disjoint ?_ ?_ (hinv.buckets_dl ℓ hℓ1 hℓH)
    · intro y hy
      have hyn : y < n := doublyLinked_mem_lt (hinv.buckets_dl ℓ hℓ1 hℓH) hy
      exact hagree (wLvlNext workAddr n m H + y)
        (by dsimp [wHArr, wLvlNext]; omega) (by dsimp [wLvlNext, wLvlHead]; omega)
    · intro y hy
      have hyn : y < n := doublyLinked_mem_lt (hinv.buckets_dl ℓ hℓ1 hℓH) hy
      exact hagree (wLvlPrev workAddr n m H + y)
        (by dsimp [wLvlNext, wLvlPrev]; omega) (by dsimp [wLvlPrev, wLvlHead]; omega)
  exact ⟨hvolH, hvol, hinv.buckets_nodup,
    fun ℓ hℓ1 hℓH x => by rw [hinR, hh]; exact hinv.buckets_mem ℓ hℓ1 hℓH x, hdl⟩

lemma peelQInv_of_fields {cfg : PruneCfg} {s s' : PruneState}
    (hpq : PeelQInv cfg s) (hpeel : s'.peelQ = s.peelQ)
    (hdegR : s'.degR = s.degR) :
    PeelQInv cfg s' := by
  rcases hpq with ⟨hnd, hsub, hdeg⟩
  refine ⟨hpeel ▸ hnd, fun x hx => hsub x (hpeel ▸ hx), fun x hx => ?_⟩
  rw [hdegR]
  exact hdeg x (hpeel ▸ hx)

lemma memFrame_to_preserved2_right {m1 m2 : ℕ → ℕ} {a b a1 b1 a2 b2 : ℕ}
    (hmf : MemFrame m1 m2 a b) (ha : a2 ≤ a) (hb : b ≤ b2) :
    PreservedOutside2 m1 m2 a1 b1 a2 b2 := by
  intro x _ hx
  apply hmf
  rcases hx with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)


/-! ### Shared builder helper + Section 5: `pushFlowStep` -/

lemma runs_seq {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st₁ st₂ st₃ : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h1 : Runs w p ω s st₁ .normal st₂ c₁)
    (h2 : Runs w p ω t st₂ o st₃ c₂) :
    Runs w p ω (.seq s t) st₁ o st₃ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₂, c₁, c₂, h1, h2, rfl⟩)

lemma eval_reg_eq (w : ℕ) (st : State) (r : ℕ) {v : ℕ} (h : st.regs r = v) :
    Expr.eval w st (.reg r) = some v := by
  rw [Expr.eval_reg, h]

lemma eval_add_eq (w : ℕ) (st : State) (r₁ r₂ : ℕ) {v₁ v₂ : ℕ}
    (h1 : st.regs r₁ = v₁) (h2 : st.regs r₂ = v₂) (hadd : v₁ + v₂ < 2 ^ w) :
    Expr.eval w st (.bin .add (.reg r₁) (.reg r₂)) = some (v₁ + v₂) :=
  Expr.eval_bin (eval_reg_eq w st r₁ h1) (eval_reg_eq w st r₂ h2) (by simp [BinOp.eval]; exact hadd)

lemma eval_load_add_eq (w : ℕ) (st : State) (r₁ r₂ : ℕ) {v₁ v₂ val : ℕ}
    (h1 : st.regs r₁ = v₁) (h2 : st.regs r₂ = v₂) (hadd : v₁ + v₂ < 2 ^ w)
    (hm : st.mem (v₁ + v₂) = val) :
    Expr.eval w st (.load (.bin .add (.reg r₁) (.reg r₂))) = some val :=
  hm ▸ Expr.eval_load (eval_add_eq w st r₁ r₂ h1 h2 hadd)

lemma le_adjH_ne_work {r : ℕ} (hr : r ≤ prCsrAdjH) :
    r ≠ prTmp1 ∧ r ≠ prTmp2 ∧ r ≠ prTmp3 ∧ r ≠ prRc ∧ r ≠ prDelta ∧
    r ≠ prIdx ∧ r ≠ prDir ∧ r ≠ prW ∧ r ≠ prJ ∧ r ≠ prStart ∧ r ≠ prEnd ∧
    r ≠ prI ∧ r ≠ prSuf ∧ r ≠ prPicked := by
  dsimp [prCsrAdjH, prI, prJ, prW, prIdx, prDir, prTmp1, prTmp2, prTmp3, prRc, prDelta, prEnd, prStart, prSuf, prPicked] at hr ⊢
  omega

lemma mkPruneMemInv
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s s' : PruneState} {buckets buckets' : ℕ → List ℕ} {st₀ st' : State}
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hagree : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r)
    (hpr : PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
      (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H))
    (hat : st'.regs prActTop = s'.active.length)
    (hpt : st'.regs prPeelTop = s'.peelQ.length)
    (houtR : ∀ u < cfg.G.n, st'.mem (outRAddr + u) = if s'.inR u = true then 1 else 0)
    (hh : ∀ u < cfg.G.n, st'.mem (wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) = s'.h u)
    (hcur : ∀ u < cfg.G.n, st'.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H + u) = s'.cur u)
    (habs : ∀ u < cfg.G.n, st'.mem (wAbs workAddr cfg.G.n cfg.G.m cfg.H + u) = s'.abs u)
    (hex : ∀ u < cfg.G.n, st'.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + u) = s'.ex u)
    (hdegR : ∀ u < cfg.G.n, st'.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + u) = s'.degR u)
    (hinAct : ∀ u < cfg.G.n, st'.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) = if s'.inActive u = true then 1 else 0)
    (hactStk : ∀ i < s'.active.length,
      st'.mem (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i) = s'.active.getD (s'.active.length - 1 - i) 0)
    (hpeelStk : ∀ i < s'.peelQ.length,
      st'.mem (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + i) = s'.peelQ.getD (s'.peelQ.length - 1 - i) 0)
    (hflowEnc : ∀ idx < cfg.G.m,
      st'.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx) = (↑cfg.C_cap + s'.flow idx).toNat)
    (hlvlH : st'.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) = 0)
    (hlvlEq : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
      st'.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = volAtLevel cfg s'.inR s'.h ℓ)
    (hbnd : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → (buckets' ℓ).Nodup)
    (hbmem : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → ∀ x, x ∈ buckets' ℓ ↔ x < cfg.G.n ∧ s'.inR x = true ∧ s'.h x = ℓ)
    (hbdl : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
      DoublyLinked st'.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H)
        cfg.G.n (buckets' ℓ) cfg.G.n (st'.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ)))
    (hexB : ∀ u < cfg.G.n, s'.ex u ≤ 4 * cfg.C_cap * cfg.G.m)
    (hpinv : PruningInv cfg s')
    (hpqinv : PeelQInv cfg s') :
    PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets' st' := by
  rcases hdisj with ⟨hdG1, hdC1, hdB1, hdG2, hdC2, hdB2, hdW⟩
  unfold pruneWorkSpace at *
  exact
    { cfg_X := hinv.cfg_X
      cfg_valid := hinv.cfg_valid
      reg_g := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_g
      reg_csr := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_csr
      reg_inB := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_inB
      reg_outR := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_outR
      reg_work := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_work
      reg_ccap := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_ccap
      reg_H := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_H
      reg_theta := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_theta
      reg_n := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_n
      reg_m := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_m
      reg_actTop := hat
      reg_peelTop := hpt
      reg_degX := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_degX
      reg_hArr := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_hArr
      reg_cur := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_cur
      reg_abs := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_abs
      reg_ex := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_ex
      reg_degR := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_degR
      reg_inAct := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_inAct
      reg_actStk := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_actStk
      reg_peelStk := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_peelStk
      reg_lvlNext := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_lvlNext
      reg_lvlPrev := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_lvlPrev
      reg_remArr := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_remArr
      reg_flowEnc := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_flowEnc
      reg_lvlVol := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_lvlVol
      reg_lvlHead := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_lvlHead
      reg_adjV := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_adjV
      reg_adjH := (hagree _ (by decide) (by decide) (by decide)).trans hinv.reg_adjH
      graph_at := fun i hi => by
        rw [hpr (gAddr + i) (by omega) (by dsimp [wHArr]; omega)]
        exact hinv.graph_at i hi
      csr_at :=
        ⟨fun u hu => by
          rw [hpr (csrAddr + u) (by omega) (by dsimp [wHArr]; omega)]
          exact hinv.csr_at.1 u hu,
         fun u hu j hj => by
          have hcsr_lt : csrOff cfg.G u + j < 2 * cfg.G.m := by
            have hsub := csrOff_le_two_mul_m cfg.G (u + 1)
            rw [csrOff_succ] at hsub
            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hsub
          refine ⟨?_, ?_⟩
          · rw [hpr (csrAddr + 2 * cfg.G.n + 1 + csrOff cfg.G u + j) (by omega)
              (by dsimp [wHArr]; omega)]
            exact (hinv.csr_at.2 u hu j hj).1
          · rw [hpr (csrAddr + 2 * cfg.G.n + 1 + 2 * cfg.G.m + csrOff cfg.G u + j) (by omega)
              (by dsimp [wHArr]; omega)]
            exact (hinv.csr_at.2 u hu j hj).2⟩
      inB_eq := fun b => by
        constructor
        · intro hb
          obtain ⟨hbn, hm⟩ := (hinv.inB_eq b).mp hb
          refine ⟨hbn, ?_⟩
          rw [hpr (inBAddr + b) (by omega) (by dsimp [wHArr]; omega)]
          exact hm
        · rintro ⟨hbn, hm⟩
          rw [hpr (inBAddr + b) (by omega) (by dsimp [wHArr]; omega)] at hm
          exact (hinv.inB_eq b).mpr ⟨hbn, hm⟩
      outR_eq := houtR
      degX_eq := fun u hu => by
        rw [hpr (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u)
          (by dsimp [wDegX]; omega) (by dsimp [wDegX, wHArr]; omega)]
        exact hinv.degX_eq u hu
      h_eq := hh
      cur_eq := hcur
      abs_eq := habs
      ex_eq := hex
      degR_eq := hdegR
      inAct_eq := hinAct
      actStk_eq := hactStk
      peelStk_eq := hpeelStk
      flowEnc_eq := hflowEnc
      lvlVol_H := hlvlH
      lvlVol_eq := hlvlEq
      buckets_nodup := hbnd
      buckets_mem := hbmem
      buckets_dl := hbdl
      ex_bound := hexB
      prune_inv := hpinv
      peelQ_inv := hpqinv }


lemma runs_seqStmts_split {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ {l1 l2 : List Stmt} {st₀ st₁ st₂ : State} {c₁ c₂ : ℕ},
      l1 ≠ [] → l2 ≠ [] →
      Runs w p ω (seqStmts l1) st₀ .normal st₁ c₁ →
      Runs w p ω (seqStmts l2) st₁ .normal st₂ c₂ →
      Runs w p ω (seqStmts (l1 ++ l2)) st₀ .normal st₂ (c₁ + c₂ + 1)
  | [], _, _, _, _, _, _, h1, _, _, _ => absurd rfl h1
  | [a], b :: bs, st₀, st₁, st₂, c₁, c₂, _, _, h1, h2 => by
    simpa [seqStmts] using runs_seq h1 h2
  | a :: b :: rest, l2, st₀, st₁, st₂, c₁, c₂, _, hl2, h1, h2 => by
    rcases runs_seq_iff.mp h1 with ⟨_, _, _, hret, _⟩ | ⟨st_m, c_s, c_r, hs, hr, rfl⟩
    · exact absurd hret (by simp)
    · have ih := runs_seqStmts_split (l1 := b :: rest) (l2 := l2) (by simp) hl2 hr h2
      simpa only [List.cons_append, seqStmts, Nat.add_assoc] using
        runs_seq_iff.mpr (Or.inr ⟨st_m, c_s, c_r + c₂ + 1, hs, ih, by omega⟩)

end MinCostFlow.Expander
