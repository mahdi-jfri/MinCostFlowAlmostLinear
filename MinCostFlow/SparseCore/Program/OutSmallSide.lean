module

public import MinCostFlow.SparseCore.Program.OutSmallSideTail

/-!
# The helper `outSmallSide` meets its statement

This file puts the parts of the helper together: the head, the two `firstMarked` queries, the
start of the walk, the walk and the end. The cost adds up as follows. The two queries and the
straight parts cost a constant number of tour queries. The walk costs two queries per round, and
it has as many rounds as the smaller part has marked ends. The list and its copy cost that
number too. So the whole cost is a constant times `(|Y| + 1)` tour queries, where `Y` is the list
of the smaller part (`outSmallSide_body_runs`). The statement of piece P7 follows for every
program that holds the helper (`sig_outSmallSide_runs_of`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle

section Main

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- **The helper `outSmallSide`.** -/
theorem outSmallSide_body_runs (T : OutTourAt S w vCap eCap p nm sm fm lm)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) {f : ℕ}
    (hproc : p.procs[f]? = some (outSmallSideBody nm fm lm))
    (tourH r₁ r₂ v v' last h : ℕ) (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool)
    (hargs : ∀ a ∈ [tourH, r₁, r₂, v, v', last, h], a < 2 ^ w) (hr₁ : r₁ < vCap)
    (hr₂ : r₂ < vCap) (hnd₁ : (s.cord r₁).Nodup) (hnd₂ : (s.cord r₂).Nodup)
    (hlt : ∀ x ∈ s.markedList r₁ ++ s.markedList r₂, x.1 < eCap)
    (hrep : T.rep.rep tourH s tx mem) (hfoot : ∀ a, T.rep.foot tourH tx a → a < h)
    (hh0 : 0 < h) (hlast : last = 0 ∨ (last + 4 < h ∧ ¬ T.rep.foot tourH tx (last + 4)))
    (hz : ZeroFrom mem h) (hsp : h + outSmallSideSpace S (2 * eCap) < 2 ^ w) :
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c tx',
      Runs w p ω body (startState [tourH, r₁, r₂, v, v', last, h] mem pos) o st' c ∧
      T.rep.rep tourH s tx' st'.mem ∧
      st'.mem h = v ∧ st'.mem (h + 1) = v' ∧ st'.mem (h + 2) = ssSide s r₁ r₂ ∧
      st'.mem (h + 4) = 0 ∧
      EndListAt st'.mem (st'.mem (h + 3)) (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)) ∧
      (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length ≤
        (s.markedList (if ssSide s r₁ r₂ = 0 then r₂ else r₁)).length ∧
      h + 5 ≤ st'.mem (h + 3) ∧
      o.value = st'.mem (h + 3) + 1 +
        (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length ∧
      o.value ≤ h + outSmallSideSpace S (2 * eCap) ∧ ZeroFrom st'.mem o.value ∧
      (last ≠ 0 → st'.mem (last + 4) = h) ∧
      (∀ a < h, ¬ T.rep.foot tourH tx a → (last = 0 ∨ a ≠ last + 4) → st'.mem a = mem a) ∧
      (∀ a, T.rep.foot tourH tx' a →
        T.rep.foot tourH tx a ∨ (h + 5 ≤ a ∧ a < st'.mem (h + 3))) ∧
      c + T.rep.phi tourH tx' st'.mem ≤
        300 * (S.mul + 1) * ((s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length + 1) *
          ordStoreLog eCap + T.rep.phi tourH tx mem := by
  have htour := hargs tourH (by simp)
  have hhw := hargs h (by simp)
  have hkey : 2 * eCap + 2 < 2 ^ w := by nlinarith
  have h1w : 1 < 2 ^ w := by omega
  have hlt₁ : ∀ x ∈ s.markedList r₁, x.1 < eCap := fun x hx => hlt x (List.mem_append_left _ hx)
  have hlt₂ : ∀ x ∈ s.markedList r₂, x.1 < eCap := fun x hx => hlt x (List.mem_append_right _ hx)
  have hl₁ := markedList_length_le s r₁ hnd₁ hlt₁
  have hl₂ := markedList_length_le s r₂ hnd₂ hlt₂
  have hmono := S.listSpace_mono
  have hqge := S.querySpace_ge
  unfold outSmallSideSpace at hsp ⊢
  have hmin : min (s.markedList r₁).length (s.markedList r₂).length ≤ 2 * eCap := by omega
  have hq1 : (2 * min (s.markedList r₁).length (s.markedList r₂).length + 2) * S.querySpace ≤
      (2 * (2 * eCap) + 2) * S.querySpace := Nat.mul_le_mul_right _ (by omega)
  have hq2 : (2 + 2 * min (s.markedList r₁).length (s.markedList r₂).length) * S.querySpace ≤
      (2 * (2 * eCap) + 2) * S.querySpace := Nat.mul_le_mul_right _ (by omega)
  have hq3 : 2 * S.querySpace ≤
      (2 * min (s.markedList r₁).length (s.markedList r₂).length + 2) * S.querySpace :=
    Nat.mul_le_mul_right _ (by omega)
  have hYk : (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length =
      min (s.markedList r₁).length (s.markedList r₂).length := by
    by_cases hc : (s.markedList r₁).length ≤ (s.markedList r₂).length
    · simp only [ssSide, hc, ite_true]; omega
    · simp only [ssSide, hc, ite_false, one_ne_zero]; omega
  have hls := hmono (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length (2 * eCap)
    (by omega)
  have hlastl : last ≠ 0 → last + 4 < h := fun hl => by
    rcases hlast with h0 | ⟨h1, -⟩
    · exact absurd h0 hl
    · exact h1
  -- the head
  obtain ⟨stA, cA, hrA, hcA, hposA, hregsA, h7A, hmemA⟩ :=
    ssHead_runs (w := w) (p := p) (ω := ω) (tourH := tourH) (r₁ := r₁) (r₂ := r₂) (v := v) (v' := v')
      mem pos (by omega) hlastl
  have hnl : ∀ a, (a = last + 4 → last = 0) → ¬ (last ≠ 0 ∧ a = last + 4) :=
    fun a ha ⟨hl, he⟩ => hl (ha he)
  have hagreeA : ∀ a, T.rep.foot tourH tx a → mem a = stA.mem a := by
    intro a ha
    have := hfoot a ha
    rw [hmemA a, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right ?_]
    rintro ⟨hl, rfl⟩
    rcases hlast with h0 | ⟨-, hn⟩
    · exact hl h0
    · exact hn ha
  obtain ⟨hrepA', hphiA⟩ := T.rep_local tourH s tx mem stA.mem hagreeA
  have hFA : SSFrame T tourH last h v v' s tx mem (h + 5) tx stA.mem := by
    refine ⟨hrepA' hrep, fun a ha => ?_, le_rfl, fun a ha => Or.inl ha, fun a ha _ hl => ?_,
      ?_, ?_, ?_, fun hl => ?_⟩
    · rw [hmemA a, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (hnl a fun he => by have := hlastl; omega)]
      exact hz a (by omega)
    · rw [hmemA a, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (hnl a fun he => by rcases hl with hl | hl <;> omega)]
    · rw [hmemA h, ite_eq_left rfl]
    · rw [hmemA, ite_eq_right (by omega), ite_eq_left rfl]
    · rw [hmemA, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (hnl _ fun he => by have := hlastl; omega)]
      exact hz _ (by omega)
    · rw [hmemA, ite_eq_right (by have := hlastl hl; omega),
        ite_eq_right (by have := hlastl hl; omega), ite_eq_left ⟨hl, rfl⟩]
  have hA : SSArgs stA tourH r₁ r₂ v v' last h :=
    ⟨by rw [hregsA 0 (by norm_num)]; rfl, by rw [hregsA 1 (by norm_num)]; rfl,
      by rw [hregsA 2 (by norm_num)]; rfl, by rw [hregsA 3 (by norm_num)]; rfl,
      by rw [hregsA 4 (by norm_num)]; rfl, by rw [hregsA 5 (by norm_num)]; rfl,
      by rw [hregsA 6 (by norm_num)]; rfl⟩
  -- the first marked ends
  obtain ⟨stB1, cB1, tx₁, hrB1, hFB1, h9B1, hothB1, hgeB1, hleB1, hcostB1⟩ :=
    ssFirst_step T stA ω (rr := 1) (dst := 9) (r := r₁) (by norm_num) (by norm_num) hfoot hlast
      hFA hA.1 h7A hA.2.1 htour hr₁ (by omega)
  have hA1 : SSArgs stB1 tourH r₁ r₂ v v' last h :=
    hA.of_regs fun r hr => hothB1 r (by omega) (by omega) (by omega)
  obtain ⟨stB2, cB2, tx₂, hrB2, hFB2, h10B2, hothB2, hgeB2, hleB2, hcostB2⟩ :=
    ssFirst_step T stB1 ω (rr := 2) (dst := 10) (r := r₂) (by norm_num) (by norm_num) hfoot
      hlast hFB1 hA1.1 rfl hA1.2.2.1 htour hr₂ (by omega)
  have hA2 : SSArgs stB2 tourH r₁ r₂ v v' last h :=
    hA1.of_regs fun r hr => hothB2 r (by omega) (by omega) (by omega)
  have h9B2 : stB2.regs 9 = optEndWord (s.markedList r₁).head? := by
    rw [hothB2 9 (by norm_num) (by norm_num) (by norm_num), h9B1]
  -- the start of the walk
  obtain ⟨stC, cC, hrC, hcC, hmemC, hposC, hregsC, h12C, h13C, h11C, h14C⟩ :=
    ssInit_runs (p := p) (ω := ω) stB2 h1w
  have hInvC : SSLoopInv T tourH r₁ r₂ v v' last h s tx mem
      (0, T.rep.phi tourH tx₂ stB2.mem) stC := by
    refine ⟨tx₂, stB2.regs 7, hmemC ▸ hFB2, by rw [hmemC],
      hA2.of_regs fun r hr => hregsC r (by omega) (by omega) (by omega) (by omega),
      hregsC 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      by rw [hregsC 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h9B2],
      by rw [hregsC 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h10B2],
      by dsimp only; omega, ?_⟩
    dsimp only
    by_cases hm₁ : s.markedList r₁ = []
    · have h9z : stB2.regs 9 = 0 := by rw [h9B2, optEndWord_head?_eq_zero.mpr hm₁]
      refine Or.inr ⟨by rw [h14C, ite_eq_left h9z], by rw [h11C, ite_eq_left h9z]; simp [ssSide, hm₁],
        by simp [hm₁]⟩
    · have h9nz : stB2.regs 9 ≠ 0 := by
        rw [h9B2]; exact fun he => hm₁ (optEndWord_head?_eq_zero.mp he)
      have h0₁ : 0 < (s.markedList r₁).length := List.length_pos_iff.mpr hm₁
      by_cases hm₂ : s.markedList r₂ = []
      · have h10z : stB2.regs 10 = 0 := by rw [h10B2, optEndWord_head?_eq_zero.mpr hm₂]
        refine Or.inr ⟨by rw [h14C, ite_eq_right h9nz, ite_eq_left h10z], ?_, by simp [hm₂]⟩
        rw [h11C, ite_eq_right h9nz, ite_eq_left h10z]
        simp [ssSide, hm₂]; omega
      · have h10nz : stB2.regs 10 ≠ 0 := by
          rw [h10B2]; exact fun he => hm₂ (optEndWord_head?_eq_zero.mp he)
        have h0₂ : 0 < (s.markedList r₂).length := List.length_pos_iff.mpr hm₂
        refine Or.inl ⟨by rw [h14C, ite_eq_right h9nz, ite_eq_right h10nz], by
          rw [h11C, ite_eq_right h9nz, ite_eq_right h10nz], h0₁, h0₂, ?_, ?_⟩
        · rw [h12C, h9B2, optEndWord_head? h0₁]
        · rw [h13C, h10B2, optEndWord_head? h0₂]
  -- the walk
  obtain ⟨oD, stD, cD, hrD, r, ⟨hoD, hInvD, h14D⟩, hcD⟩ :=
    ssLoop_runs T ω hfoot hlast hnd₁ hnd₂ hlt₁ hlt₂ htour hr₁ hr₂ hkey (by omega) _ stC hInvC
  subst hoD
  obtain ⟨tx₃, cur₃, hF₃, hphi₃, hA₃, h7₃, -, -, hcur₃, hcase⟩ := hInvD
  have h11₃ : stD.regs 11 = ssSide s r₁ r₂ := by
    rcases hcase with ⟨h14', -⟩ | ⟨-, h11', -⟩
    · omega
    · exact h11'
  dsimp only at hcur₃ hphi₃
  -- the end
  obtain ⟨stF, cF, tx₄, cur', hrF, hrep₄, hv, hv', hside, hptr, h4, hlist, hle', hle'', hzF,
    hlF, hfrF, hftF, hcF⟩ :=
    ssTail_runs T ω hfoot hlast stD tx₃ cur₃ hF₃ hA₃ h7₃ h11₃ htour hr₁ hr₂ (by omega)
  have hrun := runs_seq_normal hrA (runs_seq_normal hrB1 (runs_seq_normal hrB2
    (runs_seq_normal hrC (runs_seq_normal hrD hrF))))
  have hcur3 : h + 5 ≤ cur₃ := hF₃.2.2.1
  refine ⟨_, hproc, _, stF, _, tx₄, hrun, hrep₄, hv, hv', hside, h4, hptr ▸ hlist, ?_,
    by omega, by rw [hptr]; rfl, ?_, hzF, hlF, hfrF, fun a ha => hptr ▸ hftF a ha, ?_⟩
  · by_cases hc : (s.markedList r₁).length ≤ (s.markedList r₂).length
    · simp only [ssSide, hc, ite_true]
    · simp only [ssSide, hc, ite_false, one_ne_zero]; omega
  · show cur' + 1 + _ ≤ _
    omega
  · -- the cost
    rw [hYk] at hcF ⊢
    rw [← hphi₃] at hcD
    rw [← hphiA] at hcostB1
    generalize min (s.markedList r₁).length (s.markedList r₂).length = mn at *
    have f1 : (2 * (S.mul * ordStoreLog eCap) + 60) * (mn + 1) =
        2 * (S.mul * ordStoreLog eCap * (mn + 1)) + 60 * (mn + 1) := by ring
    have f2 : S.mul * (mn + 1) * ordStoreLog eCap = S.mul * ordStoreLog eCap * (mn + 1) := by
      ring
    have f3 : 300 * (S.mul + 1) * (mn + 1) * ordStoreLog eCap =
        300 * (S.mul * ordStoreLog eCap * (mn + 1)) + 300 * ((mn + 1) * ordStoreLog eCap) := by
      ring
    have hL : 1 ≤ ordStoreLog eCap := by unfold ordStoreLog; omega
    have f4 : mn + 1 ≤ (mn + 1) * ordStoreLog eCap := Nat.le_mul_of_pos_right _ hL
    have f5 : S.mul * ordStoreLog eCap ≤ S.mul * ordStoreLog eCap * (mn + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega

end Main

/-- **The statement of the helper**, for every program whose procedure `idx b` is the helper
with the tour procedures `nm`, `fm` and `lm`. -/
theorem sig_outSmallSide_runs_of (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (idx : ℕ → ℕ)
    (hH : ∀ p b nm sm fm lm, HasOutProcs p b nm sm fm lm →
      p.procs[idx b]? = some (outSmallSideBody nm fm lm)) :
    sig_outSmallSide_runs HasOutProcs idx := by
  refine ⟨300, ?_⟩
  intro S w vCap eCap p b nm sm fm lm hP hw T tourH r₁ r₂ v v' last h s tx mem pos ω
  exact outSmallSide_body_runs T hw (hH p b nm sm fm lm hP) tourH r₁ r₂ v v' last h s tx mem
    pos ω

end MinCostFlow.SparseCore.Program
