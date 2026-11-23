module

public import MinCostFlow.Spanner.ProgTask3RoundBody

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# The End State of Task 3

When the round loop of `task3Body` stops, the flag `cont` is `0`, so every edge of `J` is
embedded. This file turns the outer invariant `T3OuterAt` at that point into the output
condition `Task3OutAt` of the contract (`t3_outAt_of_final`).
-/

/-- An edge count bounded in `ℝ` by `γ` is bounded in `ℕ` by `⌊γ⌋₊`, so the maximum over the
edges of `J` is bounded by `γ` too. -/
lemma t3_length_le_real {J : Graph} {emb : ℕ → Walk} {γ : ℝ} (hγ : 0 ≤ γ)
    (h : ∀ eJ < J.m, ((emb eJ).edges.length : ℝ) ≤ γ) : (length J emb : ℝ) ≤ γ := by
  have hnat : length J emb ≤ ⌊γ⌋₊ := by
    unfold length
    rw [Finset.fold_max_le]
    exact ⟨Nat.zero_le _, fun eJ heJ => Nat.le_floor (h eJ (Finset.mem_range.mp heJ))⟩
  calc (length J emb : ℝ) ≤ (⌊γ⌋₊ : ℝ) := by exact_mod_cast hnat
    _ ≤ γ := Nat.floor_le hγ

/-- At the end of the round loop, the outer invariant gives the output condition of Task 3. -/
lemma t3_outAt_of_final {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {η : ℕ} {d : T3OuterData} {st : State} {Φ : ℕ} (hO : T3OuterAt ctx lay η d st Φ)
    (hη : η ≤ eta2Bound inp.J) (hU : ¬ (unembeddedSet2Pure inp.J d.emb).Nonempty) :
    Task3OutAt impl inp mem₀ st.mem d.hCur w := by
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hlo := hO.hCur_lo
  -- Every edge is embedded.
  have hall : ∀ eJ < inp.J.m, ∃ P, d.emb eJ = some P := fun eJ heJ => by
    rcases hE : d.emb eJ with _ | P
    · exact absurd ⟨eJ, by simp [unembeddedSet2Pure, heJ, hE]⟩ hU
    · exact ⟨P, rfl⟩
  have hU0 : (unembeddedSet2Pure inp.J d.emb).card = 0 :=
    Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU)
  have hg : d.getPathCnt ≤ inp.J.m := le_trans hO.getPath_cnt_le (Nat.sub_le _ _)
  set γW := impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
    (Task1Input.mwCap impl inp.J) with hγW
  have hmax : d.hCur ≤ Task3Input.maxHeapEnd impl inp := by
    rw [show Task3Input.maxHeapEnd impl inp = Task3Input.staticEndCap impl inp + 5 * inp.J.m +
      (eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW) * Task3Input.dsOneW impl inp.J +
      inp.J.m * (2 * γW + 3) from rfl]
    have hr_bd : η * inp.J.m ≤ eta2Bound inp.J * inp.J.m := Nat.mul_le_mul_right _ hη
    have hdel_bd := le_trans hO.del_le_econgUpd
      (le_trans hO.econgUpd_W (Nat.mul_le_mul_right γW hg))
    have hm1 := Nat.mul_le_mul_right (Task3Input.dsOneW impl inp.J)
      (show η * inp.J.m + d.getPathCnt + d.delCnt ≤
        eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW by omega)
    have hm2 := Nat.mul_le_mul_right (2 * γW + 3) hg
    have hh0 : d.hCur ≤ Task3Input.staticEndCap impl inp + 5 * inp.J.m +
        (η * inp.J.m + d.getPathCnt + d.delCnt) * Task3Input.dsOneW impl inp.J +
        d.getPathCnt * (2 * γW + 3) := hO.hCur_bd
    omega
  have hS := hO.staticMem
  have hγ_pos : 0 ≤ ctx.wd.γ_ExpPath := by
    have := ctx.hw_okW.γ_ExpPath_ge; have := ctx.hw_okW.φ_ds_pos
    have h2 : (2 : ℝ) ≤ 1 / ctx.wd.φ_ds := by
      rw [le_div_iff₀ ctx.hw_okW.φ_ds_pos]; linarith [ctx.hw_okW.φ_ds_half]
    linarith
  rw [hb1] at hb2
  have hEta := hO.eta2_eq; have hGP := hO.getPath_eq; have hDel := hO.del_eq
  have hEU := hO.econgUpd_eq; have hHC := hO.hCur_eq
  rw [hb1] at hEta hGP hDel hEU hHC
  have hEJ : st.mem (inp.v2 + t3OffEmbJW) = lay.embJWAddr := hb1 ▸ hS.2.1
  have hwalk : ∀ eJ < inp.J.m, st.mem (lay.embJWAddr + eJ) + (partialToWalk d.emb eJ).encode.length ≤
      d.hCur ∧ WalkAt st.mem (st.mem (lay.embJWAddr + eJ)) (partialToWalk d.emb eJ) := by
    intro eJ heJ
    obtain ⟨P, hP⟩ := hall eJ heJ
    have hm := hO.emb_mem eJ heJ
    rw [hP] at hm
    obtain ⟨-, h2, h3⟩ := hm
    simp only [partialToWalk, hP, Option.getD_some]
    exact ⟨h2, h3⟩
  refine ⟨hS.1, hO.zero_from, by unfold t3HdrSize; omega, hmax, ctx.wInp, ctx.WSubs,
    partialToWalk d.emb, η, d.getPathCnt, d.delCnt, d.econgUpd, ctx.hWInpH', ctx.hWInpEmb,
    ctx.hWInpJ, ctx.hWInpJAddr,
    ⟨ctx.memPre, ctx.memT1, ctx.v1, ctx.hT1Agr, ctx.hv1_le, ctx.hT1, ctx.hSlot5, ctx.hSlot3, ctx.hStat, ctx.hPrepEnd,
      ctx.outAt⟩,
    ⟨_, ctx.hStat⟩, ctx.hws, ctx.hw_ok, ?_, hEta, hGP, hDel, hEU, hHC, ?_, ?_, ?_, hη,
    hO.econg_le_round, hO.econg_j0_le, ?_, ?_, hg, ?_, hO.econgUpd_bound⟩
  · rw [show inp.v2 = inp.v2 + t3OffEmbJW from rfl, hEJ, hb2]; rfl
  · intro j hj
    rw [show inp.v2 + t3HdrSize = lay.embJWAddr by rw [hb2]; rfl]
    exact (hwalk j hj).2
  · rw [show inp.v2 + t3HdrSize = lay.embJWAddr by rw [hb2]; rfl]
    exact ⟨by omega, fun j hj => (hwalk j hj).1⟩
  · refine ⟨hO.emb_part.1, fun j hj => ?_⟩
    obtain ⟨P, hP⟩ := hall j hj
    simp only [partialToWalk, hP, Option.getD_some]
    exact hO.emb_part.2 j hj P hP
  · intro eJ heJ
    have h := hO.emb_len_real eJ heJ
    have h2 : ((partialToWalk d.emb eJ).edges.length : ℝ) ≤ (⌈ctx.wd.γ_ExpPath⌉₊ : ℝ) :=
      le_trans h (Nat.le_ceil _)
    exact_mod_cast h2
  · exact t3_length_le_real hγ_pos hO.emb_len_real
  · calc (d.delCnt : ℝ) ≤ (d.econgUpd : ℝ) := by exact_mod_cast hO.del_le_econgUpd
      _ ≤ _ := hO.econgUpd_bound

end MinCostFlow.Spanner
