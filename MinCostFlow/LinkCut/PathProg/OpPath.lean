module

public import MinCostFlow.LinkCut.PathProg.OpCutLink

/-!
# Path update and path summary meet the contract

Both operations reroot at `u` and expose `v`. The proofs follow those of cut and link
(`OpCutLink`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

section Width

variable {w b0 : ℕ} {p : Program} {fmt : Format w} (L : ℕ) (hh : 0 < fmt.limbBits)
  (hw : 2 * fmt.limbBits + 2 ≤ w) (hp : p.HasAt b0 (pathTreeBodies fmt.limbBits b0))

theorem extra_ge' : (stepsAt (treeLimbs L) hh hw hp).cost + 400 * treeLimbs L + 2000 ≤
    extra L hh hw hp := by
  unfold extra; omega

/-- A number that fits `L` limbs is at most the value bound. -/
theorem abs_le_valBound {h L n : ℕ} {z : ℤ} (hz : Fits h L z) : |z| ≤ valBound h L n := by
  have h1 := abs_le_of_fits hz
  unfold valBound chgBound
  have : (0 : ℤ) ≤ ((2 * n + 1 : ℕ) : ℤ) * (capacity h L : ℤ) := by positivity
  linarith

/-- The pay of an operation that reroots and exposes: the call costs at most `opRate` per unit
of the reroot and expose plus `X`, and adds at most two stack entries per splice. -/
theorem pay_rerootExpose {c X a b k k' : ℕ} {s s' : PathTreeState} {S S' : List ℕ}
    (hR : opRate (stepsAt (treeLimbs L) hh hw hp) * (a + b) + X ≤
      opRate (stepsAt (treeLimbs L) hh hw hp) * (a + b + 1) + X)
    (hX : X + 2000 ≤ extra L hh hw hp)
    (hc : c ≤ k + X) (hk : k ≤ opRate (stepsAt (treeLimbs L) hh hw hp) * (a + b))
    (hS : S'.length ≤ S.length + 2 * b) (hk' : k' = Nat.log 2 (2 * s.n + 1))
    (h1 : a + sumTreePhi pathPayload s' ≤ sumTreePhi pathPayload s + 12 * k')
    (h2 : b + heavyCount pathPayload s' ≤ heavyCount pathPayload s + 5 * k' + 5) :
    c + pathPhi pathC L s' S' ≤ pathTreeBudget pathC L s.n + pathPhi pathC L s S := by
  have hab := absorb (R := opRate (stepsAt (treeLimbs L) hh hw hp)) (a := a) (b := b)
    (X := extra L hh hw hp) (by omega)
  have hc' : c + 340 * S'.length ≤
      (opRate (stepsAt (treeLimbs L) hh hw hp) + extra L hh hw hp) * (a + b + 1) +
        340 * S.length := by omega
  subst hk'
  exact pay (rate_le L hh hw hp) hc' (by omega) (by omega)

theorem opRate_mono (a b : ℕ) (X : ℕ) :
    opRate (stepsAt (treeLimbs L) hh hw hp) * (a + b) + X ≤
      opRate (stepsAt (treeLimbs L) hh hw hp) * (a + b + 1) + X :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_succ _)) X

include hh hw hp in
/-- Path update meets the contract. -/
theorem apply_done (ω : ℕ → Bool) {b : ℕ} {s : PathTreeState} {S : List ℕ} {args : List ℕ}
    {mem : ℕ → ℕ} {pos : ℕ} (hb : args.head? = some b) (hA : ArenaAt fmt.limbBits L b s S mem)
    (hok : StateOk s S) (hpre : (pathContract fmt L).pre 2 s args mem)
    (hfoot : ∀ a, (pathRep fmt.limbBits L pathC).foot b (s, S) a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hroom : heapArg args + (pathContract fmt L).space 2 s args mem < 2 ^ w) :
    OpDone p fmt L b0 2 b s S args mem pos ω := by
  obtain ⟨-, hfits, hn, hlog, handle, u, v, ta, heap, rfl, hu, hv, hconn, hta, ht, -⟩ := hpre
  obtain rfl : b = handle := (Option.some.inj hb).symm
  set t := readPathTag mem ta fmt.limbBits L with htdef
  have hha : heapArg [b, u, v, ta, heap] = heap := rfl
  have hK : 8 ≤ treeLimbs L := by unfold treeLimbs; omega
  rw [space_op fmt L 2 (by decide), hha] at hroom
  rw [hha] at hfoot hz
  have hend := end_le hfoot
  obtain ⟨hP, ⟨trees, fl, d, W, hI, hF⟩, hE⟩ := hok
  have htf := ht.fits
  have hoka := pathApply_num W (forestB_of_fits W hfits) (numCtx_of_log hh hlog) hu hv
    (abs_le_valBound htf.1) (abs_le_valBound htf.2)
  obtain ⟨o, st', c, hr, ⟨hres, hA', hfr⟩, hc⟩ :=
    applyWrap_runs L hh hw hp ω hA hP hend (by unfold treeSpace; omega) hz hn
      (by have := hu.2; omega) (by have := hv.2; omega) hta ht hoka
  refine opDone_of (body := applyWrap b0) (core_at hp 3 (by decide)) hr hA'
    (stateOk_apply W hI hF hP hE hu hv hconn t) (lctPathApply_n pathPayload s u v t) rfl
    (by rw [hha, hres]; omega) (by rw [hha, hres, space_op fmt L 2 (by decide)]; omega)
    (by rw [hha, hres]; exact hfr) ?_
  have h3 := apply_pot W hu hv hconn t
  have hx := extra_ge' L hh hw hp
  rw [stepsAt_cost] at hx hc
  have hX : 2000 * treeLimbs L + 2000 + 140 * treeLimbs L + 500 + 2000 ≤
      extra L hh hw hp := by omega
  have hc2 : c ≤ rerootExposeCost (stepsAt (treeLimbs L) hh hw hp) s u v +
      (2000 * treeLimbs L + 2000 + 140 * treeLimbs L + 500) :=
    le_of_le_of_eq hc (by ring)
  refine pay_rerootExpose L hh hw hp
    (a := (lctPathSummaryCost pathPayload s u v).2.2.1)
    (b := (lctPathSummaryCost pathPayload s u v).2.2.2)
    (k' := Nat.log 2 (2 * s.n + 1)) (opRate_mono L hh hw hp _ _ _) hX hc2 ?_ ?_ rfl ?_ ?_
  · exact rerootExposeCost_le pathPayload_laws _ W hu hv
  · exact rerootExposeNotes_length_le pathPayload s u v S
  · exact h3.1
  · exact h3.2

include hh hw hp in
/-- Path summary meets the contract. -/
theorem summary_done (ω : ℕ → Bool) {b : ℕ} {s : PathTreeState} {S : List ℕ} {args : List ℕ}
    {mem : ℕ → ℕ} {pos : ℕ} (hb : args.head? = some b) (hA : ArenaAt fmt.limbBits L b s S mem)
    (hok : StateOk s S) (hpre : (pathContract fmt L).pre 3 s args mem)
    (hfoot : ∀ a, (pathRep fmt.limbBits L pathC).foot b (s, S) a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hroom : heapArg args + (pathContract fmt L).space 3 s args mem < 2 ^ w) :
    OpDone p fmt L b0 3 b s S args mem pos ω := by
  obtain ⟨-, hfits, hn, hlog, handle, u, v, heap, rfl, hu, hv, hconn, hfit'⟩ := hpre
  obtain rfl : b = handle := (Option.some.inj hb).symm
  have hha : heapArg [b, u, v, heap] = heap := rfl
  have hK : L ≤ treeLimbs L := by unfold treeLimbs; omega
  rw [space_op fmt L 3 (by decide), hha] at hroom
  rw [hha] at hfoot hz
  have hend := end_le hfoot
  obtain ⟨hP, ⟨trees, fl, d, W, hI, hF⟩, hE⟩ := hok
  have hokr := (rerootExpose_num W (forestB_of_fits W hfits) (numCtx_of_log hh hlog) hu hv).1
  have hfit : PathSummaryFits fmt.limbBits L (lctPathSummary pathPayload s u v).2 := by
    rw [lctPathSummary_snd]
    exact (hfit' v (by rw [lctPathSummary_n]; have := hv.2; omega)).2.1
  obtain ⟨o, st', c, hr, ⟨hres, hA', hfr, hsum⟩, hc⟩ :=
    summaryWrap_runs L hh hw hp ω hA hP hend (by unfold treeSpace; omega) hz hn
      (by have := hu.2; omega) (by have := hv.2; omega) hokr hfit
  refine opDone_of (body := summaryWrap b0) (core_at hp 4 (by decide)) hr hA'
    (stateOk_summary W hI hF hP hE hu hv) (lctPathSummary_n s u v) ⟨rfl, by rw [hha]; exact hsum⟩
    (by rw [hha, hres]; omega) (by rw [hha, hres, space_op fmt L 3 (by decide)]; omega)
    (by rw [hha, hres]; exact hfr) ?_
  have h3 := summary_pot W hu hv hconn
  have hx := extra_ge' L hh hw hp
  rw [stepsAt_cost] at hx
  have hK8 : 8 ≤ treeLimbs L := by unfold treeLimbs; omega
  have hX : 60 * L + 400 + 2000 ≤ extra L hh hw hp := by omega
  have hc2 : c ≤ rerootExposeCost (stepsAt (treeLimbs L) hh hw hp) s u v + (60 * L + 400) :=
    hc.trans_eq (Nat.add_assoc _ _ _)
  refine pay_rerootExpose L hh hw hp
    (a := (lctPathSummaryCost pathPayload s u v).2.2.1)
    (b := (lctPathSummaryCost pathPayload s u v).2.2.2)
    (k' := Nat.log 2 (2 * s.n + 1)) (opRate_mono L hh hw hp _ _ _) hX hc2 ?_ ?_ rfl ?_ ?_
  · exact rerootExposeCost_le pathPayload_laws _ W hu hv
  · exact rerootExposeNotes_length_le pathPayload s u v S
  · exact h3.1
  · exact h3.2

end Width

end MinCostFlow.LinkCut.PathProg
