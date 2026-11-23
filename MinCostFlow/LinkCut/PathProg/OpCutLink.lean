module

public import MinCostFlow.LinkCut.PathProg.OpBase

/-!
# Cut and link meet the contract

Each proof reads the arguments from the precondition, gets the numeric facts from the fits
premises, runs the wrapper, and pays. The rate is `opRate` of the payload steps plus a fixed
amount `extra` that covers the wrapper and the stack entries (`unit_le`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

section Width

variable {w b0 : ℕ} {p : Program} {fmt : Format w} (L : ℕ) (hh : 0 < fmt.limbBits)
  (hw : 2 * fmt.limbBits + 2 ≤ w) (hp : p.HasAt b0 (pathTreeBodies fmt.limbBits b0))

/-- The fixed part of the rate: everything in `unit_le` except `opRate`. -/
def extra : ℕ :=
  findRate (stepsAt (treeLimbs L) hh hw hp) (testsAt (treeLimbs L) hh hw hp (treeLimbs_pos L)) +
    (stepsAt (treeLimbs L) hh hw hp).cost + 400 * treeLimbs L + 2000

theorem rate_le : opRate (stepsAt (treeLimbs L) hh hw hp) + extra L hh hw hp ≤ pathC * (L + 1) ^ 2 := by
  simp only [extra, ← Nat.add_assoc]
  exact unit_le L hh hw hp

theorem extra_ge : 400 * treeLimbs L + 2000 ≤ extra L hh hw hp := by
  unfold extra; omega

theorem cost_ge : (stepsAt (treeLimbs L) hh hw hp).cost + 2000 ≤ extra L hh hw hp := by
  unfold extra; omega

include hh hw hp in
/-- Cut meets the contract. -/
theorem cut_done (ω : ℕ → Bool) {b : ℕ} {s : PathTreeState} {S : List ℕ} {args : List ℕ}
    {mem : ℕ → ℕ} {pos : ℕ} (hb : args.head? = some b) (hA : ArenaAt fmt.limbBits L b s S mem)
    (hok : StateOk s S) (hpre : (pathContract fmt L).pre 1 s args mem)
    (hfoot : ∀ a, (pathRep fmt.limbBits L pathC).foot b (s, S) a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hroom : heapArg args + (pathContract fmt L).space 1 s args mem < 2 ^ w) :
    OpDone p fmt L b0 1 b s S args mem pos ω := by
  obtain ⟨-, hfits, hn, hlog, handle, u, v, heap, rfl, hu, hv, -⟩ := hpre
  obtain rfl : b = handle := (Option.some.inj hb).symm
  have hha : heapArg [b, u, v, heap] = heap := rfl
  rw [space_op fmt L 1 (by decide), hha] at hroom
  rw [hha] at hfoot hz
  have hend := end_le hfoot
  obtain ⟨hP, ⟨trees, fl, d, W, hI, hF⟩, hE⟩ := hok
  have hokc := cut_num W (forestB_of_fits W hfits) (numCtx_of_log hh hlog) hu hv
  obtain ⟨o, st', c, hr, ⟨hval, hA', hfr⟩, hc⟩ :=
    cutWrap_runs L hh hw hp ω hA hP hend (by unfold treeSpace; omega) hz hn hokc
  refine opDone_of (body := cutWrap b0) (core_at hp 2 (by decide)) hr hA'
    (stateOk_cut W hI hF hP hE hu hv) (lctCut_n s u v) rfl (by rw [hha, hval])
    (by rw [hha, hval]; omega) (by rw [hha, hval]; exact hfr) ?_
  have h1 := cutCost_le pathPayload_laws (stepsAt (treeLimbs L) hh hw hp) W hu hv
  have h2 := cutNotes_length_le pathPayload s u v S
  have h3 := cut_pot W u v
  have hab := absorb (R := opRate (stepsAt (treeLimbs L) hh hw hp))
    (a := (lctCutCost pathPayload s u v).2.1) (b := (lctCutCost pathPayload s u v).2.2)
    (le_trans (by omega) (extra_ge L hh hw hp))
  have hx := extra_ge L hh hw hp
  have hc' : c + 340 * (cutNotes pathPayload s u v S).length ≤
      (opRate (stepsAt (treeLimbs L) hh hw hp) + extra L hh hw hp) *
        ((lctCutCost pathPayload s u v).2.1 + (lctCutCost pathPayload s u v).2.2 + 1) +
        340 * S.length := by omega
  exact pay (rate_le L hh hw hp) hc' (by omega) (by omega)

include hh hw hp in
/-- Link meets the contract. -/
theorem link_done (ω : ℕ → Bool) {b : ℕ} {s : PathTreeState} {S : List ℕ} {args : List ℕ}
    {mem : ℕ → ℕ} {pos : ℕ} (hb : args.head? = some b) (hA : ArenaAt fmt.limbBits L b s S mem)
    (hok : StateOk s S) (hpre : (pathContract fmt L).pre 0 s args mem)
    (hfoot : ∀ a, (pathRep fmt.limbBits L pathC).foot b (s, S) a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hroom : heapArg args + (pathContract fmt L).space 0 s args mem < 2 ^ w) :
    OpDone p fmt L b0 0 b s S args mem pos ω := by
  obtain ⟨-, hfits, hn, hlog, handle, u, v, va, heap, rfl, hu, hv, hnc, hf, hva, hval, hsome, -⟩ :=
    hpre
  obtain rfl : b = handle := (Option.some.inj hb).symm
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  rw [he] at hval
  have hha : heapArg [b, u, v, va, heap] = heap := rfl
  rw [space_op fmt L 0 (by decide), hha] at hroom
  rw [hha] at hfoot hz
  have hend := end_le hfoot
  obtain ⟨hP, ⟨trees, fl, d, W, hI, hF⟩, hE⟩ := hok
  have huv : u ≠ v := by
    rintro rfl
    exact hnc ((conn_iff W hu hv).mpr rfl)
  have hcap : (capacity fmt.limbBits L : ℤ) ≤ valBound fmt.limbBits L s.n := by
    unfold valBound chgBound
    have : (0 : ℤ) ≤ ((2 * s.n + 1 : ℕ) : ℤ) * (capacity fmt.limbBits L : ℤ) := by positivity
    linarith
  have hokl := link_num W (forestB_of_fits W hfits) (numCtx_of_log hh hlog) hu hv
    ((valB_of_fits hval.fits).mono hcap)
  obtain ⟨o, st', c, hr, ⟨hres, hA', hfr, hfh⟩, hc⟩ :=
    linkWrap_runs L hh hw hp ω hA hP hend (by unfold treeSpace; omega) hz hn
      (by have := hu.2; omega) (by have := hv.2; omega) (freeHead_le W) hva hval hokl
  refine opDone_of (body := linkWrap b0) (core_at hp 1 (by decide)) hr hA'
    (stateOk_link W hI hF hP hE hu hv hnc hf (some e)) (lctLink_n s u v (some e))
    ⟨by show lctLink pathPayload s u v (some e) =
          lctLink pathPayload s u v (readPathEdge mem va fmt.limbBits L)
        rw [he], by rw [hha]; exact hfh⟩
    (by rw [hha, hres]; omega) (by rw [hha, hres, space_op fmt L 0 (by decide)]; omega)
    (by rw [hha, hres]; exact hfr) ?_
  have h1 := linkCost_le pathPayload_laws (stepsAt (treeLimbs L) hh hw hp) W hu hv huv hf (some e)
  have h2 := linkNotes_length_le pathPayload s (isVertex_ne_zero hu) (isVertex_ne_zero hv) huv hf
    (some e) S
  have h3 := link_pot W hu hv hnc hf (some e)
  have hab := absorb (R := opRate (stepsAt (treeLimbs L) hh hw hp))
    (a := (lctLinkCost pathPayload s u v (some e)).2.1)
    (b := (lctLinkCost pathPayload s u v (some e)).2.2)
    (le_trans (by omega) (extra_ge L hh hw hp))
  have hx := extra_ge L hh hw hp
  exact pay (rot := (lctLinkCost pathPayload s u v (some e)).2.1)
    (spl := (lctLinkCost pathPayload s u v (some e)).2.2) (rate_le L hh hw hp) (by omega)
    (by omega) (by omega)

end Width

end MinCostFlow.LinkCut.PathProg
