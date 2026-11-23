module

public import MinCostFlow.LinkCut.PathProg.OpPath
public import MinCostFlow.Num.FixedDivideFacts

/-!
# Point read, point write and find-ready meet the contract

Each of these operations exposes one node. The node is active for the contract, so it is
active in the witness that the representation keeps (`active_of`). A point write has the
potentials of its expose (`write_potentials`).

Find-ready has two cases. If it finds a ready edge, it pays like an expose, and the entries it
pops are paid by the stack potential (`findCost_le`). If it finds nothing, the state is
unchanged, the stack becomes empty, and the popped entries pay for the whole call
(`findCost_zero`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

/-- A summary that fits `L` limbs fits more limbs. -/
theorem summaryFits_mono {h L K : ℕ} (hLK : L ≤ K) {s : PathSummary}
    (hs : PathSummaryFits h L s) : PathSummaryFits h K s := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨fits_of_length_le hLK h1, fits_of_length_le hLK h2, ?_⟩
  cases hd : s.detector with
  | none => trivial
  | some z =>
    rw [hd] at h3
    exact fits_of_length_le hLK h3

/-- The budget pays for a call of at most `110` steps. -/
theorem budget_ge (L n : ℕ) : 110 ≤ pathTreeBudget pathC L n := by
  unfold pathTreeBudget pathC
  have h1 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc 110 ≤ 25 * (10000000 * (L + 1) ^ 2) * 1 := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

/-- `F` per unit and `60` once fit the rate `R + (F + Y)` when `60 ≤ Y`. -/
theorem absorb_find {R F Y k : ℕ} (hk : 1 ≤ k) (hY : 60 ≤ Y) :
    F * k + 60 ≤ (R + (F + Y)) * k := by
  have e : (R + (F + Y)) * k = R * k + F * k + Y * k := by ring
  have : Y ≤ Y * k := Nat.le_mul_of_pos_right _ hk
  omega

section Width

variable {w b0 : ℕ} {p : Program} {fmt : Format w} (L : ℕ) (hh : 0 < fmt.limbBits)
  (hw : 2 * fmt.limbBits + 2 ≤ w) (hp : p.HasAt b0 (pathTreeBodies fmt.limbBits b0))

theorem extra_ge'' : (stepsAt (treeLimbs L) hh hw hp).cost + 400 * treeLimbs L + 3000 ≤
    extra L hh hw hp := by
  unfold extra findRate; omega

theorem expose_rate : 2 * exposeRate (stepsAt (treeLimbs L) hh hw hp) ≤
    opRate (stepsAt (treeLimbs L) hh hw hp) := by
  unfold opRate; omega

/-- An expose of an active node costs at most `opRate` per unit it counts. -/
theorem exposeCost_op {s : PathTreeState} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees fl d) {x : ℕ} (hx : x ∈ trees.flatMap AuxTree.toList) :
    exposeCost (stepsAt (treeLimbs L) hh hw hp) s x ≤
      opRate (stepsAt (treeLimbs L) hh hw hp) *
        ((lctExposeCost pathPayload s x).2.1 + (lctExposeCost pathPayload s x).2.2) :=
  (exposeCost_le' pathPayload_laws _ W hx).trans
    (Nat.mul_le_mul_right _ (expose_rate L hh hw hp))

include hh hw hp in
/-- Point read meets the contract. -/
theorem read_done (ω : ℕ → Bool) {b : ℕ} {s : PathTreeState} {S : List ℕ} {args : List ℕ}
    {mem : ℕ → ℕ} {pos : ℕ} (hb : args.head? = some b) (hA : ArenaAt fmt.limbBits L b s S mem)
    (hok : StateOk s S) (hpre : (pathContract fmt L).pre 4 s args mem)
    (hfoot : ∀ a, (pathRep fmt.limbBits L pathC).foot b (s, S) a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hroom : heapArg args + (pathContract fmt L).space 4 s args mem < 2 ^ w) :
    OpDone p fmt L b0 4 b s S args mem pos ω := by
  obtain ⟨-, hfits, hn, hlog, handle, x, heap, rfl, hact, hfit'⟩ := hpre
  obtain rfl : b = handle := (Option.some.inj hb).symm
  have hha : heapArg [b, x, heap] = heap := rfl
  have hK : 8 ≤ treeLimbs L := by unfold treeLimbs; omega
  have hLK : L ≤ treeLimbs L := by unfold treeLimbs; omega
  rw [space_op fmt L 4 (by decide), hha] at hroom
  rw [hha] at hfoot hz
  have hend := end_le hfoot
  obtain ⟨hP, ⟨trees, fl, d, W, hI, hF⟩, hE⟩ := hok
  have hx := active_of W hact
  have hxle := active_le W hx
  have hokx := (expose_num' W (forestB_of_fits W hfits) (numCtx_of_log hh hlog) hx).1
  have hfit := (hfit' x (by rw [lctExpose_n]; exact hxle)).1
  obtain ⟨o, st', c, hr, ⟨hres, hA', hfr, hval⟩, hc⟩ :=
    readWrap_runs L hh hw hp ω hA hP hend (by unfold treeSpace; omega) hz hn hxle hokx hfit
  refine opDone_of (body := readWrap b0) (core_at hp 5 (by decide)) hr hA'
    (stateOk_expose W hI hF hP hE hx) (lctExpose_n pathPayload s x)
    ⟨rfl, by rw [hha]; exact hval⟩
    (by rw [hha, hres]; omega) (by rw [hha, hres, space_op fmt L 4 (by decide)]; omega)
    (by rw [hha, hres]; exact hfr) ?_
  have h3 := expose_pot W hx
  have hx' := extra_ge' L hh hw hp
  rw [stepsAt_cost] at hx'
  have hX : 68 * L + 380 + 2000 ≤ extra L hh hw hp := by omega
  have hc2 : c ≤ exposeCost (stepsAt (treeLimbs L) hh hw hp) s x + (68 * L + 380) :=
    hc.trans_eq (Nat.add_assoc _ _ _)
  refine pay_rerootExpose L hh hw hp
    (a := (lctExposeCost pathPayload s x).2.1) (b := (lctExposeCost pathPayload s x).2.2)
    (k' := Nat.log 2 (2 * s.n + 1)) (opRate_mono L hh hw hp _ _ _) hX hc2 ?_ ?_ rfl ?_ ?_
  · exact exposeCost_op L hh hw hp W hx
  · exact exposeNotes_length_le pathPayload s x S
  · have := h3.1; omega
  · have := h3.2; omega

include hh hw hp in
/-- Point write meets the contract. -/
theorem write_done (ω : ℕ → Bool) {b : ℕ} {s : PathTreeState} {S : List ℕ} {args : List ℕ}
    {mem : ℕ → ℕ} {pos : ℕ} (hb : args.head? = some b) (hA : ArenaAt fmt.limbBits L b s S mem)
    (hok : StateOk s S) (hpre : (pathContract fmt L).pre 5 s args mem)
    (hfoot : ∀ a, (pathRep fmt.limbBits L pathC).foot b (s, S) a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hroom : heapArg args + (pathContract fmt L).space 5 s args mem < 2 ^ w) :
    OpDone p fmt L b0 5 b s S args mem pos ω := by
  obtain ⟨-, hfits, hn, hlog, handle, x, va, heap, rfl, hxe, hact, hva, hval, hsome, hfit'⟩ := hpre
  obtain rfl : b = handle := (Option.some.inj hb).symm
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  rw [he] at hval hfit'
  have hha : heapArg [b, x, va, heap] = heap := rfl
  have hK : 8 ≤ treeLimbs L := by unfold treeLimbs; omega
  have hLK : L ≤ treeLimbs L := by unfold treeLimbs; omega
  rw [space_op fmt L 5 (by decide), hha] at hroom
  rw [hha] at hfoot hz
  have hend := end_le hfoot
  obtain ⟨hP, ⟨trees, fl, d, W, hI, hF⟩, hE⟩ := hok
  have hx := active_of W hact
  have hxle := active_le W hx
  have hokx := (expose_num' W (forestB_of_fits W hfits) (numCtx_of_log hh hlog) hx).1
  have hokp : x ≠ 0 → (pathOk fmt.limbBits (treeLimbs L)).sumOk (pullSum pathPayload
      ((lctExpose pathPayload s x).splay.updateNode x fun nd => { nd with val := some e }) x) := by
    intro hx0
    have hs := (hfit' x (by rw [pathTreeWrite_n, lctExpose_n]; exact hxle)).2.1
    have hnode : (pathTreeWrite s x (some e)).splay.nodes x = _ := pull_nodes_self hx0
    rw [hnode] at hs
    exact summaryFits_mono hLK hs
  obtain ⟨o, st', c, hr, ⟨hres, hA', hfr⟩, hc⟩ :=
    writeWrap_runs L hh hw hp ω hA hP hend (by unfold treeSpace; omega) hz hn hxle hokx hva hval
      hokp
  refine opDone_of (body := writeWrap b0) (core_at hp 6 (by decide)) hr hA'
    (stateOk_write W hI hF hP hE hxe hx (some e))
    ((pathTreeWrite_n s x (some e)).trans (lctExpose_n pathPayload s x))
    (by
      show pathTreeWrite s x (some e) = pathTreeWrite s x (readPathEdge mem va fmt.limbBits L)
      rw [he])
    (by rw [hha, hres]; omega) (by rw [hha, hres, space_op fmt L 5 (by decide)]; omega)
    (by rw [hha, hres]; exact hfr) ?_
  have h3 := expose_pot W hx
  rw [← (write_potentials s x (some e)).1, ← (write_potentials s x (some e)).2] at h3
  have hx' := extra_ge'' L hh hw hp
  rw [stepsAt_cost] at hx' hc
  have hX : 300 * treeLimbs L + (2000 * treeLimbs L + 2000) + 68 * L + 1200 + 2000 ≤
      extra L hh hw hp := by omega
  have hc2 : c ≤ exposeCost (stepsAt (treeLimbs L) hh hw hp) s x +
      (300 * treeLimbs L + (2000 * treeLimbs L + 2000) + 68 * L + 1200) :=
    le_of_le_of_eq hc (by ring)
  refine pay_rerootExpose L hh hw hp
    (a := (lctExposeCost pathPayload s x).2.1) (b := (lctExposeCost pathPayload s x).2.2)
    (k' := Nat.log 2 (2 * s.n + 1)) (opRate_mono L hh hw hp _ _ _) hX hc2 ?_ ?_ rfl ?_ ?_
  · exact exposeCost_op L hh hw hp W hx
  · exact exposeNotes_length_le pathPayload s x S
  · have := h3.1; omega
  · have := h3.2; omega

include hh hw hp in
/-- Find-ready meets the contract. -/
theorem find_done (ω : ℕ → Bool) {b : ℕ} {s : PathTreeState} {S : List ℕ} {args : List ℕ}
    {mem : ℕ → ℕ} {pos : ℕ} (hb : args.head? = some b) (hA : ArenaAt fmt.limbBits L b s S mem)
    (hok : StateOk s S) (hpre : (pathContract fmt L).pre 6 s args mem)
    (hfoot : ∀ a, (pathRep fmt.limbBits L pathC).foot b (s, S) a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hroom : heapArg args + (pathContract fmt L).space 6 s args mem < 2 ^ w) :
    OpDone p fmt L b0 6 b s S args mem pos ω := by
  obtain ⟨-, hfits, hn, hlog, handle, heap, rfl, -⟩ := hpre
  obtain rfl : b = handle := (Option.some.inj hb).symm
  have hha : heapArg [b, heap] = heap := rfl
  rw [space_op fmt L 6 (by decide), hha] at hroom
  rw [hha] at hfoot hz
  have hend := end_le hfoot
  obtain ⟨hP, ⟨trees, fl, d, W, hI, hF⟩, hE⟩ := hok
  have hokf := findOk_of W hF hh hfits hlog S.reverse
  obtain ⟨o, st', c, hr, ⟨hres, hA', hfr, hout⟩, hc⟩ :=
    findWrap_runs L hh hw hp ω hA hP hend (by unfold treeSpace; omega) hz hn hokf
  have hI' : ReadyIdx s trees S.reverse.reverse := by rw [List.reverse_reverse]; exact hI
  have hbody : p.procs[b0 + 1 + 6]? = some (findWrap b0) := core_at hp 7 (by decide)
  have hv1 : heap ≤ o.value := by omega
  have hv2 : o.value ≤ heap + (20 * treeLimbs L + 100) := by omega
  rw [← hres] at hfr
  rcases findLoop_spec W hE hF S.reverse hI' with ⟨h0, hs, hS, hno⟩ | ⟨h0, hready, hs, S'', hI'', hS⟩
  · -- nothing is ready: the state stays, and the stack empties
    rw [hs, hS] at hA'
    have hok' : StateOk s [] := ⟨hP, ⟨trees, fl, d, W, fun t ht hr' =>
      absurd ((exists_ready_iff W hE).mpr ⟨t, ht, (pathRs_iff _).mp hr'⟩) hno, hF⟩, hE⟩
    refine opDone_of hbody hr hA' hok' rfl (Or.inl ⟨by rw [hha, hout, h0], rfl, hno⟩)
      (by rw [hha]; exact hv1) (by rw [hha, space_op fmt L 6 (by decide)]; exact hv2)
      (by rw [hha]; exact hfr) ?_
    have h1 := findCost_zero (stepsAt (treeLimbs L) hh hw hp)
      (testsAt (treeLimbs L) hh hw hp (treeLimbs_pos L)) W hE hF S.reverse hI' h0
    rw [testsAt_cost, List.length_reverse] at h1
    have h2 := budget_ge L s.n
    unfold pathPhi
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    omega
  · -- a ready edge is found and exposed
    set y := (findLoop pathPayload pathRs pathRv s S.reverse).2.2 with hydef
    have hy := active_of W hready.2.1
    rw [hs] at hA'
    have hok' : StateOk (lctExpose pathPayload s y)
        (findLoop pathPayload pathRs pathRv s S.reverse).2.1 := by
      rw [hS]; exact stateOk_expose W hI'' hF hP hE hy
    refine opDone_of hbody hr hA' hok' (lctExpose_n pathPayload s y)
      (Or.inr ⟨y, by rw [hha, hout], hready, rfl⟩)
      (by rw [hha]; exact hv1) (by rw [hha, space_op fmt L 6 (by decide)]; exact hv2)
      (by rw [hha]; exact hfr) ?_
    have h1 := findCost_le (stepsAt (treeLimbs L) hh hw hp)
      (testsAt (treeLimbs L) hh hw hp (treeLimbs_pos L)) W hF S.reverse
    rw [testsAt_cost, List.length_reverse, ← hydef] at h1
    have h3 := expose_pot W hy
    have hab := absorb_find (R := opRate (stepsAt (treeLimbs L) hh hw hp))
      (F := findRate (stepsAt (treeLimbs L) hh hw hp)
        (testsAt (treeLimbs L) hh hw hp (treeLimbs_pos L)))
      (Y := (stepsAt (treeLimbs L) hh hw hp).cost + 400 * treeLimbs L + 2000)
      (k := (lctExposeCost pathPayload s y).2.1 + (lctExposeCost pathPayload s y).2.2 + 1)
      (by omega) (by omega)
    have hc' : c + 340 * (findLoop pathPayload pathRs pathRv s S.reverse).2.1.length ≤
        (opRate (stepsAt (treeLimbs L) hh hw hp) + extra L hh hw hp) *
          ((lctExposeCost pathPayload s y).2.1 + (lctExposeCost pathPayload s y).2.2 + 1) +
          340 * S.length := by
      have e : extra L hh hw hp = findRate (stepsAt (treeLimbs L) hh hw hp)
          (testsAt (treeLimbs L) hh hw hp (treeLimbs_pos L)) +
          ((stepsAt (treeLimbs L) hh hw hp).cost + 400 * treeLimbs L + 2000) := by
        unfold extra; ring
      rw [e]
      omega
    exact pay (rate_le L hh hw hp) hc' (by have := h3.1; omega) (by have := h3.2; omega)

end Width

end MinCostFlow.LinkCut.PathProg
