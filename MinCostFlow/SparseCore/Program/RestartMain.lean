module

public import MinCostFlow.SparseCore.Program.RestartLoop
import MinCostFlow.SparseCore.Program.SpanBucket

/-!
# The restart of a branch on the machine (`RestartMain`)

`restartBranch_runs` proves `RestartBranchSpec`: the program `restartBranchStmt` restarts the
listed slots of a branch. The proof follows the three steps of the program.
1. The bundle piece runs (`BunRestartAt.runs`). It writes only to its own footprints and above
   `h`, so the bucket spanners and the view of `S_cur` are still in memory (`DSRep.Local`).
2. The loop runs (`restartLoop_triple`). It writes only to the footprint of the spanners and
   above the heap pointer `h1` that the bundle piece returned, so the new bundles, the tour, the
   view and the exported graphs are still in memory.
3. The rebuild of the branch data of P10 runs (`ScurRebuildAt.runs`) on the new spanners. It writes below its heap
   pointer only to its own footprint.
The cost is the sum of the three parts. The loop pays for each round the cost bound of operation
`0` minus the increase of the potential of the spanners (`loopCost_le`), so the total is in the
amortized form of the statement.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

private theorem sum_map_const_add (c : ℕ) (X : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map fun j => c + X j).sum = c * n + ((List.range n).map X).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ', sum_range_succ', ih, Nat.mul_succ]
    omega

/-- The amortized cost of the loop: the round bounds plus the last potential are at most `41`
per round, the bounds of operation `0`, and the first potential. -/
theorem loopCost_le (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (g : ℕ → MGraph)
    (slots : List ℕ)
    (hph : ∀ j < slots.length, specPhi P (spanAfter S6 g (slots.take (j + 1))) ≤
      spanActivateCost P (g (slots.getD j 0)) + specPhi P (spanAfter S6 g (slots.take j))) :
    rangeCost (loopStepCost P S6 g slots) 0 slots.length +
        specPhi P (spanAfter S6 g (slots.take slots.length)) ≤
      41 * slots.length + (slots.map fun s => spanActivateCost P (g s)).sum +
        specPhi P (spanAfter S6 g (slots.take 0)) := by
  rw [rangeCost_zero_eq_range]
  have hstep : loopStepCost P S6 g slots = fun j => 41 +
      (spanActivateCost P (g (slots.getD j 0)) + specPhi P (spanAfter S6 g (slots.take j)) -
        specPhi P (spanAfter S6 g (slots.take (j + 1)))) := by
    funext j; unfold loopStepCost; rw [argsSize_restartLoopArgs]
  rw [hstep, sum_map_const_add]
  have ht := sum_tele (fun j => spanActivateCost P (g (slots.getD j 0)))
    (fun j => specPhi P (spanAfter S6 g (slots.take j))) slots.length hph
  rw [sum_range_getD (fun s => spanActivateCost P (g s))] at ht
  omega

/-- **The restart of a branch** (`RestartBranchSpec`). -/
theorem restartBranch_runs {slotCap eCap k : ℕ} (P : DSParams) (cap : ℕ) (p : Program)
    (f fBun bSpan fScur : ℕ) (I5 : BunRestartAt P.w slotCap eCap k p fBun)
    (I7 : ScurRebuildAt P cap p fScur) :
    RestartBranchSpec P cap p f fBun bSpan fScur I5 I7 := by
  intro bunTbl tourH spanTbl scurH slotsPtr h b4 j slots S x cord tx S6 x6 v y s4 x4 cs ord
    mem pos ω spaceBound hf hp hbunW htourW hspanW hscurW hslotsPtrW hhW hb4W hjW hLW hSplitW hVW
    hEW hw16 hlist hlist_h hnd hfree hSact hS6act hok hk hcord hinv hrep5 hrepT hrep6 hrep7 hrep4
    hroots hdisj d54 dT4 d64 d74 hf5 hfT hf6 hf7 hf4 hz hspaceSum hspaceW
  obtain ⟨d5T, d56, d57, dT6, dT7, d67⟩ := hdisj
  have hnW : slots.length < 2 ^ P.w := by omega
  have hsp5 : h + I5.space (cs.G.m + slots.length) < 2 ^ P.w := by omega
  -- Step 1: the bundle piece.
  obtain ⟨body5, hb5, o5, st5, c5, S', x', tx', hrun5, hrep5', hrepT', hinv', hSoth, hSlot,
      hh1lo, hh1hi, hz5, hfr5, hft5, hftT, hd5T', hcost5⟩ :=
    I5.runs bunTbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω hbunW htourW hnW
      hslotsPtrW hhW hlist hlist_h hnd hSact hk hcord hinv hrep5 hrepT hf5 hfT d5T hz hsp5
  set h1 := o5.value with hh1def
  set st0 := startState [bunTbl, tourH, spanTbl, scurH, slots.length, slotsPtr, h, b4, j,
      P.splitBound, P.vCap, P.eCap, P.L] mem pos
    with hst0
  set st1 : State := { st5 with regs := Function.update st0.regs 13 h1 } with hst1
  have hcall5 : Runs P.w p ω (.call 13 fBun [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6]) st0
      .normal st1 (argsSize [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6] + c5 + 1) :=
    (runs_call_iff (r := 13) (f := fBun) (args := [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6])
      (st := st0) (o := .normal) (st' := st1)).mpr
      ⟨[bunTbl, tourH, slots.length, slotsPtr, h], body5, o5, st5, c5, rfl, hb5, hrun5, rfl,
        rfl, rfl⟩
  have hloc6 := bucketSpannerRep_local P cap
  -- the spanners, the view and P4 survive the bundle piece
  have hkeep5 : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → mem a = st5.mem a :=
    fun a ha => (hfr5 a (hf6 a ha) (fun h5 => d56 a h5 ha) (fun hT => dT6 a hT ha)).symm
  have hrep6_1 := (hloc6 spanTbl S6 x6 mem st5.mem hkeep5).1 hrep6
  have hphi6_1 := (hloc6 spanTbl S6 x6 mem st5.mem hkeep5).2
  have hlist1 : ListAt st5.mem slotsPtr slots := by
    intro i hi
    have hf := hfree (slotsPtr + i) (by omega) (by omega)
    rw [hfr5 _ (by omega) hf.1 hf.2.1]
    exact hlist i hi
  -- Step 2: the loop.
  have LH : LoopHyps P cap st1.regs spanTbl slotsPtr h h1 S6 x6 (restartSlotGraph S cs ord k)
      slots st5.mem :=
    { hR2 := by simp [hst1, hst0, startState]
      hR4 := by simp [hst1, hst0, startState]
      hR5 := by simp [hst1, hst0, startState]
      hR6 := by simp [hst1, hst0, startState]
      hR9 := by simp [hst1, hst0, startState]
      hR10 := by simp [hst1, hst0, startState]
      hR11 := by simp [hst1, hst0, startState]
      hR12 := by simp [hst1, hst0, startState]
      hw16 := hw16
      hL := hLW
      hSplit := hSplitW
      hV := hVW
      hE := hEW
      hlist := hlist1
      hlist_h := hlist_h
      hlist_free := fun a ha1 ha2 => (hfree a ha1 ha2).2.2.1
      hh1 := hh1lo
      hexp := by
        intro i hi
        obtain ⟨hs, B, B', hSB, hSB', hag, hex⟩ := hSlot i hi
        refine ⟨B'.graph, hex, ?_⟩
        show normGraph B'.graph = normGraph (restartSlotBundle S cs ord k slots[i]).graph
        unfold restartSlotBundle
        simp only [hs, ↓reduceDIte, hSB]
        exact normGraph_of_bunAgree hag
      hok := hok
      hact := fun s hs => (hS6act s hs).1
      hrep := hrep6_1
      hfoot := hf6
      hz := hz5
      hspace := by omega }
  obtain ⟨oL, st2, cL, hrunL, hpostL, hcL⟩ :=
    restartLoop_triple hp LH st1 ω ⟨rfl, fun _ _ => rfl, by simp [hst1]⟩
  cases oL with
  | returned u => exact absurd hpostL (by simp)
  | normal =>
  obtain ⟨hregs2, -, hc1, hc2, hz2, hfr2, hph, x6n, hrep6n, hft6n⟩ := hpostL
  set hc := st2.regs 13 with hhc
  set S6f := restartSpanState S6 S cs ord k slots with hS6fdef
  have hS6f : spanAfter S6 (restartSlotGraph S cs ord k) (slots.take slots.length) = S6f := by
    rw [List.take_length]; rfl
  rw [hS6f] at hrep6n
  have hsum := sum_range_getD (fun s => spanActivateSpace P (restartSlotGraph S cs ord k s)) slots
  have hcW : hc ≤ h1 + (slots.map fun s => spanActivateSpace P (restartSlotGraph S cs ord k s)).sum :=
    by rw [← hsum]; exact hc2
  -- memory of the loop
  have hkeep2 : ∀ a, a < h1 → ¬ (bucketSpannerRep P cap).foot spanTbl x6 a →
      st2.mem a = st5.mem a := hfr2
  have hkeepY : ∀ a, I7.rep.foot scurH y a → mem a = st2.mem a := by
    intro a ha
    have hah := hf7 a ha
    rw [hkeep2 a (by omega) (fun h6 => d67 a h6 ha),
      hfr5 a hah (fun h5 => d57 a h5 ha) (fun hT => dT7 a hT ha)]
  have hrep7_2 := (I7.rep_local scurH v y mem st2.mem hkeepY).1 hrep7
  have hphi7_2 := (I7.rep_local scurH v y mem st2.mem hkeepY).2
  have hkeep4 : ∀ a, I7.rep4.foot b4 x4 a → mem a = st2.mem a := by
    intro a ha
    have hah := hf4 a ha
    rw [hkeep2 a (by omega) (fun h6 => d64 a h6 ha),
      hfr5 a hah (fun h5 => d54 a h5 ha) (fun hT => dT4 a hT ha)]
  have hrep4_2 := (I7.rep4_local b4 s4 x4 mem st2.mem hkeep4).1 hrep4
  have hphi4_2 := (I7.rep4_local b4 s4 x4 mem st2.mem hkeep4).2
  have hlist2 : ListAt st2.mem slotsPtr slots := by
    intro i hi
    have hf := hfree (slotsPtr + i) (by omega) (by omega)
    rw [hkeep2 _ (by omega) hf.2.2.1]
    exact hlist1 i hi
  have hr2 : st2.regs 2 = spanTbl := by rw [hregs2 2 (by decide) (by decide)]; simp [hst1, hst0, startState]
  have hr3 : st2.regs 3 = scurH := by rw [hregs2 3 (by decide) (by decide)]; simp [hst1, hst0, startState]
  have hr4 : st2.regs 4 = slots.length := by rw [hregs2 4 (by decide) (by decide)]; simp [hst1, hst0, startState]
  have hr5 : st2.regs 5 = slotsPtr := by rw [hregs2 5 (by decide) (by decide)]; simp [hst1, hst0, startState]
  have hr7 : st2.regs 7 = b4 := by rw [hregs2 7 (by decide) (by decide)]; simp [hst1, hst0, startState]
  have hr8 : st2.regs 8 = j := by rw [hregs2 8 (by decide) (by decide)]; simp [hst1, hst0, startState]
  -- Step 3: the rebuild of `S_cur`.
  have hact7 : ∀ s ∈ slots, ∃ hs : s < cap, (S6f ⟨s, hs⟩).isSome := fun s hs =>
    ⟨(hS6act s hs).1, by simp [hS6fdef, restartSpanState, hs]⟩
  have hft6n' : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6n a → a < hc := by
    intro a ha
    rcases hft6n a ha with h6 | ⟨_, hlt⟩
    · have := hf6 a h6; omega
    · exact hlt
  have hd7n : ∀ a, I7.rep.foot scurH y a → ¬ (bucketSpannerRep P cap).foot spanTbl x6n a := by
    intro a ha hn
    rcases hft6n a hn with h6 | ⟨hle, _⟩
    · exact d67 a h6 ha
    · have := hf7 a ha; omega
  have hd6n4 : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6n a → ¬ I7.rep4.foot b4 x4 a := by
    intro a ha h4
    rcases hft6n a ha with h6 | ⟨hle, _⟩
    · exact d64 a h6 h4
    · have := hf4 a h4; omega
  have hsp7 : hc + I7.space (I7.size v S6f slots + slots.length) < 2 ^ P.w := by
    omega
  obtain ⟨body7, hb7, o7, st7, c7, y', x4', hrun7, hrep7', hrep4', hlo7, hhi7, hz7, hfr7, hft7,
      hft4, hd74', hcost7⟩ :=
    I7.runs scurH spanTbl slotsPtr hc b4 j slots v y S6f x6n s4 x4 st2.mem st2.pos ω hscurW hspanW
      hnW hslotsPtrW hb4W hjW (by omega) hlist2 (by omega) hact7 hrep7_2 hrep6n hrep4_2 hroots
      (fun a ha => by have := hf7 a ha; omega) hft6n' (fun a ha => by have := hf4 a ha; omega)
      hd7n d74 hd6n4 (fun a ha1 ha2 => (hfree a ha1 ha2).2.2.2) hz2 hsp7
  set st3 : State := { st7 with regs := Function.update st2.regs 13 o7.value } with hst3
  have hargs7 : evalArgs P.w st2 [.reg 3, .reg 2, .reg 4, .reg 5, .reg 7, .reg 8, .reg 13] =
      some [scurH, spanTbl, slots.length, slotsPtr, b4, j, hc] := by
    simp [evalArgs, Expr.eval, hr2, hr3, hr4, hr5, hr7, hr8, hhc]
  have hcall7 : Runs P.w p ω
      (.call 13 fScur [.reg 3, .reg 2, .reg 4, .reg 5, .reg 7, .reg 8, .reg 13]) st2
      .normal st3
      (argsSize [.reg 3, .reg 2, .reg 4, .reg 5, .reg 7, .reg 8, .reg 13] + c7 + 1) :=
    (runs_call_iff (r := 13) (f := fScur)
      (args := [.reg 3, .reg 2, .reg 4, .reg 5, .reg 7, .reg 8, .reg 13])
      (st := st2) (o := .normal) (st' := st3)).mpr
      ⟨_, body7, o7, st7, c7, hargs7, hb7, hrun7, rfl, rfl, rfl⟩
  have hret : Runs P.w p ω (.ret (.reg 13)) st3 (.returned o7.value) st3 2 :=
    runs_ret_iff.mpr ⟨o7.value, by simp [Expr.eval, hst3], rfl, rfl, rfl⟩
  have hrunT1 := runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hcall7, hret, rfl⟩)
  have hrunT2 := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hrunL, hrunT1, rfl⟩)
  have hrun := runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hcall5, hrunT2, rfl⟩)
  -- memory after the rebuild
  have hkeep7 : ∀ a, a < h1 → ¬ (bucketSpannerRep P cap).foot spanTbl x6 a →
      ¬ I7.rep.foot scurH y a → ¬ I7.rep4.foot b4 x4 a → st7.mem a = st5.mem a := by
    intro a ha h6 h7 h4
    rw [hfr7 a (by omega) h7 h4, hkeep2 a ha h6]
  have hx'keep : ∀ a, I5.rep.foot bunTbl x' a → st5.mem a = st7.mem a := by
    intro a ha
    rcases hft5 a ha with h5 | ⟨hle, hlt⟩
    · have := hf5 a h5
      exact (hkeep7 a (by omega) (d56 a h5) (d57 a h5) (d54 a h5)).symm
    · exact (hkeep7 a hlt (fun h6 => by have := hf6 a h6; omega)
        (fun h7 => by have := hf7 a h7; omega) (fun h4 => by have := hf4 a h4; omega)).symm
  have htx'keep : ∀ a, I5.tour.foot tourH tx' a → st5.mem a = st7.mem a := by
    intro a ha
    rcases hftT a ha with hT | ⟨hle, hlt⟩
    · have := hfT a hT
      exact (hkeep7 a (by omega) (dT6 a hT) (dT7 a hT) (dT4 a hT)).symm
    · exact (hkeep7 a hlt (fun h6 => by have := hf6 a h6; omega)
        (fun h7 => by have := hf7 a h7; omega) (fun h4 => by have := hf4 a h4; omega)).symm
  have hx6nkeep : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6n a → st2.mem a = st7.mem a := by
    intro a ha
    exact (hfr7 a (hft6n' a ha) (fun h7 => hd7n a h7 ha) (hd6n4 a ha)).symm
  have hrep5F := (I5.rep_local bunTbl S' x' st5.mem st7.mem hx'keep).1 hrep5'
  have hphi5F := (I5.rep_local bunTbl S' x' st5.mem st7.mem hx'keep).2
  have hrepTF := (I5.tour_local tourH cord tx' st5.mem st7.mem htx'keep).1 hrepT'
  have hphiTF := (I5.tour_local tourH cord tx' st5.mem st7.mem htx'keep).2
  have hrep6F := (hloc6 spanTbl S6f x6n st2.mem st7.mem hx6nkeep).1 hrep6n
  have hphi6F := (hloc6 spanTbl S6f x6n st2.mem st7.mem hx6nkeep).2
  -- costs
  have hLc := loopCost_le P S6 (restartSlotGraph S cs ord k) slots hph
  rw [hS6f, List.take_zero, spanAfter_nil] at hLc
  have hphi6n := bucketPhi_eq_specPhi hrep6n
  have hphi60 := bucketPhi_eq_specPhi hrep6_1
  simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero] at hcL
  have hov : (Outcome.returned o7.value).value = o7.value := rfl
  refine ⟨_, hf, .returned o7.value, st3, _, S', x', tx', x6n, y', x4',
    by unfold restartBranchStmt; exact hrun, hrep5F, hrepTF, hinv', hrep6F, hrep7', hrep4', hSoth,
    ?_,
    by rw [hov]; omega, by rw [hov]; omega, by rw [hov]; exact hz7, ?_, ?_, ?_, ?_,
    ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hd74', ?_⟩
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    obtain ⟨hs', B, B', hSB, hSB', hag, -⟩ := hSlot i hi
    refine ⟨hs', B', hSB', ?_⟩
    unfold restartSlotBundle
    simp only [hs', ↓reduceDIte, hSB]
    exact hag
  · intro a ha h5 hT h6 h7 h4
    show st7.mem a = mem a
    rw [hkeep7 a (by omega) h6 h7 h4]
    exact hfr5 a ha h5 hT
  · intro a ha
    rcases hft5 a ha with h5 | ⟨hle, hlt⟩
    · exact Or.inl h5
    · exact Or.inr ⟨hle, by omega⟩
  · intro a ha
    rcases hftT a ha with hT | ⟨hle, hlt⟩
    · exact Or.inl hT
    · exact Or.inr ⟨hle, by omega⟩
  · intro a ha
    rcases hft6n a ha with h6 | ⟨hle, hlt⟩
    · exact Or.inl h6
    · exact Or.inr ⟨by omega, by omega⟩
  · intro a ha
    rcases hft7 a ha with h7 | ⟨hle, hlt⟩
    · exact Or.inl h7
    · exact Or.inr ⟨by omega, hlt⟩
  · intro a ha
    rcases hft4 a ha with h4 | ⟨hle, hlt⟩
    · exact Or.inl h4
    · exact Or.inr ⟨by omega, hlt⟩
  · exact hd5T'
  · intro a ha hb
    rcases hft5 a ha with h5 | ⟨hle, hlt⟩ <;> rcases hft6n a hb with h6 | ⟨hle', hlt'⟩
    · exact d56 a h5 h6
    · have := hf5 a h5; omega
    · have := hf6 a h6; omega
    · omega
  · intro a ha hb
    rcases hft5 a ha with h5 | ⟨hle, hlt⟩ <;> rcases hft7 a hb with h7 | ⟨hle', hlt'⟩
    · exact d57 a h5 h7
    · have := hf5 a h5; omega
    · have := hf7 a h7; omega
    · omega
  · intro a ha hb
    rcases hftT a ha with hT | ⟨hle, hlt⟩ <;> rcases hft6n a hb with h6 | ⟨hle', hlt'⟩
    · exact dT6 a hT h6
    · have := hfT a hT; omega
    · have := hf6 a h6; omega
    · omega
  · intro a ha hb
    rcases hftT a ha with hT | ⟨hle, hlt⟩ <;> rcases hft7 a hb with h7 | ⟨hle', hlt'⟩
    · exact dT7 a hT h7
    · have := hfT a hT; omega
    · have := hf7 a h7; omega
    · omega
  · intro a ha hb
    rcases hft6n a ha with h6 | ⟨hle, hlt⟩ <;> rcases hft7 a hb with h7 | ⟨hle', hlt'⟩
    · exact d67 a h6 h7
    · have := hf6 a h6; omega
    · have := hf7 a h7; omega
    · omega
  · intro a ha hb
    rcases hft5 a ha with h5 | ⟨hle, hlt⟩ <;> rcases hft4 a hb with h4 | ⟨hle', hlt'⟩
    · exact d54 a h5 h4
    · have := hf5 a h5; omega
    · have := hf4 a h4; omega
    · omega
  · intro a ha hb
    rcases hftT a ha with hT | ⟨hle, hlt⟩ <;> rcases hft4 a hb with h4 | ⟨hle', hlt'⟩
    · exact dT4 a hT h4
    · have := hfT a hT; omega
    · have := hf4 a h4; omega
    · omega
  · intro a ha hb
    rcases hft6n a ha with h6 | ⟨hle, hlt⟩ <;> rcases hft4 a hb with h4 | ⟨hle', hlt'⟩
    · exact d64 a h6 h4
    · have := hf6 a h6; omega
    · have := hf4 a h4; omega
    · omega
  · simp only [argsSize_cons, argsSize_nil, Expr.size_reg] at *
    have e6 : (bucketSpannerRep P cap).phi spanTbl x6n st7.mem = specPhi P S6f :=
      hphi6F.symm.trans hphi6n
    have e60 : (bucketSpannerRep P cap).phi spanTbl x6 mem = specPhi P S6 :=
      hphi6_1.trans hphi60
    show _ + I5.rep.phi bunTbl x' st7.mem + I5.tour.phi tourH tx' st7.mem +
      (bucketSpannerRep P cap).phi spanTbl x6n st7.mem + I7.rep.phi scurH y' st7.mem +
      I7.rep4.phi b4 x4' st7.mem ≤ _
    rw [← hphi5F, ← hphiTF, e6, e60, hphi7_2, hphi4_2]
    omega

end

end MinCostFlow.SparseCore.Program.Restart
