module

public import MinCostFlow.LowStretch.PSearchSet1

/-!
# A step that settles a node keeps the invariant

When `dijStep` settles `u`, `pstep` adds the arcs of `u` to the five sums (`Inv.settle_sums`),
puts `u` at the end of the settled list and, if `u` is the highway node `H[j]` at the pointer,
moves the pointer to `H[j+1]` and turns on the slot of `H[j+1]`. The main result is
`Inv.settle`: the invariant holds again, and the measure drops by the cost of the step.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace SC

variable {C : SC} {w : ℕ} {a : SG} {mem : ℕ → ℕ}

open Classical in
/-- **The sums after a settle.** `psum` adds what the arcs of `u` add to the five sums. -/
theorem Inv.settle_sums (h : C.Ok w) (hI : C.Inv w a mem) {mem1 : ℕ → ℕ} {d' : DS}
    {qs' : ℕ → List (ℕ × ℕ)} {cur pos : ℕ}
    (hk1 : ∀ x, C.L.KeepS C.X.G.R x → mem1 x = mem x)
    (hs1 : C.L.Shape w mem1 C.X.G.Nodes) (hr1 : C.L.Rep mem1 C.X.G.Nodes d' qs')
    (hinv1 : C.gF.Inv C.X.G.s C.L.INF cur pos d') (hdone1 : d'.sett cur → C.gF.hi cur ≤ pos)
    (hsett' : ∀ v, d'.sett v ↔ a.d.sett v ∨ v = mem1 (C.X.G.R + 1))
    (hns : ¬ a.d.sett (mem1 (C.X.G.R + 1)))
    (hkey : mem1 C.X.G.R = C.δF (mem1 (C.X.G.R + 1))) (t : Fin 5) :
    mem1 (C.X.SUM + t) + ((C.Xf a).ps mem1).sm mem1 t ((C.Xf a).ps mem1).hi =
      C.es (a.ℓ ++ [mem1 (C.X.G.R + 1)]) t := by
  set u := mem1 (C.X.G.R + 1) with hu
  have hus : d'.sett u := (hsett' u).mpr (Or.inr rfl)
  have huN : u ∈ C.X.G.Nodes := ((hr1.sett u).mp hus).1
  have hun : u < C.L.NN := ((hs1.ok_iff u).mpr huN).1
  have hF1 : ∀ x, C.Fix x → mem1 x = C.mem0 x := fun x hx => (hk1 x hx.1).trans (hI.fix x hx)
  have hCTL := h.hCTL
  have hSUM := h.hSUM
  have huℓ : u ∉ a.ℓ := fun hm => hns ((hI.sett u).mpr hm)
  rw [hk1 _ (keepS_of_ge h (by omega)), hI.sums t]
  unfold es
  rw [esum_snoc huℓ ((hI.okN_iff h u).mpr huN)
    (fun v hv => (hI.okN_iff h v).mpr ((hI.rep.sett v).mp ((hI.sett v).mpr hv)).1)
    (fun j hj => (h.ends j hj).2.2) t]
  congr 1
  have eLO : mem1 (C.L.LO + u) = C.mem0 (C.L.LO + u) := hF1 _ (h.fLO u hun).1
  have eHI : mem1 (C.L.HI + u) = C.mem0 (C.L.HI + u) := hF1 _ (h.fLO u hun).2.1
  have hiM := h.hiMM u hun
  -- the arcs of `u` before its slot read cells that are never written
  have hsum : ∀ Fs : ℕ → ℕ → ℕ,
      ∑ k ∈ Finset.Ico (mem1 (C.L.LO + u)) (mem1 (C.L.HI + u) - 1),
          Fs (mem1 (C.L.HD + k)) (mem1 (C.X.ORD + k) / 2) =
        ∑ j ∈ (Finset.range C.nA).filter (C.ea · = u), Fs (C.eb j) j +
        ∑ j ∈ (Finset.range C.nA).filter (C.eb · = u), Fs (C.ea j) j := by
    intro Fs
    rw [eLO, eHI, ← h.hsum u huN Fs]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨k1, k2⟩ := Finset.mem_Ico.mp hk
    have hkM : k < C.L.MM := by omega
    have hnot : ∀ i < C.H.length, k ≠ C.slot (C.hv i) := by
      intro i hi he
      have hlo : (C.L.g C.mem0).lo u ≤ k := by simp only [DL.g, if_pos hun]; exact k1
      have hhi : k < (C.L.g C.mem0).hi u := by simp only [DL.g, if_pos hun]; omega
      have e := h.own u k i hlo hhi hi he
      unfold slot at he
      rw [← e] at he
      omega
    rw [hF1 _ (h.fHD k hkM hnot), hF1 _ (h.fCS k hkM).2.2]
  have hok : ∀ y < C.L.NN, (mem1 (C.L.OK + y) = C.L.os ↔ C.okN y) := by
    intro y hy
    rw [hF1 _ (h.fLO y hy).2.2.1]
    show _ ↔ y < C.L.NN ∧ _
    exact ⟨fun e => ⟨hy, e⟩, fun e => e.2⟩
  have hends : ∀ j < C.nA, C.ea j < C.L.NN ∧ C.eb j < C.L.NN :=
    fun j hj => ⟨(h.ends j hj).1, (h.ends j hj).2.1⟩
  have hst : ∀ y, C.okN y → (mem1 (C.L.TS + 2 * C.L.NN + y) = C.L.rs ↔ y ∈ a.ℓ ++ [u]) := by
    intro y hy
    have hyN := (hI.okN_iff h y).mp hy
    rw [List.mem_append, List.mem_singleton, ← hI.sett, ← hsett', hr1.sett]
    exact ⟨fun e => ⟨hyN, e⟩, fun e => e.2⟩
  have hty : ∀ y, C.okN y → y ∈ a.ℓ ++ [u] → mem1 (C.L.TS + C.L.NN + y) = C.δF y := by
    intro y hy hm
    have hyN := (hI.okN_iff h y).mp hy
    have hys : d'.sett y := (hsett' y).mpr (by
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl ((hI.sett y).mpr hm)
      · exact Or.inr hm)
    have hyNN : y < C.L.NN := ((hs1.ok_iff y).mpr hyN).1
    have hok' : mem1 (C.L.OK + y) = C.L.os := (hok y hyNN).mpr hy
    have ht := DL.ty_lt hs1 hr1 hinv1 hyNN hok' ((hr1.sett y).mp hys).2
    rw [← ht.2.2.1]
    exact tent_eq hinv1 hdone1 hys
  have hwt : ∀ j < C.nA, 1 <<< (C.X.Es - mem1 (C.X.EXP + mem1 (C.X.AS + 2 * j))) =
      (C.wtP ∘ C.pr) j := by
    intro j hj
    rw [hF1 _ (h.fAS j hj).1, hF1 _ (h.fAS j hj).2]
    exact h.hwt j hj
  exact psum_sm ((C.Xf a).ps mem1) mem1 hsum hok hends hst hty hkey hwt t

/-- **A step of Dijkstra that settles a node.** -/
theorem Inv.settle (h : C.Ok w) (hI : C.Inv w a mem) {mem1 mem2 mem' : ℕ → ℕ}
    (hT : (C.Xf a).TB mem → ¬ ((C.Xf a).pt mem).Pass mem ∧ (C.Xf a).k mem ≤ (C.Xf a).bq mem)
    (hp : stepPost w (C.Xf a).G (C.L.argsR C.X.G.R) mem 2 mem1)
    (hs2 : ∀ t : Fin 5, mem2 ((C.Xf a).SUM + t) =
      mem1 ((C.Xf a).SUM + t) + ((C.Xf a).ps mem1).sm mem1 t ((C.Xf a).ps mem1).hi)
    (hf2 : ∀ x, (x < (C.Xf a).SUM ∨ (C.Xf a).SUM + 5 ≤ x) → mem2 x = mem1 x)
    (hm : mem' = (C.Xf a).setM mem1 mem2) :
    ∃ a', C.Inv w a' mem' ∧ C.μ a' + pstepCost (C.Xf a).args mem + 50 ≤ C.μ a ∧
      C.L.pot C.mem0 C.X.G.Nodes a'.d a'.qs ≤ C.L.pot C.mem0 C.X.G.Nodes a.d a.qs := by
  rcases hp with ⟨h0, -⟩ | ⟨h0, -⟩ |
    ⟨-, d', qs', hns, ⟨-, hmin⟩, hL', hsett', hs1, hr1, hinv1, hcap1, hpot, hk1, hp1, hz1, hS1, -⟩
  · omega
  · omega
  change ¬ a.d.sett (mem1 (C.X.G.R + 1)) at hns
  change ∀ e ∈ a.d.Q, mem1 C.X.G.R ≤ e.1 at hmin
  change d'.L = mem1 C.X.G.R at hL'
  change d'.sett = (fun v => a.d.sett v ∨ v = mem1 (C.X.G.R + 1)) at hsett'
  change C.L.Shape w mem1 C.X.G.Nodes at hs1
  change C.L.Rep mem1 C.X.G.Nodes d' qs' at hr1
  change (C.L.g mem).Inv C.X.G.s C.L.INF (mem1 (C.X.G.R + 1))
    ((C.L.g mem).hi (mem1 (C.X.G.R + 1))) d' at hinv1
  change ∀ c < C.L.J, mem1 (pqT C.L.D C.L.J c) ≤ C.L.setSum mem C.X.G.Nodes d'.sett + 1 at hcap1
  change C.L.pot mem C.X.G.Nodes d' qs' + dijCost (C.L.argsR C.X.G.R) mem ≤
    C.L.pot mem C.X.G.Nodes a.d a.qs at hpot
  change ∀ x, C.L.KeepS C.X.G.R x → mem1 x = mem x at hk1
  change (C.L.g mem).ParInv C.X.G.s C.L.INF d' (C.L.par mem1) (C.L.parc mem1) at hp1
  change C.L.TZ mem1 qs' at hz1
  change C.L.Stamps mem1 at hS1
  have hf2' : ∀ x, (x < C.X.SUM ∨ C.X.SUM + 5 ≤ x) → mem2 x = mem1 x := hf2
  have hsv : ∀ v, d'.sett v ↔ a.d.sett v ∨ v = mem1 (C.X.G.R + 1) := fun v => by rw [hsett']
  set u := mem1 (C.X.G.R + 1) with hu
  have hus : d'.sett u := (hsv u).mpr (Or.inr rfl)
  have huN : u ∈ C.X.G.Nodes := ((hr1.sett u).mp hus).1
  have hun : u < C.L.NN := ((hs1.ok_iff u).mpr huN).1
  have huℓ : u ∉ a.ℓ := fun hm => hns ((hI.sett u).mpr hm)
  have hF1 : ∀ x, C.Fix x → mem1 x = C.mem0 x := fun x hx => (hk1 x hx.1).trans (hI.fix x hx)
  have hk : ∀ x, C.X.G.R + 2 ≤ x → mem1 x = mem x := fun x hx => hk1 x (keepS_of_ge h hx)
  have hlow1 : ∀ x < C.L.TS, mem1 x = mem x := fun x hx => hk1 x (Or.inl hx)
  have hg1 : C.L.g mem1 = C.L.g mem := DL.g_congr C.L hI.shape hlow1
  have hgj : C.L.g mem = C.gC a.j := hI.g h
  have hCTL := h.hCTL
  have hSUM := h.hSUM
  have hSL := h.hSL
  have hTS := h.TS_lt hI
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hI.lay
  -- the key of `u`
  have hinv0 := hinv1
  rw [hgj] at hinv1
  have hLu : d'.tent u = d'.L := hinv1.cur_L hus
  have hreach : (C.L.g mem).Reach C.X.G.s u d'.L := by
    rw [hgj, ← hLu]; exact hinv1.reach u (by rw [hLu]; exact hinv1.L_lt)
  have hkey : d'.L = mem (C.L.D + 4) / C.L.J :=
    hI.key_eq hns hreach hinv1.L_lt (fun e he => by rw [hL']; exact hmin e he)
  -- `u` is no later highway node than the pointer
  have hlater : ∀ i, a.j < i → i < C.H.length → u ≠ C.hv i := by
    intro i h1 h2 he
    have hj : a.j < C.H.length := by omega
    have hnj : ¬ d'.sett (C.hv a.j) := by
      rw [hsv]
      rintro (hs | he')
      · have := (hI.hsett a.j hj).mp hs; omega
      · have := h.hv_inj hj h2 (he'.trans he); omega
    exact h.hw_order hinv1 (fun _ => le_rfl) hus hj hnj h2 h1 he
  have hJ5 : ∀ i, a.j < i → i < C.H.length → ¬ d'.sett (C.hv i) := by
    intro i h1 h2
    rw [hsv]
    rintro (hs | he)
    · have := (hI.hsett i h2).mp hs; omega
    · exact hlater i h1 h2 he.symm
  have hinvF := hinv1.sub (h.gC_subF hJ5)
  -- the slot that may be turned on
  have hNu : mem1 (C.X.NXT + u) = C.mem0 (C.X.NXT + u) := hF1 _ (h.fLO u hun).2.2.2
  have hnN : mem1 (C.X.NXT + u) < C.L.NN := by rw [hNu]; exact h.nxt u hun
  have hHn : mem1 (C.L.HI + mem1 (C.X.NXT + u)) = C.mem0 (C.L.HI + mem1 (C.X.NXT + u)) :=
    hF1 _ (h.fLO _ hnN).2.1
  have hAlt : C.L.HD + (mem1 (C.L.HI + mem1 (C.X.NXT + u)) - 1) < C.X.G.R := by
    have := h.hiMM _ hnN; rw [hHn]; omega
  have hptr : mem1 (C.X.CTL + 2) = mem (C.X.CTL + 2) := hk _ (by omega)
  have hh' : u = mem1 (C.X.CTL + 2) → a.j < C.H.length ∧ u = C.hv a.j ∧
      mem1 (C.X.NXT + u) = (C.H ++ [C.X.S]).getD (a.j + 1) 0 ∧
      mem1 (C.X.NXT + u) = if a.j + 1 < C.H.length then C.hv (a.j + 1) else C.X.S := by
    intro e1
    obtain ⟨hj, hu'⟩ := hI.ptr_hv h (e1.trans hptr) huN
    have e : mem1 (C.X.NXT + u) = C.nx a.j := by rw [hNu, hu']; rfl
    exact ⟨hj, hu', e.trans (h.hnx a.j hj), e.trans (h.nx_eq hj)⟩
  have haddr : u = mem1 (C.X.CTL + 2) → mem1 (C.X.NXT + u) < C.X.S →
      a.j + 1 < C.H.length ∧ mem1 (C.X.NXT + u) = C.hv (a.j + 1) ∧
      C.L.HD + (mem1 (C.L.HI + mem1 (C.X.NXT + u)) - 1) = C.L.HD + C.slot (C.hv (a.j + 1)) ∧
      mem1 (C.X.NXT + mem1 (C.X.NXT + u)) = C.nx (a.j + 1) := by
    intro e1 e2
    have h4 := (hh' e1).2.2.2
    by_cases hj1 : a.j + 1 < C.H.length
    · rw [if_pos hj1] at h4
      refine ⟨hj1, h4, by rw [hHn, h4]; rfl, ?_⟩
      rw [h4, hF1 _ (h.fLO _ (h.hv_lt hj1)).2.2.2]; rfl
    · rw [if_neg hj1] at h4; omega
  -- the cells of the settle phase
  have sNe : ∀ x, x ≠ C.X.SL + mem1 (C.X.CTL + 1) → x ≠ C.X.CTL + 1 → x ≠ C.X.CTL + 3 →
      x ≠ C.X.CTL + 2 → (u = mem1 (C.X.CTL + 2) → mem1 (C.X.NXT + u) < C.X.S →
        x ≠ C.L.HD + (mem1 (C.L.HI + mem1 (C.X.NXT + u)) - 1)) → mem' x = mem2 x :=
    fun x e1 e2 e3 e4 e5 => by rw [hm]; exact PSG.setM_ne e1 e2 e3 e4 e5
  have hlow : ∀ x < C.X.CTL, (∀ i < C.H.length, x ≠ C.L.HD + C.slot (C.hv i)) →
      mem' x = mem1 x := by
    intro x hx hns'
    have hSLn : mem1 (C.X.CTL + 1) = a.ℓ.length := by rw [hk _ (by omega)]; exact hI.ns
    rw [sNe x (by omega) (by omega) (by omega) (by omega) (fun e1 e2 => by
      rw [(haddr e1 e2).2.2.1]; exact hns' _ (haddr e1 e2).1), hf2' x (Or.inl (by omega))]
  have hns1 : mem1 (C.X.CTL + 1) = a.ℓ.length := by rw [hk _ (by omega)]; exact hI.ns
  -- the frame of Dijkstra
  have hfa := DL.frameAll (mem' := mem') hs1 hr1 hz1 hS1
    (fun x h1 h2 => hlow x (by unfold pqSize at h2; have := h.hR; unfold pqSize at this; omega)
      fun i hi => by have := hI.slot_lt_TS h hi; omega)
    (fun v hv => ⟨hlow _ (by omega) (h.fLO v hv).1.2.2, hlow _ (by omega) (h.fLO v hv).2.1.2.2,
      hlow _ (by omega) (h.fLO v hv).2.2.1.2.2⟩)
    (fun k hk' => ⟨hlow _ (by omega) (h.fCS k hk').1.2.2, hlow _ (by omega) (h.fCS k hk').2.1.2.2,
      by
        by_cases hw : u = mem1 (C.X.CTL + 2) ∧ mem1 (C.X.NXT + u) < C.X.S ∧
            C.L.HD + k = C.L.HD + (mem1 (C.L.HI + mem1 (C.X.NXT + u)) - 1)
        · rw [hw.2.2, hm]
          refine lt_of_eq_of_lt (PSG.setM_HD (X := C.Xf a) (mem2 := mem2) hw.1 hw.2.1) ?_
          show mem1 (C.X.NXT + mem1 (C.X.NXT + u)) < C.L.NN
          rw [hF1 _ (h.fLO _ hnN).2.2.2]
          exact h.nxt _ hnN
        · rw [sNe _ (by omega) (by omega) (by omega) (by omega)
            (fun e1 e2 he => hw ⟨e1, e2, he⟩), hf2' _ (Or.inl (by omega))]
          exact (hs1.heads k hk').1⟩)
  obtain ⟨fs, fr, fz, fS, fdeg, fpar⟩ := hfa
  -- the pointer and the slots
  have a1 : C.X.CTL + 2 ≠ C.L.HD + (mem1 (C.L.HI + mem1 (C.X.NXT + u)) - 1) := by omega
  have a1' : C.X.CTL + 2 ≠ C.X.SL + mem1 (C.X.CTL + 1) := by omega
  have hC2 : mem' (C.X.CTL + 2) =
      if u = mem1 (C.X.CTL + 2) then mem1 (C.X.NXT + u) else mem (C.X.CTL + 2) := by
    rw [hm]
    refine (PSG.setM_C2 (X := C.Xf a) (mem2 := mem2) a1 a1').trans ?_
    show (if u = mem1 (C.X.CTL + 2) then mem1 (C.X.NXT + u) else mem2 (C.X.CTL + 2)) = _
    rw [hf2' _ (Or.inl (by omega)), hptr]
  have hslot0 : ∀ i < C.H.length,
      (u = mem1 (C.X.CTL + 2) → mem1 (C.X.NXT + u) < C.X.S → i ≠ a.j + 1) →
      mem' (C.L.HD + C.slot (C.hv i)) = mem (C.L.HD + C.slot (C.hv i)) := by
    intro i hi hne
    have := hI.slot_lt_TS h hi
    rw [sNe _ (by omega) (by omega) (by omega) (by omega) (fun e1 e2 he => hne e1 e2 (by
        rw [(haddr e1 e2).2.2.1] at he
        exact h.slot_inj hi (haddr e1 e2).1 (by omega))),
      hf2' _ (Or.inl (by omega)), hlow1 _ this]
  have key : ∃ j', a.j ≤ j' ∧ j' ≤ C.H.length ∧
      (∀ i < C.H.length, (d'.sett (C.hv i) ↔ i < j')) ∧
      mem' (C.X.CTL + 2) = (C.H ++ [C.X.S]).getD j' 0 ∧
      ∀ i < C.H.length, mem' (C.L.HD + C.slot (C.hv i)) = if i ≤ j' then C.nx i else C.X.S := by
    by_cases hup : u = mem1 (C.X.CTL + 2)
    · obtain ⟨hj, hu', hg', -⟩ := hh' hup
      refine ⟨a.j + 1, by omega, by omega, fun i hi => ?_, by rw [hC2, if_pos hup, hg'],
        fun i hi => ?_⟩
      · rw [hsv, hI.hsett i hi]
        constructor
        · rintro (h1 | h1)
          · omega
          · have := h.hv_inj hi hj (h1.trans hu'); omega
        · intro h1
          by_cases h2 : i < a.j
          · exact Or.inl h2
          · exact Or.inr (by rw [hu', show i = a.j by omega])
      · by_cases hi1 : i = a.j + 1
        · subst hi1
          have e2 : mem1 (C.X.NXT + u) < C.X.S := by
            rw [(hh' hup).2.2.2, if_pos hi]; exact h.HS _ hi
          obtain ⟨-, -, he3, he4⟩ := haddr hup e2
          rw [← he3, hm]
          refine (PSG.setM_HD (X := C.Xf a) (mem2 := mem2) hup e2).trans ?_
          show mem1 (C.X.NXT + mem1 (C.X.NXT + u)) = _
          rw [he4, if_pos le_rfl]
        · rw [hslot0 i hi (fun _ _ => hi1), hI.slots i hi]
          by_cases h3 : i ≤ a.j
          · rw [if_pos h3, if_pos (by omega)]
          · rw [if_neg h3, if_neg (by omega)]
    · refine ⟨a.j, le_rfl, hI.jle, fun i hi => ?_, by rw [hC2, if_neg hup, hI.ptr],
        fun i hi => ?_⟩
      · rw [hsv, hI.hsett i hi]
        constructor
        · rintro (h1 | h1)
          · exact h1
          · by_contra h2
            rcases Nat.lt_or_ge a.j i with h3 | h3
            · exact hlater i h3 hi h1.symm
            · have hij : i = a.j := by omega
              apply hup
              rw [hptr, hI.ptr, ← h1, hij, List.getD_append _ _ _ _ (by omega)]; rfl
        · exact Or.inl
      · rw [hslot0 i hi (fun e1 => absurd e1 hup), hI.slots i hi]
  obtain ⟨j', hjj, hjL, hJ2, hJ3, hJ4⟩ := key
  have hfix' : ∀ x, C.Fix x → mem' x = C.mem0 x := fun x hx => by
    rw [hlow x hx.2.1 hx.2.2, hF1 x hx]
  have hg' : C.L.g mem' = C.gC j' := h.g_eq hfix' hJ4
  have hsub : AG.Sub (C.gC a.j) (C.gC j') d' := h.gC_sub hjj hJ5
  rw [hgj] at hp1
  -- the other cells
  have hR := h.hR
  unfold pqSize at hR
  have i1 : ∀ c < C.L.J, mem' (pqT C.L.D C.L.J c) ≤ C.L.setSum mem' C.X.G.Nodes d'.sett + 1 := by
    intro c hc
    have hpq : pqT C.L.D C.L.J c < C.X.G.R := by unfold pqT; omega
    have hpq' : C.L.TS ≤ pqT C.L.D C.L.J c := by unfold pqT; omega
    rw [hlow _ (by omega) (fun i hi => by have := hI.slot_lt_TS h hi; omega),
      setSum_eq_of_deg fdeg, setSum_eq_of_deg (DL.deg_eq_of_g hg1)]
    exact hcap1 c hc
  have hkeyF : mem1 C.X.G.R = C.δF u := by
    rw [← hL', ← hLu]; exact tent_eq hinvF (fun _ => le_rfl) hus
  have i2 : ∀ t : Fin 5, mem' (C.X.SUM + t) = C.es (a.ℓ ++ [u]) t := by
    intro t
    have ht := t.isLt
    rw [sNe _ (by omega) (by omega) (by omega) (by omega) (fun _ _ => by omega)]
    have e := hs2 t
    change mem2 (C.X.SUM + ↑t) = mem1 (C.X.SUM + ↑t) + _ at e
    rw [e]
    exact hI.settle_sums h hk1 hs1 hr1 hinvF (fun _ => le_rfl) hsv hns hkeyF t
  have a2 : C.X.CTL + 1 ≠ C.L.HD + (mem1 (C.L.HI + mem1 (C.X.NXT + u)) - 1) := by omega
  have i3 : mem' (C.X.CTL + 1) = (a.ℓ ++ [u]).length := by
    rw [hm]
    refine (PSG.setM_C1 (X := C.Xf a) (mem2 := mem2) a2).trans ?_
    show mem1 (C.X.CTL + 1) + 1 = _
    rw [hns1, List.length_append, List.length_singleton]
  have i4 : ∀ i < (a.ℓ ++ [u]).length, mem' (C.X.SL + i) = (a.ℓ ++ [u]).getD i 0 := by
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases hil : i < a.ℓ.length
    · rw [sNe _ (by omega) (by omega) (by omega) (by omega) (fun _ _ => by omega),
        hf2' _ (Or.inr (by omega)), hk _ (by omega), hI.sl i hil, List.getD_append _ _ _ _ hil]
    · have hi' : i = a.ℓ.length := by omega
      subst hi'
      have b2 : C.X.SL + mem1 (C.X.CTL + 1) ≠ C.X.CTL + 1 := by omega
      have b3 : C.X.SL + mem1 (C.X.CTL + 1) ≠ C.X.CTL + 3 := by omega
      have b4 : C.X.SL + mem1 (C.X.CTL + 1) ≠ C.X.CTL + 2 := by omega
      have b5 : C.X.SL + mem1 (C.X.CTL + 1) ≠
          C.L.HD + (mem1 (C.L.HI + mem1 (C.X.NXT + u)) - 1) := by omega
      have e : mem' (C.X.SL + mem1 (C.X.CTL + 1)) = u := by
        rw [hm]; exact PSG.setM_SL (X := C.Xf a) b2 b3 b4 b5
      rw [show C.X.SL + a.ℓ.length = C.X.SL + mem1 (C.X.CTL + 1) by rw [hns1], e,
        List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      rfl
  have a3 : C.X.CTL + 3 ≠ C.L.HD + (mem1 (C.L.HI + mem1 (C.X.NXT + u)) - 1) := by omega
  have i5 : mem' (C.X.CTL + 3) = d'.L := by
    rw [hm]; exact (PSG.setM_C3 (X := C.Xf a) (mem2 := mem2) a3).trans hL'.symm
  have i6 : mem' C.X.CTL = a.q := by
    rw [sNe _ (by omega) (by omega) (by omega) (by omega) (fun _ _ => by omega),
      hf2' _ (Or.inl (by omega)), hk _ (by omega), hI.qc]
  have i7 : (a.ℓ ++ [u]).Nodup := List.nodup_append.mpr ⟨hI.nd, List.nodup_singleton u,
    fun x hx y hy hxy => huℓ (by rw [List.mem_singleton] at hy; rw [← hy, ← hxy]; exact hx)⟩
  have i8 : ∀ v, d'.sett v ↔ v ∈ a.ℓ ++ [u] := fun v => by
    rw [hsv, List.mem_append, List.mem_singleton, hI.sett]
  obtain ⟨hqd, hbn⟩ := hI.settle_buckets h hT hkey hinv1.L_lt
  have hpot' : C.L.pot C.mem0 C.X.G.Nodes d' qs' + dijCost (C.L.argsR C.X.G.R) mem ≤
      C.L.pot C.mem0 C.X.G.Nodes a.d a.qs := by
    rw [← pot_eq_of_deg (hI.deg h), ← pot_eq_of_deg (hI.deg h)]; exact hpot
  refine ⟨⟨d', qs', u, C.gF.hi u, a.ℓ ++ [u], j', a.q⟩, ⟨fs, fr,
    by rw [hg']; exact hinv1.sub hsub, fun _ => by rw [hg']; exact le_rfl, i1,
    by rw [hg']; exact (fpar _ _ hp1).sub hsub, fz, fS, hfix', hjL, hJ3, hJ4, hJ2, i3, i4, i7,
    i8, i5, i2, i6, hI.q1, hI.qL, hqd, hI.bdone, hbn, fun x hx => by
      have := hI.len_le; have := h.hSUM; have := h.hSL
      rw [sNe x (by omega) (by omega) (by omega) (by omega) (fun e1 e2 => by
        rw [(haddr e1 e2).2.2.1]; have := hI.slot_lt_TS h (haddr e1 e2).1; omega),
        hf2' x (Or.inr (by omega)), hk _ (by omega)]
      exact hI.top x hx⟩, ?_, le_trans (Nat.le_add_right _ _) hpot'⟩
  have hcost : pstepCost (C.Xf a).args mem = 2 * dijCost (C.L.argsR C.X.G.R) mem + 600 :=
    (C.Xf a).cost_dij mem fun hh => by
      have := hT hh.1
      rcases hh.2 with h' | h'
      · omega
      · exact this.1 h'
  have hst := stCost_le_dijCost (L := C.L) (R := C.X.G.R) (mem := mem)
  have hst5 : 500 ≤ stCost C.L.J := by unfold stCost; omega
  have e1 : C.μ ⟨d', qs', u, C.gF.hi u, a.ℓ ++ [u], j', a.q⟩ =
      4 * C.L.pot C.mem0 C.X.G.Nodes d' qs' + 500 * (C.X.Lb + 1 - a.q) + 2 * stCost C.L.J +
        2000 := rfl
  have e0 : C.μ a = 4 * C.L.pot C.mem0 C.X.G.Nodes a.d a.qs +
      500 * (C.X.Lb + 1 - a.q) + 2 * stCost C.L.J + 2000 := rfl
  rw [e1, e0, hcost]
  exact drop_arith _ _ _ _ _ hpot' hst hst5

end SC

end MinCostFlow.LowStretch
