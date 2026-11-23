module

public import MinCostFlow.LowStretch.ProgChildTopB
public import MinCostFlow.LowStretch.ProgPreKMath

/-!
# The top level: the four calls

The four calls of the top level, `chxP`, `csrB` on the pieces, `keyP` and `csrB` on the keys,
leave what `TopOk` says (`CS.topOk_of`), and they run within `CS.topCost`
(`CS.topCalls_runs`). Each call writes only its own scratch array, so the arrays written
earlier keep their values.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ}

/-- **What the four calls leave.** `Ma` is the memory after `chxP`, `Mb` after the node groups,
`Mc` after the keys and `Md` after the key groups. -/
theorem topOk_of (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {Ma Mb Mc Md : ℕ → ℕ} (hA : S.ChxDone Ma)
    (hB1 : ∀ u ≤ S.nch, Mb (S.OFFN + u) = offOf (fun i => Ma (S.CHX + i)) S.s u)
    (hB2 : ∀ u < S.nch, ∀ j < (grp (fun i => Ma (S.CHX + i)) S.s u).length,
      Mb (S.ORDN + offOf (fun i => Ma (S.CHX + i)) S.s u + j) =
        (grp (fun i => Ma (S.CHX + i)) S.s u).getD j 0)
    (hB3 : ∀ a, ¬ csrOut S.OFFN S.CNTN S.ORDN S.nch S.s a → Mb a = Ma a)
    (hC1 : ∀ i < S.nA, Mc (S.KEY + i) = (S.keyE Mb).key i)
    (hC2 : ∀ a, (a < S.KEY ∨ S.KEY + S.nA ≤ a) → Mc a = Mb a)
    (hD1 : ∀ u ≤ S.nch + 1, Md (S.OFFK + u) = offOf (fun i => Mc (S.KEY + i)) S.nA u)
    (hD2 : ∀ u < S.nch + 1, ∀ j < (grp (fun i => Mc (S.KEY + i)) S.nA u).length,
      Md (S.ORDK + offOf (fun i => Mc (S.KEY + i)) S.nA u + j) =
        (grp (fun i => Mc (S.KEY + i)) S.nA u).getD j 0)
    (hD3 : ∀ a, ¬ csrOut S.OFFK S.CNTK S.ORDK (S.nch + 1) S.nA a → Md a = Mc a) :
    TopOk S Md := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := S.lay
  have eB : ∀ a, (a < S.OFFN ∨ S.KEY ≤ a) → Mb a = Ma a := fun a ha =>
    hB3 a (by unfold csrOut; omega)
  have eD : ∀ a, (a < S.OFFK ∨ S.HM ≤ a) → Md a = Mc a := fun a ha =>
    hD3 a (by unfold csrOut; omega)
  have hlow : ∀ a < S.CHX, Md a = S.mem a := fun a ha => by
    rw [eD a (by omega), hC2 a (by omega), eB a (by omega), hA.out hpre (by omega)]
  have hlowB : ∀ a < S.h, Mb a = S.mem a := fun a ha => by
    rw [eB a (by omega), hA.out hpre (by omega)]
  have cxB : ∀ u < S.s, Mb (S.CHX + u) = Ma (S.CHX + u) := fun u hu => eB _ (by omega)
  have cxD : ∀ u < S.s, Md (S.CHX + u) = Ma (S.CHX + u) := fun u hu => by
    rw [eD _ (by omega), hC2 _ (by omega), eB _ (by omega)]
  have hkey : ∀ i < S.nA, Mc (S.KEY + i) = S.keyF Md i := fun i hi => by
    rw [hC1 i hi]
    exact keyE_key hpre hlowB cxB cxD hi
  have hfN : ∀ i < S.s, (fun i => Ma (S.CHX + i)) i = S.chxF Md i := fun i hi => by
    unfold chxF; rw [if_pos hi, cxD i hi]
  have hfK : ∀ i < S.nA, (fun i => Mc (S.KEY + i)) i = S.keyF Md i := fun i hi => hkey i hi
  refine ⟨fun k hk u hu => ?_, fun u hu hn => ?_, fun u hu => ?_, fun u hu j hj => ?_,
    fun u hu => ?_, fun u hu j hj => ?_, fun a ha => hlow a (by omega), fun a h1 h2 => ?_,
    fun a ha => ?_⟩
  · have := (pre_of hpre).nd_lt k hk u hu
    rw [cxD u this]
    exact hA.one hk hu
  · rw [cxD u hu]
    exact hA.zero hpre hn
  · rw [eD _ (by omega), hC2 _ (by omega), hB1 u hu]
    exact offOf_congr hfN u
  · rw [← grp_congr hfN u] at hj ⊢
    rw [← offOf_congr hfN u]
    have h1 := offOf_succ (f := fun i => Ma (S.CHX + i)) S.s u
    have h2 := offOf_le' (fun i => Ma (S.CHX + i)) S.s (u + 1)
    rw [eD _ (by omega), hC2 _ (by omega)]
    exact hB2 u hu j hj
  · rw [hD1 u hu]
    exact offOf_congr hfK u
  · rw [← grp_congr hfK u] at hj ⊢
    rw [← offOf_congr hfK u]
    exact hD2 u hu j hj
  · rw [hlow a h2]
    exact hpre.zero a h1
  · rw [eD a (by omega), hC2 a (by omega), eB a (by omega), hA.out hpre (by omega)]
    exact hpre.zero a (by omega)

/-- **The four calls of the top level.** From the registers `topF` and the memory at the call,
they end in a memory that meets `TopOk`, with the registers other than `28` unchanged. -/
theorem topCalls_runs {p : Program} {ω : ℕ → Bool} {I : CIdx}
    (fcx : MeetsContract w p I.cx (chxC w)) (fcsr : MeetsContract w p I.csr (csrC w))
    (fkey : MeetsContract w p I.key (keyC w))
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hb : S.H0 + S.nch + 4 < 2 ^ w) {st : State} (hR : st.regs = S.topF) (hM : st.mem = S.mem)
    {s : Stmt} {Q : Outcome → State → Prop} {A T : ℕ}
    (hrest : ∀ st' : State, S.TopR st' → TopOk S st'.mem →
      ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧ A + S.topCost + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call 28 I.cx (rgs [17, 18, 19, 7]))
      (.seq (.call 28 I.csr (rgs [7, 5, 4, 8, 9, 10]))
      (.seq (.call 28 I.key (rgs [6, 20, 21, 22, 23, 7, 4, 11]))
      (.seq (.call 28 I.csr (rgs [11, 6, 24, 12, 13, 14])) s)))) st o st' c ∧ Q o st' ∧
      A + c ≤ T := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := S.lay
  have hF := topF_lt hpre hb
  have hR0 : S.TopR st := fun r _ => by rw [hR]
  have wd : ∀ (l vs : List ℕ), l.map S.topF = vs → ∀ v ∈ vs, v < 2 ^ w := fun l vs h v hv => by
    rw [← h] at hv
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hv
    exact hF r
  have hspan := po_span_le hpre
  have hnP := nch_eq hpre
  have hnA : S.nA = S.X.nA := rfl
  refine runs_seq_callR_le fcx (vs := [S.X.nP, S.X.PL, S.X.PO, S.CHX]) ((hR0.map (by decide)).trans rfl) (wd [17, 18, 19, 7] _ rfl)
    ⟨S.chxE, S.s, rfl, hM.symm, chxE_ok hpre (by omega)⟩ (fun v1 Ma q1 hA => ?_)
  have hA' : S.ChxDone Ma := by
    have := hA S.chxE rfl hM.symm
    exact ⟨this.1, fun a ha => (this.2 a ha).trans (congrFun hM a)⟩
  have hR1 := hR0.upd v1 Ma q1
  refine runs_seq_callR_le fcsr (vs := [S.CHX, S.s, S.nch, S.OFFN, S.CNTN, S.ORDN]) ((hR1.map (by decide)).trans rfl) (wd [7, 5, 4, 8, 9, 10] _ rfl)
    ⟨_, _, _, _, _, _, rfl, fun i _ => hA'.lt hpre i, by omega, by omega, by omega, by omega⟩
    (fun v2 Mb q2 hB => ?_)
  have hB1 : ∀ u ≤ S.nch, Mb (S.OFFN + u) = offOf (fun i => Ma (S.CHX + i)) S.s u := hB.1
  have hB2 : ∀ u < S.nch, ∀ j < (grp (fun i => Ma (S.CHX + i)) S.s u).length,
      Mb (S.ORDN + offOf (fun i => Ma (S.CHX + i)) S.s u + j) =
        (grp (fun i => Ma (S.CHX + i)) S.s u).getD j 0 := hB.2.1
  have hB3 : ∀ a, ¬ csrOut S.OFFN S.CNTN S.ORDN S.nch S.s a → Mb a = Ma a := hB.2.2
  have hR2 := hR1.upd v2 Mb q2
  have hlowB : ∀ a < S.h, Mb a = S.mem a := fun a ha => by
    rw [hB3 a (by unfold csrOut; omega), hA'.out hpre (by omega)]
  refine runs_seq_callR_le fkey (vs := (S.keyE Mb).args) ((hR2.map (by decide)).trans rfl) (wd [6, 20, 21, 22, 23, 7, 4, 11] _ rfl)
    ⟨S.keyE Mb, rfl, rfl, keyE_ok hpre hb hlowB⟩ (fun v3 Mc q3 hC => ?_)
  have hC1 : ∀ i < S.nA, Mc (S.KEY + i) = (S.keyE Mb).key i := (hC (S.keyE Mb) rfl rfl).1
  have hC2 : ∀ a, (a < S.KEY ∨ S.KEY + S.nA ≤ a) → Mc a = Mb a := (hC (S.keyE Mb) rfl rfl).2
  have hR3 := hR2.upd v3 Mc q3
  have cxB : ∀ u < S.s, Mb (S.CHX + u) = Ma (S.CHX + u) := fun u hu =>
    hB3 _ (by unfold csrOut; omega)
  have hkey : ∀ i < S.nA, Mc (S.KEY + i) < S.nch + 1 := fun i hi => by
    rw [hC1 i hi]
    unfold KYE.key
    split_ifs
    · obtain ⟨-, -, -, hact⟩ := keyE_ends hpre hlowB hi
      have hu := (Cl.mem_act.mp hact).2.1
      have := hpre.ok.sv_lt hu
      have hs := (pre_of hpre).s
      obtain ⟨-, e1, -, -⟩ := keyE_ends hpre hlowB hi
      show Mb (S.CHX + (S.keyE Mb).nd ((S.keyE Mb).eu i)) < _
      rw [e1, keyE_nd hpre hlowB hu, cxB _ (by omega)]
      have := hA'.lt hpre (S.R.sv S.T S.c (S.G.pu (S.actP i)))
      omega
    · show S.nch < _; omega
  refine runs_seq_callR_le fcsr (vs := [S.KEY, S.nA, S.nch + 1, S.OFFK, S.CNTK, S.ORDK]) ((hR3.map (by decide)).trans rfl) (wd [11, 6, 24, 12, 13, 14] _ rfl)
    ⟨_, _, _, _, _, _, rfl, hkey, by omega, by omega, by omega, by omega⟩
    (fun v4 Md q4 hD => ?_)
  have hD1 : ∀ u ≤ S.nch + 1, Md (S.OFFK + u) = offOf (fun i => Mc (S.KEY + i)) S.nA u := hD.1
  have hD2 : ∀ u < S.nch + 1, ∀ j < (grp (fun i => Mc (S.KEY + i)) S.nA u).length,
      Md (S.ORDK + offOf (fun i => Mc (S.KEY + i)) S.nA u + j) =
        (grp (fun i => Mc (S.KEY + i)) S.nA u).getD j 0 := hD.2.1
  have hD3 : ∀ a, ¬ csrOut S.OFFK S.CNTK S.ORDK (S.nch + 1) S.nA a → Md a = Mc a := hD.2.2
  have hR4 := hR3.upd v4 Md q4
  have hTop := topOk_of hpre hA' hB1 hB2 hB3 hC1 hC2 hD1 hD2 hD3
  obtain ⟨o, st', c, h1, h2, h3⟩ := hrest _ hR4 hTop
  refine ⟨o, st', c, h1, h2, ?_⟩
  have c1 : (chxC w).cost [S.X.nP, S.X.PL, S.X.PO, S.CHX] S.mem ≤ 40 * (S.s + S.nch) := by
    show 40 * (S.mem (S.X.PO + S.X.nP) - S.mem S.X.PO + S.X.nP + 1) ≤ _
    omega
  have c2 : (csrC w).cost [S.CHX, S.s, S.nch, S.OFFN, S.CNTN, S.ORDN] Ma =
    100 * (S.s + S.nch + 1) := rfl
  have c3 : (keyC w).cost (S.keyE Mb).args Mb = 120 * (S.nA + 1) := rfl
  have c4 : (csrC w).cost [S.KEY, S.nA, S.nch + 1, S.OFFK, S.CNTK, S.ORDK] Mc =
    100 * (S.nA + (S.nch + 1) + 1) := rfl
  have hc : S.topCost = 1000 + 300 * (S.s + S.nch + S.nA) := rfl
  rw [← hM] at c1
  dsimp only
  simp only [List.length_cons, List.length_nil]
  omega

end CS

end MinCostFlow.LowStretch
