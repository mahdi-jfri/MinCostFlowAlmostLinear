module

public import MinCostFlow.LowStretch.ProgClusterLoop3

/-!
# The invariant after the special petal

`PW.LInv.after_sp`: the special petal is carved before the loop of the regular petals, at
`u = 0` and with no petal before it, from the node `vt` of the target of the cluster. Then the
invariant holds with this petal added and `k0 = 1`: the rule for regular petals applies only from
petal `1` on. The proof is that of `PW.LInv.after_pet`, with the node `vt` in place of `u`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

open Classical in
set_option maxHeartbeats 4000000 in
/-- **The invariant after the special petal.** It is carved before the loop, at `u = 0`, from
the target node `vt`. -/
theorem LInv.after_sp {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a st) (hL : W.LLay A Q w) (hps : a.ps = []) (hu0 : a.u = 0)
    (hrs1 : a.rs + 1 + W.s < 2 ^ w) {vt e lo : ℕ} (hu : vt < W.s)
    {n : ℕ} (hp : W.Path st.mem vt n) (hpa : W.sv (e) = vt)
    (hpaX : e ∈ W.c.X) {hw : List ℕ}
    (hd : W.c.HwDec W.G (e) (W.stp A st.mem vt n) hw)
    {r i m : ℕ} {ℓ : List ℕ} {mem1 memf : ℕ → ℕ}
    (hpet : W.c.PetalOk W.G W.P (W.Y st.mem) lo ⟨e, hw, r, i⟩)
    (hcarve : W.c.carve W.G (W.Y st.mem) ⟨e, hw, r, i⟩ =
      (W.Y st.mem).filter (fun x => W.sv x ∈ ℓ))
    (hnd : ℓ.Nodup) (hsub : ∀ v ∈ ℓ, v ∈ W.Nodes st.mem) (hmn : m < n)
    (e0 : hw.getD i 0 = st.mem (A.PP + W.pe st.mem vt m))
    (e1 : hv W.G (e) hw i = st.mem (A.PA + W.pe st.mem vt m))
    (e2 : hv W.G (e) hw (i + 1) = st.mem (A.PB + W.pe st.mem vt m))
    (hB1 : W.Btw w mem1 (a.rs + 1)) (hT1 : W.Tree A mem1) (hc1 : W.Cone mem1)
    (hok1 : ∀ v < W.s, mem1 (W.L.OK + v) = if v ∈ ℓ then W.L.os + 1 else st.mem (W.L.OK + v))
    (hsafe1 : ∀ x, W.Safe x → mem1 x = st.mem x)
    (hlow1 : ∀ x, x < W.L.TS → (x < W.L.HD ∨ W.L.HD + W.L.MM ≤ x) →
      ¬ (W.L.OK ≤ x ∧ x < W.L.OK + W.s) → mem1 x = st.mem x)
    (hf0 : ∀ x, ¬ W.Out Q x → memf x = mem1 x)
    (hf1 : ∀ j < ℓ.length, memf (Q.PL + st.mem (Q.PO + a.ps.length) + j) = ℓ.getD j 0)
    (hf2 : memf (Q.PO + (a.ps.length + 1)) = st.mem (Q.PO + a.ps.length) + ℓ.length)
    (hf3 : memf (Q.CT + (a.ps.length + 1)) = e)
    (hf4 : memf (Q.CC + (a.ps.length + 1)) = st.mem (A.PA + W.pe st.mem vt m))
    (hf5 : memf (Q.PT + a.ps.length) = st.mem (A.PP + W.pe st.mem vt m))
    (hf6 : ∀ x, W.Out Q x →
      ¬ (Q.PL + st.mem (Q.PO + a.ps.length) ≤ x ∧
        x < Q.PL + st.mem (Q.PO + a.ps.length) + ℓ.length) →
      x ≠ Q.PO + (a.ps.length + 1) → x ≠ Q.CT + (a.ps.length + 1) →
      x ≠ Q.CC + (a.ps.length + 1) → x ≠ Q.PT + a.ps.length → memf x = st.mem x)
    {stf : State} (hmf : stf.mem = memf)
    (hr : ∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 → stf.regs i = st.regs i)
    (hr13 : stf.regs 13 = a.rs + 1) (hr32 : stf.regs 32 = a.u)
    (hr41 : stf.regs 41 = a.ps.length + 1) :
    W.LInv A Q sp 1 M0 w ⟨a.u, a.rs + 1, a.ps ++ [⟨e, hw, r, i⟩],
      W.Φ mem1⟩ stf := by
  set pd : PD := ⟨e, hw, r, i⟩ with hpd
  have h := hI.btw.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN; have hR := h.hR; have hCTL := h.hCTL
  have hSUM := h.hSUM; have hSL := h.hSL
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have hpl := hL.pl; have hpo := hL.po; have hct := hL.ct; have hcc := hL.cc; have hpt := hL.pt
  have hout := fun {x : ℕ} (hx : W.Out Q x) => hL.out_ge hx
  -- cells below the settled list are not outputs
  have hlowf : ∀ x < W.SL, memf x = mem1 x := fun x hx => hf0 x fun ho => by
    have := hout ho; omega
  have hA0 : ∀ x < W.L.HD, memf x = st.mem x := fun x hx => by
    rw [hlowf x (by omega), hsafe1 x (Or.inl hx)]
  have hTS : ∀ x < W.L.TS, memf x = mem1 x := fun x hx => hlowf x (by omega)
  -- the new remaining set
  have hY1 : W.Y mem1 = (W.Y st.mem).filter (fun x => W.sv x ∉ ℓ) := Y_after h hok1
  have hN1 : W.Nodes mem1 = (W.Nodes st.mem).filter (fun v => v ∉ ℓ) :=
    Nodes_after h hok1 (hlow1 _ (by omega) (Or.inr (by omega)) (by omega))
  -- the target is carved
  have heC : e ∈ W.c.carve W.G (W.Y st.mem) pd := by
    have := hpet.2.2.2.1 0 (Nat.zero_le _); rwa [Cl.hv_zero] at this
  have huℓ : vt ∈ ℓ := by
    rw [hcarve, Finset.mem_filter] at heC; rw [← hpa]; exact heC.2
  -- the path in `M0`
  have hNXT0 : ∀ v < W.L.NN, st.mem (W.NXT + v) = M0 (W.NXT + v) := fun v hv =>
    hI.low _ (by omega) (Or.inr (by omega)) (by omega)
  have hpe0 : ∀ j, W.pe M0 vt j = W.pe st.mem vt j := fun j =>
    pe_congr (mem := st.mem) h (fun v hv => (hNXT0 v hv).symm) (show vt < W.L.NN by omega) j
  have hAM0 : ∀ v < W.s, st.mem (A.PP + v) = M0 (A.PP + v) ∧ st.mem (A.PA + v) = M0 (A.PA + v) ∧
      st.mem (A.PB + v) = M0 (A.PB + v) := fun v hv =>
    ⟨hI.safe _ (Or.inl (by omega)) fun ho => by have := hout ho; omega,
      hI.safe _ (Or.inl (by omega)) fun ho => by have := hout ho; omega,
      hI.safe _ (Or.inl (by omega)) fun ho => by have := hout ho; omega⟩
  have hpm : W.pe st.mem vt m < W.s := hp.lt h.root_lt hmn.le
  -- the number of petals
  have huN : vt ∈ W.Nodes st.mem := hsub _ huℓ
  have hN0 : 0 < (W.Nodes st.mem).card := Finset.card_pos.mpr ⟨_, huN⟩
  have hkle := hI.kle
  have hks : a.ps.length < W.s := by omega
  have hℓN : ℓ.length ≤ (W.Nodes st.mem).card := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card fun v hv => hsub v (List.mem_toFinset.mp hv)
  have hroom := hI.room
  refine
    { regs := fun j hj h13 h32 h41 => by rw [hr j hj h13 h32 h41]; exact hI.regs j hj h13 h32 h41
      r13 := hr13, r32 := hr32
      r41 := by rw [hr41, List.length_append, List.length_singleton]
      k0le := by simp only [List.length_append, List.length_singleton]; omega
      btw := hB1.congr_low (by rw [hmf]; exact hlowf)
      tree := hT1.congr (fun v hv => by
          rw [hmf]
          exact ⟨hTS _ (by omega), hTS _ (by omega), hlowf _ (by omega), hlowf _ (by omega),
            hlowf _ (by omega), hlowf _ (by omega), hlowf _ (by omega)⟩)
        (fun v hv => by rw [hmf]; exact hTS _ (by have := hB1.ok.slot_lt hv; omega))
        h.root_lt fun x hx => h.sv_lt hx
      cone := Cone.congr hB1.ok hc1 (by rw [hmf]; exact hTS)
      φ := by rw [hmf]; exact Φ_congr hB1.ok hTS
      Y := ?_, safe := ?_, low := ?_, scan := ?_, reg := ?_, po := ?_, out := ?_, room := ?_
      kle := ?_
      ule := by show a.u ≤ W.s; omega
      rsw := by show a.rs + 1 + (W.s - a.u) < 2 ^ w; omega }
  · -- the remaining set
    rw [hmf, Y_congr hB1.ok hTS, hY1]
    dsimp only
    rw [List.length_append, List.length_singleton, Cl.Z_append_last, ← hI.Y, hcarve]
    ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  · intro x hx hno
    rw [hmf, hf0 x hno, hsafe1 x hx]; exact hI.safe x hx hno
  · intro x hx e1' e2'
    rw [hmf, hTS x hx, hlow1 x hx e1' e2']; exact hI.low x hx e1' e2'
  · intro v hv
    exact absurd hv (by rw [hu0]; omega)
  · intro j hj1 hj2
    simp only [List.length_append, List.length_singleton, hps, List.length_nil] at hj2
    omega
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    rw [hmf]
    rcases Nat.lt_or_ge (j + 1) a.ps.length with hjk | hjk
    · rw [hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hI.po j (by omega)
    · rcases Nat.lt_or_ge j a.ps.length with hjk' | hjk'
      · have hj' : j + 1 = a.ps.length := by omega
        rw [hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          hj', hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        have := hI.po j (by omega); rw [hj'] at this; exact this
      · have hj' : j = a.ps.length := by omega
        rw [hj', hf2, hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)]
        omega
  · -- the outputs
    intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    rw [hmf]
    rcases Nat.lt_or_ge j a.ps.length with hjk | hjk
    · have hm1 := hI.po_mono (j := j + 1) (k := a.ps.length) (by omega) le_rfl
      refine PetOut.congr (hI.out j hjk) (fun x hx => ?_) (Cl.W_append hjk)
        (Cl.Dec.pd_append_lt hjk)
      rcases hx with rfl | rfl | ⟨hx1, hx2⟩ | rfl | rfl | rfl
      · exact hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hj' : j = a.ps.length := by omega
      subst hj'
      have hPOk : memf (Q.PO + a.ps.length) = st.mem (Q.PO + a.ps.length) :=
        hf6 _ (by unfold Out; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hnl : nl Q memf a.ps.length = ℓ := by
        unfold nl
        rw [hf2, hPOk, Nat.add_sub_cancel_left]
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [hf1 j (by simpa using h1), List.getD_eq_getElem _ _ h2]
      have hW : W.c.W W.G ⟨sp, a.ps ++ [pd]⟩ a.ps.length = (W.Y st.mem).filter
          (fun x => W.sv x ∈ ℓ) := by
        rw [Cl.W_append_last, ← hI.Y, hcarve]
      have hm0 : ∀ v < W.L.NN, M0 (W.NXT + v) = st.mem (W.NXT + v) := fun v hv =>
        (hNXT0 v hv).symm
      have hp0 : W.Path M0 vt n := (Path_congr (mem := st.mem) h hm0 (by omega)).mpr hp
      have hst0 : W.stp A M0 vt n = W.stp A st.mem vt n :=
        stp_congr (mem := st.mem) h hm0 (by omega) fun j hj => by
          have := hp.lt h.root_lt hj.le
          exact ⟨(hAM0 _ this).1.symm, (hAM0 _ this).2.1.symm, (hAM0 _ this).2.2.symm⟩
      refine ⟨by rw [hnl]; exact hnd, fun v => ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnl, hW]
        constructor
        · intro hv
          have hvN := hsub v hv
          have hvs : v < W.s := h.nodes_lt hvN
          obtain ⟨x, hx, rfl⟩ := h.sv_surj hvs
          refine ⟨x, Finset.mem_filter.mpr ⟨mem_Y.mpr ⟨hx, ?_⟩, hv⟩, rfl⟩
          unfold Nodes at hvN; exact (Finset.mem_filter.mp hvN).2
        · rintro ⟨x, hx, rfl⟩; exact (Finset.mem_filter.mp hx).2
      · rw [Cl.Dec.pd_append_eq]; exact hf3
      · unfold Cl.Dec.xc; rw [Cl.Dec.pd_append_eq, hf4]; exact e1.symm
      · unfold Cl.Dec.portal; rw [Cl.Dec.pd_append_eq, hf5]; exact e0.symm
      · rw [Cl.Dec.pd_append_eq]
        show ∃ n m, W.Path M0 (W.sv e) n ∧ e ∈ W.c.X ∧ W.c.HwDec W.G e (W.stp A M0 (W.sv e) n) hw ∧
          m < n ∧ hw.getD i 0 = M0 (A.PP + W.pe M0 (W.sv e) m) ∧
          hv W.G e hw i = M0 (A.PA + W.pe M0 (W.sv e) m) ∧
          hv W.G e hw (i + 1) = M0 (A.PB + W.pe M0 (W.sv e) m)
        rw [hpa]
        simp only [hpe0]
        exact ⟨n, m, hp0, hpaX, by convert hd using 2, hmn, by rw [e0]; exact (hAM0 _ hpm).1,
          by rw [e1]; exact (hAM0 _ hpm).2.1, by rw [e2]; exact (hAM0 _ hpm).2.2⟩
  · -- the room
    have hc := Finset.card_filter_add_card_filter_not (s := W.Nodes st.mem)
      (fun v => v ∈ ℓ)
    have hℓc : ((W.Nodes st.mem).filter (fun v => v ∈ ℓ)).card = ℓ.length := by
      rw [← List.toFinset_card_of_nodup hnd]
      congr 1; ext v; simp only [Finset.mem_filter, List.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub v h, h⟩⟩
    rw [hmf, Nodes_congr hB1.ok hTS, hN1]
    simp only [List.length_append, List.length_singleton]
    rw [hf2]
    omega
  · -- the number of petals
    have hc := Finset.card_filter_add_card_filter_not (s := W.Nodes st.mem)
      (fun v => v ∈ ℓ)
    have hℓc : ((W.Nodes st.mem).filter (fun v => v ∈ ℓ)).card = ℓ.length := by
      rw [← List.toFinset_card_of_nodup hnd]
      congr 1; ext v; simp only [Finset.mem_filter, List.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub v h, h⟩⟩
    have hℓ1 : 1 ≤ ℓ.length := List.length_pos_of_mem huℓ
    rw [hmf, Nodes_congr hB1.ok hTS, hN1]
    simp only [List.length_append, List.length_singleton]
    omega

end PW

end MinCostFlow.LowStretch
