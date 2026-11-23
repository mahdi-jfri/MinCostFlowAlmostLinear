module

public import MinCostFlow.LowStretch.ProgClusterTree2

/-!
# One petal along the tree

`PW.Btw.petal_runs`: between two petals, a target `e` whose node `v` is allowed and whose path of
parents has `n` steps gives a run of `petalP`. The petal meets `PetalOk` with its portal at step
`m` of the path; its settled list `ℓ` holds the nodes of the petal; afterwards the facts between
petals, the tree and the cone hold again with the next stamp, the marks of `ℓ` are `os + 1`, and
the cells below the heads and above the settled list are as before. The cost is paid by the drop
of `Φ`, the sum of `deg + 1` over the allowed nodes, and a term `CJ` that depends only on `J` and
`L`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem deg_rs (L : DL) (r : ℕ) : DL.deg { L with rs := r } = L.deg := rfl

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {rs : ℕ} {A : TA}

/-- The cells that a petal keeps: below the heads and above the settled list. -/
def Safe (W : PW) (x : ℕ) : Prop := x < W.L.HD ∨ W.SL + W.L.NN + 1 ≤ x

/-- The arrays of the tree lie in cells that a petal keeps. -/
def TA.Safe (A : TA) (W : PW) : Prop :=
  ∀ v < W.s, W.Safe (A.PP + v) ∧ W.Safe (A.PF + v) ∧ W.Safe (A.PA + v) ∧ W.Safe (A.PB + v) ∧
    W.Safe (A.FD + v)

/-- The potential of the allowed nodes. -/
noncomputable def Φ (W : PW) (mem : ℕ → ℕ) : ℕ := ∑ u ∈ W.Nodes mem, (W.L.deg mem u + 1)

/-- The cost of a petal besides the drop of the potential. -/
def CJ (J Lb : ℕ) : ℕ :=
  4 * (50 * (Nat.log 2 J + 2) + 600) + 500 * Lb + psPreCost J + 150 * J + 1500

/-- The factor of the potential. -/
def Kφ (J : ℕ) : ℕ := 4 * (100 * (Nat.log 2 J + 2) + 900) + 200

theorem Y_on (h : W.Ok w mem) {u : ℕ} (hu : u < W.s) : W.Y (W.on mem u) = W.Y mem := by
  obtain ⟨l1, l2, l3, l4, l5, -⟩ := h.lay
  have hc := h.slot_cell hu
  unfold Y
  exact Finset.filter_congr fun a _ => by rw [on_ne (by omega)]

theorem Nodes_on (h : W.Ok w mem) {u : ℕ} (hu : u < W.s) : W.Nodes (W.on mem u) = W.Nodes mem := by
  obtain ⟨l1, l2, l3, l4, l5, -⟩ := h.lay
  have hc := h.slot_cell hu
  unfold Nodes
  exact Finset.filter_congr fun a _ => by rw [on_ne (by omega)]

theorem deg_congr {mem' : ℕ → ℕ} (h : ∀ v < W.L.NN, mem' (W.L.LO + v) = mem (W.L.LO + v) ∧
    mem' (W.L.HI + v) = mem (W.L.HI + v)) (u : ℕ) : W.L.deg mem' u = W.L.deg mem u := by
  unfold DL.deg DL.g
  dsimp only
  split_ifs with hu
  · rw [(h u hu).1, (h u hu).2]
  · rfl

/-- The settled list has at least one cell per node, and at least `deg + 1` per node. -/
theorem len_le_sum {N : Finset ℕ} {ℓ : List ℕ} (hnd : ℓ.Nodup) (hsub : ∀ v ∈ ℓ, v ∈ N)
    (f : ℕ → ℕ) : ℓ.length ≤ ∑ u ∈ N.filter (· ∈ ℓ), (f u + 1) := by
  have he : N.filter (· ∈ ℓ) = ℓ.toFinset := by
    ext v; simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hsub v h, h⟩⟩
  rw [he, ← List.toFinset_card_of_nodup hnd, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun _ _ => by omega

open Classical in
theorem pot_eq (L : DL) (mem : ℕ → ℕ) (N : Finset ℕ) (d : DS) (qs : ℕ → List (ℕ × ℕ)) :
    ∃ S, L.pot mem N d qs = (100 * (Nat.log 2 L.J + 2) + 900) * S +
      (50 * (Nat.log 2 L.J + 2) + 600) * (pqAll L.J qs).length ∧
      S = ∑ u ∈ N.filter (fun u => ¬ d.sett u), (L.deg mem u + 1) := ⟨_, rfl, rfl⟩

variable {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ} {lo : ℕ}

open Classical in
set_option maxHeartbeats 4000000 in
/-- **One petal along the tree.** -/
theorem Btw.petal_runs {p : Program} {bS bF bT bPush bPS bClr : ℕ}
    (hS : p.HasAt bS [psrchA bPush bPS bClr]) (hPush : MeetsContract w p bPush (pqPushC w))
    (hPS : MeetsContract w p bPS (pstepC w)) (hClr : MeetsContract w p bClr (pqClearC w))
    (hF : MeetsContract w p bF (pfinC w)) (hT' : MeetsContract w p bT (portC w))
    (hB : W.Btw w mem rs) (hT : W.Tree A mem) (hc : W.Cone mem) (hA : A.Safe W)
    {e n : ℕ} (hp : W.Path mem (W.sv e) n) (he : e ∈ W.c.X)
    (hal : mem (W.L.OK + W.sv e) = W.L.os)
    (hd : W.c.HwDec W.G e (W.stp A mem (W.sv e) n) hw)
    (wb : lo + (W.Lb + 1) * W.bw + 2 < 2 ^ w)
    (wT1 : (8 * W.M * (W.κ + W.nA) + (lo + (W.Lb + 1) * W.bw + 1) * (W.nA * 2 ^ W.Es)) *
      (W.Sm + 1) < 2 ^ w)
    (hRm : lo + (W.Lb + 1) * W.bw ≤ W.Rm) (hINF : lo + (W.Lb + 1) * W.bw < W.L.INF)
    (hrs : rs < 2 ^ w)
    (hwA : ∀ x ∈ W.pargs (W.on mem (W.sv e)) e (W.stp A mem (W.sv e) n) hw lo rs, x < 2 ^ w)
    (hdist : lo + W.Lb * W.bw < W.c.d W.G W.c.x0 e) (pos : ℕ) (ω : ℕ → Bool) :
    ∃ o st' c, Runs w p ω (petalP bS bF bT)
        (startState (W.pargs (W.on mem (W.sv e)) e (W.stp A mem (W.sv e) n) hw lo rs) mem pos)
        o st' c ∧
      ∃ (i m : ℕ) (ℓ : List ℕ),
        W.c.PetalOk W.G W.P (W.Y mem) lo ⟨e, hw, o.value - 2, i⟩ ∧
        W.c.carve W.G (W.Y mem) ⟨e, hw, o.value - 2, i⟩ =
          (W.Y mem).filter (fun x => W.sv x ∈ ℓ) ∧
        ℓ.Nodup ∧ (∀ u ∈ ℓ, u ∈ W.Nodes mem) ∧ m < n ∧
        hw.getD i 0 = mem (A.PP + W.pe mem (W.sv e) m) ∧
        hv W.G e hw i = mem (A.PA + W.pe mem (W.sv e) m) ∧
        hv W.G e hw (i + 1) = mem (A.PB + W.pe mem (W.sv e) m) ∧
        st'.mem (W.CTL + 3) = W.pe mem (W.sv e) m ∧ st'.mem (W.CTL + 1) = ℓ.length ∧
        (∀ j < ℓ.length, st'.mem (W.SL + j) = ℓ.getD j 0) ∧
        W.Btw w st'.mem (rs + 1) ∧ W.Tree A st'.mem ∧ W.Cone st'.mem ∧
        (∀ u < W.s, st'.mem (W.L.OK + u) = if u ∈ ℓ then W.L.os + 1 else mem (W.L.OK + u)) ∧
        (∀ x, W.Safe x → st'.mem x = mem x) ∧
        (∀ x, x < W.L.TS → (x < W.L.HD ∨ W.L.HD + W.L.MM ≤ x) →
          ¬ (W.L.OK ≤ x ∧ x < W.L.OK + W.s) → st'.mem x = mem x) ∧
        c + Kφ W.L.J * W.Φ st'.mem + 80 * ℓ.length ≤ Kφ W.L.J * W.Φ mem + CJ W.L.J W.Lb := by
  have h := hB.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN
  have hvs : W.sv e < W.s := h.sv_lt he
  have hcs := h.slot_cell hvs
  have hPSf := hB.ps hT hp he rfl (hc.path hp hal) hd wb wT1 hRm hINF
  obtain ⟨h1, hpq, htz, hst, -, -⟩ := hB.on_ok hvs
  obtain ⟨o, st', c, hrun, a, memL, memC, i, m, hm, hfd, hclr, hpet, hcarve, hj, e0, e1, e2, q1, q2,
    q3, q4, q5, hcost⟩ := h1.petalP_runs hS hPush hPS hClr hF hT' hPSf hrs hpq htz hst rfl hwA
      hdist pos ω
  obtain ⟨hB', hok', hlow'⟩ := hB.after hvs h1 hPSf hfd.1 hclr hm hj q2 q3 q4
  have hI := hfd.1
  have hY := Y_on h hvs
  have hN := Nodes_on h hvs
  rw [hY] at hpet hcarve
  have hcarve' : W.c.carve W.G (W.Y mem) ⟨e, hw, o.value - 2, i⟩ =
      (W.Y mem).filter (fun x => W.sv x ∈ a.ℓ) := by
    rw [hcarve]; exact Finset.filter_congr fun x _ => hI.sett _
  have hℓsub : ∀ u ∈ a.ℓ, u ∈ W.Nodes mem := fun u hu => hN ▸ (h1.sett_lt hI hu).1
  have hlen := stp_length (W := W) (A := A) (mem := mem) (W.sv e) n
  have hmn : m < n := hlen ▸ hm
  have hgm := stp_getElem (W := W) (A := A) (mem := mem) (v := W.sv e) (n := n) (i := m) hm
  have hR := h.hR; have hCTL := h.hCTL; have hSUM := h.hSUM; have hSL := h.hSL
  have hsafe : ∀ x, W.Safe x → st'.mem x = mem x := fun x hx => by
    unfold Safe at hx
    rw [q5 x hx, on_ne (by omega)]
  have hH : (W.Hl e (W.stp A mem (W.sv e) n)).getD m 0 = W.pe mem (W.sv e) m := by
    rw [hT.Hl_eq hp rfl, List.getD_eq_getElem _ _ (by simp; omega)]; simp
  -- the counter and the settled list
  have hℓlt : ∀ j < a.ℓ.length, a.ℓ.getD j 0 < W.s := fun j hj' => (h1.sett_lt hI (getD_mem' hj')).2
  obtain ⟨c1, -, c3⟩ := h1.after_ctl hI hclr
  have hq4 : ∀ x, W.CTL ≤ x → x ≠ W.CTL + 3 → st'.mem x = memC x := fun x hx1 hx2 =>
    q4 x hx2 (fun j hj' => by
      have := hℓlt j hj'
      have := h1.hiMM (a.ℓ.getD j 0) (by omega)
      constructor <;> omega) (by
        have hmH : (W.Hl e (W.stp A mem (W.sv e) n)).getD (m + 1) 0 < W.s :=
          h1.H_lt hPSf (getD_mem' (by rw [Hl_length]; omega))
        have := h1.hiMM _ (show (W.Hl e (W.stp A mem (W.sv e) n)).getD (m + 1) 0 < W.L.NN by
          omega)
        omega)
  -- the tree and the cone
  have hT2 : W.Tree A st'.mem := hT.congr (fun v hv => by
      obtain ⟨f1, f2, f3, f4, f5⟩ := hA v hv
      refine ⟨hlow' _ (by omega) (Or.inr (by omega)) (by omega),
        hlow' _ (by omega) (Or.inl (by omega)) (by omega), hsafe _ f1, hsafe _ f2, hsafe _ f3,
        hsafe _ f4, hsafe _ f5⟩)
    (fun v hv => by
      have := h.slot_lt hv
      exact hlow' _ (by omega) (Or.inr (by omega)) (by omega)) h.root_lt fun a ha => h.sv_lt ha
  have hc2 : W.Cone st'.mem := hc.after hT hok' hcarve' fun v hv =>
    hlow' _ (by omega) (Or.inr (by omega)) (by omega)
  -- the cost
  have hdeg1 : ∀ u, W.L.deg (W.on mem (W.sv e)) u = W.L.deg mem u :=
    deg_congr fun v hv => ⟨on_ne (by omega), on_ne (by omega)⟩
  have hdeg2 : ∀ u, W.L.deg st'.mem u = W.L.deg mem u :=
    deg_congr fun v hv => ⟨hlow' _ (by omega) (Or.inl (by omega)) (by omega),
      hlow' _ (by omega) (Or.inl (by omega)) (by omega)⟩
  have hN2 : W.Nodes st'.mem = (W.Nodes mem).filter (fun u => u ∉ a.ℓ) := by
    ext v
    simp only [Nodes, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hv, hv'⟩
      rcases Nat.lt_or_ge v W.s with hvs' | hvs'
      · rw [hok' v hvs'] at hv'
        split_ifs at hv' with hl
        · omega
        · exact ⟨⟨hv, hv'⟩, hl⟩
      · have hv2 : v = W.s := by omega
        subst hv2
        rw [hlow' _ (by omega) (Or.inr (by omega)) (by omega)] at hv'
        exact absurd hv' h.sS
    · rintro ⟨⟨hv, hv'⟩, hl⟩
      have hvs' : v < W.s := h.lt_s_of hv hv'
      rw [hok' v hvs', if_neg hl]
      exact ⟨hv, hv'⟩
  have hΦ2 : W.Φ st'.mem = ∑ u ∈ (W.Nodes mem).filter (fun u => u ∉ a.ℓ), (W.L.deg mem u + 1) := by
    unfold Φ; rw [hN2]; exact Finset.sum_congr rfl fun u _ => by rw [hdeg2]
  have hsplit := Finset.sum_filter_add_sum_filter_not (W.Nodes mem) (fun u => u ∈ a.ℓ)
    (fun u => W.L.deg mem u + 1)
  have hS1 := len_le_sum hI.nd hℓsub (fun u => W.L.deg mem u)
  -- the measure at the start and at the stop
  set C := W.sc (W.on mem (W.sv e)) e (W.stp A mem (W.sv e) n) hw lo rs with hCdef
  obtain ⟨S0, hp0, hS0⟩ := pot_eq C.L C.mem0 C.X.G.Nodes C.a0.d C.a0.qs
  obtain ⟨Sa, hpa, hSa⟩ := pot_eq C.L C.mem0 C.X.G.Nodes a.d a.qs
  have hS0' : S0 = W.Φ mem := by
    rw [hS0]
    change ∑ u ∈ (W.Nodes (W.on mem (W.sv e))).filter _,
      (W.L.deg (W.on mem (W.sv e)) u + 1) = _
    rw [Finset.filter_true_of_mem (fun u _ => by simp [SC.a0, DL.d0]), hN]
    exact Finset.sum_congr rfl fun u _ => by rw [hdeg1]
  have hSa' : Sa = ∑ u ∈ (W.Nodes mem).filter (fun u => u ∉ a.ℓ), (W.L.deg mem u + 1) := by
    rw [hSa]
    change ∑ u ∈ (W.Nodes (W.on mem (W.sv e))).filter _,
      (W.L.deg (W.on mem (W.sv e)) u + 1) = _
    rw [hN]
    refine Finset.sum_congr (Finset.filter_congr fun u _ => by rw [hI.sett]) fun u _ => ?_
    rw [hdeg1]
  have hq1 : (pqAll W.L.J (DL.qs1 (W.sv e))).length = 1 := by
    rw [DL.pqAll_qs1 hpq.J_pos]; rfl
  have hμ0 : C.μ C.a0 =
      4 * ((100 * (Nat.log 2 W.L.J + 2) + 900) * S0 + (50 * (Nat.log 2 W.L.J + 2) + 600)) +
        500 * W.Lb + 2 * stCost W.L.J + 2000 := by
    unfold SC.μ; rw [hp0]
    change 4 * ((100 * (Nat.log 2 W.L.J + 2) + 900) * S0 +
      (50 * (Nat.log 2 W.L.J + 2) + 600) * (pqAll W.L.J (DL.qs1 (W.sv e))).length) +
      500 * (W.Lb + 1 - 1) + 2 * stCost W.L.J + 2000 = _
    rw [hq1]; simp only [Nat.add_sub_cancel, mul_one]
  have hμa : 4 * ((100 * (Nat.log 2 W.L.J + 2) + 900) * Sa) + 2 * stCost W.L.J + 2000 ≤
      C.μ a := by
    unfold SC.μ; rw [hpa]
    change _ ≤ 4 * ((100 * (Nat.log 2 W.L.J + 2) + 900) * Sa + _) + _ + 2 * stCost W.L.J + 2000
    omega
  -- the portal lies on the settled part of the highway
  have hjℓ : a.j ≤ a.ℓ.length := by
    have hnd := hPSf.nd
    have hsub : ((W.Hl e (W.stp A mem (W.sv e) n)).take a.j).toFinset ⊆ a.ℓ.toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      rw [List.length_take] at hk
      rw [List.getElem_take]
      have hk2 : k < (W.Hl e (W.stp A mem (W.sv e) n)).length := by omega
      have := (hI.hsett k hk2).mpr (by omega)
      rw [hI.sett] at this
      change (W.Hl e (W.stp A mem (W.sv e) n)).getD k 0 ∈ a.ℓ at this
      rwa [List.getD_eq_getElem _ _ hk2] at this
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist _ _)),
      List.toFinset_card_of_nodup hI.nd, List.length_take] at this
    have := hI.jle
    change a.j ≤ (W.Hl e (W.stp A mem (W.sv e) n)).length at this
    omega
  refine ⟨o, st', c, hrun, i, m, a.ℓ, hpet, hcarve', hI.nd, hℓsub, hmn,
    by rw [e0, hgm], by rw [e1, hgm], by rw [e2, hgm], by rw [q1, hH],
    by rw [hq4 _ (by omega) (by omega)]; exact c1,
    fun j hj' => by rw [hq4 _ (by omega) (by omega)]; exact c3 j hj',
    hB', hT2, hc2, hok', hsafe, hlow', ?_⟩
  set S1 := ∑ u ∈ (W.Nodes mem).filter (fun u => u ∈ a.ℓ), (W.L.deg mem u + 1) with hS1def
  have hΦm : W.Φ mem = S1 + Sa := by rw [hSa']; exact hsplit.symm
  rw [hΦ2, ← hSa', hΦm]
  have e3 : Kφ W.L.J * (S1 + Sa) =
      4 * ((100 * (Nat.log 2 W.L.J + 2) + 900) *
        S1) +
      4 * ((100 * (Nat.log 2 W.L.J + 2) + 900) * Sa) +
      200 * S1 + 200 * Sa := by
    unfold Kφ; ring
  have e4 : Kφ W.L.J * Sa = 4 * ((100 * (Nat.log 2 W.L.J + 2) + 900) * Sa) + 200 * Sa := by
    unfold Kφ; ring
  have e5 : (100 * (Nat.log 2 W.L.J + 2) + 900) * S0 =
      (100 * (Nat.log 2 W.L.J + 2) + 900) *
        S1 +
      (100 * (Nat.log 2 W.L.J + 2) + 900) * Sa := by
    rw [hS0', hΦm]; ring
  rw [e3, e4]
  unfold CJ
  omega

end PW

end MinCostFlow.LowStretch
