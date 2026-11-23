module

public import MinCostFlow.LowStretch.PSearchPre

/-!
# The steps of the petal search that settle nothing

The petal search is in some state of Dijkstra, with least key `k`. Let `K = min(k, INF)`. Every
radius `r` with `d.L ≤ r < K` has the same petal: the vertices of `Y` whose super-vertex is
settled (`Inv.carve`). So the five sums in memory are the sums of region growing for that petal
(`Inv.elink`), and the test of `ptest` is the pair of tests of region growing (`Inv.pass`).

Two kinds of calls of `pstep` return `1` without settling a node. A test that fails at the end of
the bucket moves the bucket pointer (`Inv.adv`): the bucket then fails for every radius. A step of
Dijkstra that drops a stale entry changes only the queue (`Inv.drop`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {P : Par} {c : Cl}

/-- **One interval, one bucket**, as `BFail.step`, with the petal the same only up to the end of
the bucket. -/
theorem BFail.step2 (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {pd : PD}
    {lo q a k : ℕ} (hf : BFail G P c Y pd lo q a)
    (hsame : ∀ r, a ≤ r → r < k → r ≤ lo + q * c.bw G P →
      c.carve G Y (pd.withR r) = c.carve G Y (pd.withR (min (k - 1) (lo + q * c.bw G P))))
    (htest : lo + (q - 1) * c.bw G P < k → a ≤ lo + q * c.bw G P →
      ¬ (c.cost G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) * c.sq G P q ≤
          8 * c.vol G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) ∧
        c.vol G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) ≤ c.T G P q)) :
    BFail G P c Y pd lo q k := by
  intro r hr h1 h2 ⟨t1, t2⟩
  by_cases hra : r < a
  · exact hf r hra h1 h2 ⟨t1, t2⟩
  push Not at hra
  have hrr : r ≤ min (k - 1) (lo + q * c.bw G P) := le_min (by omega) h2
  have hcost : c.cost G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) =
      c.cost G P Y (pd.withR r) := by
    unfold cost; rw [hsame r hra hr h2]
  refine htest (by omega) (by omega) ⟨?_, ?_⟩
  · rw [hcost]
    exact t1.trans (by linarith [vol_mono (P := P) hGo hc hY pd hrr])
  · exact (vol_mono (P := P) hGo hc hY pd (min_le_right _ _)).trans t2

end Cl

/-- **The frame of Dijkstra.** A memory that agrees with `mem` on the cells of Dijkstra (the
heads may change, to nodes) holds the same state. -/
theorem DL.frameAll {L : DL} {w : ℕ} {mem mem' : ℕ → ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} (hs : L.Shape w mem Nodes) (hr : L.Rep mem Nodes d qs)
    (hz : L.TZ mem qs) (hS : L.Stamps mem)
    (h1 : ∀ x, L.TS ≤ x → x < L.D + pqSize L.J L.A → mem' x = mem x)
    (h2 : ∀ v < L.NN, mem' (L.LO + v) = mem (L.LO + v) ∧ mem' (L.HI + v) = mem (L.HI + v) ∧
      mem' (L.OK + v) = mem (L.OK + v))
    (h3 : ∀ k < L.MM, mem' (L.CS + k) = mem (L.CS + k) ∧ mem' (L.CL + k) = mem (L.CL + k) ∧
      mem' (L.HD + k) < L.NN) :
    L.Shape w mem' Nodes ∧ L.Rep mem' Nodes d qs ∧ L.TZ mem' qs ∧ L.Stamps mem' ∧
      (∀ u, L.deg mem' u = L.deg mem u) ∧
      ∀ (g : AG) s, g.ParInv s L.INF d (L.par mem) (L.parc mem) →
        g.ParInv s L.INF d (L.par mem') (L.parc mem') := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hlo : (L.g mem').lo = (L.g mem).lo := funext fun u => by
    simp only [DL.g]; split_ifs with hu
    · exact (h2 u hu).1
    · rfl
  have hhi : (L.g mem').hi = (L.g mem).hi := funext fun u => by
    simp only [DL.g]; split_ifs with hu
    · exact (h2 u hu).2.1
    · rfl
  have hok : ∀ v, (L.g mem').ok v ↔ (L.g mem).ok v := fun v => by
    simp only [DL.g]
    constructor
    · rintro ⟨hv, he⟩; exact ⟨hv, by rw [← (h2 v hv).2.2]; exact he⟩
    · rintro ⟨hv, he⟩; exact ⟨hv, by rw [(h2 v hv).2.2]; exact he⟩
  have hdeg : ∀ u, L.deg mem' u = L.deg mem u := fun u => by unfold DL.deg; rw [hlo, hhi]
  have hv : ∀ v ∈ Nodes, v < L.NN := fun v hv => ((hs.ok_iff v).mpr hv).1
  refine ⟨⟨fun v => (hok v).trans (hs.ok_iff v), fun u hu => by rw [hlo, hhi]; exact hs.arcs u hu,
    fun k hk => ⟨(h3 k hk).2.2, by rw [(h3 k hk).2.1]; exact (hs.heads k hk).2.1,
      by rw [(h3 k hk).1]; exact (hs.heads k hk).2.2⟩,
    fun k hk k' hk' he => by
      rw [(h3 k hk).2.1, (h3 k' hk').2.1] at he
      rw [(h3 k hk).1, (h3 k' hk').1]; exact hs.classes k hk k' hk' he,
    by simp only [hdeg]; exact hs.budget, hs.lay, hs.fits, hs.rs_lt, hs.os_lt, hs.INF_pos⟩,
    ⟨PQRep.congr hr.pq fun x hx1 hx2 => h1 x (by omega) hx2, fun v => ?_, fun v => ?_, hr.Q,
      fun c e he k hk hc => ?_⟩, fun c hc hq => ?_, fun v hvn => ?_, hdeg, fun g s hp => ?_⟩
  · rw [hr.tent v]
    split_ifs with hvn
    · have := hv v hvn
      unfold DL.tentOf
      rw [h1 _ (by omega) (by unfold pqSize; omega), h1 _ (by omega) (by unfold pqSize; omega)]
    · rfl
  · rw [hr.sett v]
    constructor
    · rintro ⟨hvn, he⟩
      have := hv v hvn
      exact ⟨hvn, by rw [h1 _ (by omega) (by unfold pqSize; omega)]; exact he⟩
    · rintro ⟨hvn, he⟩
      have := hv v hvn
      exact ⟨hvn, by rw [← h1 _ (by omega) (by unfold pqSize; omega)]; exact he⟩
  · rw [(h3 k hk).1]
    exact hr.mono c e he k hk (by rw [← (h3 k hk).2.1]; exact hc)
  · rw [h1 _ (by unfold pqT; omega) (by unfold pqT pqSize; omega)]
    exact hz c hc hq
  · rw [h1 _ (by omega) (by unfold pqSize; omega), h1 _ (by omega) (by unfold pqSize; omega)]
    exact hS v hvn
  · exact DL.parInv_frame hs hr hp fun v hvn =>
      ⟨h1 _ (by omega) (by unfold pqSize; omega), h1 _ (by omega) (by unfold pqSize; omega)⟩

namespace SC

variable {C : SC} {w : ℕ} {a : SG} {mem : ℕ → ℕ}

/-- The least key, capped at `INF`. -/
def kq (C : SC) (mem : ℕ → ℕ) : ℕ := min (mem (C.L.D + 4) / C.L.J) C.L.INF

/-- `K = min(k, INF)` bounds the queue. -/
theorem Inv.kmin (hI : C.Inv w a mem) :
    C.kq mem ≤ C.L.INF ∧ a.d.L ≤ C.kq mem ∧ ∀ e ∈ a.d.Q, C.kq mem ≤ e.1 := by
  have hroot := hI.rep.pq.root_spec
  rw [show C.L.D + 3 + 1 = C.L.D + 4 from rfl] at hroot
  have hQ := hI.rep.Q
  refine ⟨min_le_right _ _, ?_, fun e he => ?_⟩
  · by_cases hlt : mem (C.L.D + 4) / C.L.J < C.L.INF
    · obtain ⟨e, rest, he, he1, hc, -⟩ := hroot.1 hlt
      have hmem : e ∈ a.d.Q := by
        rw [hQ]; exact mem_pqAll.mpr ⟨_, hc, by rw [he]; exact List.mem_cons_self⟩
      have := (hI.inv.keys e hmem).1
      unfold kq; omega
    · unfold kq; have := hI.inv.L_lt; omega
  · by_cases hlt : mem (C.L.D + 4) / C.L.J < C.L.INF
    · obtain ⟨e0, rest, -, he01, -, hmin⟩ := hroot.1 hlt
      have := hmin e (by rw [← hQ]; exact he)
      unfold kq; omega
    · have hall := hroot.2 (by omega)
      rw [hQ] at he
      obtain ⟨c, -, hec⟩ := mem_pqAll.mp he
      rw [hall c] at hec
      exact absurd hec List.not_mem_nil

theorem Inv.okN_iff (h : C.Ok w) (hI : C.Inv w a mem) (v : ℕ) : C.okN v ↔ v ∈ C.X.G.Nodes := by
  rw [← hI.shape.ok_iff v, hI.g h]
  exact (h.Fok v).symm

open Classical in
/-- **The petal is the settled part.** -/
theorem Inv.carve (h : C.Ok w) (hI : C.Inv w a mem) {r : ℕ} (hr : r < C.kq mem)
    (hdr : a.d.L ≤ r) (hrR : r ≤ C.Rm) :
    C.c.carve C.G C.Y (C.pd.withR r) = C.Y.filter (fun x => a.d.sett (C.sv x)) := by
  obtain ⟨hK, hLK, hQ⟩ := hI.kmin
  have hinv := hI.invF h
  rw [← h.hsv] at hinv
  exact h.link.carve_eq hinv (hI.doneF h) hK hLK hQ rfl rfl hr hdr hrR

open Classical in
/-- The entries and the settled list match the petal. -/
theorem Inv.elink (h : C.Ok w) (hI : C.Inv w a mem) {r : ℕ} (hr : r < C.kq mem)
    (hdr : a.d.L ≤ r) (hrR : r ≤ C.Rm) :
    C.c.ELink C.G C.P C.Y (C.c.carve C.G C.Y (C.pd.withR r)) (C.pd.withR r) C.sv C.nA C.pr
      C.ea C.eb C.okN C.δF a.ℓ := by
  have hcv := hI.carve h hr hdr hrR
  have hin : ∀ x, x ∈ C.c.carve C.G C.Y (C.pd.withR r) ↔ x ∈ C.Y ∧ a.d.sett (C.sv x) := by
    intro x; rw [hcv, Finset.mem_filter]
  obtain ⟨hK, hLK, hQ⟩ := hI.kmin
  have hinv := hI.invF h
  rw [← h.hsv] at hinv
  refine ⟨h.img, h.inj, h.hea, h.heb, h.okY, fun j hj => ⟨?_, ?_⟩, ?_, fun x hx => ?_⟩
  · rw [hin, ← hI.sett, ← h.hea j hj]
    constructor
    · intro hs
      exact ⟨(h.okY j hj).1.mp ((hI.okN_iff h _).mpr ((hI.rep.sett _).mp hs).1), hs⟩
    · rintro ⟨-, hs⟩; exact hs
  · rw [hin, ← hI.sett, ← h.heb j hj]
    constructor
    · intro hs
      exact ⟨(h.okY j hj).2.mp ((hI.okN_iff h _).mpr ((hI.rep.sett _).mp hs).1), hs⟩
    · rintro ⟨-, hs⟩; exact hs
  · rw [hcv]; exact Finset.filter_subset _ _
  · obtain ⟨hxY, hxs⟩ := (hin x).mp hx
    have hle : a.d.tent (C.sv x) ≤ C.Rm := (hI.inv.settled_le _ hxs).trans (hdr.trans hrR)
    rw [h.link.ent_eq hinv (hI.doneF h) hK hLK hQ (pd := C.pd.withR r) rfl rfl hxY hxs hle,
      hI.tent h hxs]

theorem Inv.tb_iff (hI : C.Inv w a mem) : (C.Xf a).TB mem ↔
    a.q < C.X.Lb + 1 ∧ C.X.lo + (a.q - 1) * C.X.bw < mem (C.L.D + 4) / C.L.J ∧
      a.d.L < mem (C.L.D + 4) / C.L.J := by
  show mem C.X.CTL < C.X.Lb + 1 ∧ C.X.lo + (mem C.X.CTL - 1) * C.X.bw < mem (C.L.D + 4) / C.L.J ∧
    mem (C.X.CTL + 3) < mem (C.L.D + 4) / C.L.J ↔ _
  rw [hI.qc, hI.lastL]

theorem Inv.bq_eq (hI : C.Inv w a mem) : (C.Xf a).bq mem = C.X.lo + a.q * C.X.bw := by
  show C.X.lo + mem C.X.CTL * C.X.bw = _; rw [hI.qc]

theorem k_eq : (C.Xf a).k mem = mem (C.L.D + 4) / C.L.J := rfl

/-- Where the tested radius lies. -/
theorem Inv.rr_facts (h : C.Ok w) (hI : C.Inv w a mem) (hT : (C.Xf a).TB mem) :
    (C.Xf a).rr mem < C.kq mem ∧ a.d.L ≤ (C.Xf a).rr mem ∧ (C.Xf a).rr mem ≤ C.Rm ∧
      1 ≤ a.q ∧ a.q ≤ C.X.Lb ∧ C.X.lo + (a.q - 1) * C.X.bw ≤ (C.Xf a).rr mem ∧
      (C.Xf a).rr mem ≤ C.X.lo + a.q * C.X.bw := by
  obtain ⟨t1, t2, t3⟩ := hI.tb_iff.mp hT
  have hqL : a.q ≤ C.X.Lb := by omega
  have hqd := hI.qd hqL
  have hq1 := hI.q1
  have hm1 : a.q * C.X.bw ≤ (C.X.Lb + 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
  have hm2 : (a.q - 1) * C.X.bw ≤ a.q * C.X.bw := Nat.mul_le_mul_right _ (by omega)
  have hRm := h.hRm
  have hINF := h.hINF
  unfold kq
  by_cases hb : (C.Xf a).bq mem < (C.Xf a).k mem
  · rw [PSG.rr_of_lt _ _ hb, hI.bq_eq]
    rw [hI.bq_eq, k_eq] at hb
    exact ⟨by omega, by omega, by omega, hq1, hqL, by omega, le_rfl⟩
  · rw [PSG.rr_of_ge _ _ hb, k_eq]
    rw [hI.bq_eq, k_eq] at hb
    exact ⟨by omega, by omega, by omega, hq1, hqL, by omega, by omega⟩

/-- **The test of `ptest`** is the pair of tests of region growing at the tested radius. -/
theorem Inv.pass (h : C.Ok w) (hI : C.Inv w a mem) (hT : (C.Xf a).TB mem) :
    ((C.Xf a).pt mem).Pass mem ↔
      (C.c.cost C.G C.P C.Y (C.pd.withR ((C.Xf a).rr mem)) * C.c.sq C.G C.P a.q ≤
        8 * C.c.vol C.G C.P C.Y (C.pd.withR ((C.Xf a).rr mem)) ∧
      C.c.vol C.G C.P C.Y (C.pd.withR ((C.Xf a).rr mem)) ≤ C.c.T C.G C.P a.q) := by
  obtain ⟨hr1, hr2, hr3, hq1, hqL, -, -⟩ := hI.rr_facts h hT
  refine Cl.pass_iff h.hcw C.wtP h.hwM (by have := h.hM; omega) (hI.elink h hr1 hr2 hr3) _ mem
    rfl rfl h.hκ ?_ ?_ h.hnact hI.sums
  · show mem (C.X.SQ + mem C.X.CTL) = _
    rw [hI.qc, hI.fix _ (h.fSQ _ (by omega)).1]; exact h.hsq _ hq1 hqL
  · show mem (C.X.P2 + mem C.X.CTL) = _
    rw [hI.qc, hI.fix _ (h.fSQ _ (by omega)).2]; exact h.hP2 _ hq1 hqL

theorem Inv.lay (hI : C.Inv w a mem) :
    C.L.LO + C.L.NN ≤ C.L.TS ∧ C.L.HI + C.L.NN ≤ C.L.TS ∧ C.L.HD + C.L.MM ≤ C.L.TS ∧
      C.L.CS + C.L.MM ≤ C.L.TS ∧ C.L.CL + C.L.MM ≤ C.L.TS ∧ C.L.OK + C.L.NN ≤ C.L.TS ∧
      C.L.TS + 5 * C.L.NN ≤ C.L.D := hI.shape.lay

/-- **A write above Dijkstra.** -/
theorem Inv.frame_hi (h : C.Ok w) (hI : C.Inv w a mem) {mem' : ℕ → ℕ}
    (hm : ∀ x < C.X.G.R + 2, mem' x = mem x) :
    C.L.Shape w mem' C.X.G.Nodes ∧ C.L.Rep mem' C.X.G.Nodes a.d a.qs ∧ C.L.TZ mem' a.qs ∧
      C.L.Stamps mem' ∧ C.L.g mem' = C.L.g mem ∧
      (∀ c < C.L.J, mem' (pqT C.L.D C.L.J c) ≤ C.L.setSum mem' C.X.G.Nodes a.d.sett + 1) ∧
      (C.L.g mem').ParInv C.X.G.s C.L.INF a.d (C.L.par mem') (C.L.parc mem') := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hI.lay
  have hR := h.hR
  unfold pqSize at hR
  have hfa := DL.frameAll hI.shape hI.rep hI.tz hI.stamps
    (fun x _ hx => hm x (by unfold pqSize at hx; omega))
    (fun v hv => ⟨hm _ (by omega), hm _ (by omega), hm _ (by omega)⟩)
    (fun k hk => ⟨hm _ (by omega), hm _ (by omega),
      (hm (C.L.HD + k) (by omega)).symm ▸ (hI.shape.heads k hk).1⟩)
  have hg : C.L.g mem' = C.L.g mem := DL.g_congr C.L hI.shape fun x hx => hm x (by omega)
  refine ⟨hfa.1, hfa.2.1, hfa.2.2.1, hfa.2.2.2.1, hg, fun c hc => ?_, ?_⟩
  · rw [hm _ (by unfold pqT; omega), setSum_eq_of_deg hfa.2.2.2.2.1]
    exact hI.cap c hc
  · rw [hg]; exact hfa.2.2.2.2.2 _ _ hI.par

/-- The slot cells lie below `TS`. -/
theorem Inv.slot_lt_TS (h : C.Ok w) (hI : C.Inv w a mem) {i : ℕ} (hi : i < C.H.length) :
    C.L.HD + C.slot (C.hv i) < C.L.TS := by
  have := (hI.lay).2.2.1; have := h.slot_lt hi; omega

theorem Ok.TS_lt (h : C.Ok w) (hI : C.Inv w a mem) : C.L.TS < C.X.G.R := by
  have := (hI.lay).2.2.2.2.2.2; have := h.hR; unfold pqSize at this; omega

/-- **A test that fails at the end of its bucket** moves the bucket pointer. -/
theorem Inv.adv (h : C.Ok w) (hI : C.Inv w a mem) (hT : (C.Xf a).TB mem)
    (hP : ¬ ((C.Xf a).pt mem).Pass mem) (hb : (C.Xf a).bq mem < (C.Xf a).k mem) {mem' : ℕ → ℕ}
    (hm : mem' = Function.update mem (C.Xf a).CTL ((C.Xf a).qp mem + 1)) :
    C.Inv w { a with q := a.q + 1 } mem' ∧
      C.μ { a with q := a.q + 1 } + pstepCost (C.Xf a).args mem + 50 ≤ C.μ a := by
  have hm' : mem' = Function.update mem C.X.CTL (a.q + 1) := by rw [hm, ← hI.qc]; rfl
  have hCTL := h.hCTL
  have hSUM := h.hSUM
  have hSL := h.hSL
  have hTS := h.TS_lt hI
  have hne : ∀ x, x ≠ C.X.CTL → mem' x = mem x := fun x hx => by
    rw [hm']; exact Function.update_of_ne hx _ _
  obtain ⟨hs', hr', hz', hS', hg, hcap', hp'⟩ := hI.frame_hi h fun x hx => hne x (by omega)
  obtain ⟨hr1, hr2, hr3, hq1, hqL, -, -⟩ := hI.rr_facts h hT
  have hbw := h.hbw
  have hINF := h.hINF
  have hRm := h.hRm
  have hbq := hI.bq_eq
  have hrr : (C.Xf a).rr mem = C.X.lo + a.q * C.X.bw := by rw [PSG.rr_of_lt _ _ hb, hbq]
  have hm1 : a.q * C.X.bw ≤ (C.X.Lb + 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
  -- the bucket `q` fails for every radius
  have hbK : C.X.lo + a.q * C.X.bw < C.kq mem := by
    have : C.X.lo + a.q * C.X.bw < mem (C.L.D + 4) / C.L.J := by
      rw [← hbq]; exact hb
    unfold kq; omega
  have hall : ∀ x, C.BF a.q x := by
    have hK : C.BF a.q (C.kq mem) := by
      refine Cl.BFail.step2 h.hGo h.link.conn h.link.hY (hI.bnow a.q le_rfl hqL) ?_ ?_
      · intro r h1 h2 h3
        rw [← hbw] at h3 ⊢
        rw [hI.carve h h2 h1 (by omega), hI.carve h (by omega) (by omega) (by omega)]
      · intro _ _
        rw [← hbw, show min (C.kq mem - 1) (C.X.lo + a.q * C.X.bw) = C.X.lo + a.q * C.X.bw by
          omega, ← hrr]
        exact fun ht => hP ((hI.pass h hT).mpr ht)
    exact Cl.BFail.all hK (by rw [← hbw]; exact hbK)
  have hcost : pstepCost (C.Xf a).args mem = 400 := (C.Xf a).cost_tb mem ⟨hT, hb⟩
  have i1 : a.d.sett a.cur → (C.L.g mem').hi a.cur ≤ a.pos := by rw [hg]; exact hI.done
  have i2 : ∀ x, C.Fix x → mem' x = C.mem0 x := fun x hx => by
    rw [hne x (by have := hx.2.1; omega)]; exact hI.fix x hx
  have i3 : ∀ i < C.H.length, mem' (C.L.HD + C.slot (C.hv i)) =
      if i ≤ a.j then C.nx i else C.X.S := fun i hi => by
    rw [hne _ (by have := hI.slot_lt_TS h hi; omega)]; exact hI.slots i hi
  have i4 : ∀ i < a.ℓ.length, mem' (C.X.SL + i) = a.ℓ.getD i 0 := fun i hi => by
    rw [hne _ (by omega)]; exact hI.sl i hi
  have i5 : ∀ t : Fin 5, mem' (C.X.SUM + t) = C.es a.ℓ t := fun t => by
    rw [hne _ (by omega)]; exact hI.sums t
  have i6 : a.q + 1 ≤ C.X.Lb → a.d.L ≤ C.X.lo + (a.q + 1) * C.X.bw := fun hq => by
    have := hI.qd (by omega)
    have : a.q * C.X.bw ≤ (a.q + 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
    omega
  have i7 : ∀ q, 1 ≤ q → q < a.q + 1 → ∀ x, C.BF q x := fun q h1 h2 => by
    by_cases hq : q < a.q
    · exact hI.bdone q h1 hq
    · rw [show q = a.q by omega]; exact hall
  refine ⟨⟨hs', hr', by rw [hg]; exact hI.inv, i1, hcap', hp', hz', hS', i2, hI.jle,
    by rw [hne _ (by omega)]; exact hI.ptr, i3, hI.hsett, by rw [hne _ (by omega)]; exact hI.ns,
    i4, hI.nd, hI.sett, by rw [hne _ (by omega)]; exact hI.lastL, i5,
    by rw [hm']; exact Function.update_self _ _ _, show 1 ≤ a.q + 1 by omega,
    show a.q + 1 ≤ C.X.Lb + 1 by omega, i6, i7,
    fun q h1 h2 => hI.bnow q (by have h1' : a.q + 1 ≤ q := h1; omega) h2,
    fun x hx => by have := h.hSUM; have := h.hSL; rw [hne x (by omega)]; exact hI.top x hx⟩, ?_⟩
  have e1 : C.μ { a with q := a.q + 1 } = 4 * C.L.pot C.mem0 C.X.G.Nodes a.d a.qs +
      500 * (C.X.Lb + 1 - (a.q + 1)) + 2 * stCost C.L.J + 2000 := rfl
  have e0 : C.μ a = 4 * C.L.pot C.mem0 C.X.G.Nodes a.d a.qs +
      500 * (C.X.Lb + 1 - a.q) + 2 * stCost C.L.J + 2000 := rfl
  rw [e1, e0, hcost]
  generalize C.L.pot C.mem0 C.X.G.Nodes a.d a.qs = P0
  generalize stCost C.L.J = S0
  omega

theorem drop_arith (P1 P0 D0 S0 x : ℕ) (h1 : P1 + D0 ≤ P0) (h2 : S0 ≤ D0) (h3 : 500 ≤ S0) :
    4 * P1 + x + 2 * S0 + 2000 + (2 * D0 + 600) + 50 ≤ 4 * P0 + x + 2 * S0 + 2000 := by
  linarith

/-- **A step of Dijkstra that drops an entry.** -/
theorem Inv.drop (h : C.Ok w) (hI : C.Inv w a mem) {mem1 : ℕ → ℕ}
    (hp : stepPost w (C.Xf a).G (C.L.argsR C.X.G.R) mem 1 mem1)
    (hT : (C.Xf a).TB mem → ¬ ((C.Xf a).pt mem).Pass mem ∧ (C.Xf a).k mem ≤ (C.Xf a).bq mem) :
    ∃ a', C.Inv w a' mem1 ∧ C.μ a' + pstepCost (C.Xf a).args mem + 50 ≤ C.μ a ∧
      C.L.pot C.mem0 C.X.G.Nodes a'.d a'.qs ≤ C.L.pot C.mem0 C.X.G.Nodes a.d a.qs := by
  rcases hp with ⟨h0, -⟩ | ⟨-, qs', hs', hr', hinv', hcap', hpot, hk', hp', hz', hS'⟩ | ⟨h2, -⟩
  · omega
  swap
  · omega
  have hg : C.L.g mem1 = C.L.g mem := DL.g_congr C.L hI.shape fun x hx => hk' x (Or.inl hx)
  have hk : ∀ x, C.X.G.R + 2 ≤ x → mem1 x = mem x := fun x hx => hk' x (keepS_of_ge h hx)
  have hCTL := h.hCTL
  have hSUM := h.hSUM
  have hSL := h.hSL
  have hcost : pstepCost (C.Xf a).args mem = 2 * dijCost (C.L.argsR C.X.G.R) mem + 600 :=
    (C.Xf a).cost_dij mem fun hh => by
      have := hT hh.1
      rcases hh.2 with h' | h'
      · omega
      · exact this.1 h'
  have hst := stCost_le_dijCost (L := C.L) (R := C.X.G.R) (mem := mem)
  have hst5 : 500 ≤ stCost C.L.J := by unfold stCost; omega
  have i1 : ∀ c < C.L.J, mem1 (pqT C.L.D C.L.J c) ≤ C.L.setSum mem1 C.X.G.Nodes a.d.sett + 1 :=
    fun c hc => by rw [setSum_eq_of_deg (DL.deg_eq_of_g hg)]; exact hcap' c hc
  have i2 : ∀ x, C.Fix x → mem1 x = C.mem0 x := fun x hx => by rw [hk' x hx.1]; exact hI.fix x hx
  have i3 : ∀ i < C.H.length, mem1 (C.L.HD + C.slot (C.hv i)) =
      if i ≤ a.j then C.nx i else C.X.S := fun i hi => by
    rw [hk' _ (Or.inl (hI.slot_lt_TS h hi))]; exact hI.slots i hi
  have i4 : ∀ i < a.ℓ.length, mem1 (C.X.SL + i) = a.ℓ.getD i 0 := fun i hi => by
    rw [hk _ (by omega)]; exact hI.sl i hi
  have i5 : ∀ t : Fin 5, mem1 (C.X.SUM + t) = C.es a.ℓ t := fun t => by
    rw [hk _ (by omega)]; exact hI.sums t
  have hpot' : C.L.pot C.mem0 C.X.G.Nodes { a.d with Q := pqAll C.L.J qs' } qs' +
      dijCost (C.L.argsR C.X.G.R) mem ≤ C.L.pot C.mem0 C.X.G.Nodes a.d a.qs := by
    rw [← pot_eq_of_deg (hI.deg h), ← pot_eq_of_deg (hI.deg h)]; exact hpot
  refine ⟨{ a with d := { a.d with Q := pqAll C.L.J qs' }, qs := qs' }, ⟨hs', hr',
    by rw [hg]; exact hinv', by rw [hg]; exact hI.done, i1, by rw [hg]; exact hp', hz', hS', i2,
    hI.jle, by rw [hk _ (by omega)]; exact hI.ptr, i3, hI.hsett,
    by rw [hk _ (by omega)]; exact hI.ns, i4, hI.nd, hI.sett,
    by rw [hk _ (by omega)]; exact hI.lastL, i5, by rw [hk _ (by omega)]; exact hI.qc,
    hI.q1, hI.qL, hI.qd, hI.bdone, hI.bnow, fun x hx => by
      rw [hk _ (by omega)]; exact hI.top x hx⟩, ?_, le_trans (Nat.le_add_right _ _) hpot'⟩
  have e1 : C.μ { a with d := { a.d with Q := pqAll C.L.J qs' }, qs := qs' } =
      4 * C.L.pot C.mem0 C.X.G.Nodes { a.d with Q := pqAll C.L.J qs' } qs' +
      500 * (C.X.Lb + 1 - a.q) + 2 * stCost C.L.J + 2000 := rfl
  have e0 : C.μ a = 4 * C.L.pot C.mem0 C.X.G.Nodes a.d a.qs +
      500 * (C.X.Lb + 1 - a.q) + 2 * stCost C.L.J + 2000 := rfl
  rw [e1, e0, hcost]
  exact drop_arith _ _ _ _ _ hpot' hst hst5

end SC

end MinCostFlow.LowStretch
