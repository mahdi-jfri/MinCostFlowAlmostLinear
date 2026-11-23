module

public import MinCostFlow.LowStretch.ProgClusterLoop

/-!
# The loop of the regular petals: facts that depend on few cells

The facts between petals, the cone, the potential, the remaining set, the paths of parents and
the outputs of the earlier petals depend only on a few cells. The writes of the loop after a
petal (the copy of the settled list and the outputs of the petal) do not touch them.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {mem mem' : ℕ → ℕ} {rs : ℕ} {A : TA}

/-- The facts between petals depend only on the cells below the settled list. -/
theorem Btw.congr_low (hB : W.Btw w mem rs) (hm : ∀ x < W.SL, mem' x = mem x) :
    W.Btw w mem' rs := by
  have h := hB.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hR := h.hR; have hCTL := h.hCTL; have hSUM := h.hSUM; have hSL := h.hSL
  have hfits := h.fits
  unfold pqSize at hR
  have hsl : ∀ u < W.s, W.slotA mem' u = W.slotA mem u := fun u hu => by
    unfold slotA; rw [hm _ (by have := h.hNN; omega)]
  refine ⟨h.congr (fun x _ _ hx => hm x (by omega)) (fun u hu k k1 k2 => hm _ (by
      have := h.hiMM u (by have := h.hNN; omega); omega)) (fun k hk => by
      rw [hm _ (by omega)]; exact h.hdNN k hk),
    DL.PQRep.congr hB.pq fun x _ hx => hm x (by unfold pqSize at hx; omega),
    fun c hc => by rw [hm _ (by unfold pqT; omega)]; exact hB.tz c hc,
    fun v hv => by rw [hm _ (by omega), hm _ (by omega)]; exact hB.st v hv,
    fun u hu => by
      rw [hsl u hu, hm _ (by have := h.slot_lt hu; omega)]; exact hB.sl u hu⟩

/-- The cone depends only on the marks and on `NXT`. -/
theorem Cone.congr (h : W.Ok w mem) (hc : W.Cone mem) (hm : ∀ x < W.L.TS, mem' x = mem x) :
    W.Cone mem' := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN
  intro v hv hok hr
  rw [hm _ (by omega)] at hok
  have := h.nxt v (by omega)
  rw [hm (W.NXT + v) (by omega), hm _ (by omega)]
  exact hc v hv hok hr

theorem Nodes_congr (h : W.Ok w mem) (hm : ∀ x < W.L.TS, mem' x = mem x) :
    W.Nodes mem' = W.Nodes mem := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES
  unfold Nodes
  exact Finset.filter_congr fun v hv => by
    rw [Finset.mem_range] at hv; rw [hm _ (by omega)]

theorem Φ_congr (h : W.Ok w mem) (hm : ∀ x < W.L.TS, mem' x = mem x) : W.Φ mem' = W.Φ mem := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES
  unfold Φ
  rw [Nodes_congr h hm]
  exact Finset.sum_congr rfl fun u _ => by
    rw [deg_congr (mem := mem) fun v hv => ⟨hm _ (by omega), hm _ (by omega)⟩]

theorem Y_congr (h : W.Ok w mem) (hm : ∀ x < W.L.TS, mem' x = mem x) : W.Y mem' = W.Y mem := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN
  unfold Y
  exact Finset.filter_congr fun a ha => by rw [hm _ (by have := h.sv_lt ha; omega)]

theorem pe_lt (h : W.Ok w mem) {v : ℕ} (hv : v < W.L.NN) : ∀ i, W.pe mem v i < W.L.NN := by
  intro i
  induction i with
  | zero => exact hv
  | succ i ih => rw [pe_succ']; exact h.nxt _ ih

/-- The path of parents depends only on `NXT`. -/
theorem pe_congr (h : W.Ok w mem) (hm : ∀ v < W.L.NN, mem' (W.NXT + v) = mem (W.NXT + v))
    {v : ℕ} (hv : v < W.L.NN) : ∀ i, W.pe mem' v i = W.pe mem v i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => rw [pe_succ', pe_succ', ih, hm _ (pe_lt h hv i)]

theorem Path_congr (h : W.Ok w mem) (hm : ∀ v < W.L.NN, mem' (W.NXT + v) = mem (W.NXT + v))
    {v n : ℕ} (hv : v < W.L.NN) : W.Path mem' v n ↔ W.Path mem v n := by
  unfold Path; simp only [pe_congr h hm hv]

theorem stp_congr (h : W.Ok w mem) (hm : ∀ v < W.L.NN, mem' (W.NXT + v) = mem (W.NXT + v))
    {v n : ℕ} (hv : v < W.L.NN)
    (hA : ∀ i < n, mem' (A.PP + W.pe mem v i) = mem (A.PP + W.pe mem v i) ∧
      mem' (A.PA + W.pe mem v i) = mem (A.PA + W.pe mem v i) ∧
      mem' (A.PB + W.pe mem v i) = mem (A.PB + W.pe mem v i)) :
    W.stp A mem' v n = W.stp A mem v n := by
  unfold stp
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [pe_congr h hm hv, (hA i hi').1, (hA i hi').2.1, (hA i hi').2.2]

end PW

end MinCostFlow.LowStretch
