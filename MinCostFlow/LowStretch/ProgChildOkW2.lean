module

public import MinCostFlow.LowStretch.ProgChildOkW
public import MinCostFlow.LowStretch.ProgChildRec

/-!
# The record of a raw child, without the invariant

The record that the child step builds for a raw child `c.raw G D k` (its `θ`-nodes, and the
active pairs of `c` inside it with the flags of the child) meets `Rec.OkW` (`Rec.ok_rawW`). The
proof is that of `Rec.ok_raw` without the invariant. A pair inside the child between two
super-vertices that is not stored is not active in `c`, so it weighs more than four times the
radius of `c` (`Rec.Ok.heavy4`), and the radius of the child is at most that of `c`
(`Cl.raw_Δ`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open KT

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {D : Cl.Dec}

namespace Rec

/-- **The record of a raw child, without the invariant.** -/
theorem ok_rawW (h : R.Ok T G P c) (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D) {k : ℕ}
    (hk : k < D.nch) {R' : Rec} (hnd : R'.nodes.Nodup)
    (hnodes : ∀ j, j ∈ R'.nodes ↔ ∃ a ∈ (c.raw G D k).X, T.top c.θ a = j)
    (hSnd : (R'.S.map Prod.fst).Nodup)
    (hS : ∀ e ∈ R'.S, e.2 = if e.1 ∈ (c.raw G D k).half then 1 else 0)
    (hSm : ∀ p, p ∈ R'.S.map Prod.fst ↔
      p ∈ c.act G P ∧ G.pu p ∈ (c.raw G D k).X ∧ G.pv p ∈ (c.raw G D k).X) :
    R'.OkW T G (c.raw G D k) := by
  have hθ : (c.raw G D k).θ = c.θ := Cl.raw_θ k
  have hsub := Cl.raw_X_subset (G := G) (c := c) (D := D) k
  have hsat := Cl.sat_raw (D := D) h k
  refine ⟨Cl.raw_good h.inv.good hD (h.inv.Δ_pos h.hB hX) h.hGo hk, by rw [hθ]; exact h.inv.one_le,
    h.tree, h.hG, h.hGo, hnd, fun j hj => ?_, fun j hj v hv hu => ?_, fun v => ?_,
    fun e he => ?_, hSnd, fun p hm hu hv hnl hp => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (hnodes j).mp hj
    exact top_lt_N h.tree (h.n_of_mem (hsub ha)) h.inv.one_le
  · obtain ⟨a, ha, rfl⟩ := (hnodes j).mp hj
    have han := h.n_of_mem (hsub ha)
    rw [hθ]
    exact ((IsTop.of_common h.tree (by have := h.tree.n_lt; omega)
      (isTop_top h.tree han h.inv.one_le) (isTop_top h.tree han h.inv.one_le).1 hu
      (isTop_top h.tree han h.inv.one_le).2.1).eq_top h.tree hv h.inv.one_le).symm
  · rw [hθ]
    constructor
    · intro hv
      exact ⟨h.n_of_mem (hsub hv), (hnodes _).mpr ⟨v, hv, rfl⟩⟩
    · rintro ⟨hv, hm⟩
      obtain ⟨a, ha, he⟩ := (hnodes _).mp hm
      exact hsat a ha v hv (by rw [he]; exact (isTop_top h.tree hv h.inv.one_le).1)
  · have hp : e.1 ∈ R'.S.map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨hpa, hu, hv⟩ := (hSm _).mp hp
    obtain ⟨hm, hu', hv', hnl, -⟩ := Cl.mem_act.mp hpa
    have hf := hS e he
    refine ⟨hm, hu, hv, ?_, by rw [hf]; split_ifs <;> omega, by rw [hf]; split_ifs <;> simp_all⟩
    rw [hθ]
    intro he'
    exact hnl ((Cl.lconn_iff h.tree h.hG h.sat h.sub h.inv.one_le hu' hv').mpr he')
  · have hnl' : ¬ c.LConn G (G.pu p) (G.pv p) := fun hl => hnl ((h.lconn_raw k hu hv).mpr hl)
    have hna : p ∉ c.act G P := fun hpa => hp ((hSm p).mpr ⟨hpa, hu, hv⟩)
    have h4 := h.heavy4 hm (hsub hu) (hsub hv) hnl' hna
    have h3 := Cl.raw_Δ h.inv.good hD h.hGo hk
    omega

end Rec

end MinCostFlow.LowStretch
