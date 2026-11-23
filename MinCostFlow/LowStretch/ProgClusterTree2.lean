module

public import MinCostFlow.LowStretch.ProgClusterTree

/-!
# The setting of a petal along the tree, and the cone of the parents

`PW.Btw.ps`: between two petals, a target `e` in an allowed node `v` whose path of parents stays
among allowed nodes gives the facts `PW.PS` of the search from `e`, with the steps `stp` of the
path.

`PW.Cone`: the parent of every allowed node other than the node of the center is allowed. A
petal keeps this (`PW.Cone.after`). If the parent `u` of an allowed node `v` is carved, the arc
from `u` back to `v` along the tree pair has shifted length `0`, hence cost `0`, so `v` is reached
at the cost of `u` and is carved too (`Cl.carve_closed`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

open Classical in
/-- A petal is closed under arcs of shifted length `0`. -/
theorem carve_closed {Y : Finset ℕ} {pd : PD} {p a b : ℕ} (hb : b ∈ c.carve G Y pd)
    (ha : a ∈ Y) (hj : G.Joins p b a)
    (hd : c.d G c.x0 a = c.d G c.x0 b + c.len G p) : a ∈ c.carve G Y pd := by
  unfold carve at hb ⊢
  rw [Finset.mem_filter] at hb ⊢
  obtain ⟨-, k, hk, hdr⟩ := hb
  have h0 : c.wbar G p b a = 0 := by unfold wbar; omega
  have harc := Arc.normal (c := c) (t := pd.tj) (hw := pd.hw) hj
  rw [h0, show rc c.θ 0 = 0 by simp [rc]] at harc
  exact ⟨ha, k, hk, by simpa using DR.step hdr harc (Finset.mem_coe.mpr ha)⟩

end Cl

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {rs : ℕ} {A : TA}

theorem stp_getD {v n k : ℕ} (hk : k < n) : (W.stp A mem v n).getD k (0, 0, 0) =
    (mem (A.PP + W.pe mem v k), mem (A.PA + W.pe mem v k), mem (A.PB + W.pe mem v k)) := by
  rw [List.getD_eq_getElem _ _ (by rw [stp_length]; exact hk), stp_getElem]

/-- **The setting of a petal along the tree.** -/
theorem Btw.ps (hB : W.Btw w mem rs) (hT : W.Tree A mem) {v n e : ℕ} (hp : W.Path mem v n)
    (he : e ∈ W.c.X) (hsv : W.sv e = v) (hal : ∀ i ≤ n, mem (W.L.OK + W.pe mem v i) = W.L.os)
    {hw : List ℕ} (hd : W.c.HwDec W.G e (W.stp A mem v n) hw) {lo : ℕ}
    (wb : lo + (W.Lb + 1) * W.bw + 2 < 2 ^ w)
    (wT1 : (8 * W.M * (W.κ + W.nA) + (lo + (W.Lb + 1) * W.bw + 1) * (W.nA * 2 ^ W.Es)) *
      (W.Sm + 1) < 2 ^ w)
    (hRm : lo + (W.Lb + 1) * W.bw ≤ W.Rm) (hINF : lo + (W.Lb + 1) * W.bw < W.L.INF) :
    W.PS w (W.on mem v) e (W.stp A mem v n) hw lo := by
  have h := hB.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hNN := h.hNN
  have hv : v < W.s := hsv ▸ h.sv_lt he
  have hc := h.slot_cell hv
  have hr := h.root_lt
  have hlt : ∀ i ≤ n, W.pe mem v i < W.s := fun i hi => hp.lt hr hi
  obtain ⟨-, -, -, -, hS, hon⟩ := hB.on_ok hv
  have hent := fun {i : ℕ} (hi : i ≤ n) => hT.ent (A := A) hp he hsv hi
  have hlen := stp_length (W := W) (A := A) (mem := mem) v n
  refine ⟨hd, fun i hi => ?_, ?_, fun k hk => ?_, fun k hk => ?_, ?_, fun k hk => ?_, ?_,
    fun u hu hne => ?_, wb, wT1, hRm, hINF⟩
  · rw [hlen] at hi
    rw [mem_Y, (hent hi).2, on_ne (by have := hlt i hi; omega)]
    exact ⟨(hent hi).1, hal i hi⟩
  · rw [hT.Hl_eq hp hsv]; exact hT.path_nodup hp
  · rw [hlen] at hk
    rw [stp_getD hk]
    exact (hT.edge _ (hp.2 k hk).2 (hp.2 k hk).1).2.2.2.2.2.2.2.1
  · rw [hlen] at hk
    rw [(hent hk.le).2, (hent (show k + 1 ≤ n by omega)).2, on_ne (by have := hlt k hk.le; omega),
      pe_succ']
  · rw [hlen, (hent le_rfl).2, hp.1, on_ne (by have := h.root_lt; omega)]
    exact hT.root
  · rw [hlen] at hk
    have hk' := hp.2 k hk
    rw [(hent hk.le).2, h.slotA_on hv (by omega), on_ne (by
      have := h.slot_lt hk'.2; omega), stp_getD hk]
    exact (hT.edge _ hk'.2 hk'.1).2.2.2.2.2.2.2.2.1
  · rw [hsv, hon, on_ne (by omega)]
  · rw [hsv] at hne; exact hS u hu hne

/-! ### The cone of the parents -/

/-- The parent of every allowed node, other than the node of the center, is allowed. -/
def Cone (W : PW) (mem : ℕ → ℕ) : Prop :=
  ∀ v < W.s, mem (W.L.OK + v) = W.L.os → v ≠ W.root → mem (W.L.OK + mem (W.NXT + v)) = W.L.os

/-- Along the path of an allowed node, every node is allowed. -/
theorem Cone.path (hc : W.Cone mem) {v n : ℕ} (hp : W.Path mem v n)
    (hv : mem (W.L.OK + v) = W.L.os) : ∀ i ≤ n, mem (W.L.OK + W.pe mem v i) = W.L.os := by
  intro i hi
  induction i with
  | zero => exact hv
  | succ i ih =>
    rw [pe_succ']
    exact hc _ (hp.2 i (by omega)).2 (ih (by omega)) (hp.2 i (by omega)).1

/-- **A petal keeps the cone.** The new marks are `os + 1` on the settled nodes `ℓ`, whose
vertices form the petal, and the old marks elsewhere. -/
theorem Cone.after (hT : W.Tree A mem) (hc : W.Cone mem) {mem' : ℕ → ℕ}
    {ℓ : List ℕ} {pd : PD}
    (hok : ∀ v < W.s, mem' (W.L.OK + v) = if v ∈ ℓ then W.L.os + 1 else mem (W.L.OK + v))
    (hcarve : W.c.carve W.G (W.Y mem) pd = (W.Y mem).filter (fun x => W.sv x ∈ ℓ))
    (hnxt : ∀ v < W.s, mem' (W.NXT + v) = mem (W.NXT + v)) : W.Cone mem' := by
  intro v hv hok' hr
  have hvl : v ∉ ℓ := fun hl => by rw [hok v hv, if_pos hl] at hok'; omega
  rw [hok v hv, if_neg hvl] at hok'
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, -⟩ := hT.edge v hv hr
  rw [hnxt v hv, hok _ e1]
  have hu := hc v hv hok' hr
  split_ifs with hul
  · exfalso
    have hB : mem (A.PB + v) ∈ W.c.carve W.G (W.Y mem) pd := by
      rw [hcarve, Finset.mem_filter, mem_Y, e5]
      exact ⟨⟨e4, hu⟩, hul⟩
    have hA := Cl.carve_closed hB (mem_Y.mpr ⟨e2, by rw [e3]; exact hok'⟩) e6.symm e7
    rw [hcarve, Finset.mem_filter, e3] at hA
    exact hvl hA.2
  · exact hu

end PW

end MinCostFlow.LowStretch
