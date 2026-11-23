module

public import MinCostFlow.LowStretch.ProgClusterPetalR

/-!
# From one petal to the next

Between two petals only the marks `OK` of the carved nodes and the heads of the slots change
(besides the scratch cells of the search). `PW.Ok.congr` shows that the fixed facts `PW.Ok` then
still hold. `PW.Btw` collects what holds between two petals: `PW.Ok`, empty queues, stamps below
the next stamp, and every slot off.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {rs : ℕ}

/-- **The fixed facts survive** a change of the marks of the nodes, of the slot heads, and of
cells outside the arrays that `PW.Ok` reads. -/
theorem Ok.congr (h : W.Ok w mem) {mem' : ℕ → ℕ}
    (hfr : ∀ x, (x < W.L.HD ∨ W.L.HD + W.L.MM ≤ x) → ¬ (W.L.OK ≤ x ∧ x < W.L.OK + W.s) →
      x < W.L.TS → mem' x = mem x)
    (hhd : ∀ u < W.s, ∀ k, mem (W.L.LO + u) ≤ k → k + 1 < mem (W.L.HI + u) →
      mem' (W.L.HD + k) = mem (W.L.HD + k))
    (hNN : ∀ k < W.L.MM, mem' (W.L.HD + k) < W.L.NN) : W.Ok w mem' := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hR := h.hR; have hCTL := h.hCTL; have hSUM := h.hSUM; have hSL := h.hSL
  have hNN' := h.hNN
  have eLO : ∀ v < W.L.NN, mem' (W.L.LO + v) = mem (W.L.LO + v) := fun v hv =>
    hfr _ (Or.inl (by omega)) (by omega) (by omega)
  have eHI : ∀ v < W.L.NN, mem' (W.L.HI + v) = mem (W.L.HI + v) := fun v hv =>
    hfr _ (Or.inl (by omega)) (by omega) (by omega)
  have eCS : ∀ k < W.L.MM, mem' (W.L.CS + k) = mem (W.L.CS + k) := fun k hk =>
    hfr _ (Or.inr (by omega)) (by omega) (by omega)
  have eCL : ∀ k < W.L.MM, mem' (W.L.CL + k) = mem (W.L.CL + k) := fun k hk =>
    hfr _ (Or.inr (by omega)) (by omega) (by omega)
  have eORD : ∀ k < W.L.MM, mem' (W.ORD + k) = mem (W.ORD + k) := fun k hk =>
    hfr _ (Or.inr (by omega)) (by omega) (by omega)
  have eNXT : ∀ v < W.L.NN, mem' (W.NXT + v) = mem (W.NXT + v) := fun v hv =>
    hfr _ (Or.inr (by omega)) (by omega) (by omega)
  have eAS : ∀ j < W.nA, mem' (W.AS + 2 * j) = mem (W.AS + 2 * j) := fun j hj =>
    hfr _ (Or.inr (by omega)) (by omega) (by omega)
  have eEXP : ∀ j < W.nA, mem' (W.EXP + mem' (W.AS + 2 * j)) = mem (W.EXP + mem (W.AS + 2 * j)) :=
    fun j hj => by
      have := h.lEXP j hj
      rw [eAS j hj]; exact hfr _ (Or.inr (by omega)) (by omega) (by omega)
  have eSQ : ∀ q ≤ W.Lb + 1, mem' (W.SQ + q) = mem (W.SQ + q) ∧ mem' (W.P2 + q) = mem (W.P2 + q) :=
    fun q hq => ⟨hfr _ (Or.inr (by omega)) (by omega) (by omega),
      hfr _ (Or.inr (by omega)) (by omega) (by omega)⟩
  have eSN : mem' (W.L.OK + W.s) = mem (W.L.OK + W.s) :=
    hfr _ (Or.inr (by omega)) (by omega) (by omega)
  -- the ranges of the arcs of a node
  have hrange : ∀ u < W.s, ∀ k, mem (W.L.LO + u) ≤ k → k < mem (W.L.HI + u) → k < W.L.MM :=
    fun u hu k _ h2 => by have := h.hiMM u (by omega); omega
  refine
    { hrec := h.hrec, conn := h.conn, hNN := h.hNN, sS := by rw [eSN]; exact h.sS,
      lohi := fun u hu => by rw [eLO u (by omega), eHI u (by omega)]; exact h.lohi u hu,
      chain := fun u hu => by rw [eLO _ (by omega), eHI u (by omega)]; exact h.chain u hu,
      hiMM := fun v hv => by rw [eHI v hv]; exact h.hiMM v hv,
      lay := h.lay, lEXP := fun j hj => by rw [eAS j hj]; exact h.lEXP j hj, lES := h.lES,
      hR := h.hR, hCTL := h.hCTL, hSUM := h.hSUM, hSL := h.hSL, wSL := h.wSL,
      heads := fun k hk => by rw [eCL k hk, eCS k hk]; exact h.heads k hk,
      classes := fun k hk k' hk' => by
        rw [eCL k hk, eCL k' hk', eCS k hk, eCS k' hk']; exact h.classes k hk k' hk',
      budget := by
        have : ∑ u ∈ Finset.range W.s, (mem' (W.L.HI + u) - mem' (W.L.LO + u) + 1) =
            ∑ u ∈ Finset.range W.s, (mem (W.L.HI + u) - mem (W.L.LO + u) + 1) :=
          Finset.sum_congr rfl fun u hu => by
            have := Finset.mem_range.mp hu
            rw [eHI u (by omega), eLO u (by omega)]
        rw [this]; exact h.budget,
      fits := h.fits, os_lt := h.os_lt, INF_pos := h.INF_pos,
      arcsN := fun u hu Q => by
        rw [← h.arcsN u hu Q, eLO u (by omega), eHI u (by omega)]
        constructor
        · rintro ⟨k, k1, k2, hq⟩
          refine ⟨k, k1, k2, ?_⟩
          rwa [hhd u hu k k1 k2, eCS k (hrange u hu k k1 (by omega))] at hq
        · rintro ⟨k, k1, k2, hq⟩
          refine ⟨k, k1, k2, ?_⟩
          rwa [hhd u hu k k1 k2, eCS k (hrange u hu k k1 (by omega))],
      hdNN := hNN,
      hdN := fun u hu k k1 k2 => by
        rw [eLO u (by omega)] at k1; rw [eHI u (by omega)] at k2
        rw [hhd u hu k k1 k2]; exact h.hdN u hu k k1 k2,
      ordA := fun u hu k k1 k2 => by
        rw [eLO u (by omega)] at k1; rw [eHI u (by omega)] at k2
        rw [eORD k (hrange u hu k k1 (by omega))]; exact h.ordA u hu k k1 k2,
      hsum := fun u hu Fs => by
        rw [← h.hsum u hu Fs, eLO u (by omega), eHI u (by omega)]
        refine Finset.sum_congr rfl fun k hk => ?_
        obtain ⟨k1, k2⟩ := Finset.mem_Ico.mp hk
        rw [hhd u hu k k1 (by omega), eORD k (hrange u hu k k1 (by omega))],
      img := h.img, inj := h.inj,
      hwt := fun j hj => by rw [eEXP j hj]; exact h.hwt j hj,
      wE := fun j hj => by rw [eEXP j hj]; exact h.wE j hj,
      hwM := h.hwM, wU := h.wU, wR2 := h.wR2, wL := h.wL, wSm := h.wSm, wSQ := h.wSQ,
      wP2 := h.wP2, wNXT := h.wNXT,
      nxt := fun v hv => by rw [eNXT v hv]; exact h.nxt v hv,
      hSm := fun q hq => by rw [(eSQ q hq).1, (eSQ q hq).2]; exact h.hSm q hq,
      wT2 := h.wT2, hM := h.hM, hLb := h.hLb, hbw := h.hbw, hκ := h.hκ, hnact := h.hnact,
      hsq := fun q h1 h2 => by rw [(eSQ q (by omega)).1]; exact h.hsq q h1 h2,
      hP2 := fun q h1 h2 => by rw [(eSQ q (by omega)).2]; exact h.hP2 q h1 h2,
      hcw := h.hcw, hκ1 := h.hκ1, hL1 := h.hL1, hΔ := h.hΔ, hV := h.hV, hRm2 := h.hRm2 }

/-- A non-slot arc of a node is not the slot of any node. -/
theorem Ok.not_slot (h : W.Ok w mem) {u v k : ℕ} (hu : u < W.s) (hv : v < W.s)
    (k1 : mem (W.L.LO + u) ≤ k) (k2 : k + 1 < mem (W.L.HI + u)) : k ≠ W.slotA mem v := by
  intro hk
  have := h.own (le_of_lt hu) hv k1 (by omega) hk
  subst this
  unfold slotA at hk; omega

/-! ### Between two petals -/

/-- What holds between two petals, with the next stamp `rs`: the fixed facts, empty queues with
tails at `0`, stamps below `rs`, and every slot off. -/
structure Btw (w : ℕ) (mem : ℕ → ℕ) (rs : ℕ) : Prop where
  ok : W.Ok w mem
  pq : PQRep mem W.L.D W.L.J W.L.A W.L.INF (fun _ => [])
  tz : ∀ c < W.L.J, mem (pqT W.L.D W.L.J c) = 0
  st : ∀ v < W.L.NN, mem (W.L.TS + v) < rs ∧ mem (W.L.TS + 2 * W.L.NN + v) < rs
  sl : ∀ u < W.s, mem (W.L.HD + W.slotA mem u) = W.s

/-- The memory with the slot of `u` on. -/
def on (W : PW) (mem : ℕ → ℕ) (u : ℕ) : ℕ → ℕ :=
  Function.update mem (W.L.HD + W.slotA mem u) (mem (W.NXT + u))

/-- The cell of the slot of `u` lies among the heads. -/
theorem Ok.slot_cell (h : W.Ok w mem) {u : ℕ} (hu : u < W.s) :
    W.L.HD ≤ W.L.HD + W.slotA mem u ∧ W.L.HD + W.slotA mem u < W.L.HD + W.L.MM := by
  have := h.slot_lt hu; omega

theorem on_ne {u x : ℕ} (hx : x ≠ W.L.HD + W.slotA mem u) : W.on mem u x = mem x :=
  Function.update_of_ne hx _ _

theorem Ok.slotA_on (h : W.Ok w mem) {u v : ℕ} (hu : u < W.s) (hv : v < W.L.NN) :
    W.slotA (W.on mem u) v = W.slotA mem v := by
  obtain ⟨l1, l2, -⟩ := h.lay
  have := h.slot_cell hu
  unfold slotA; rw [on_ne (by omega)]

/-- **Turning on the slot of `u`** keeps the fixed facts, the queues and the stamps. -/
theorem Btw.on_ok (hB : W.Btw w mem rs) {u : ℕ} (hu : u < W.s) :
    W.Ok w (W.on mem u) ∧ PQRep (W.on mem u) W.L.D W.L.J W.L.A W.L.INF (fun _ => []) ∧
      (∀ c < W.L.J, W.on mem u (pqT W.L.D W.L.J c) = 0) ∧
      (∀ v < W.L.NN, W.on mem u (W.L.TS + v) < rs ∧ W.on mem u (W.L.TS + 2 * W.L.NN + v) < rs) ∧
      (∀ v < W.s, v ≠ u → W.on mem u (W.L.HD + W.slotA (W.on mem u) v) = W.s) ∧
      W.on mem u (W.L.HD + W.slotA (W.on mem u) u) = mem (W.NXT + u) := by
  have h := hB.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hR := h.hR; have hNN := h.hNN; have hES := h.lES
  have hc := h.slot_cell hu
  have hfits := h.fits
  refine ⟨h.congr (fun x hx _ _ => on_ne (by omega)) (fun v hv k k1 k2 => on_ne fun e =>
      h.not_slot hv hu k1 k2 (by omega)) (fun k hk => ?_),
    DL.PQRep.congr hB.pq fun a ha _ => on_ne (by omega), fun c hc' => ?_, fun v hv => ?_,
    fun v hv hvu => ?_, ?_⟩
  · unfold on; rw [Function.update_apply]
    split_ifs
    · exact h.nxt u (by omega)
    · exact h.hdNN k hk
  · rw [on_ne (by unfold pqT; omega)]; exact hB.tz c hc'
  · rw [on_ne (by omega), on_ne (by omega)]; exact hB.st v hv
  · rw [h.slotA_on hu (by omega), on_ne fun e => hvu (h.slot_inj hv hu (by omega))]
    exact hB.sl v hv
  · rw [h.slotA_on hu (by omega)]; unfold on; exact Function.update_self _ _ _

theorem mem_iff_getD {l : List ℕ} {v : ℕ} : v ∈ l ↔ ∃ i < l.length, l.getD i 0 = v := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]⟩

variable {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ} {lo : ℕ}

open Classical in
set_option maxHeartbeats 1000000 in
/-- **After a petal**, the facts between petals hold again with the next stamp, and the marks of
the settled nodes are `os + 1`. -/
theorem Btw.after (hB : W.Btw w mem rs) (hus : W.sv t < W.s) (h1 : W.Ok w (W.on mem (W.sv t)))
    (hp : W.PS w (W.on mem (W.sv t)) t st hw lo) {a : SG} {memL memC mem' : ℕ → ℕ}
    (hI : (W.sc (W.on mem (W.sv t)) t st hw lo rs).Inv w a memL)
    (hclr : (W.sc (W.on mem (W.sv t)) t st hw lo rs).SClr memL memC) {m : ℕ}
    (hm : m < st.length) (hj : m + 1 = a.j)
    (q2 : ∀ i < a.ℓ.length, mem' (W.L.OK + a.ℓ.getD i 0) = W.L.os + 1 ∧
      mem' (W.L.HD + (W.on mem (W.sv t) (W.L.HI + a.ℓ.getD i 0) - 1)) = W.s)
    (q3 : mem' (W.L.HD + (W.on mem (W.sv t) (W.L.HI + (W.Hl t st).getD (m + 1) 0) - 1)) = W.s)
    (q4 : ∀ x, x ≠ W.CTL + 3 → (∀ i < a.ℓ.length, x ≠ W.L.OK + a.ℓ.getD i 0 ∧
      x ≠ W.L.HD + (W.on mem (W.sv t) (W.L.HI + a.ℓ.getD i 0) - 1)) →
      x ≠ W.L.HD + (W.on mem (W.sv t) (W.L.HI + (W.Hl t st).getD (m + 1) 0) - 1) →
      mem' x = memC x) :
    W.Btw w mem' (rs + 1) ∧
      (∀ v < W.s, mem' (W.L.OK + v) = if v ∈ a.ℓ then W.L.os + 1 else mem (W.L.OK + v)) ∧
      ∀ x, x < W.L.TS → (x < W.L.HD ∨ W.L.HD + W.L.MM ≤ x) →
        ¬ (W.L.OK ≤ x ∧ x < W.L.OK + W.s) → mem' x = mem x := by
  set mem1 := W.on mem (W.sv t) with hmem1
  have h := hB.ok
  have hC := h1.sc_ok (rs := rs) hp
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hR := h.hR; have hCTL := h.hCTL; have hNN := h.hNN; have hES := h.lES
  have hfits := h.fits
  have hlen : (W.Hl t st).length = st.length + 1 := Hl_length t st
  have hℓ : ∀ i < a.ℓ.length, a.ℓ.getD i 0 < W.s := fun i hi =>
    (h1.sett_lt hI (getD_mem' hi)).2
  have hH : ∀ i < (W.Hl t st).length, (W.Hl t st).getD i 0 < W.s := fun i hi =>
    h1.H_lt hp (getD_mem' hi)
  have hmH := hH (m + 1) (by omega)
  -- the slot cells of the nodes
  have hsl1 : ∀ v < W.s, W.slotA mem1 v < W.L.MM := fun v hv => h1.slot_lt hv
  have hsA : ∀ v, W.L.HD + (mem1 (W.L.HI + v) - 1) = W.L.HD + W.slotA mem1 v := fun v => rfl
  -- cells that the tail does not write
  have hq4 : ∀ x, x ≠ W.CTL + 3 → (∀ i < a.ℓ.length, x ≠ W.L.OK + a.ℓ.getD i 0) →
      (∀ v < W.s, x = W.L.HD + W.slotA mem1 v → v ∉ a.ℓ ∧ v ≠ (W.Hl t st).getD (m + 1) 0) →
      mem' x = memC x := fun x e1 e2 e3 => q4 x e1 (fun i hi => ⟨e2 i hi, fun e =>
        (e3 _ (hℓ i hi) (e.trans (hsA _))).1 (getD_mem' hi)⟩) fun e =>
          (e3 _ hmH (e.trans (hsA _))).2 rfl
  have hCL : ∀ x, x < W.L.D → memC x = memL x := fun x hx =>
    hclr.2.2 _ (h.not_pqOut (Or.inl hx))
  -- below the heads and between the heads and the stamps, outside the marks
  have hfrC : ∀ x, x < W.L.TS → (x < W.L.HD ∨ W.L.HD + W.L.MM ≤ x) →
      ¬ (W.L.OK ≤ x ∧ x < W.L.OK + W.s) → mem' x = mem1 x := fun x hx e1 e2 => by
    rw [hq4 x (by omega) (fun i hi => by have := hℓ i hi; omega)
      (fun v hv e => by have := hsl1 v hv; omega), hCL x (by omega)]
    exact hI.fix _ (h1.fix hp (by omega))
  have hHI : ∀ v < W.L.NN, mem' (W.L.HI + v) = mem (W.L.HI + v) := fun v hv => by
    rw [hfrC _ (by omega) (Or.inl (by omega)) (by omega), hmem1, on_ne (by
      have := h.slot_cell hus; omega)]
  have hsA' : ∀ v < W.L.NN, W.slotA mem' v = W.slotA mem1 v := fun v hv => by
    unfold slotA; rw [hHI v hv, hmem1, on_ne (by have := h.slot_cell hus; omega)]
  -- the heads that are not slots of the highway
  have hnotH : ∀ k < W.L.MM, (∀ i < (W.Hl t st).length, k ≠ W.slotA mem1 ((W.Hl t st).getD i 0)) →
      memL (W.L.HD + k) = mem1 (W.L.HD + k) := fun k hk hk' =>
    hI.fix _ (hC.fHD k hk hk')
  refine ⟨⟨h1.congr (fun x e1 e2 e3 => hfrC x e3 e1 e2) (fun v hv k k1 k2 => ?_) (fun k hk => ?_),
    DL.PQRep.congr hclr.1 fun x hx1 hx2 => hq4 x (by unfold pqSize at *; omega)
      (fun i hi => by have := hℓ i hi; omega) (fun v hv e => by have := hsl1 v hv; omega),
    fun c hc => ?_, fun v hv => ?_, fun v hv => ?_⟩, fun v hv => ?_, fun x e1 e2 e3 => ?_⟩
  · -- a non-slot arc
    have hns : ∀ u < W.s, k ≠ W.slotA mem1 u := fun u hu => h1.not_slot hv hu k1 k2
    have := h1.hiMM v (by omega)
    rw [hq4 _ (by omega) (fun i hi => by have := hℓ i hi; omega)
      (fun u hu e => absurd (Nat.add_left_cancel e) (hns u hu)), hCL _ (by omega),
      hnotH k (by have := h1.hiMM v (by omega); omega) fun i hi => hns _ (hH i hi)]
  · -- every head is a node
    by_cases hw : ∃ v < W.s, k = W.slotA mem1 v ∧ (v ∈ a.ℓ ∨ v = (W.Hl t st).getD (m + 1) 0)
    · obtain ⟨v, hv, rfl, hv' | rfl⟩ := hw
      · obtain ⟨i, hi, rfl⟩ := mem_iff_getD.mp hv'
        rw [← hsA, (q2 i hi).2]; omega
      · rw [← hsA, q3]; omega
    · rw [hq4 _ (by omega) (fun i hi => by have := hℓ i hi; omega) (fun v hv e => by
        refine ⟨fun h' => hw ⟨v, hv, Nat.add_left_cancel e, Or.inl h'⟩,
          fun h' => hw ⟨v, hv, Nat.add_left_cancel e, Or.inr h'⟩⟩), hCL _ (by omega)]
      exact (hI.shape.heads k hk).1
  · rw [hq4 _ (by unfold pqT pqSize at *; omega)
      (fun i hi => by have := hℓ i hi; unfold pqT; omega)
      (fun v hv e => by have := hsl1 v hv; unfold pqT at e; omega)]
    exact hclr.2.1 c hc
  · have hs := hI.stamps v hv
    change memL (W.L.TS + v) ≤ rs ∧ memL (W.L.TS + 2 * W.L.NN + v) ≤ rs at hs
    rw [hq4 _ (by omega) (fun i hi => by have := hℓ i hi; omega)
        (fun u hu e => by have := hsl1 u hu; omega), hCL _ (by omega),
      hq4 (W.L.TS + 2 * W.L.NN + v) (by omega) (fun i hi => by have := hℓ i hi; omega)
        (fun u hu e => by have := hsl1 u hu; omega), hCL _ (by omega)]
    omega
  · -- every slot is off
    rw [hsA' v (by omega)]
    by_cases hvl : v ∈ a.ℓ
    · obtain ⟨i, hi, rfl⟩ := mem_iff_getD.mp hvl
      exact (q2 i hi).2
    by_cases hvm : v = (W.Hl t st).getD (m + 1) 0
    · subst hvm; exact q3
    rw [hq4 _ (by have := hsl1 v hv; omega) (fun i hi => by have := hsl1 v hv; omega)
      (fun u hu e => by
        have := h1.slot_inj hu hv (Nat.add_left_cancel e).symm
        subst this; exact ⟨hvl, hvm⟩), hCL _ (by have := hsl1 v hv; omega)]
    by_cases hvH : ∃ i < (W.Hl t st).length, v = (W.Hl t st).getD i 0
    · obtain ⟨i, hi, rfl⟩ := hvH
      have := hI.slots i hi
      change memL (W.L.HD + W.slotA mem1 ((W.Hl t st).getD i 0)) =
        if i ≤ a.j then mem1 (W.NXT + (W.Hl t st).getD i 0) else W.s at this
      rw [this, if_neg]
      intro hij
      rcases Nat.lt_or_ge i a.j with hij' | hij'
      · exact hvl ((hI.sett _).mp ((hI.hsett i hi).mpr hij'))
      · exact hvm (by rw [show i = m + 1 by omega])
    · push_neg at hvH
      rw [hnotH _ (hsl1 v hv) fun i hi e => hvH i hi (h1.slot_inj hv (hH i hi) e)]
      have hne : v ≠ W.sv t := fun e => hvH 0 (by omega) (by rw [e]; rfl)
      show W.on mem (W.sv t) (W.L.HD + W.slotA (W.on mem (W.sv t)) v) = W.s
      rw [h.slotA_on hus (by omega), on_ne fun e => hne (h.slot_inj hv hus (Nat.add_left_cancel e))]
      exact hB.sl v hv
  · -- the marks
    split_ifs with hvl
    · obtain ⟨i, hi, rfl⟩ := mem_iff_getD.mp hvl
      exact (q2 i hi).1
    · rw [hq4 _ (by omega) (fun i hi e => hvl (by rw [Nat.add_left_cancel e]; exact getD_mem' hi))
        (fun u hu e => by have := hsl1 u hu; omega),
        (h1.after_fix hp hI hclr (show v < W.L.NN by omega)).2.2.2, hmem1,
        on_ne (by have := h.slot_cell hus; omega)]

  · rw [hfrC x e1 e2 e3, hmem1, on_ne (by have := h.slot_cell hus; omega)]

end PW

end MinCostFlow.LowStretch
