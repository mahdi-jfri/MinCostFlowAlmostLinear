module

public import MinCostFlow.LowStretch.ProgClusterSC

/-!
# The setting of a petal search inside a cluster: the proof of `SC.Ok`

`PW.sc_ok`: the fixed facts `PW.Ok` and the facts `PW.PS` of one search give `SC.Ok` for its
setting. The link to the petal metric comes from `plink_of` (`ProgClusterLink`): the arcs before
the slots are the entries (`PW.Ok.arcsN`), the slots of the highway nodes are the steps, and the
other slots go to the dummy node.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ}

/-! ### The arc ranges -/

/-- The arc ranges come one after the other. -/
theorem Ok.hi_le_lo (h : W.Ok w mem) {u v : ℕ} (huv : u < v) (hv : v ≤ W.s) :
    mem (W.L.HI + u) ≤ mem (W.L.LO + v) := by
  induction v with
  | zero => omega
  | succ v ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp huv with h1 | h1
    · have := ih h1 (by omega)
      have := h.lohi v (by omega)
      have := h.chain v (by omega)
      omega
    · subst h1; exact (h.chain u (by omega)).le

/-- An arc of `u` that is the slot of a node `v < s` is an arc of `v`, so `u = v`. -/
theorem Ok.own (h : W.Ok w mem) {u v k : ℕ} (hu : u ≤ W.s) (hv : v < W.s)
    (k1 : mem (W.L.LO + u) ≤ k) (k2 : k < mem (W.L.HI + u)) (hk : k = W.slotA mem v) : u = v := by
  have hl := h.lohi v hv
  unfold slotA at hk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have := h.hi_le_lo h1 (by omega)
    have := h.chain v hv
    omega
  · have := h.hi_le_lo h1 hu
    omega

theorem Ok.slot_inj (h : W.Ok w mem) {u v : ℕ} (hu : u < W.s) (hv : v < W.s)
    (he : W.slotA mem u = W.slotA mem v) : u = v := by
  have hl := h.lohi u hu
  exact h.own (by omega) hv (k := W.slotA mem u) (by unfold slotA; omega) (by unfold slotA; omega) he

/-! ### The heads with slots on -/

theorem hdF_of (mem : ℕ → ℕ) {H : List ℕ} {k : ℕ} (hk : ∀ u ∈ H, k ≠ W.slotA mem u) :
    W.hdF mem H k = (W.L.g mem).hd k := by
  induction H with
  | nil => rfl
  | cons u H ih =>
    simp only [hdF]
    rw [if_neg (hk u List.mem_cons_self)]
    exact ih fun v hv => hk v (List.mem_cons_of_mem _ hv)

theorem hdF_slot (mem : ℕ → ℕ) {H : List ℕ} {u : ℕ} (hu : u ∈ H)
    (hinj : ∀ v ∈ H, W.slotA mem v = W.slotA mem u → v = u) :
    W.hdF mem H (W.slotA mem u) = mem (W.NXT + u) := by
  induction H with
  | nil => simp at hu
  | cons v H ih =>
    simp only [hdF]
    by_cases e : W.slotA mem u = W.slotA mem v
    · rw [if_pos e, hinj v List.mem_cons_self e.symm]
    · rw [if_neg e]
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact absurd rfl e
      · exact ih hu' fun v' hv' => hinj v' (List.mem_cons_of_mem _ hv')

/-! ### The highway nodes -/

theorem Hl_length (t : ℕ) (st : List (ℕ × ℕ × ℕ)) : (W.Hl t st).length = st.length + 1 := by
  simp [Hl]

theorem Hl_getD (t : ℕ) (st : List (ℕ × ℕ × ℕ)) {i : ℕ} (hi : i ≤ st.length) :
    (W.Hl t st).getD i 0 = W.sv (Cl.stEnt t st i) := by
  unfold Hl Cl.stEnt
  cases i with
  | zero => rfl
  | succ i =>
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega),
      List.getD_eq_getElem _ _ (by simp; omega)]
    simp

theorem mem_Hl {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {u : ℕ} (hu : u ∈ W.Hl t st) :
    ∃ i ≤ st.length, u = W.sv (Cl.stEnt t st i) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  rw [Hl_length] at hi
  refine ⟨i, by omega, ?_⟩
  rw [← Hl_getD t st (by omega), List.getD_eq_getElem _ _ (by rw [Hl_length]; exact hi)]

theorem mem_Y {a : ℕ} : a ∈ W.Y mem ↔ a ∈ W.c.X ∧ mem (W.L.OK + W.sv a) = W.L.os := by
  unfold Y; simp

theorem Ok.sv_lt (h : W.Ok w mem) {a : ℕ} (ha : a ∈ W.c.X) : W.sv a < W.s :=
  h.hrec.sv_lt ha

theorem Ok.sv_iff (h : W.Ok w mem) {a b : ℕ} (ha : a ∈ W.c.X) (hb : b ∈ W.c.X) :
    W.sv a = W.sv b ↔ W.c.LConn W.G a b :=
  h.hrec.sv_iff ha hb

/-- The remaining set is a union of super-vertices. -/
theorem Ok.Y_cl (h : W.Ok w mem) {a b : ℕ} (ha : a ∈ W.Y mem) (hb : b ∈ W.c.X)
    (hl : W.c.LConn W.G a b) : b ∈ W.Y mem := by
  rw [mem_Y] at ha ⊢
  rw [← (h.sv_iff ha.1 hb).mpr hl]
  exact ⟨hb, ha.2⟩

/-- An entry joins two different super-vertices of `X`. -/
theorem Ok.entry (h : W.Ok w mem) {j : ℕ} (hj : j < W.nA) :
    W.pr j ∈ W.c.act W.G W.P ∧ W.G.pu (W.pr j) ∈ W.c.X ∧ W.G.pv (W.pr j) ∈ W.c.X ∧
      ¬ W.c.LConn W.G (W.G.pu (W.pr j)) (W.G.pv (W.pr j)) := by
  have hm : W.pr j ∈ W.c.act W.G W.P := by
    rw [← h.img]; exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hj)
  obtain ⟨-, h2, h3, h4, -⟩ := Cl.mem_act.mp hm
  exact ⟨hm, h2, h3, h4⟩

/-! ### Nodes and the remaining set -/

theorem Ok.lt_s_of (h : W.Ok w mem) {u : ℕ} (hu : u < W.L.NN) (ho : mem (W.L.OK + u) = W.L.os) :
    u < W.s := by
  have := h.hNN
  rcases Nat.lt_or_ge u W.s with h1 | h1
  · exact h1
  · have e : u = W.s := by omega
    subst e; exact absurd ho h.sS

theorem Ok.nodes_lt (h : W.Ok w mem) {u : ℕ} (hu : u ∈ W.Nodes mem) : u < W.s := by
  unfold Nodes at hu
  rw [Finset.mem_filter, Finset.mem_range] at hu
  exact h.lt_s_of hu.1 hu.2

theorem Ok.svY (h : W.Ok w mem) {a : ℕ} (ha : a ∈ W.Y mem) :
    W.sv a < W.s ∧ mem (W.L.OK + W.sv a) = W.L.os :=
  ⟨h.sv_lt (mem_Y.mp ha).1, (mem_Y.mp ha).2⟩

theorem Ok.okY (h : W.Ok w mem) {a : ℕ} (ha : a ∈ W.c.X) :
    (W.L.g mem).ok (W.sv a) ↔ a ∈ W.Y mem := by
  have := h.sv_lt ha
  have := h.hNN
  show W.sv a < W.L.NN ∧ _ ↔ _
  rw [mem_Y]
  exact ⟨fun h1 => ⟨ha, h1.2⟩, fun h1 => ⟨by omega, h1.2⟩⟩

theorem Ok.slot_lt (h : W.Ok w mem) {u : ℕ} (hu : u < W.s) : W.slotA mem u < W.L.MM := by
  have := h.lohi u hu
  have := h.hiMM u (by have := h.hNN; omega)
  unfold slotA; omega

variable {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ} {lo rs : ℕ}

theorem PS.t_mem (hp : W.PS w mem t st hw lo) : t ∈ W.Y mem := by
  simpa [Cl.stEnt] using hp.entY 0 (Nat.zero_le _)

theorem getD_mem' {H : List ℕ} {i : ℕ} (hi : i < H.length) : H.getD i 0 ∈ H := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem Ok.H_lt (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {u : ℕ} (hu : u ∈ W.Hl t st) :
    u < W.s := by
  obtain ⟨i, hi, rfl⟩ := mem_Hl hu
  exact (h.svY (hp.entY i hi)).1

theorem Ok.hinjH (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {u : ℕ} (hu : u ∈ W.Hl t st) :
    ∀ v ∈ W.Hl t st, W.slotA mem v = W.slotA mem u → v = u := fun v hv e =>
  h.slot_inj (h.H_lt hp hv) (h.H_lt hp hu) e

theorem stEnt_succ {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {i : ℕ} (hi : i < st.length) :
    Cl.stEnt t st (i + 1) = st[i].2.2 := by
  simp [Cl.stEnt, List.getD_eq_getElem?_getD, hi]

theorem Ok.sv_fst (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {i : ℕ} (hi : i < st.length) :
    W.sv st[i].2.1 = W.sv (Cl.stEnt t st i) ∧ st[i].2.1 ∈ W.Y mem := by
  have hl := hp.hwd.stOk.lconn_ent hi
  rw [List.getD_eq_getElem _ _ hi] at hl
  have hY := hp.entY i hi.le
  have hX : st[i].2.1 ∈ W.c.X := by
    obtain ⟨ps, hw⟩ := hl; simpa using hw.end_mem
  exact ⟨((h.sv_iff (mem_Y.mp hY).1 hX).mpr hl).symm, h.Y_cl hY hX hl⟩

/-! ### The arcs of the full graph -/

/-- An arc of a node before its slot is not a slot of the highway. -/
theorem Ok.hd_ns (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {u kk : ℕ} (hu : u < W.s)
    (k1 : mem (W.L.LO + u) ≤ kk) (k2 : kk + 1 < mem (W.L.HI + u)) :
    (W.gF mem (W.Hl t st)).hd kk = mem (W.L.HD + kk) := by
  have hkM : kk < W.L.MM := by have := h.hiMM u (by have := h.hNN; omega); omega
  show W.hdF mem (W.Hl t st) kk = _
  rw [hdF_of mem fun v hv e => ?_]
  · show (if kk < W.L.MM then _ else 0) = _
    rw [if_pos hkM]
  · have := h.own (u := u) (v := v) (k := kk) hu.le (h.H_lt hp hv) k1 (by omega) e
    subst this
    unfold slotA at e; omega

/-- The slot step `k` is an arc of the full graph. -/
theorem Ok.harc (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {k : ℕ} (hk : k < st.length) :
    (W.gF mem (W.Hl t st)).Arc (W.sv (Cl.stEnt t st k)) (W.sv (Cl.stEnt t st (k + 1)))
      (W.c.len W.G (st.getD k (0, 0, 0)).1) := by
  have hu := (h.svY (hp.entY k hk.le)).1
  have hun : W.sv (Cl.stEnt t st k) < W.L.NN := by have := h.hNN; omega
  have hv := h.svY (hp.entY (k + 1) hk)
  have hl := h.lohi _ hu
  have huH : W.sv (Cl.stEnt t st k) ∈ W.Hl t st := by
    rw [← Hl_getD t st hk.le]; exact getD_mem' (by rw [Hl_length]; omega)
  refine ⟨W.slotA mem (W.sv (Cl.stEnt t st k)), ?_, ?_, ?_, ?_, ?_⟩
  · show (if _ < W.L.NN then _ else 0) ≤ _
    rw [if_pos hun]; unfold slotA; omega
  · show _ < (if _ < W.L.NN then _ else 0)
    rw [if_pos hun]; unfold slotA; omega
  · show W.hdF mem (W.Hl t st) _ = _
    rw [hdF_slot mem huH (h.hinjH hp huH)]
    exact hp.nxt k hk
  · show (if _ < W.L.MM then _ else 0) = _
    rw [if_pos (h.slot_lt hu)]
    exact hp.scost k hk
  · exact ⟨by have := h.hNN; omega, hv.2⟩

theorem Ok.hcmpH (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) :
    ∀ s ∈ st, s.2.1 ∈ W.Y mem → s.2.2 ∈ W.Y mem →
      (W.gF mem (W.Hl t st)).Arc (W.sv s.2.1) (W.sv s.2.2) (W.c.len W.G s.1) := by
  intro s hs _ _
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  have := h.harc hp hi
  rw [(h.sv_fst hp hi).1, ← stEnt_succ hi]
  rwa [List.getD_eq_getElem _ _ hi] at this

theorem Ok.hcmpN (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) :
    ∀ p a b, a ∈ W.Y mem → b ∈ W.Y mem → W.G.Joins p a b → ¬ W.c.LConn W.G a b →
      rc W.c.θ (W.c.wbar W.G p a b) ≤ W.Rm →
      (W.gF mem (W.Hl t st)).Arc (W.sv a) (W.sv b) (rc W.c.θ (W.c.wbar W.G p a b)) := by
  intro p a b ha hb hj hnl hr
  have haX := (mem_Y.mp ha).1
  have hbX := (mem_Y.mp hb).1
  have hact : p ∈ W.c.act W.G W.P := by
    by_contra hna
    have := h.hrec.rc_ge hj haX hbX hnl hna
    have := h.hRm2
    omega
  rw [← h.img] at hact
  obtain ⟨j, hj', rfl⟩ := Finset.mem_image.mp hact
  have hjn := Finset.mem_range.mp hj'
  have hsa := h.sv_lt haX
  obtain ⟨kk, k1, k2, e1, e2⟩ := (h.arcsN (W.sv a) hsa
    (fun x y => x = W.sv b ∧ y = rc W.c.θ (W.c.wbar W.G (W.pr j) a b))).mpr (by
      refine ⟨j, hjn, ?_⟩
      rcases hj.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · subst e1 e2; exact Or.inl ⟨rfl, rfl, rfl⟩
      · subst e1 e2; exact Or.inr ⟨rfl, rfl, rfl⟩)
  have hun : W.sv a < W.L.NN := by have := h.hNN; omega
  have hkM : kk < W.L.MM := by have := h.hiMM _ hun; omega
  refine ⟨kk, ?_, ?_, ?_, ?_, ?_⟩
  · show (if _ < W.L.NN then _ else 0) ≤ _
    rw [if_pos hun]; exact k1
  · show _ < (if _ < W.L.NN then _ else 0)
    rw [if_pos hun]; omega
  · rw [h.hd_ns hp hsa k1 k2]; exact e1
  · show (if _ < W.L.MM then _ else 0) = _
    rw [if_pos hkM]; exact e2
  · exact (h.okY hbX).mpr hb

theorem Ok.hsnd (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) :
    ∀ u v k, (u = W.sv t ∨ (W.gF mem (W.Hl t st)).ok u) → (W.gF mem (W.Hl t st)).Arc u v k →
      (∃ p a b, a ∈ W.Y mem ∧ b ∈ W.Y mem ∧ W.G.Joins p a b ∧ W.sv a = u ∧ W.sv b = v ∧
        k = rc W.c.θ (W.c.wbar W.G p a b)) ∨
      (∃ s ∈ st, s.2.1 ∈ W.Y mem ∧ s.2.2 ∈ W.Y mem ∧ W.sv s.2.1 = u ∧ W.sv s.2.2 = v ∧
        k = W.c.len W.G s.1) := by
  intro u v k hu harc
  obtain ⟨kk, k1, k2, hd, hc, hok⟩ := harc
  have hus : u < W.s ∧ mem (W.L.OK + u) = W.L.os := by
    rcases hu with rfl | hu
    · exact h.svY hp.t_mem
    · have hu' : u < W.L.NN ∧ mem (W.L.OK + u) = W.L.os := hu
      exact ⟨h.lt_s_of hu'.1 hu'.2, hu'.2⟩
  obtain ⟨hus, huo⟩ := hus
  have hun : u < W.L.NN := by have := h.hNN; omega
  change (if u < W.L.NN then mem (W.L.LO + u) else 0) ≤ kk at k1
  change kk < (if u < W.L.NN then mem (W.L.HI + u) else 0) at k2
  rw [if_pos hun] at k1 k2
  have hok' : v < W.L.NN ∧ mem (W.L.OK + v) = W.L.os := hok
  have hvs := h.lt_s_of hok'.1 hok'.2
  have hkM : kk < W.L.MM := lt_of_lt_of_le k2 (h.hiMM u hun)
  change (if kk < W.L.MM then mem (W.L.CS + kk) else 0) = k at hc
  rw [if_pos hkM] at hc
  have hY : ∀ a ∈ W.c.X, mem (W.L.OK + W.sv a) = W.L.os → a ∈ W.Y mem :=
    fun a ha ho => mem_Y.mpr ⟨ha, ho⟩
  by_cases hns : kk + 1 < mem (W.L.HI + u)
  · left
    rw [h.hd_ns hp hus k1 hns] at hd
    obtain ⟨j, hj, hjj⟩ := (h.arcsN u hus (fun x y => x = v ∧ y = k)).mp ⟨kk, k1, hns, hd, hc⟩
    obtain ⟨hm, hpu, hpv, -⟩ := h.entry hj
    have hpm : W.pr j < W.G.m := (Cl.mem_act.mp hm).1
    rcases hjj with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · refine ⟨W.pr j, _, _, hY _ hpu ?_, hY _ hpv ?_, ⟨hpm, Or.inl ⟨rfl, rfl⟩⟩, e1, e2, e3.symm⟩
      · rw [show W.sv (W.G.pu (W.pr j)) = u from e1]; exact huo
      · rw [show W.sv (W.G.pv (W.pr j)) = v from e2]; exact hok'.2
    · refine ⟨W.pr j, _, _, hY _ hpv ?_, hY _ hpu ?_, ⟨hpm, Or.inr ⟨rfl, rfl⟩⟩, e1, e2, e3.symm⟩
      · rw [show W.sv (W.G.pv (W.pr j)) = u from e1]; exact huo
      · rw [show W.sv (W.G.pu (W.pr j)) = v from e2]; exact hok'.2
  · have hkk : kk = W.slotA mem u := by unfold slotA; omega
    by_cases huH : u ∈ W.Hl t st
    · have hd' : (W.gF mem (W.Hl t st)).hd kk = mem (W.NXT + u) := by
        rw [hkk]; exact hdF_slot mem huH (h.hinjH hp huH)
      obtain ⟨i, hi, rfl⟩ := mem_Hl huH
      rcases Nat.lt_or_ge i st.length with hi' | hi'
      · right
        have hf := h.sv_fst hp hi'
        refine ⟨st[i], List.getElem_mem hi', hf.2, ?_, hf.1, ?_, ?_⟩
        · rw [← stEnt_succ hi']; exact hp.entY (i + 1) hi'
        · rw [← stEnt_succ hi', ← hd, hd', hp.nxt i hi']
        · rw [← hc, hkk, hp.scost i hi', List.getD_eq_getElem _ _ hi']
      · have e : i = st.length := by omega
        subst e
        rw [hd', hp.nxtE] at hd
        omega
    · exfalso
      have hut : u ≠ W.sv t := by
        rintro rfl; exact huH List.mem_cons_self
      have e1 : (W.gF mem (W.Hl t st)).hd kk = mem (W.L.HD + kk) := by
        show W.hdF mem (W.Hl t st) kk = _
        rw [hdF_of mem fun v' hv' e => huH ?_]
        · show (if kk < W.L.MM then _ else 0) = _
          rw [if_pos hkM]
        · have e' := h.slot_inj hus (h.H_lt hp hv') (hkk.symm.trans e)
          subst e'; exact hv'
      rw [e1, hkk, hp.slS u hus hut] at hd
      omega

/-! ### The highway costs -/

theorem hcL_succ (G : PG) (c : Cl) {st : List (ℕ × ℕ × ℕ)} {i : ℕ} (hi : i < st.length) :
    Cl.hcL G c st (i + 1) = Cl.hcL G c st i + c.len G (st.getD i (0, 0, 0)).1 := by
  simp only [Cl.hcL]
  rw [List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, hi]

theorem Ok.link (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) :
    W.c.PLink W.G t hw (W.Y mem) W.sv (W.gF mem (W.Hl t st)) W.Rm :=
  Cl.plink_of h.conn (Finset.filter_subset _ _) hp.t_mem (fun _ ha _ hb hl => h.Y_cl ha hb hl)
    (fun _ ha _ hb => h.sv_iff ha hb) hp.hwd (h.hsnd hp) (h.hcmpN hp) (h.hcmpH hp)

theorem Ok.hhc (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) :
    ∀ i < (W.Hl t st).length, (W.gF mem (W.Hl t st)).Reach (W.sv t) ((W.Hl t st).getD i 0)
      (Cl.hcL W.G W.c st i) ∧
      ∀ k, (W.gF mem (W.Hl t st)).Reach (W.sv t) ((W.Hl t st).getD i 0) k →
        Cl.hcL W.G W.c st i ≤ k := by
  intro i hi
  rw [Hl_length] at hi
  rw [Hl_getD t st (by omega)]
  exact Cl.hc_of h.conn hp.hwd (h.link hp) (fun _ ha _ hb => h.sv_iff ha hb) hp.entY
    (fun k hk => h.harc hp hk) (by omega)

/-! ### The cells that the search never writes -/

theorem Ok.TS_CTL (h : W.Ok w mem) : W.L.TS < W.CTL := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, l12⟩ := h.lay
  have := h.hR; have := h.hCTL; omega

theorem Ok.fixOf (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {a : ℕ} (ha : a < W.L.TS)
    (hs : ∀ i < (W.Hl t st).length, a ≠ W.L.HD + W.slotA mem ((W.Hl t st).getD i 0)) :
    (W.sc mem t st hw lo rs).Fix a :=
  ⟨Or.inl ha, ha.trans h.TS_CTL, hs⟩

theorem Ok.fix (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {a : ℕ}
    (ha : a < W.L.HD ∨ (W.L.HD + W.L.MM ≤ a ∧ a < W.L.TS)) : (W.sc mem t st hw lo rs).Fix a := by
  obtain ⟨-, -, l3, l4, l5, l6, l7, l8, l9, l10, l11, -⟩ := h.lay
  have := h.lES
  refine h.fixOf hp (by omega) fun i hi => ?_
  have := h.slot_lt (h.H_lt hp (getD_mem' hi))
  omega

/-- **The setting of a petal search satisfies `SC.Ok`.** -/
theorem Ok.sc_ok (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) : (W.sc mem t st hw lo rs).Ok w := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES
  have hNN := h.hNN
  have hHi : ∀ i < (W.Hl t st).length, (W.Hl t st).getD i 0 = W.sv (Cl.stEnt t st i) :=
    fun i hi => Hl_getD t st (by rw [Hl_length] at hi; omega)
  have hHY : ∀ i < (W.Hl t st).length, Cl.stEnt t st i ∈ W.Y mem :=
    fun i hi => hp.entY i (by rw [Hl_length] at hi; omega)
  exact {
    Hnd := hp.nd
    Hne := by show 0 < (W.Hl t st).length; rw [Hl_length]; omega
    H0 := rfl
    HS := fun i hi => h.H_lt hp (getD_mem' hi)
    HN := fun i hi => by
      show (W.Hl t st).getD i 0 ∈ W.Nodes mem
      unfold Nodes
      rw [Finset.mem_filter, Finset.mem_range, hHi i hi]
      have := h.svY (hHY i hi)
      exact ⟨by omega, this.2⟩
    SN := by show W.s < W.L.NN; omega
    Sok := fun hs => h.sS hs.2
    hnx := fun i hi => by
      show mem (W.NXT + (W.Hl t st).getD i 0) = (W.Hl t st ++ [W.s]).getD (i + 1) 0
      have hi' : i < (W.Hl t st).length := hi
      rw [Hl_length] at hi'
      rw [hHi i hi, List.getD_eq_getElem?_getD]
      rcases Nat.lt_or_ge i st.length with h1 | h1
      · rw [List.getElem?_append_left (by rw [Hl_length]; omega), ← List.getD_eq_getElem?_getD,
          Hl_getD t st h1]
        exact hp.nxt i h1
      · have e : i = st.length := by omega
        subst e
        rw [List.getElem?_append_right (by rw [Hl_length]), Hl_length]
        simpa using hp.nxtE
    lohi := fun v hv => h.lohi v (h.nodes_lt hv)
    own := fun u k i k1 k2 hi hk => by
      have hiS := h.H_lt hp (getD_mem' hi)
      by_cases hu : u < W.L.NN
      · change (if u < W.L.NN then mem (W.L.LO + u) else 0) ≤ k at k1
        change k < (if u < W.L.NN then mem (W.L.HI + u) else 0) at k2
        rw [if_pos hu] at k1 k2
        exact h.own (by omega) hiS k1 k2 hk
      · change k < (if u < W.L.NN then mem (W.L.HI + u) else 0) at k2
        rw [if_neg hu] at k2
        omega
    Flo := fun _ => rfl
    Fhi := fun _ => rfl
    Fcs := fun _ => rfl
    Fok := fun _ => Iff.rfl
    Fhd := fun k hk => hdF_of mem fun u hu e => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      exact hk i hi (by
        show k = W.slotA mem ((W.Hl t st).getD i 0)
        rw [List.getD_eq_getElem _ _ hi]; exact e)
    Fsl := fun i hi => hdF_slot mem (getD_mem' hi) (h.hinjH hp (getD_mem' hi))
    hhc := h.hhc hp
    hinc := fun i hi => by
      show Cl.hcL W.G W.c st i < Cl.hcL W.G W.c st (i + 1)
      change i + 1 < (W.Hl t st).length at hi
      rw [Hl_length] at hi
      rw [hcL_succ W.G W.c (by omega)]
      have := hp.pos i (by omega)
      omega
    fLO := fun v hv => by
      change v < W.L.NN at hv
      exact ⟨h.fix hp (a := W.L.LO + v) (Or.inl (by omega)),
        h.fix hp (a := W.L.HI + v) (Or.inl (by omega)),
        h.fix hp (a := W.L.OK + v) (Or.inr ⟨by omega, by omega⟩),
        h.fix hp (a := W.NXT + v) (Or.inr ⟨by omega, by omega⟩)⟩
    fCS := fun k hk => by
      change k < W.L.MM at hk
      exact ⟨h.fix hp (a := W.L.CS + k) (Or.inr ⟨by omega, by omega⟩),
        h.fix hp (a := W.L.CL + k) (Or.inr ⟨by omega, by omega⟩),
        h.fix hp (a := W.ORD + k) (Or.inr ⟨by omega, by omega⟩)⟩
    fHD := fun k hk hs => by
      change k < W.L.MM at hk
      exact h.fixOf hp (a := W.L.HD + k) (by omega) fun i hi e => hs i hi (Nat.add_left_cancel e)
    fAS := fun j hj => by
      change j < W.nA at hj
      have := h.lEXP j hj
      exact ⟨h.fix hp (a := W.AS + 2 * j) (Or.inr ⟨by omega, by omega⟩),
        h.fix hp (a := W.EXP + mem (W.AS + 2 * j)) (Or.inr ⟨by omega, by omega⟩)⟩
    fSQ := fun q hq => by
      change q ≤ W.Lb + 1 at hq
      exact ⟨h.fix hp (a := W.SQ + q) (Or.inr ⟨by omega, by omega⟩),
        h.fix hp (a := W.P2 + q) (Or.inr ⟨by omega, by omega⟩)⟩
    hR := h.hR
    hCTL := h.hCTL
    hSUM := h.hSUM
    hSL := h.hSL
    wSL := h.wSL
    ordA := fun u hu => h.ordA u (h.nodes_lt hu)
    hsum := fun u hu => h.hsum u (h.nodes_lt hu)
    hwt := h.hwt
    ends := fun j hj => by
      obtain ⟨-, hpu, hpv, hnl⟩ := h.entry hj
      have := h.sv_lt hpu
      have := h.sv_lt hpv
      refine ⟨by show W.sv (W.G.pu (W.pr j)) < W.L.NN; omega,
        by show W.sv (W.G.pv (W.pr j)) < W.L.NN; omega, fun e => hnl ?_⟩
      exact (h.sv_iff hpu hpv).mp e
    wU := h.wU
    wE := h.wE
    wR2 := h.wR2
    wb := hp.wb
    wL := h.wL
    wSm := h.wSm
    wSQ := h.wSQ
    wP2 := h.wP2
    wNXT := h.wNXT
    nxt := h.nxt
    hiMM := h.hiMM
    hSm := h.hSm
    wT1 := hp.wT1
    wT2 := h.wT2
    hRm := hp.hRm
    hINF := hp.hINF
    hM := h.hM
    hLb := h.hLb
    hbw := h.hbw
    hκ := h.hκ
    hnact := h.hnact
    hsq := h.hsq
    hP2 := h.hP2
    hcw := h.hcw
    hwM := h.hwM
    link := h.link hp
    hsv := rfl
    img := h.img
    inj := h.inj
    hea := fun _ _ => rfl
    heb := fun _ _ => rfl
    okY := fun j hj => by
      obtain ⟨-, hpu, hpv, -⟩ := h.entry hj
      exact ⟨h.okY hpu, h.okY hpv⟩
    hGo := h.hrec.hGo
    hκ1 := h.hκ1
    hL1 := h.hL1
    hΔ := h.hΔ
    hV := h.hV }

end PW

end MinCostFlow.LowStretch
