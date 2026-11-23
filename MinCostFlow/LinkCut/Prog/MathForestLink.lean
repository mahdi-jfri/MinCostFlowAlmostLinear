module

public import MinCostFlow.LinkCut.Prog.MathForestLinkSetup

/-!
# Word-RAM `link` Procedure Correctness

Proves `lctLinkBody_runs`: running `lctLinkBody lp` on a valid represented forest `F` with
disconnected vertices `e.u, e.v` and edge payload `(cPtr, fPtr, afPtr, abPtr)` succeeds,
maintains `LctMemRep` and Word-RAM `Respects`, and pays amortized cost bounded by
`lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1)`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section LinkBudgetArith

private theorem link_reroot_room_arith {hp L phi0 logN n p2w : ℕ}
    (h : hp + phi0 + C_LINK_OP L * logN + 7000 * (L + 1) * (n + 2) + 7 * L + 1 < p2w) :
    (hp + 7 * L) + phi0 + (C_REROOT_OP L + C_EXPOSE_OP L) * logN + 7000 * (L + 1) * (n + 2) + 1 < p2w ∧
      14000 < p2w ∧ hp + 7 * L < p2w := by
  have hc : C_REROOT_OP L + C_EXPOSE_OP L ≤ C_LINK_OP L := by
    unfold C_REROOT_OP C_EXPOSE_OP C_LINK_OP; omega
  have hmul : (C_REROOT_OP L + C_EXPOSE_OP L) * logN ≤ C_LINK_OP L * logN :=
    Nat.mul_le_mul_right logN hc
  have h14 : 14000 ≤ 7000 * (L + 1) * (n + 2) := by
    have hm1 : 1 ≤ (L + 1) := by omega
    have hm2 : 2 ≤ (n + 2) := by omega
    have hmul' : 1 * 2 ≤ (L + 1) * (n + 2) := Nat.mul_le_mul hm1 hm2
    have hm3 : 7000 * 2 ≤ 7000 * ((L + 1) * (n + 2)) := Nat.mul_le_mul_left 7000 hmul'
    rw [Nat.mul_assoc]
    omega
  set a := (C_REROOT_OP L + C_EXPOSE_OP L) * logN
  set b := C_LINK_OP L * logN
  set c := 7000 * (L + 1) * (n + 2)
  have hle : a ≤ b := hmul
  have h14' : 14000 ≤ c := h14
  omega

private lemma pure_splay_room_arith {c_re c_exp s2 hp_eff phi0 phi2 cr_ce a b p2w : ℕ}
    (hle : hp_eff ≤ s2) (hab : a ≤ b)
    (h1 : c_re + c_exp + (s2 - hp_eff) + phi2 ≤ phi0 + cr_ce)
    (h2 : hp_eff + phi0 + cr_ce + b + 1 < p2w) :
    s2 + a < p2w := by
  omega

private theorem link_splay_room_arith {c_re c_exp s2 hp_eff phi0 phi2 cr_ce n L p2w : ℕ}
    (hle : hp_eff ≤ s2)
    (h1 : c_re + c_exp + (s2 - hp_eff) + phi2 ≤ phi0 + cr_ce)
    (h2 : hp_eff + phi0 + cr_ce + 7000 * (L + 1) * (n + 2) + 1 < p2w) :
    s2 + 6000 * (L + 1) * (n + 2) < p2w :=
  pure_splay_room_arith hle (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))) h1 h2

private lemma link_kpull_le_7000 (L n : ℕ) : K_PULL L + 1 ≤ 7000 * (L + 1) * (n + 2) := by
  have h1 : K_PULL L + 1 ≤ 7000 * (L + 1) * 2 := by unfold K_PULL; omega
  exact le_trans h1 (Nat.mul_le_mul_left _ (Nat.le_add_left 2 n))

private lemma link_4L_le_7000 (L n : ℕ) : 4 * L ≤ 7000 * (L + 1) * (n + 2) := by
  have h1 : 4 * L ≤ 7000 * (L + 1) * 2 := by omega
  exact le_trans h1 (Nat.mul_le_mul_left _ (Nat.le_add_left 2 n))

private lemma pure_pull_room_arith {c_re c_exp c_sp s2 s3 hp L7 phi0 phi2 phi3 re_k cs lnk m7 a4 kp p2w : ℕ}
    (hre : c_re + c_exp + (s2 - (hp + L7)) + phi2 ≤ phi0 + re_k)
    (hsp : c_sp + (s3 - s2) + phi3 ≤ phi2 + cs)
    (hb : re_k + cs ≤ lnk)
    (hle2 : hp + L7 ≤ s2) (hle3 : s2 ≤ s3)
    (ha4 : a4 ≤ m7) (hpu : kp + 1 ≤ m7)
    (hroom : hp + phi0 + lnk + m7 + L7 + 1 < p2w) :
    s3 + a4 < p2w ∧ s3 + kp + 1 < p2w := by
  omega

private theorem link_pull_room_arith {c_re c_exp c_sp s2 s3 hp L phi0 phi2 phi3 logN n p2w : ℕ}
    (hre : c_re + c_exp + (s2 - (hp + 7 * L)) + phi2 ≤ phi0 + (C_REROOT_OP L + C_EXPOSE_OP L) * logN)
    (hsp : c_sp + (s3 - s2) + phi3 ≤ phi2 + 3 * K_SPLAY_STEP L * logN + C_SPLAY_CONST L)
    (hle2 : hp + 7 * L ≤ s2) (hle3 : s2 ≤ s3) (hlog : 1 ≤ logN)
    (hroom : hp + phi0 + C_LINK_OP L * logN + 7000 * (L + 1) * (n + 2) + 7 * L + 1 < p2w) :
    s3 + 4 * L < p2w ∧ s3 + K_PULL L + 1 < p2w := by
  have hks : K_SPLAY_STEP L ≤ 9200 * (L + 1) := by
    unfold K_SPLAY_STEP K_DOUBLE K_PUSH_PATH K_ROTATE K_PUSH_DOWN K_PULL; omega
  have hcs : C_SPLAY_CONST L ≤ 6800 * (L + 1) * logN := by
    unfold C_SPLAY_CONST
    exact Nat.le_mul_of_pos_right _ hlog
  have hsum_k : C_REROOT_OP L + C_EXPOSE_OP L + 3 * 9200 * (L + 1) + 6800 * (L + 1) ≤ C_LINK_OP L := by
    unfold C_REROOT_OP C_EXPOSE_OP C_LINK_OP; omega
  have hmul : (C_REROOT_OP L + C_EXPOSE_OP L + 3 * 9200 * (L + 1) + 6800 * (L + 1)) * logN ≤
      C_LINK_OP L * logN := Nat.mul_le_mul_right logN hsum_k
  have h3k : 3 * K_SPLAY_STEP L * logN ≤ 3 * 9200 * (L + 1) * logN := by
    have : 3 * K_SPLAY_STEP L ≤ 3 * 9200 * (L + 1) := by omega
    have hm := Nat.mul_le_mul_right logN this
    simpa [Nat.mul_assoc] using hm
  have hdist : (C_REROOT_OP L + C_EXPOSE_OP L) * logN + 3 * 9200 * (L + 1) * logN +
      6800 * (L + 1) * logN =
      (C_REROOT_OP L + C_EXPOSE_OP L + 3 * 9200 * (L + 1) + 6800 * (L + 1)) * logN := by ring
  have hb : (C_REROOT_OP L + C_EXPOSE_OP L) * logN + (3 * K_SPLAY_STEP L * logN + C_SPLAY_CONST L) ≤
      C_LINK_OP L * logN := by
    calc (C_REROOT_OP L + C_EXPOSE_OP L) * logN + (3 * K_SPLAY_STEP L * logN + C_SPLAY_CONST L)
        ≤ (C_REROOT_OP L + C_EXPOSE_OP L) * logN + 3 * 9200 * (L + 1) * logN + 6800 * (L + 1) * logN := by
          omega
      _ = (C_REROOT_OP L + C_EXPOSE_OP L + 3 * 9200 * (L + 1) + 6800 * (L + 1)) * logN := hdist
      _ ≤ C_LINK_OP L * logN := hmul
  exact pure_pull_room_arith hre (by simpa [Nat.add_assoc] using hsp) hb hle2 hle3
    (link_4L_le_7000 L n) (link_kpull_le_7000 L n) hroom

private lemma link_coeff_budget_arith (L : ℕ) :
    C_REROOT_OP L + C_EXPOSE_OP L + 5 * 9200 * (L + 1) + 16500 * (L + 1) ≤ C_LINK_OP L := by
  unfold C_REROOT_OP C_EXPOSE_OP C_LINK_OP
  omega

private lemma link_const_budget_arith {L logN : ℕ} (hlog : 1 ≤ logN) :
    C_SPLAY_CONST L + K_PULL L + C_HEAVY L + 157 * L + 471 ≤ 16500 * (L + 1) * logN := by
  have hch := c_heavy_le L
  have h1 : 16500 * (L + 1) ≤ 16500 * (L + 1) * logN := Nat.le_mul_of_pos_right _ hlog
  unfold C_SPLAY_CONST K_PULL
  omega

private lemma pure_final_budget_arith
    {c_tot c_pa c_re c_exp c_sp c_splice c_pu s2 s3 s_p hp L7 L150 L157 phi0 phi2 phi3 phi_p re_k k3 k2 cs kp ch lnk m7 space p2w : ℕ}
    (hct : c_tot ≤ c_pa + c_re + c_exp + c_sp + c_splice + c_pu + 60)
    (hcpa : c_pa ≤ L150 + 210) (hcsplice : c_splice ≤ 200) (hL7 : L150 + L7 = L157)
    (hre : c_re + c_exp + (s2 - (hp + L7)) + phi2 ≤ phi0 + re_k)
    (hsp : c_sp + (s3 - s2) + phi3 ≤ phi2 + k3 + cs)
    (hpu : c_pu + (s_p - s3) ≤ kp)
    (hphi : phi_p ≤ phi3 + k2 + ch)
    (htot : re_k + k3 + k2 + cs + kp + ch + L157 + 471 ≤ lnk)
    (hle2 : hp + L7 ≤ s2) (hle3 : s2 ≤ s3) (hlep : s3 ≤ s_p)
    (hroom : hp + phi0 + lnk + m7 + L7 + 1 < p2w)
    (hspace : phi0 + lnk + L7 + 1 ≤ space) :
    s_p + 1 < p2w ∧ s_p + 1 ≤ hp + space ∧
      c_tot + (s_p + 1 - hp) + phi_p ≤ phi0 + lnk := by
  omega

private theorem link_final_budget_arith
    {c_tot c_pa c_re c_exp c_sp c_splice c_pu s2 s3 s_p hp L phi0 phi2 phi3 phi_p logN n space p2w : ℕ}
    (hct : c_tot ≤ c_pa + c_re + c_exp + c_sp + c_splice + c_pu + 60)
    (hcpa : c_pa ≤ 150 * L + 210) (hcsplice : c_splice ≤ 200)
    (hre : c_re + c_exp + (s2 - (hp + 7 * L)) + phi2 ≤ phi0 + (C_REROOT_OP L + C_EXPOSE_OP L) * logN)
    (hsp : c_sp + (s3 - s2) + phi3 ≤ phi2 + 3 * K_SPLAY_STEP L * logN + C_SPLAY_CONST L)
    (hpu : c_pu + (s_p - s3) ≤ K_PULL L)
    (hphi : phi_p ≤ phi3 + 2 * K_SPLAY_STEP L * logN + C_HEAVY L)
    (hle2 : hp + 7 * L ≤ s2) (hle3 : s2 ≤ s3) (hlep : s3 ≤ s_p) (hlog : 1 ≤ logN)
    (hroom : hp + phi0 + C_LINK_OP L * logN + 7000 * (L + 1) * (n + 2) + 7 * L + 1 < p2w)
    (hspace : phi0 + C_LINK_OP L * logN + 7 * L + 1 ≤ space) :
    s_p + 1 < p2w ∧ s_p + 1 ≤ hp + space ∧
      c_tot + (s_p + 1 - hp) + phi_p ≤ phi0 + C_LINK_OP L * logN := by
  have hks : K_SPLAY_STEP L ≤ 9200 * (L + 1) := by
    unfold K_SPLAY_STEP K_DOUBLE K_PUSH_PATH K_ROTATE K_PUSH_DOWN K_PULL; omega
  have h5k : 3 * K_SPLAY_STEP L * logN + 2 * K_SPLAY_STEP L * logN ≤ 5 * 9200 * (L + 1) * logN := by
    have : 5 * K_SPLAY_STEP L ≤ 5 * 9200 * (L + 1) := by omega
    have hm := Nat.mul_le_mul_right logN this
    have heq : 3 * K_SPLAY_STEP L * logN + 2 * K_SPLAY_STEP L * logN = (5 * K_SPLAY_STEP L) * logN := by
      ring
    omega
  have hmul := Nat.mul_le_mul_right logN (link_coeff_budget_arith L)
  have hdist : (C_REROOT_OP L + C_EXPOSE_OP L) * logN + 5 * 9200 * (L + 1) * logN +
      16500 * (L + 1) * logN =
      (C_REROOT_OP L + C_EXPOSE_OP L + 5 * 9200 * (L + 1) + 16500 * (L + 1)) * logN := by ring
  have htot_le : (C_REROOT_OP L + C_EXPOSE_OP L) * logN + 3 * K_SPLAY_STEP L * logN +
      2 * K_SPLAY_STEP L * logN + C_SPLAY_CONST L + K_PULL L + C_HEAVY L + 157 * L + 471 ≤
      C_LINK_OP L * logN := by
    have hconst_le := link_const_budget_arith (L := L) hlog
    calc (C_REROOT_OP L + C_EXPOSE_OP L) * logN + 3 * K_SPLAY_STEP L * logN +
          2 * K_SPLAY_STEP L * logN + C_SPLAY_CONST L + K_PULL L + C_HEAVY L + 157 * L + 471
        = (C_REROOT_OP L + C_EXPOSE_OP L) * logN + (3 * K_SPLAY_STEP L * logN + 2 * K_SPLAY_STEP L * logN) +
          (C_SPLAY_CONST L + K_PULL L + C_HEAVY L + 157 * L + 471) := by ring
      _ ≤ (C_REROOT_OP L + C_EXPOSE_OP L) * logN + 5 * 9200 * (L + 1) * logN + 16500 * (L + 1) * logN :=
          Nat.add_le_add (Nat.add_le_add_left h5k _) hconst_le
      _ = (C_REROOT_OP L + C_EXPOSE_OP L + 5 * 9200 * (L + 1) + 16500 * (L + 1)) * logN := hdist
      _ ≤ C_LINK_OP L * logN := hmul
  exact pure_final_budget_arith hct hcpa hcsplice (by omega : 150 * L + 7 * L = 157 * L)
    hre hsp hpu hphi htot_le hle2 hle3 hlep hroom hspace

private lemma link_perm_flatMap {α β : Type*} (f : α → List β) {l₁ l₂ : List α}
    (hp : l₁.Perm l₂) : (l₁.flatMap f).Perm (l₂.flatMap f) := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp only [List.flatMap_cons]; exact ih.append_left (f x)
  | swap x y l =>
      simp only [List.flatMap_cons, ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private lemma link_c_tot_arith (c_pa c_re c_exp c_sp c_splice c_pu : ℕ) :
    c_pa + (2 + c_re + 1 + (2 + c_exp + 1 + (2 + c_sp + 1 +
      (c_splice + (2 + c_pu + 1 + (5 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤
      c_pa + c_re + c_exp + c_sp + c_splice + c_pu + 60 := by
  omega

private lemma link_fin_lt_arith {sp sw kp_c kp p2w : ℕ}
    (h1 : sw ≤ sp) (h2 : kp_c + (sp - sw) ≤ kp) (h3 : sw + kp + 1 < p2w) :
    sp + 1 < p2w := by
  omega

end LinkBudgetArith

section LinkRoots

/-- The root of a root is itself. -/
theorem rootAbove_rootAbove {par : ℕ → ℕ} {cap : ℕ}
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0) {x : ℕ} (hx1 : 1 ≤ x)
    (hx2 : x ≤ cap) : rootAbove par cap (rootAbove par cap x) = rootAbove par cap x :=
  rootAbove_self_of_par_zero (le_trans hx1 hx2) (rootAbove_zero_par (hacyc x hx1 hx2) (by omega))

/-- How `link` moves the represented roots: the vertices in the tree of `u` get the root of `v`,
and the other roots stay. The parent maps are those before the call (`mem₀`), after
`reroot u; expose v` (`mem₂`), and at the end (`mem_p`). -/
theorem link_canonRoot {w h L P b u v ed : ℕ} {F : MathForest} {x₀ x₂ : LctConc}
    {mem₀ mem₂ mem_p : ℕ → ℕ}
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hrep₂ : LctMemRep w h L P b F x₂ mem₂)
    (hu : u < F.n) (hv : v < F.n) (hdisc : ¬ F.SameComp u v)
    (hmove : RootMove (lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n))
      (lctAuxParent mem₂ (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (u + 1))
    (hacyc_p : ∀ z, 1 ≤ z → z ≤ lctCap F.n →
      iterParent (lctAuxParent mem_p (lctNodesBase b) (lctCap F.n)) (lctCap F.n) z = 0)
    (hupd : ∀ z, lctAuxParent mem_p (lctNodesBase b) (lctCap F.n) z =
      if z = ed then v + 1 else if z = u + 1 then ed
      else lctAuxParent mem₂ (lctNodesBase b) (lctCap F.n) z)
    (hno_ed : ∀ z, lctAuxParent mem₂ (lctNodesBase b) (lctCap F.n) z ≠ ed)
    (hed1 : F.n + 1 ≤ ed) (hed2 : ed ≤ lctCap F.n)
    (hpar_u : lctAuxParent mem₂ (lctNodesBase b) (lctCap F.n) (u + 1) = 0) :
    ∀ z < F.n, lctCanonRoot mem_p b F.n z =
      if lctCanonRoot mem₀ b F.n z = lctCanonRoot mem₀ b F.n u then lctCanonRoot mem₀ b F.n v
      else lctCanonRoot mem₀ b F.n z := by
  intro z hz
  let nb := lctNodesBase b
  let cap := lctCap F.n
  let par₀ := lctAuxParent mem₀ nb cap
  let par₂ := lctAuxParent mem₂ nb cap
  let par_p := lctAuxParent mem_p nb cap
  have hcap : ∀ y < F.n, y + 1 ≤ cap := fun y hy => by dsimp only [cap, lctCap]; omega
  have hp0 : ∀ mem : ℕ → ℕ, lctAuxParent mem nb cap 0 = 0 := fun mem => lctAuxParent_zero mem nb cap
  have hle : ∀ mem : ℕ → ℕ, ∀ y, 1 ≤ y → y ≤ cap → lctAuxParent mem nb cap y ≤ cap :=
    fun mem y _ _ => lctAuxParent_le_cap mem nb cap y
  have hacyc₀ := hrep₀.subdivOk.1
  have hacyc₂ := hrep₂.subdivOk.1
  -- roots before the call
  have hR : ∀ y < F.n, rootAbove par₀ cap (y + 1) = lctCanonRoot mem₀ b F.n y + 1 :=
    fun y hy => (hrep₀.lctCanonRoot_spec hy).2.1.symm
  have hR_ne : rootAbove par₀ cap (v + 1) ≠ rootAbove par₀ cap (u + 1) := fun h =>
    hdisc ((hrep₀.sameComp_iff_rootAbove hu hv).2 h.symm)
  have hR_ne_u : rootAbove par₀ cap (v + 1) ≠ u + 1 := fun h => by
    apply hR_ne
    have hidem := rootAbove_rootAbove hacyc₀ (by omega : 1 ≤ v + 1)
      (hcap v hv)
    rw [h] at hidem
    rw [hidem, h]
  have hR2v : rootAbove par₂ cap (v + 1) = rootAbove par₀ cap (v + 1) := by
    rw [hmove (v + 1) (by omega) (hcap v hv)]
    split_ifs with h
    · exact absurd h hR_ne
    · rfl
  have hlink := rootAbove_link (par₃ := par₂) (par_p := par_p) (hp0 mem₂) (hle mem₂) hacyc₂
    (hp0 mem_p) (hle mem_p) hacyc_p hupd hno_ed (by omega) (hcap u hu) hpar_u (by omega) (hcap v hv)
    (by omega) hed2 (by omega) (by omega)
    (by rw [hR2v]; exact hR_ne_u)
  have hfin := hlink (z + 1) (by omega) (hcap z hz) (by omega)
  have hdef : lctCanonRoot mem_p b F.n z = rootAbove par_p cap (z + 1) - 1 := rfl
  rw [hdef, hfin, hmove (z + 1) (by omega) (hcap z hz)]
  have hkey : rootAbove par₀ cap (z + 1) = u + 1 →
      rootAbove par₀ cap (z + 1) = rootAbove par₀ cap (u + 1) := fun h => by
    have hidem := rootAbove_rootAbove hacyc₀ (by omega : 1 ≤ z + 1) (hcap z hz)
    rw [h] at hidem
    rw [hidem, h]
  have e1 := hR z hz
  have e2 := hR u hu
  have e3 := hR v hv
  rw [e1, e2] at hkey
  have hkey' : lctCanonRoot mem₀ b F.n z + 1 = u + 1 →
      lctCanonRoot mem₀ b F.n z = lctCanonRoot mem₀ b F.n u := fun h => by
    have := hkey h; omega
  by_cases hc : lctCanonRoot mem₀ b F.n z = lctCanonRoot mem₀ b F.n u
  · rw [e1, e2, hR2v, e3]
    split_ifs <;> omega
  · have hne : lctCanonRoot mem₀ b F.n z + 1 ≠ u + 1 := fun h => hc (hkey' h)
    rw [e1, e2, hR2v, e3]
    split_ifs <;> omega

end LinkRoots

section LinkMain

/-- Correctness and amortized complexity theorem for `lctLinkBody`. -/
theorem lctLinkBody_runs {w h L P b cPtr fPtr afPtr abPtr hp_caller space pos : ℕ}
    {F : MathForest} {x₀ : LctConc} {e : ForestEdge}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : e.u < F.n) (hv : e.v < F.n) (hdisc : ¬ F.SameComp e.u e.v)
    (heid_fresh : ∀ e' ∈ F.edges, e'.eid ≠ e.eid) (heid_w : e.eid < 2 ^ w)
    (hfit_e : EdgeFits h L P e)
    (hc_valid : Valid mem₀ cPtr h L) (hc_bd : cPtr + L ≤ hp_caller) (hc_val : intVal mem₀ cPtr h L = e.cost)
    (hf_valid : Valid mem₀ fPtr h L) (hf_bd : fPtr + L ≤ hp_caller)
    (hf_val : ((intVal mem₀ fPtr h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.flow)
    (haf_valid : Valid mem₀ afPtr h L) (haf_bd : afPtr + L ≤ hp_caller)
    (haf_val : ((intVal mem₀ afPtr h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availFwd)
    (hab_valid : Valid mem₀ abPtr h L) (hab_bd : abPtr + L ≤ hp_caller)
    (hab_val : ((intVal mem₀ abPtr h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availBwd)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hroom : hp_caller + lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) +
        7000 * (L + 1) * (F.n + 2) + 7 * L + 1 < 2 ^ w)
    (hspace : lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) + 7 * L + 1 ≤ space)
    (ω : ℕ → Bool) :
    ∃ hp_final st' c x',
      Runs w p ω (lctLinkBody lp)
        (startState [b, e.u, e.v, e.eid, cPtr, fPtr, afPtr, abPtr, hp_caller] mem₀ pos)
        (.returned hp_final) st' c ∧
      LctMemRep w h L P b (F.link e) x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_final b x' st'.mem ∧
      c + (hp_final - hp_caller) + lctPhi L st'.mem b (F.link e).n ≤
        lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z =
        if lctCanonRoot mem₀ b F.n z = lctCanonRoot mem₀ b F.n e.u then lctCanonRoot mem₀ b F.n e.v
        else lctCanonRoot mem₀ b F.n z := by
  let u := e.u
  let v := e.v
  let nb := lctNodesBase b
  let cap := lctCap F.n
  let hp_eff := hp_caller + 7 * L
  let logN := Nat.log 2 (F.n + 2) + 1
  have hlog_pos : 1 ≤ logN := by omega
  rcases link_reroot_room_arith hroom with ⟨hroom_re, h14000, heff_w⟩
  have harena_le : lctArenaHi b cap ≤ hp_caller := by
    have hlt := b_lt_lctArenaHi b cap
    have hpos : 0 < lctArenaHi b cap := lt_of_le_of_lt (Nat.zero_le b) hlt
    have hf := hfoot (lctArenaHi b cap - 1)
      (lctFoot_arena (x := x₀) (by omega) (by rw [hrep₀.2.2.2.2.1]; exact Nat.sub_lt hpos (by decide)))
    omega
  rcases link_prealloc_runs hp_base hrep₀ hu hv hc_valid hc_bd hc_val hf_valid hf_bd hf_val
      haf_valid haf_bd haf_val hab_valid hab_bd hab_val hfoot hz₀ heff_w h14000 (ω := ω)
      (pos := pos) (eid := e.eid) with
    ⟨mem_pre, regs_pa, pos_pa, c_pa, hrun_pa, hc_pa, hz_eff, hagree_pre, hrep_pre, hphi_pre,
      hcf_val, hcf_int, hcb_val, hcb_int, hfl_val, hfl_int, haf_val, haf_int, hab_val, hab_int,
      hr0, hr1, hr2, hr3, _, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr19, _⟩
  let mem₁ := Function.update mem_pre (nb - 1) hp_eff
  have hroom_re' : hp_eff + lctPhi L mem_pre b F.n +
      (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w := by
    rw [hphi_pre]; exact hroom_re
  rcases rerootExpose_link_runs p lp mem_pre hp_base hp_sp hexpose_eq hrep_pre hu hv
      (fun a ha => lt_of_lt_of_le (hfoot a ha) (by omega)) hz_eff (by omega : hp_caller ≤ hp_eff)
      hroom_re' ω (pos := pos_pa) with
    ⟨st₁, st₂, c_re, c_exp, l_v, rest_v, x₂, hrun_re, hrun_exp, hi₂, hsafe₂, hz₂, hle₂,
      hpp_v2, hpar_u2, _, hlast_v2, hbd_re, hrep₂, _, hslot_safe, hptr_safe, _, _, hmove₂⟩
  have hphi_re' : c_re + c_exp + (st₂.mem (nb - 1) - hp_eff) + lctPhi L st₂.mem b F.n ≤
      lctPhi L mem₀ b F.n + (C_REROOT_OP L + C_EXPOSE_OP L) * logN := by
    rw [← hphi_pre]; exact hbd_re
  have hnot_tv := link_not_sameComp_disjoint hi₂ hrep₂ hu hv hdisc hpar_u2 hlast_v2
  rcases link_find_u_tree hi₂ hu hnot_tv with
    ⟨t_u, rest_other, _, hperm_all, hu_in_tu, htu_free⟩
  have hroom_sp : st₂.mem (nb - 1) + 6000 * (L + 1) * (F.n + 2) < 2 ^ w :=
    link_splay_room_arith hle₂ hphi_re' hroom_re
  have harena_eff : nb + NODE_STRIDE * (cap + 1) ≤ hp_eff := by
    have : nb + NODE_STRIDE * (cap + 1) = lctArenaHi b cap := rfl
    omega
  rcases splay_expose_invs_runs p lp mem₁ st₂.mem hp_base hp_sp hslot_safe harena_eff hsafe₂ hi₂
      hperm_all hu_in_tu htu_free hroom_sp ω (pos := st₂.pos) with
    ⟨st₃, c_sp, t_u', hrun_sp, hi₃', hsafe₃, hroot_u, _, _, _, hrev_u3, _, _, hout_tu,
      hfr₃, hpar_sp, _, hbd_sp⟩
  have hpar_u3 : lctAuxParent st₃.mem nb cap (u + 1) = 0 := by
    rw [hpar_sp (u + 1)]; exact hpar_u2
  have hpp_v3 : nodeField st₃.mem nb (v + 1) OFF_PPAR = 0 := by
    have hnd_all2 : ((AuxTree.node (v + 1) l_v .leaf :: rest_v).flatMap AuxTree.toList).Nodup :=
      hi₂.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
    have hnd_p : ((t_u :: AuxTree.node (v + 1) l_v .leaf :: rest_other).flatMap AuxTree.toList).Nodup :=
      (link_perm_flatMap AuxTree.toList hperm_all.symm).nodup_iff.2 hnd_all2
    have hv_nin_tu : v + 1 ∉ t_u.toList := fun hm => by
      rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons] at hnd_p
      exact hnd_p.2.2 (v + 1) hm (v + 1) (List.mem_append.2 (Or.inl (by simp [AuxTree.toList]))) rfl
    have hv_cap : v + 1 ≤ cap := by unfold cap lctCap; omega
    rw [hout_tu (v + 1) hv_cap hv_nin_tu OFF_PPAR (by unfold OFF_PPAR NODE_STRIDE; omega)]
    exact hpp_v2
  rcases link_splayed_u_leaf_left hi₃' hroot_u hrev_u3 hpar_u3 with ⟨r_u, rfl, hpp_u3⟩
  have hfree_ne : x₀.freeEdges ≠ [] := hrep₀.freeEdges_ne_nil_of_lt (by omega)
  cases hfree_eq : x₀.freeEdges with
  | nil => exact absurd hfree_eq hfree_ne
  | cons ed free' =>
      rw [hfree_eq] at hi₃'
      have hed_bd := hi₃'.freeNodeOk ed List.mem_cons_self
      have hed_mem_rest : AuxTree.node ed .leaf .leaf ∈ rest_other := by
        have hm := hed_bd.2.2.1
        simp only [List.mem_cons] at hm
        rcases hm with heq | heq | hm
        · exfalso; have := congrArg AuxTree.rootId heq; dsimp [AuxTree.rootId] at this; omega
        · exfalso; have := congrArg AuxTree.rootId heq; dsimp [AuxTree.rootId] at this; omega
        · exact hm
      classical
      let rest_fin := rest_other.erase (AuxTree.node ed .leaf .leaf)
      have hperm_ro : rest_other.Perm (AuxTree.node ed .leaf .leaf :: rest_fin) :=
        List.perm_cons_erase hed_mem_rest
      have hperm_fin3 :
          (AuxTree.node (u + 1) .leaf r_u :: AuxTree.node (v + 1) l_v .leaf :: rest_other).Perm
          (AuxTree.node (u + 1) .leaf r_u :: AuxTree.node (v + 1) l_v .leaf ::
            AuxTree.node ed .leaf .leaf :: rest_fin) :=
        List.Perm.cons _ (List.Perm.cons _ hperm_ro)
      have hi₃ := lctExposeInvs_perm_trees hi₃' hperm_fin3
      have hfree_hdr : st₃.mem (b + LCT_HDR_FREE) = ed := hi₃.freeChain.1
      set nextFree := nodeField st₃.mem nb ed OFF_EU
      have hed1 : 1 ≤ ed := by omega
      have hed2 : ed ≤ cap := hed_bd.2.1
      have hucap : u + 1 ≤ cap := by unfold cap lctCap; omega
      let regs_sp_in :=
        Function.update (Function.update (Function.update regs_pa 25 0) 25 (v + 1)) 25 (u + 1)
      have hrs_ne25 : ∀ i, i ≠ 25 → regs_sp_in i = regs_pa i := fun i hi => by
        simp [regs_sp_in, Function.update_of_ne hi]
      rcases link_splice_runs
          ((hrs_ne25 0 (by decide)).trans hr0) ((hrs_ne25 1 (by decide)).trans hr1)
          ((hrs_ne25 2 (by decide)).trans hr2) ((hrs_ne25 3 (by decide)).trans hr3)
          ((hrs_ne25 10 (by decide)).trans hr10) ((hrs_ne25 11 (by decide)).trans hr11)
          ((hrs_ne25 12 (by decide)).trans hr12) ((hrs_ne25 13 (by decide)).trans hr13)
          ((hrs_ne25 14 (by decide)).trans hr14) ((hrs_ne25 15 (by decide)).trans hr15)
          ((hrs_ne25 16 (by decide)).trans hr16) ((hrs_ne25 19 (by decide)).trans hr19)
          rfl hfree_hdr rfl (by omega : nb + NODE_STRIDE * (cap + 1) < 2 ^ w)
          ⟨hed1, hed2⟩ hucap h14000 (p := p) (ω := ω) (pos := st₃.pos) with
        ⟨regs_sp, c_splice, hrun_splice, hc_splice, hrs0, hrs10, hrs21⟩
      set mem_w := lctLinkWriteMem st₃.mem nb b u v e.eid hp_caller (hp_caller + 6 * L)
        (hp_caller + L) (hp_caller + 2 * L) (hp_caller + 3 * L) nextFree ed
      have hpre_eq_caller : ∀ a, a < hp_caller ∨ hp_eff ≤ a → mem_pre a = mem₀ a := hagree_pre
      have hsafe₃_weak : SafeMem (Function.update mem₀ (nb - 1) hp_caller) nb cap hp_caller st₃.mem :=
        link_safeMem_weaken rfl (by omega : hp_caller ≤ hp_eff) harena_le hpre_eq_caller hsafe₃
      have hvcap : v + 1 ≤ cap := by unfold cap lctCap; omega
      have hsafe_w : SafeMem
          (Function.update (Function.update mem₀ (nb - 1) hp_caller) (b + LCT_HDR_FREE) nextFree)
          nb cap hp_caller mem_w :=
        lctLinkWriteMem_safeMem rfl harena_le hucap hvcap hed1 hed2
          (le_refl _) (by omega) (by omega) (by omega) (by omega) hsafe₃_weak
      have hnb_ge3 : 3 ≤ nb := lctNodesBase_ge3 b
      have hm3_eff : hp_eff ≤ st₃.mem (nb - 1) := le_trans hle₂ hfr₃.2.2.1
      have hm_w_hp : mem_w (nb - 1) = st₃.mem (nb - 1) := by
        have hnb_ne_free : nb - 1 ≠ b + LCT_HDR_FREE := by
          dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
        have hnb_lt_ed : nb - 1 < nb + NODE_STRIDE * ed :=
          lt_of_lt_of_le (by omega) (Nat.le_add_right nb _)
        have hnb_ne_par : nb - 1 ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT :=
          Nat.ne_of_lt (lt_of_lt_of_le (by omega)
            (le_trans (Nat.le_add_right nb _) (Nat.le_add_right _ _)))
        exact lctLinkWriteMem_outside hnb_ne_free (Or.inl hnb_lt_ed) hnb_ne_par
      have hm_w_L : mem_w (nb - 3) = L := by
        have h3_ne_free : nb - 3 ≠ b + LCT_HDR_FREE := by
          dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
        have h3_lt_ed : nb - 3 < nb + NODE_STRIDE * ed :=
          lt_of_lt_of_le (by omega) (Nat.le_add_right nb _)
        have h3_ne_par : nb - 3 ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT :=
          Nat.ne_of_lt (lt_of_lt_of_le (by omega)
            (le_trans (Nat.le_add_right nb _) (Nat.le_add_right _ _)))
        dsimp only [mem_w]
        rw [lctLinkWriteMem_outside h3_ne_free (Or.inl h3_lt_ed) h3_ne_par]
        exact hi₃.hdrL
      have hz_w : ZeroFrom mem_w (mem_w (nb - 1)) := by
        intro a ha
        rw [hm_w_hp] at ha
        have ha_eff : hp_eff ≤ a := le_trans hm3_eff ha
        have ha_arena : lctArenaHi b cap ≤ a := le_trans (le_trans harena_le (by omega)) ha_eff
        have hne_free : a ≠ b + LCT_HDR_FREE := by
          have : b + LCT_HDR_FREE < lctArenaHi b cap := by
            unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE; omega
          omega
        have hout_ed : nb + NODE_STRIDE * ed + NODE_STRIDE ≤ a := by
          have hm : NODE_STRIDE * (ed + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
          rw [Nat.mul_add, Nat.mul_one] at hm
          have : lctArenaHi b cap = nb + NODE_STRIDE * (cap + 1) := rfl
          omega
        have hne_par : a ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := by
          have hm : NODE_STRIDE * (u + 1) + OFF_PARENT < NODE_STRIDE * (cap + 1) := by
            have h1 := Nat.mul_le_mul_left NODE_STRIDE (by omega : (u + 1) + 1 ≤ cap + 1)
            rw [Nat.mul_add, Nat.mul_one] at h1
            unfold OFF_PARENT NODE_STRIDE at *; omega
          have : lctArenaHi b cap = nb + NODE_STRIDE * (cap + 1) := rfl
          omega
        dsimp only [mem_w]
        rw [lctLinkWriteMem_outside hne_free (Or.inr hout_ed) hne_par]
        exact hfr₃.2.2.2.2.1 a ha
      have hslot_w : SlotZeroOk mem_w nb := fun off hoff => by
        have ha_ne_free : nb + off ≠ b + LCT_HDR_FREE := by
          dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
        have ha_lt_ed : nb + off < nb + NODE_STRIDE * ed := by
          have hm : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ hed1
          omega
        have ha_ne_par : nb + off ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := by
          have hm : NODE_STRIDE ≤ NODE_STRIDE * (u + 1) := Nat.le_mul_of_pos_right _ (by omega)
          omega
        dsimp only [mem_w]
        rw [lctLinkWriteMem_outside ha_ne_free (Or.inl ha_lt_ed) ha_ne_par]
        exact hi₃.sf.2.2.2.2.2.2.2.1 off hoff
      have hmem₃_eff : ∀ a, hp_caller ≤ a → a < hp_eff → st₃.mem a = mem_pre a := fun a ha1 ha2 => by
        have h1 : nb + NODE_STRIDE * (cap + 1) ≤ a := le_trans harena_le ha1
        have heq := hsafe₃.2.1 a (Or.inr (Or.inr ⟨h1, ha2⟩))
        have hne_hp : a ≠ nb - 1 := by
          have : nb - 1 < lctArenaHi b cap := by
            dsimp only [nb]; unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega
          omega
        dsimp only [mem₁] at heq
        rw [heq, Function.update_of_ne hne_hp]
      have hagree_w_pre : ∀ a, hp_caller ≤ a → a < hp_eff → mem_w a = mem_pre a := fun a ha1 ha2 => by
        have h1 : lctArenaHi b cap ≤ a := le_trans harena_le ha1
        have hne_free : a ≠ b + LCT_HDR_FREE := by
          have : b + LCT_HDR_FREE < lctArenaHi b cap := by
            unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE; omega
          omega
        have hout_ed : nb + NODE_STRIDE * ed + NODE_STRIDE ≤ a := by
          have hm : NODE_STRIDE * (ed + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
          rw [Nat.mul_add, Nat.mul_one] at hm
          have : lctArenaHi b cap = nb + NODE_STRIDE * (cap + 1) := rfl
          omega
        have hne_par : a ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := by
          have hm : NODE_STRIDE * (u + 1) + OFF_PARENT < NODE_STRIDE * (cap + 1) := by
            have h1' := Nat.mul_le_mul_left NODE_STRIDE (by omega : (u + 1) + 1 ≤ cap + 1)
            rw [Nat.mul_add, Nat.mul_one] at h1'
            unfold OFF_PARENT NODE_STRIDE at *; omega
          have : lctArenaHi b cap = nb + NODE_STRIDE * (cap + 1) := rfl
          omega
        dsimp only [mem_w]
        rw [lctLinkWriteMem_outside hne_free (Or.inr hout_ed) hne_par]
        exact hmem₃_eff a ha1 ha2
      have h3_cf : Valid st₃.mem hp_caller h L ∧ intVal st₃.mem hp_caller h L = e.cost := by
        have hblk : ∀ i < L, st₃.mem (hp_caller + i) = mem_pre (hp_caller + i) := fun i hi =>
          hmem₃_eff (hp_caller + i) (by omega) (by omega)
        exact ⟨valid_agree_block hblk hcf_val, (intVal_agree_block hblk).trans hcf_int⟩
      have h3_cb : Valid st₃.mem (hp_caller + 6 * L) h L ∧
          intVal st₃.mem (hp_caller + 6 * L) h L = wrap h L (-e.cost) := by
        have hblk : ∀ i < L, st₃.mem (hp_caller + 6 * L + i) = mem_pre (hp_caller + 6 * L + i) :=
          fun i hi => hmem₃_eff (hp_caller + 6 * L + i) (by omega) (by omega)
        exact ⟨valid_agree_block hblk hcb_val, (intVal_agree_block hblk).trans hcb_int⟩
      have h3_fl : Valid st₃.mem (hp_caller + L) h L :=
        valid_agree_block (fun i hi => hmem₃_eff (hp_caller + L + i) (by omega) (by omega)) hfl_val
      have h3_af : Valid st₃.mem (hp_caller + 2 * L) h L :=
        valid_agree_block (fun i hi => hmem₃_eff (hp_caller + 2 * L + i) (by omega) (by omega)) haf_val
      have h3_ab : Valid st₃.mem (hp_caller + 3 * L) h L :=
        valid_agree_block (fun i hi => hmem₃_eff (hp_caller + 3 * L + i) (by omega) (by omega)) hab_val
      have hw_cf : Valid mem_w hp_caller h L ∧ intVal mem_w hp_caller h L = e.cost := by
        have hblk : ∀ i < L, mem_w (hp_caller + i) = mem_pre (hp_caller + i) := fun i hi =>
          hagree_w_pre (hp_caller + i) (by omega) (by omega)
        exact ⟨valid_agree_block hblk hcf_val, (intVal_agree_block hblk).trans hcf_int⟩
      have hw_cb : Valid mem_w (hp_caller + 6 * L) h L ∧
          intVal mem_w (hp_caller + 6 * L) h L = wrap h L (-e.cost) := by
        have hblk : ∀ i < L, mem_w (hp_caller + 6 * L + i) = mem_pre (hp_caller + 6 * L + i) :=
          fun i hi => hagree_w_pre (hp_caller + 6 * L + i) (by omega) (by omega)
        exact ⟨valid_agree_block hblk hcb_val, (intVal_agree_block hblk).trans hcb_int⟩
      have hw_fl : Valid mem_w (hp_caller + L) h L ∧
          ((intVal mem_w (hp_caller + L) h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.flow := by
        have hblk : ∀ i < L, mem_w (hp_caller + L + i) = mem_pre (hp_caller + L + i) :=
          fun i hi => hagree_w_pre (hp_caller + L + i) (by omega) (by omega)
        exact ⟨valid_agree_block hblk hfl_val, by rw [intVal_agree_block hblk]; exact hfl_int⟩
      have hw_af : Valid mem_w (hp_caller + 2 * L) h L ∧
          ((intVal mem_w (hp_caller + 2 * L) h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availFwd := by
        have hblk : ∀ i < L, mem_w (hp_caller + 2 * L + i) = mem_pre (hp_caller + 2 * L + i) :=
          fun i hi => hagree_w_pre (hp_caller + 2 * L + i) (by omega) (by omega)
        exact ⟨valid_agree_block hblk haf_val, by rw [intVal_agree_block hblk]; exact haf_int⟩
      have hw_ab : Valid mem_w (hp_caller + 3 * L) h L ∧
          ((intVal mem_w (hp_caller + 3 * L) h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availBwd := by
        have hblk : ∀ i < L, mem_w (hp_caller + 3 * L + i) = mem_pre (hp_caller + 3 * L + i) :=
          fun i hi => hagree_w_pre (hp_caller + 3 * L + i) (by omega) (by omega)
        exact ⟨valid_agree_block hblk hab_val, by rw [intVal_agree_block hblk]; exact hab_int⟩
      rcases link_pull_room_arith hphi_re' hbd_sp hle₂ hfr₃.2.2.1 hlog_pos hroom with
        ⟨hs3_lt_room, hsp_room_lt⟩
      have hed_nin_tu : ed ∉ (AuxTree.node (u + 1) .leaf r_u).toList := fun hm => by
        have hnd3 := hi₃.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
        rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append,
          List.flatMap_cons, List.nodup_append] at hnd3
        exact hnd3.2.2 ed hm ed (List.mem_append.2 (Or.inr (List.mem_append.2
          (Or.inl (by simp [AuxTree.toList]))))) rfl
      have htu_tok := (hi₃.sf.trees_ok (.node (u + 1) .leaf r_u) (by simp)).2.2
      have htu_nd : (AuxTree.node (u + 1) .leaf r_u).toList.Nodup := by
        have hnd3 := hi₃.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
        rw [List.flatMap_cons, List.nodup_append] at hnd3
        exact hnd3.1
      have hs3_lt_w : st₃.mem (nb - 1) < 2 ^ w :=
        lt_of_le_of_lt (Nat.le_add_right _ (4 * L)) hs3_lt_room
      have hm3_lt_w : mem_w (nb - 1) < 2 ^ w := by rw [hm_w_hp]; exact hs3_lt_w
      have hcap_hp : cap < hp_caller := by
        have : cap < lctArenaHi b cap := by
          unfold lctArenaHi lctNodesBase NODE_STRIDE
          have hm : 1 ≤ NODE_STRIDE := by unfold NODE_STRIDE; omega
          have := Nat.le_mul_of_pos_left (cap + 1) hm
          omega
        exact lt_of_lt_of_le this harena_le
      have hu_lt_w : u < 2 ^ w := by
        have : u < cap := by unfold u cap lctCap; omega
        omega
      have hv_lt_w : v < 2 ^ w := by
        have : v < cap := by unfold v cap lctCap; omega
        omega
      have hcf_hi : hp_caller + L ≤ st₃.mem (nb - 1) := le_trans (by omega) hm3_eff
      have hcb_lo : nb + NODE_STRIDE * (lctCap F.n + 1) ≤ hp_caller + 6 * L :=
        le_trans harena_le (by omega)
      have hcb_hi : hp_caller + 6 * L + L ≤ st₃.mem (nb - 1) := le_trans (by omega) hm3_eff
      have hfl_lo : nb + NODE_STRIDE * (lctCap F.n + 1) ≤ hp_caller + L :=
        le_trans harena_le (by omega)
      have hfl_hi : hp_caller + L + L ≤ st₃.mem (nb - 1) := le_trans (by omega) hm3_eff
      have haf_lo : nb + NODE_STRIDE * (lctCap F.n + 1) ≤ hp_caller + 2 * L :=
        le_trans harena_le (by omega)
      have haf_hi : hp_caller + 2 * L + L ≤ st₃.mem (nb - 1) := le_trans (by omega) hm3_eff
      have hab_lo : nb + NODE_STRIDE * (lctCap F.n + 1) ≤ hp_caller + 3 * L :=
        le_trans harena_le (by omega)
      have hab_hi : hp_caller + 3 * L + L ≤ st₃.mem (nb - 1) := le_trans (by omega) hm3_eff
      have htu_tok' : TreeMemMatch w h L st₃.mem nb (lctCap F.n) (.node (u + 1) .leaf r_u) 0 0 := by
        dsimp [AuxTree.rootId] at htu_tok; rw [hpp_u3] at htu_tok; exact htu_tok
      have hpull_pre : PullPre w h L mem_w nb cap ed .leaf (.node (u + 1) .leaf r_u) 0 (v + 1) :=
        lctLink_pullPre rfl hed1 hed2 hu hv hs3_lt_w
          (le_trans harena_le (le_trans (by omega : hp_caller ≤ hp_eff) hm3_eff))
          heid_w hu_lt_w hv_lt_w
          ⟨harena_le, hcf_hi, h3_cf.1, h3_cf.2⟩
          ⟨hcb_lo, hcb_hi, h3_cb.1, h3_cb.2⟩
          ⟨hfl_lo, hfl_hi, h3_fl⟩
          ⟨haf_lo, haf_hi, h3_af⟩
          ⟨hab_lo, hab_hi, h3_ab⟩
          hfit_e.1 htu_tok' hpp_u3 htu_nd hed_nin_tu
      let mem_safe_free :=
        Function.update (Function.update mem₀ (nb - 1) hp_caller) (b + LCT_HDR_FREE) nextFree
      have hslot_sf : SlotZeroOk mem_safe_free nb := fun off hoff => by
        have h1 : nb + off ≠ b + LCT_HDR_FREE := by
          dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
        have h2 : nb + off ≠ nb - 1 := by omega
        dsimp only [mem_safe_free]
        rw [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hrep₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 off hoff
      have hnb3_lt : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := by
        have : nb + NODE_STRIDE * (cap + 1) = lctArenaHi b cap := rfl
        omega
      rcases pull_lct_runs p lp.splay mem_safe_free mem_w hp_base.splay_hasAt hp_sp hp_base.splay_ok
          hnb3_lt hnb_ge3 hm_w_L harena_le hslot_sf hsafe_w
          (by rw [hm_w_hp]; exact le_trans harena_le (le_trans (by omega : hp_caller ≤ hp_eff) hm3_eff))
          hz_w (by rw [hm_w_hp]; exact hs3_lt_room)
          hslot_w hed2 (by simp [AuxTree.toList]) hed_nin_tu hpull_pre ω (pos := st₃.pos) with
        ⟨st_p, c_pu, hrun_pu, hsafe_p, hpu_cost, hpu_lo, hpu_cap, htm_p, hout_p, hnonAgg_p, hfr_p⟩
      have hpu_cost' : c_pu + (st_p.mem (nb - 1) - st₃.mem (nb - 1)) ≤ K_PULL L := by
        rw [hm_w_hp] at hpu_cost; exact hpu_cost
      have hpu_le3 : st₃.mem (nb - 1) ≤ st_p.mem (nb - 1) := by
        rw [hm_w_hp] at hpu_lo; exact hpu_lo
      have hfin_lt_w : st_p.mem (nb - 1) + 1 < 2 ^ w :=
        link_fin_lt_arith hpu_le3 hpu_cost' hsp_room_lt
      have hs3_p1_lt_w : st₃.mem (nb - 1) + 1 < 2 ^ w := by omega
      have hag_mem1 : ∀ a, a < b ∨ lctArenaHi b cap ≤ a ∧ a < hp_eff → mem₁ a = mem_pre a := fun a ha => by
        have h1 : b ≤ nb - 1 := by dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE; omega
        have h2 : nb - 1 < lctArenaHi b cap := by
          dsimp only [nb]; unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega
        have hne : a ≠ nb - 1 := by rcases ha with ha | ha <;> omega
        simp [mem₁, Function.update_of_ne hne]
      have hrep₃ : LctMemRep w h L P b F
          { n := F.n, trees := AuxTree.node (u + 1) .leaf r_u :: AuxTree.node (v + 1) l_v .leaf ::
              AuxTree.node ed .leaf .leaf :: rest_fin,
            freeEdges := ed :: free', edgeMap := x₀.edgeMap,
            regions := x₀.regions ++ [(hp_eff, st₃.mem (nb - 1) + 1)],
            hpHi := st₃.mem (nb - 1) + 1 } st₃.mem :=
        (exitOp_rep (space := st₃.mem (nb - 1) + 1) hrep_pre
          (fun a ha => lt_of_lt_of_le (hfoot a ha) (by omega)) le_rfl rfl hrep_pre.valid
          hrep_pre.edgeFits hslot_safe hptr_safe hag_mem1 hsafe₃ hi₃.sf hi₃.hdrN hi₃.hdrCap
          hi₃.hdrL hi₃.hdrP hrep_pre.edgeMap_snd_perm
          (by rw [← hfree_eq]; exact hrep_pre.slots_perm)
          hi₃.freeChain hi₃.freeNodeOk hi₃.vertexOk hi₃.edgeOk hi₃.auxPathOk hi₃.subdivOk
          hs3_p1_lt_w (Nat.le_add_left _ _) (fun _ _ => rfl)).1
      have hrev_u3' : nodeField st₃.mem nb (u + 1) OFF_REV = 0 := by
        simpa [revFlag] using hrev_u3
      have hm_w_hp' : lctLinkWriteMem st₃.mem (lctNodesBase b) b e.u e.v e.eid hp_caller
          (hp_caller + 6 * L) (hp_caller + L) (hp_caller + 2 * L) (hp_caller + 3 * L) nextFree ed
          (lctNodesBase b - 1) = st₃.mem (nb - 1) := hm_w_hp
      rcases link_invs_after_pull (F := F) (e := e)
          (rfl : (F.link e).n = F.n) rfl rfl hu hv hdisc hfit_e hrep₀.valid
          hrep₀.edgeMap_snd_perm (by rw [← hfree_eq]; exact hrep₀.slots_perm)
          hrep₃ hi₃ hrev_u3' hpar_u3 rfl
          ⟨harena_le, by rw [hm_w_hp']; exact hcf_hi⟩
          ⟨hcb_lo, by rw [hm_w_hp']; exact hcb_hi⟩
          ⟨hfl_lo, by rw [hm_w_hp']; exact hfl_hi⟩
          ⟨haf_lo, by rw [hm_w_hp']; exact haf_hi⟩
          ⟨hab_lo, by rw [hm_w_hp']; exact hab_hi⟩
          hw_cf.2 hw_fl.2 hw_af.2 hw_ab.2 (Nat.lt_of_succ_lt hfin_lt_w)
          htm_p hout_p hnonAgg_p hfr_p hfree_hdr rfl with
        ⟨hi_p, hpar_eq, _, hrest_agree, _, hpp_ed_p⟩
      have hpp_vp : nodeField st_p.mem nb (v + 1) OFF_PPAR = 0 := by
        have hv_addr_lt : nb + NODE_STRIDE * (v + 1) + OFF_PPAR < mem_w (nb - 1) := by
          have hm : NODE_STRIDE * (v + 1) + OFF_PPAR < NODE_STRIDE * (cap + 1) := by
            have h1 := Nat.mul_le_mul_left NODE_STRIDE (by omega : (v + 1) + 1 ≤ cap + 1)
            rw [Nat.mul_add, Nat.mul_one] at h1
            unfold OFF_PPAR NODE_STRIDE at *; omega
          rw [hm_w_hp]
          have : nb + NODE_STRIDE * (cap + 1) = lctArenaHi b cap := rfl
          omega
        have hv_ne_hp : nb + NODE_STRIDE * (v + 1) + OFF_PPAR ≠ nb - 1 := by
          have hm : NODE_STRIDE ≤ NODE_STRIDE * (v + 1) := Nat.le_mul_of_pos_right _ (by omega)
          omega
        have hv_out_ed : nb + NODE_STRIDE * (v + 1) + OFF_PPAR < nb + NODE_STRIDE * ed ∨
            nb + NODE_STRIDE * ed + NODE_STRIDE ≤ nb + NODE_STRIDE * (v + 1) + OFF_PPAR := by
          left
          have hm1 : NODE_STRIDE * (v + 1) + OFF_PPAR < NODE_STRIDE * (v + 2) := by
            rw [Nat.mul_add, Nat.mul_one]; unfold OFF_PPAR NODE_STRIDE at *; omega
          have hm2 : NODE_STRIDE * (v + 2) ≤ NODE_STRIDE * ed :=
            Nat.mul_le_mul_left _ (by omega : v + 2 ≤ ed)
          omega
        have heq1 : nodeField st_p.mem nb (v + 1) OFF_PPAR = nodeField mem_w nb (v + 1) OFF_PPAR :=
          hout_p _ hv_ne_hp hv_out_ed hv_addr_lt
        have heq2 : nodeField mem_w nb (v + 1) OFF_PPAR = nodeField st₃.mem nb (v + 1) OFF_PPAR :=
          lctLinkWriteMem_nodeField_other rfl (by omega) (by unfold OFF_PPAR NODE_STRIDE; omega)
            (by omega) (fun _ => by unfold OFF_PPAR OFF_PARENT; decide)
        rw [heq1, heq2]
        exact hpp_v3
      have hi_p' : LctExposeInvs w h L P b F.n free' ((ed, e) :: x₀.edgeMap)
          (AuxTree.node ed .leaf (AuxTree.node (u + 1) .leaf r_u) ::
            AuxTree.node (v + 1) l_v .leaf :: rest_fin) st_p.mem := hi_p
      have hphi_fin := link_phi_le hi₃ hi_p' hpar_eq hrest_agree hpp_u3 hpar_u3 hpp_v3 hpp_vp hpp_ed_p
      have hhp_off_w : LCT_HDR_HP < 2 ^ w := by unfold LCT_HDR_HP; omega
      have hbh_lt_w : b + LCT_HDR_HP < 2 ^ w := by
        have : b + LCT_HDR_HP = nb - 1 := by
          dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
        have : nb - 1 < nb + NODE_STRIDE * (cap + 1) := by
          unfold NODE_STRIDE; omega
        omega
      have hbh_eq : b + LCT_HDR_HP = nb - 1 := by
        dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
      let regs_pu := Function.update regs_sp 25 0
      have hr0_pu : regs_pu 0 = b := by simp [regs_pu, Function.update_of_ne, hrs0]
      have hassign26 :
          Runs w p ω (.assign 26 (.load (.bin .add (.reg 0) (.const LCT_HDR_HP))))
            { mem := st_p.mem, regs := regs_pu, pos := st_p.pos } .normal
            { mem := st_p.mem, regs := Function.update regs_pu 26 (st_p.mem (nb - 1)),
              pos := st_p.pos } 5 :=
        runs_assign_iff.2 ⟨st_p.mem (nb - 1),
          Expr.eval_load_mem (Expr.eval_add (by simp [Expr.eval_reg, hr0_pu])
            (Expr.eval_const hhp_off_w) hbh_lt_w) (by simp [hbh_eq]),
          rfl, rfl, by simp [Expr.size]⟩
      have hret :
          Runs w p ω (.ret (.bin .add (.reg 26) (.const 1)))
            { mem := st_p.mem, regs := Function.update regs_pu 26 (st_p.mem (nb - 1)),
              pos := st_p.pos }
            (.returned (st_p.mem (nb - 1) + 1))
            { mem := st_p.mem, regs := Function.update regs_pu 26 (st_p.mem (nb - 1)),
              pos := st_p.pos } 4 :=
        runs_ret_iff.2 ⟨st_p.mem (nb - 1) + 1,
          Expr.eval_add (by simp [Expr.eval_reg]) (Expr.eval_const (by omega : 1 < 2 ^ w))
            hfin_lt_w,
          rfl, rfl, by simp [Expr.size]⟩
      have heval_re : evalArgs w
          { mem := Function.update mem_pre (nb - 1) hp_eff, regs := regs_pa, pos := pos_pa }
          [.reg 10, .reg 11] = some [nb, u + 1] :=
        WordRAM.evalArgs_cons (by simp [Expr.eval_reg, hr10]; rfl)
          (WordRAM.evalArgs_cons (by simp [Expr.eval_reg, hr11]; rfl) (WordRAM.evalArgs_nil w _))
      have heval_exp : evalArgs w
          { mem := st₁.mem, regs := Function.update regs_pa 25 0, pos := st₁.pos }
          [.reg 10, .reg 12] = some [nb, v + 1] :=
        WordRAM.evalArgs_cons (by simp [Expr.eval_reg, hr10]; rfl)
          (WordRAM.evalArgs_cons (by simp [Expr.eval_reg, hr12]; rfl) (WordRAM.evalArgs_nil w _))
      have heval_sp : evalArgs w
          { mem := st₂.mem, regs := Function.update (Function.update regs_pa 25 0) 25 (v + 1),
            pos := st₂.pos } [.reg 10, .reg 11] = some [nb, u + 1] :=
        WordRAM.evalArgs_cons (by simp [Expr.eval_reg, hr10]; rfl)
          (WordRAM.evalArgs_cons (by simp [Expr.eval_reg, hr11]; rfl) (WordRAM.evalArgs_nil w _))
      have heval_pu : evalArgs w { mem := mem_w, regs := regs_sp, pos := st₃.pos }
          [.reg 10, .reg 21] = some [nb, ed] :=
        WordRAM.evalArgs_cons (by simp [Expr.eval_reg, hrs10]; rfl)
          (WordRAM.evalArgs_cons (by simp [Expr.eval_reg, hrs21]) (WordRAM.evalArgs_nil w _))
      have hpu_chain := link_runs_seq_call_runs heval_pu hp_base.splay_ok.pull_eq hrun_pu
        (link_runs_seq_normal hassign26 hret)
      have hsp_chain := link_runs_seq_normal hrun_splice hpu_chain
      have hsplay_chain := link_runs_seq_call_runs heval_sp hp_base.splay_ok.splay_eq hrun_sp hsp_chain
      have hexp_chain := link_runs_seq_call_runs heval_exp hexpose_eq hrun_exp hsplay_chain
      have hre_chain := link_runs_seq_call_runs heval_re hreroot_eq hrun_re hexp_chain
      have hbody_run : Runs w p ω (lctLinkBody lp)
          (startState [b, e.u, e.v, e.eid, cPtr, fPtr, afPtr, abPtr, hp_caller] mem₀ pos)
          (.returned (st_p.mem (nb - 1) + 1)) _ _ :=
        link_runs_seq_normal hrun_pa hre_chain
      have hmem_safe_free_agree : ∀ a, a < b ∨ lctArenaHi b cap ≤ a ∧ a < hp_caller →
          mem_safe_free a = mem₀ a := fun a ha => by
        have hne1 : a ≠ b + LCT_HDR_FREE := by
          have : b + LCT_HDR_FREE < lctArenaHi b cap := by
            unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE; omega
          rcases ha with ha | ha <;> omega
        have hne2 : a ≠ nb - 1 := by
          have h1 : b ≤ nb - 1 := by dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE; omega
          have h2 : nb - 1 < lctArenaHi b cap := by
            dsimp only [nb]; unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega
          rcases ha with ha | ha <;> omega
        simp [mem_safe_free, Function.update_of_ne hne1, Function.update_of_ne hne2]
      have hptr_safe_free : PtrFootOk b mem_safe_free x₀ L := by
        intro u' hu' off hoff
        have hmem_node : nodeField mem_safe_free nb u' off = nodeField mem₀ nb u' off := by
          have hne1 : nb + NODE_STRIDE * u' + off ≠ b + LCT_HDR_FREE := by
            dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
          have hne2 : nb + NODE_STRIDE * u' + off ≠ nb - 1 := by omega
          dsimp only [nodeField, mem_safe_free]
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        have hheap_le : mem₀ (nb - 1) ≤ mem_safe_free (nb - 1) := by
          have hne1 : nb - 1 ≠ b + LCT_HDR_FREE := by
            dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
          simp only [mem_safe_free, Function.update_of_ne hne1, Function.update_self]
          have hlt0 := hrep₀.2.2.2.2.2.2.1
          have hm0 := hrep₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          rw [hbh_eq] at hm0
          have hft := hfoot (x₀.hpHi - 1) hrep₀.2.2.2.2.2.2.2.1
          omega
        have hmem_node' : nodeField mem_safe_free (lctNodesBase b) u' off =
            nodeField mem₀ (lctNodesBase b) u' off := hmem_node
        have hheap_le' : mem₀ (lctNodesBase b - 1) ≤ mem_safe_free (lctNodesBase b - 1) := hheap_le
        rcases hrep₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 u' hu' off hoff with
          h0 | ⟨ha1, ha2, ha3⟩
        · left; rw [hmem_node']; exact h0
        · right; rw [hmem_node']
          exact ⟨ha1, le_trans ha2 hheap_le', ha3⟩
      have hargsz1 : argsSize [.reg 10, .reg 11] = 2 := by decide
      have hargsz2 : argsSize [.reg 10, .reg 12] = 2 := by decide
      have hargsz3 : argsSize [.reg 10, .reg 21] = 2 := by decide
      have hc_tot_bd : c_pa + (argsSize [.reg 10, .reg 11] + c_re + 1 +
          (argsSize [.reg 10, .reg 12] + c_exp + 1 +
          (argsSize [.reg 10, .reg 11] + c_sp + 1 +
          (c_splice + (argsSize [.reg 10, .reg 21] + c_pu + 1 + (5 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤
          c_pa + c_re + c_exp + c_sp + c_splice + c_pu + 60 := by
        rw [hargsz1, hargsz2, hargsz3]
        exact link_c_tot_arith c_pa c_re c_exp c_sp c_splice c_pu
      have hfin_cost := link_final_budget_arith (s2 := st₂.mem (nb - 1)) (s3 := st₃.mem (nb - 1))
        (s_p := st_p.mem (nb - 1)) (hp := hp_caller) (L := L)
        (phi0 := lctPhi L mem₀ b F.n) (phi2 := lctPhi L st₂.mem b F.n)
        (phi3 := lctPhi L st₃.mem b F.n) (phi_p := lctPhi L st_p.mem b F.n)
        (c_pa := c_pa) (c_re := c_re) (c_exp := c_exp) (c_sp := c_sp) (c_splice := c_splice)
        (c_pu := c_pu) hc_tot_bd hc_pa hc_splice hphi_re' hbd_sp
        hpu_cost' hphi_fin hle₂ hfr₃.2.2.1 hpu_le3 hlog_pos hroom hspace
      have hedge_fits_link : ∀ e' ∈ (F.link e).edges, EdgeFits h L P e' := fun e' he' => by
        simp only [MathForest.link, List.mem_cons] at he'
        rcases he' with rfl | he'
        · exact hfit_e
        · exact hrep₀.edgeFits e' he'
      have hexit := exitOp_rep (F0 := F) (F1 := F.link e) (x0 := x₀) (mem0 := mem₀)
        (mem_safe := mem_safe_free) (mem_end := st_p.mem) (mem_fin := st_p.mem)
        (trees1 := AuxTree.node ed .leaf (AuxTree.node (u + 1) .leaf r_u) ::
          AuxTree.node (v + 1) l_v .leaf :: rest_fin)
        (freeEdges1 := free') (edgeMap1 := (ed, e) :: x₀.edgeMap)
        hrep₀ hfoot (le_refl hp_caller) rfl
        (MathForest.link_valid hrep₀.valid hu hv hdisc heid_fresh)
        hedge_fits_link hslot_sf hptr_safe_free hmem_safe_free_agree hsafe_p
        hi_p.sf hi_p.hdrN hi_p.hdrCap hi_p.hdrL hi_p.hdrP
        (List.Perm.cons e hrep₀.edgeMap_snd_perm)
        (by
          have hp0 := hrep₀.slots_perm
          rw [hfree_eq] at hp0
          dsimp only [MathForest.link]
          exact ((List.perm_middle (l₁ := List.map Prod.fst x₀.edgeMap) (l₂ := free') (a := ed)).symm).trans hp0)
        hi_p.freeChain hi_p.freeNodeOk hi_p.vertexOk hi_p.edgeOk hi_p.auxPathOk hi_p.subdivOk
        hfin_cost.1 hfin_cost.2.1 (fun _ _ => rfl)
      have hpar_pre : ∀ z, lctAuxParent mem₀ nb cap z = lctAuxParent mem_pre nb cap z :=
        lctAuxParent_agree (fun i _ hi => hagree_pre i (Or.inl (lt_of_lt_of_le hi harena_le)))
      have hmove₀ : RootMove (lctAuxParent mem₀ nb cap) (lctAuxParent st₂.mem nb cap) cap
          (u + 1) := (funext hpar_pre) ▸ hmove₂
      have hedge_lt : ∀ q ∈ x₀.edgeMap, q.2.u < F.n ∧ q.2.v < F.n := fun q hq => by
        have he := hrep₀.valid.1 q.2 (hrep₀.edgeMap_snd_perm.mem_iff.1 (List.mem_map.2 ⟨q, hq, rfl⟩))
        exact ⟨he.1, he.2.1⟩
      have hno_ed₃ := lctLink_par_notin_free hi₃ (by rw [← hfree_eq]; exact hrep₀.slots_perm)
        hedge_lt (List.mem_cons_self)
      have hroots := link_canonRoot (ed := ed) hrep₀ hrep₂ hu hv hdisc hmove₀ hi_p'.subdivOk.1
        (fun z => by rw [hpar_eq z, hpar_sp z])
        (fun z => by rw [← hpar_sp z]; exact hno_ed₃ z) hed_bd.1 hed_bd.2.1 hpar_u2
      exact ⟨st_p.mem (nb - 1) + 1, _, _, _, hbody_run, hexit.1, hexit.2.1, by
        simpa [MathForest.link, hexit.2.2] using hfin_cost.2.2, hroots⟩

end LinkMain

end MinCostFlow.LinkCut.Prog
