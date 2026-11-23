module

public import MinCostFlow.LowStretch.ProgKruskal

/-!
# Kruskal's merge tree: the whole run

`krP` starts with every vertex alone and then calls `kstP` on the pairs `L`, read as
`KEYS[i] mod Mo` for `i < c`. At the end the memory holds `krun G L` (`krP_spec`). When `L` is
sorted by weight and covers every pair, `krun G L` is a merge tree (`krun_ok`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {G : PG}

/-- The pairs that `krP` processes, in order. -/
def kL (mem : ℕ → ℕ) (KEYS Mo c : ℕ) : List ℕ := (List.range c).map (fun i => mem (KEYS + i) % Mo)

theorem kL_length (mem : ℕ → ℕ) (KEYS Mo c : ℕ) : (kL mem KEYS Mo c).length = c := by simp [kL]

theorem kL_getElem (mem : ℕ → ℕ) (KEYS Mo c i : ℕ) (hi : i < (kL mem KEYS Mo c).length) :
    (kL mem KEYS Mo c)[i] = mem (KEYS + i) % Mo := by simp [kL]

theorem krun_take_succ (L : List ℕ) {i : ℕ} (hi : i < L.length) :
    krun G (L.take (i + 1)) = kstep G (krun G (L.take i)) L[i] := by
  unfold krun
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-- Every prefix of the run satisfies the invariant. -/
theorem inv_prefix {L : List ℕ} (hL : ∀ q ∈ L, q < G.m) (hsort : L.Pairwise (G.pω · ≤ G.pω ·))
    (hcov : ∀ p < G.m, ∃ r0 ∈ L, KS.SameEnds G p r0 ∧ G.pω r0 ≤ G.pω p)
    (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) :
    ∀ i ≤ L.length, (krun G (L.take i)).Inv G (L.take i) (L.drop i) := by
  intro i
  induction i with
  | zero => intro _; simpa [krun] using KS.inv_init (G := G) L
  | succ i ih =>
    intro hi
    have hi' : i < L.length := by omega
    have h := ih (by omega)
    rw [List.drop_eq_getElem_cons hi'] at h
    have hqm := hL _ (List.getElem_mem hi')
    have hs : ∀ q' ∈ L.drop (i + 1), G.pω L[i] ≤ G.pω q' := by
      have := hsort.sublist (List.drop_sublist i L)
      rw [List.drop_eq_getElem_cons hi'] at this
      exact (List.pairwise_cons.mp this).1
    have hcov' : ∀ p < G.m, ∃ r0 ∈ L.take i ++ L[i] :: L.drop (i + 1),
        KS.SameEnds G p r0 ∧ G.pω r0 ≤ G.pω p := by
      rw [← List.drop_eq_getElem_cons hi', List.take_append_drop]; exact hcov
    have h' := h.step (hG _ hqm) hqm hcov' hs hG
    rw [krun_take_succ L hi', List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some]
    exact h'

/-- The registers of `krP` that never change. -/
def KR (E : KL) (c KEYS Mo IN PW : ℕ) (st : State) : Prop :=
  st.regs 0 = E.n ∧ st.regs 1 = c ∧ st.regs 2 = KEYS ∧ st.regs 3 = Mo ∧ st.regs 4 = IN ∧
    st.regs 5 = PW ∧ st.regs 6 = E.UF ∧ st.regs 7 = E.SZ ∧ st.regs 8 = E.TN ∧ st.regs 9 = E.KPAR ∧
    st.regs 10 = E.KCH1 ∧ st.regs 11 = E.KCH2 ∧ st.regs 12 = E.KMW ∧ st.regs 13 = E.KMP

theorem KR.upd {E : KL} {c KEYS Mo IN PW : ℕ} {st : State} (h : KR E c KEYS Mo IN PW st) {r : ℕ}
    (hr : 14 ≤ r) (v : ℕ) : KR E c KEYS Mo IN PW { st with regs := Function.update st.regs r v } := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)

theorem KR.mem {E : KL} {c KEYS Mo IN PW : ℕ} {st : State} (h : KR E c KEYS Mo IN PW st)
    (M : ℕ → ℕ) : KR E c KEYS Mo IN PW { st with mem := M } := h

/-- The body of the first loop: vertex `i` alone. -/
def krInit : Stmt :=
  .seq (.store (.bin .add (.reg 6) (.reg 15)) (.reg 15))
  (.seq (.store (.bin .add (.reg 7) (.reg 15)) (.const 1))
  (.seq (.store (.bin .add (.reg 8) (.reg 15)) (.reg 15))
  (.seq (.store (.bin .add (.reg 9) (.reg 15)) (.reg 15))
  (.store (.bin .add (.reg 12) (.reg 15)) (.const 0)))))

/-- `krP bK` with `args = n :: c :: KEYS :: Mo :: IN :: PW :: E.arr`; `kstP` sits at `bK`. It
returns the number of nodes. -/
def krP (bK : ℕ) : Stmt :=
  .seq (forRange 15 (.const 0) (.reg 0) krInit)
  (.seq (.assign 14 (.reg 0))
  (.seq (forRange 15 (.const 0) (.reg 1)
    (.call 14 bK [.bin .mod (.load (.bin .add (.reg 2) (.reg 15))) (.reg 3), .reg 14, .reg 4,
      .reg 5, .reg 0, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13]))
  (.ret (.reg 14))))

theorem krP_noRand (bK : ℕ) : (krP bK).NoRand := by
  simp [krP, krInit, forRange, forUp, Stmt.NoRand]

/-- The contract of `krP` for the graph `G`. -/
def krC (w : ℕ) (G : PG) : Contract where
  pre args mem := ∃ c KEYS Mo IN PW : ℕ, ∃ E : KL,
    args = E.n :: c :: KEYS :: Mo :: IN :: PW :: E.arr ∧ E.Lay ∧ E.n = G.n ∧
    (∀ q ∈ kL mem KEYS Mo c, q < G.m) ∧
    (kL mem KEYS Mo c).Pairwise (G.pω · ≤ G.pω ·) ∧
    (∀ p < G.m, ∃ r0 ∈ kL mem KEYS Mo c, KS.SameEnds G p r0 ∧ G.pω r0 ≤ G.pω p) ∧
    (∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) ∧
    (∀ q < G.m, mem (IN + 3 * q) = G.pu q ∧ mem (IN + 3 * q + 1) = G.pv q ∧
      mem (PW + q) = G.pω q) ∧
    (∀ i < c, mem (KEYS + i) < 2 ^ w) ∧
    IN + 3 * G.m ≤ E.UF ∧ PW + G.m ≤ E.UF ∧ KEYS + c ≤ E.UF ∧ 1 ≤ E.n ∧ E.KMP + 2 * E.n < 2 ^ w
  post args mem v mem' := ∀ c KEYS Mo IN PW : ℕ, ∀ E : KL,
    args = E.n :: c :: KEYS :: Mo :: IN :: PW :: E.arr →
    v = (krun G (kL mem KEYS Mo c)).T.N ∧ (∃ dep, KRep mem' E (krun G (kL mem KEYS Mo c)) dep) ∧
    ∀ a, (a < E.UF ∨ E.KMP + 2 * E.n ≤ a) → mem' a = mem a
  cost args _ := 100 * (args.getD 0 0 + 1) +
    args.getD 1 0 * (40 * Nat.log 2 (args.getD 0 0) + 400)

theorem KL.eq_of_args6 {E E' : KL} {a b c d e a' b' c' d' e' : ℕ}
    (h : E.n :: a :: b :: c :: d :: e :: E.arr = E'.n :: a' :: b' :: c' :: d' :: e' :: E'.arr) :
    E' = E ∧ a' = a ∧ b' = b ∧ c' = c ∧ d' = d ∧ e' = e := by
  cases E; cases E'; simp only [KL.arr, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := h
  subst_vars; simp

theorem ufRoots_all {M : ℕ → ℕ} {UF n : ℕ} (h : ∀ x < n, M (UF + x) = x) :
    (ufRoots M UF n).card = n := by
  unfold ufRoots
  rw [Finset.filter_true_of_mem (fun x hx => h x (Finset.mem_range.mp hx))]
  simp

/-- What the first loop has written after the vertices below `i`. -/
def KInit (E : KL) (M : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ v < i, M (E.UF + v) = v ∧ M (E.SZ + v) = 1 ∧ M (E.TN + v) = v ∧ M (E.KPAR + v) = v ∧
    M (E.KMW + v) = 0

theorem KInit.step {E : KL} {M : ℕ → ℕ} {i : ℕ} (h : KInit E M i) (hl : E.Lay) (hi : i < E.n) :
    KInit E (Function.update (Function.update (Function.update (Function.update (Function.update M
      (E.UF + i) i) (E.SZ + i) 1) (E.TN + i) i) (E.KPAR + i) i) (E.KMW + i) 0) (i + 1) := by
  have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4; have l5 := hl.l5
  have l6 := hl.l6
  unfold KInit at h ⊢
  intro v hv
  by_cases hvi : v = i
  · subst hvi
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_self]
  · obtain ⟨z1, z2, z3, z4, z5⟩ := h v (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)] <;> assumption

theorem KInit.out {E : KL} {M : ℕ → ℕ} {i a : ℕ} (hl : E.Lay) (hi : i < E.n)
    (ha : a < E.UF ∨ E.KMP + 2 * E.n ≤ a) :
    (Function.update (Function.update (Function.update (Function.update (Function.update M
      (E.UF + i) i) (E.SZ + i) 1) (E.TN + i) i) (E.KPAR + i) i) (E.KMW + i) 0) a = M a := by
  have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4; have l5 := hl.l5
  have l6 := hl.l6; have l7 := hl.l7
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | omega

/-- After the first loop, the memory holds the start state. -/
theorem KInit.rep {E : KL} {M : ℕ → ℕ} (h : KInit E M E.n) (hn : E.n = G.n) :
    KRep M E (kinit G) (fun _ => 0) := by
  refine ⟨ufRep_init (fun x hx => ⟨(h x hx).1, (h x hx).2.1, (h x hx).2.2.1⟩), ?_,
    fun k hk => (h k (by simp [kinit] at hk; omega)).2.2.2.1,
    fun k hk => (h k (by simp [kinit] at hk; omega)).2.2.2.2,
    fun k h1 h2 => absurd h2 (by simp [kinit]; omega)⟩
  rw [ufRoots_all (fun x hx => (h x hx).1)]
  simp [kinit, hn]

theorem krP_spec {w : ℕ} {p : Program} {b bK bF : ℕ} (hp : p.HasAt b [krP bK])
    (hk : p.HasAt bK [kstP bF]) (hf : p.HasAt bF [findP]) (G : PG) :
    MeetsContract w p b (krC w G) := by
  intro args mem pos ω hwords hpre
  obtain ⟨c, KEYS, Mo, IN, PW, E, rfl, hl, hn, hL, hsort, hcov, hG, hmem, hkw, hIN, hPW, hKE, hn1, hw⟩ :=
    hpre
  have hproc : p.procs[b]? = some (krP bK) := hp 0 (by simp)
  have hS := fun s q => kstP_spec (w := w) hk hf G s q
  clear hp hk hf
  have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4; have l5 := hl.l5
  have l6 := hl.l6; have l7 := hl.l7
  have hw1 : 1 < 2 ^ w := by omega
  set L := kL mem KEYS Mo c with hLdef
  have hLlen : L.length = c := kL_length _ _ _ _
  have hinv := inv_prefix hL hsort hcov hG
  have hmax : ∀ q < G.m, IN + 3 * q + 1 < E.UF ∧ PW + q < E.UF := fun q hq => ⟨by omega, by omega⟩
  have hR0 : KR E c KEYS Mo IN PW (startState (E.n :: c :: KEYS :: Mo :: IN :: PW :: E.arr) mem pos) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the first loop
  let IC : ℕ → State → Prop := fun i st => KR E c KEYS Mo IN PW st ∧ st.regs 15 = i ∧
    (∀ a, (a < E.UF ∨ E.KMP + 2 * E.n ≤ a) → st.mem a = mem a) ∧ KInit E st.mem i
  have hInit := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 0)
    (body := krInit) (P := fun st => KR E c KEYS Mo IN PW st ∧ st.mem = mem) (Inv := IC) 40 0 E.n
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hr.upd (by omega) _, by simp, fun a _ => by simp [hm],
      fun v hv => absurd hv (by omega)⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h15, hfr, hz⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hr
      refine runs_start_le ?_
      dsimp only [krInit]
      wram_run
      · refine ⟨⟨(hr'.mem _).upd (by omega) _, by simp, fun a ha => ?_, ?_⟩, h15⟩
        · rw [← hfr a ha]; exact KInit.out hl (by omega) ha
        · exact hz.step hl (by omega)
      · wram_cost)
  -- the main loop
  let OI : ℕ → State → Prop := fun i st => KR E c KEYS Mo IN PW st ∧ st.regs 15 = i ∧
    st.regs 14 = (krun G (L.take i)).T.N ∧ (∃ dep, KRep st.mem E (krun G (L.take i)) dep) ∧
    ∀ a, (a < E.UF ∨ E.KMP + 2 * E.n ≤ a) → st.mem a = mem a
  have hMain := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 1)
    (body := .call 14 bK [.bin .mod (.load (.bin .add (.reg 2) (.reg 15))) (.reg 3), .reg 14,
      .reg 4, .reg 5, .reg 0, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13])
    (P := fun st => OI 0 { st with regs := Function.update st.regs 15 0 }) (Inv := OI)
    (40 * Nat.log 2 E.n + 340) 0 c (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨by eval_expr, hP⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h15, h14, ⟨dep, hK⟩, hfr⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hr
      have hiL : i < L.length := by omega
      have hq : st.mem (KEYS + i) % Mo = L[i] := by
        rw [kL_getElem, hfr _ (Or.inl (by omega))]
      have hqm : L[i] < G.m := hL _ (List.getElem_mem hiL)
      obtain ⟨mu, mv, mw⟩ := hmem _ hqm
      obtain ⟨hpu, hpv⟩ := hG _ hqm
      have hmax' := hmax _ hqm
      have hSi := hS (krun G (L.take i)) L[i]
      have hq' : st.mem (st.regs 2 + st.regs 15) % st.regs 3 = L[i] := by rw [a2, h15, a3]; exact hq
      have hqw : L[i] < 2 ^ w := by omega
      have hNw : (krun G (L.take i)).T.N < 2 ^ w := by
        have := hK.cnt; omega
      refine runs_start_le ?_
      have hkw' : st.mem (KEYS + i) < 2 ^ w := by rw [hfr _ (Or.inl (by omega))]; exact hkw i hi
      wram_step
      · refine ⟨IN, PW, E, dep, L.take i, L.drop i, by rw [hq]; rfl, hl, hK, hinv i hiL.le, hn,
          hpu, hpv, ?_, ?_, ?_, by omega, by omega, hw⟩
        · rw [hfr _ (Or.inl (by omega))]; exact mu
        · rw [hfr _ (Or.inl (by omega))]; exact mv
        · rw [hfr _ (Or.inl (by omega))]; exact mw
      · intro v mem' pos' hpost
        rw [hq] at hpost
        obtain ⟨hv, hK', hfr'⟩ := hpost IN PW E rfl
        refine ⟨⟨⟨(hr'.upd (by omega) _).upd (by omega) _, by simp, ?_, ?_, fun a ha => ?_⟩, ?_⟩, ?_⟩
        · simp [hv, krun_take_succ L hiL]
        · rw [krun_take_succ L hiL]; exact hK'
        · show mem' a = mem a
          rw [hfr' a ha]; exact hfr a ha
        · simp [h15]
        · simp only [kstC, List.getD_cons_zero, List.getD_cons_succ]
          wram_cost)
  refine ⟨krP bK, hproc, ?_⟩
  dsimp only [krP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hInit ⟨hR0, rfl⟩ (fun st1 h1 => ?_)
  obtain ⟨hr1, -, hfr1, hz1⟩ := h1
  have hr1' := hr1
  obtain ⟨a0, -⟩ := hr1
  wram_step
  refine runs_seq_triple_le hMain ?_ (fun st2 h2 => ?_)
  · refine ⟨(hr1'.upd (by omega) _).upd (by omega) _, by simp, by simp [krun, kinit, hn], ⟨fun _ => 0, ?_⟩,
      fun a ha => hfr1 a ha⟩
    exact hz1.rep hn
  obtain ⟨hr2, -, h142, hK2, hfr2⟩ := h2
  rw [List.take_of_length_le (by omega)] at h142 hK2
  refine runs_ret_le (by eval_expr) (fun c' KEYS' Mo' IN' PW' E' he => ?_) ?_
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := KL.eq_of_args6 he
    exact ⟨rfl, hK2, hfr2⟩
  · simp only [krC, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    simp only [Nat.sub_zero]
    generalize Nat.log 2 E.n = lg
    have := Nat.mul_le_mul_left c (show 40 * lg + 340 + 1 + 8 ≤ 40 * lg + 400 by omega)
    omega

end MinCostFlow.LowStretch
