module

public import MinCostFlow.LowStretch.KOrder
public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# Sizes, leaf order and heads of the merge tree, in memory

`koP` reads the merge tree `T` (parents and children) and writes, for every node `k`, the number
of leaves `sz k` to `KSZ + k`, the start `lo k` of its interval to `KLO + k` and its head `hd k`
to `HEAD + k`. It also writes the leaf order: leaf `v` at `ORDL + lo v` (`koP_spec`). The sizes
are computed from the leaves up, the starts and heads from the root down. The cost is linear in
the number of nodes.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers that `koP` works with. -/
structure KO where
  n : ℕ
  N : ℕ
  KPAR : ℕ
  KCH1 : ℕ
  KCH2 : ℕ
  KSZ : ℕ
  KLO : ℕ
  HEAD : ℕ
  ORDL : ℕ

/-- The arguments of `koP`. -/
def KO.args (E : KO) : List ℕ := [E.n, E.N, E.KPAR, E.KCH1, E.KCH2, E.KSZ, E.KLO, E.HEAD, E.ORDL]

/-- The precondition: the tree in memory, and room for the new arrays. -/
structure KO.Ok (E : KO) (w : ℕ) (T : KT) (G : PG) (mem : ℕ → ℕ) : Prop where
  tree : T.Ok G
  hN : T.N = E.N
  hn : G.n = E.n
  par : ∀ k < E.N, mem (E.KPAR + k) = T.par k
  ch : ∀ k, E.n ≤ k → k < E.N → mem (E.KCH1 + k) = T.ch1 k ∧ mem (E.KCH2 + k) = T.ch2 k
  l1 : E.KSZ + E.N ≤ E.KLO
  l2 : E.KLO + E.N ≤ E.HEAD
  l3 : E.HEAD + E.N ≤ E.ORDL
  l4 : E.ORDL + E.n < 2 ^ w
  l5 : E.KPAR + E.N ≤ E.KSZ ∧ E.KCH1 + E.N ≤ E.KSZ ∧ E.KCH2 + E.N ≤ E.KSZ

/-- The first loop: sizes, from the leaves up. -/
def koB1 : Stmt :=
  .cond (.bin .lt (.reg 9) (.reg 0)) (.store (.bin .add (.reg 5) (.reg 9)) (.const 1))
    (.store (.bin .add (.reg 5) (.reg 9))
      (.bin .add (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 3) (.reg 9)))))
        (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 4) (.reg 9)))))))

/-- The second loop: starts and heads of the two children of node `N - 1 - j`. -/
def koB2 : Stmt :=
  .seq (.assign 10 (.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 9)))
  (.seq (.assign 11 (.load (.bin .add (.reg 3) (.reg 10))))
  (.seq (.assign 12 (.load (.bin .add (.reg 4) (.reg 10))))
  (.seq (.assign 13 (.load (.bin .add (.reg 6) (.reg 10))))
  (.seq (.assign 14 (.load (.bin .add (.reg 7) (.reg 10))))
  (.seq (.assign 15 (.load (.bin .add (.reg 5) (.reg 11))))
  (.seq (.assign 16 (.load (.bin .add (.reg 5) (.reg 12))))
  (.seq (.store (.bin .add (.reg 6) (.reg 11)) (.reg 13))
  (.seq (.store (.bin .add (.reg 6) (.reg 12)) (.bin .add (.reg 13) (.reg 15)))
  (.cond (.bin .lt (.reg 15) (.reg 16))
    (.seq (.store (.bin .add (.reg 7) (.reg 12)) (.reg 14)) (.store (.bin .add (.reg 7) (.reg 11)) (.reg 11)))
    (.seq (.store (.bin .add (.reg 7) (.reg 11)) (.reg 14)) (.store (.bin .add (.reg 7) (.reg 12)) (.reg 12))))))))))))

/-- `koP` with `args = E.args`. -/
def koP : Stmt :=
  .seq (forRange 9 (.const 0) (.reg 1) koB1)
  (.seq (.store (.bin .add (.reg 6) (.bin .sub (.reg 1) (.const 1))) (.const 0))
  (.seq (.store (.bin .add (.reg 7) (.bin .sub (.reg 1) (.const 1))) (.bin .sub (.reg 1) (.const 1)))
  (.seq (forRange 9 (.const 0) (.bin .sub (.reg 1) (.reg 0)) koB2)
  (.seq (forRange 9 (.const 0) (.reg 0)
    (.store (.bin .add (.reg 8) (.load (.bin .add (.reg 6) (.reg 9)))) (.reg 9)))
  (.ret (.const 0))))))

theorem koP_noRand : koP.NoRand := by
  simp [koP, koB1, koB2, forRange, forUp, Stmt.NoRand]

/-- The contract of `koP` for the tree `T` of the graph `G`. -/
def koC (w : ℕ) (T : KT) (G : PG) : Contract where
  pre args mem := ∃ E : KO, args = E.args ∧ E.Ok w T G mem
  post args mem _ mem' := ∀ E : KO, args = E.args →
    (∀ k < E.N, mem' (E.KSZ + k) = T.sz G k ∧ mem' (E.KLO + k) = T.lo G k ∧
      mem' (E.HEAD + k) = T.hd G k) ∧
    (∀ v < E.n, mem' (E.ORDL + T.lo G v) = v) ∧
    ∀ a, (a < E.KSZ ∨ E.ORDL + E.n ≤ a) → mem' a = mem a
  cost args _ := 200 * (args.getD 1 0 + 1)

theorem KO.eq_of_args {E E' : KO} (h : E.args = E'.args) : E' = E := by
  cases E; cases E'; simp only [KO.args, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h
  subst_vars; rfl

namespace KO

variable {E : KO} {w : ℕ} {T : KT} {G : PG} {M0 : ℕ → ℕ}

/-- After the first loop has seen the nodes below `k`. -/
def SZI (E : KO) (T : KT) (G : PG) (M : ℕ → ℕ) (k : ℕ) : Prop := ∀ k' < k, M (E.KSZ + k') = T.sz G k'

theorem SZI.step {M : ℕ → ℕ} {k v : ℕ} (h : SZI E T G M k) (hv : v = T.sz G k) :
    SZI E T G (Function.update M (E.KSZ + k) v) (k + 1) := by
  intro k' hk'
  by_cases e : k' = k
  · subst e; simp [hv]
  · rw [Function.update_of_ne (by omega)]; exact h k' (by omega)

/-- After the second loop has handled the nodes `N - 1, …, N - j`: every node whose parent is one
of them, and the root, has its start and head. -/
def TI (E : KO) (T : KT) (G : PG) (M : ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ x < E.N, (x = E.N - 1 ∨ (x + 1 < E.N ∧ E.N - j ≤ T.par x)) →
    M (E.KLO + x) = T.lo G x ∧ M (E.HEAD + x) = T.hd G x

theorem TI.step (hE : E.Ok w T G M0) {M : ℕ → ℕ} {j : ℕ} (h : TI E T G M j)
    (hj : j < E.N - E.n) {a b : ℕ}
    (hab : a = T.heavy G (E.N - 1 - j) ∧ b = T.light G (E.N - 1 - j)) :
    TI E T G (Function.update (Function.update (Function.update (Function.update M
      (E.KLO + T.ch1 (E.N - 1 - j)) (M (E.KLO + (E.N - 1 - j))))
      (E.KLO + T.ch2 (E.N - 1 - j)) (M (E.KLO + (E.N - 1 - j)) + T.sz G (T.ch1 (E.N - 1 - j))))
      (E.HEAD + a) (M (E.HEAD + (E.N - 1 - j)))) (E.HEAD + b) b) (j + 1) := by
  have l1 := hE.l1; have l2 := hE.l2; have l3 := hE.l3
  have ht := hE.tree
  have hN := hE.hN; have hn := hE.hn
  set k := E.N - 1 - j with hk
  have hkn : G.n ≤ k := by omega
  have hkN : k < T.N := by omega
  obtain ⟨hp1, hp2, hne, hlt1, hlt2⟩ := ht.ch k hkn hkN
  have hkk : E.N - 1 - j = k := rfl
  -- the values at `k`
  have hk0 : M (E.KLO + k) = T.lo G k ∧ M (E.HEAD + k) = T.hd G k := by
    refine h k (by omega) ?_
    by_cases hr : k + 1 < E.N
    · exact Or.inr ⟨hr, by have := (ht.par_lt k (by omega)).1; omega⟩
    · exact Or.inl (by omega)
  have hab' : (a = T.ch1 k ∧ b = T.ch2 k) ∨ (a = T.ch2 k ∧ b = T.ch1 k) := by
    rcases KT.heavy_light ht hkn hkN with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨hab.1.trans e1, hab.2.trans e2⟩
    · exact Or.inr ⟨hab.1.trans e1, hab.2.trans e2⟩
  have hhd_a : T.hd G a = T.hd G k := by rw [hab.1]; exact KT.heavy_ch1 ht hkn hkN
  have hhd_b : T.hd G b = b := by rw [hab.2]; exact KT.hd_lightc ht hkn hkN
  intro x hx hcond
  by_cases hx1 : x = T.ch1 k
  · subst hx1
    have e1 : E.KLO + T.ch1 k ≠ E.KLO + T.ch2 k := by omega
    refine ⟨?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne e1, Function.update_self, hk0.1, KT.lo_ch1 ht hkn hkN]
    · rcases hab' with ⟨ea, eb⟩ | ⟨ea, eb⟩
      · rw [Function.update_of_ne (by rw [eb]; omega), ← ea, Function.update_self, hk0.2, hhd_a]
      · rw [← eb, Function.update_self, hhd_b]
  by_cases hx2 : x = T.ch2 k
  · subst hx2
    refine ⟨?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self, hk0.1, KT.lo_ch2 ht hkn hkN]
    · rcases hab' with ⟨ea, eb⟩ | ⟨ea, eb⟩
      · rw [← eb, Function.update_self, hhd_b]
      · rw [Function.update_of_ne (by rw [eb]; omega), ← ea, Function.update_self, hk0.2, hhd_a]
  -- other nodes: unchanged, and their parent was handled before
  have hold : x = E.N - 1 ∨ (x + 1 < E.N ∧ E.N - j ≤ T.par x) := by
    rcases hcond with e | ⟨hr, hp⟩
    · exact Or.inl e
    · right; refine ⟨hr, ?_⟩
      by_contra hlt
      have hpk : T.par x = k := by omega
      rcases ht.par_ch x (by omega) with e | e <;> rw [hpk] at e
      · exact hx1 e
      · exact hx2 e
  have hab1 : x ≠ a := by rcases hab' with ⟨ea, -⟩ | ⟨ea, -⟩ <;> rw [ea] <;> assumption
  have hab2 : x ≠ b := by rcases hab' with ⟨-, eb⟩ | ⟨-, eb⟩ <;> rw [eb] <;> assumption
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  exact h x hx hold

/-- `TI.step` with the addresses and values given by equations, and the cells it keeps. -/
theorem TI.step' (hE : E.Ok w T G M0) {M : ℕ → ℕ} {j : ℕ} (h : TI E T G M j)
    (hj : j < E.N - E.n) {a b A1 A2 A3 A4 V1 V2 V3 V4 : ℕ}
    (hab : a = T.heavy G (E.N - 1 - j) ∧ b = T.light G (E.N - 1 - j))
    (e1 : A1 = E.KLO + T.ch1 (E.N - 1 - j)) (f1 : V1 = M (E.KLO + (E.N - 1 - j)))
    (e2 : A2 = E.KLO + T.ch2 (E.N - 1 - j))
    (f2 : V2 = M (E.KLO + (E.N - 1 - j)) + T.sz G (T.ch1 (E.N - 1 - j)))
    (e3 : A3 = E.HEAD + a) (f3 : V3 = M (E.HEAD + (E.N - 1 - j))) (e4 : A4 = E.HEAD + b)
    (f4 : V4 = b) :
    TI E T G (Function.update (Function.update (Function.update (Function.update M A1 V1) A2 V2)
      A3 V3) A4 V4) (j + 1) ∧
    ∀ x, (x < E.KLO ∨ E.ORDL ≤ x) → Function.update (Function.update (Function.update
      (Function.update M A1 V1) A2 V2) A3 V3) A4 V4 x = M x := by
  subst A1 V1 A2 V2 A3 V3 A4 V4
  refine ⟨h.step hE hj hab, fun x hx => ?_⟩
  have l1 := hE.l1; have l2 := hE.l2; have l3 := hE.l3
  have ht := hE.tree
  have hN := hE.hN; have hn := hE.hn
  obtain ⟨-, -, -, hlt1, hlt2⟩ := ht.ch (E.N - 1 - j) (by omega) (by omega)
  have ha : a < E.N := by
    rcases KT.heavy_light ht (k := E.N - 1 - j) (by omega) (by omega) with ⟨e, -⟩ | ⟨e, -⟩ <;>
      rw [hab.1, e] <;> omega
  have hb : b < E.N := by
    rcases KT.heavy_light ht (k := E.N - 1 - j) (by omega) (by omega) with ⟨-, e⟩ | ⟨-, e⟩ <;>
      rw [hab.2, e] <;> omega
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- After the last loop has seen the leaves below `v`. -/
def OI (E : KO) (T : KT) (G : PG) (M : ℕ → ℕ) (v : ℕ) : Prop :=
  ∀ v' < v, M (E.ORDL + T.lo G v') = v'

theorem OI.step (hE : E.Ok w T G M0) {M : ℕ → ℕ} {v : ℕ} (h : OI E T G M v) (hv : v < E.n) :
    OI E T G (Function.update M (E.ORDL + T.lo G v) v) (v + 1) := by
  have ht := hE.tree
  have hn := hE.hn
  have hN := ht.n_lt
  intro v' hv'
  by_cases e : v' = v
  · subst e; simp
  · have hne : T.lo G v' ≠ T.lo G v := fun he => e (KT.lo_injOn ht (T.N - 1) (by omega)
      (by simp only [Finset.mem_coe]; exact KT.mem_lv.mpr ⟨by omega, ht.all v' (by omega)⟩)
      (by simp only [Finset.mem_coe]; exact KT.mem_lv.mpr ⟨by omega, ht.all v (by omega)⟩) he)
    rw [Function.update_of_ne (by omega)]; exact h v' (by omega)

/-- The registers that never change. -/
def R (E : KO) (st : State) : Prop :=
  st.regs 0 = E.n ∧ st.regs 1 = E.N ∧ st.regs 2 = E.KPAR ∧ st.regs 3 = E.KCH1 ∧
    st.regs 4 = E.KCH2 ∧ st.regs 5 = E.KSZ ∧ st.regs 6 = E.KLO ∧ st.regs 7 = E.HEAD ∧
    st.regs 8 = E.ORDL

theorem R.upd {st : State} (h : E.R st) {r : ℕ} (hr : 9 ≤ r) (v : ℕ) :
    E.R { st with regs := Function.update st.regs r v } := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)

theorem R.mem {st : State} (h : E.R st) (M : ℕ → ℕ) : E.R { st with mem := M } := h

end KO

set_option maxHeartbeats 1000000 in
theorem koP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [koP]) (T : KT) (G : PG) :
    MeetsContract w p b (koC w T G) := by
  intro args mem pos ω hwords hpre
  obtain ⟨E, rfl, hE⟩ := hpre
  have hproc : p.procs[b]? = some koP := hp 0 (by simp)
  clear hp
  have l1 := hE.l1; have l2 := hE.l2; have l3 := hE.l3; have l4 := hE.l4; have l5 := hE.l5
  have ht := hE.tree
  have hN := hE.hN; have hn := hE.hn
  have hnN := ht.n_lt
  have hw1 : 1 < 2 ^ w := by omega
  have hR0 : E.R (startState E.args mem pos) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hszn : ∀ k, T.sz G k ≤ E.n := fun k => hn ▸ KT.sz_le_n k
  -- the first loop
  let I1 : ℕ → State → Prop := fun k st => E.R st ∧ st.regs 9 = k ∧ KO.SZI E T G st.mem k ∧
    ∀ a, (a < E.KSZ ∨ E.KSZ + E.N ≤ a) → st.mem a = mem a
  have hL1 := Triple.forRange_const (p := p) (r := 9) (lo := .const 0) (hi := .reg 1)
    (body := koB1) (P := fun st => E.R st ∧ st.mem = mem) (Inv := I1) 30 0 E.N
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hr.upd (by omega) _, by simp,
      fun k hk => absurd hk (by omega), fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun k _ hk st ω hI => by
      obtain ⟨hr, h9, hS, hfr⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hr
      refine runs_start_le ?_
      dsimp only [koB1]
      by_cases hkn : k < E.n
      · have hsz : T.sz G k = 1 := KT.sz_leaf ht (by omega)
        wram_run
        · refine ⟨⟨(hr'.mem _).upd (by omega) _, by simp, hS.step hsz.symm, fun a ha => ?_⟩, h9⟩
          show Function.update st.mem (E.KSZ + k) 1 a = mem a
          rw [Function.update_of_ne (by omega)]; exact hfr a ha
        · wram_cost
      · have hkn' : G.n ≤ k := by omega
        obtain ⟨c1, c2⟩ := hE.ch k (by omega) hk
        obtain ⟨-, -, -, hlt1, hlt2⟩ := ht.ch k hkn' (by omega)
        have e1 : st.mem (E.KCH1 + k) = T.ch1 k := by rw [hfr _ (Or.inl (by omega))]; exact c1
        have e2 : st.mem (E.KCH2 + k) = T.ch2 k := by rw [hfr _ (Or.inl (by omega))]; exact c2
        have s1 := hS (T.ch1 k) hlt1
        have s2 := hS (T.ch2 k) hlt2
        have hsz := KT.sz_inner ht hkn' (by omega)
        have b1 := hszn (T.ch1 k)
        have b2 := hszn (T.ch2 k)
        have hsum : st.mem (E.KSZ + st.mem (E.KCH1 + k)) + st.mem (E.KSZ + st.mem (E.KCH2 + k)) =
            T.sz G k := by
          rw [e1, e2, s1, s2, hsz]
        have hsw : T.sz G k < 2 ^ w := by have := hszn k; omega
        wram_run
        · refine ⟨⟨(hr'.mem _).upd (by omega) _, by simp, ?_, fun a ha => ?_⟩, h9⟩
          · exact hS.step hsum
          · show Function.update st.mem (E.KSZ + k) _ a = mem a
            rw [Function.update_of_ne (by omega)]; exact hfr a ha
        · wram_cost)
  refine ⟨koP, hproc, ?_⟩
  dsimp only [koP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hL1 ⟨hR0, rfl⟩ (fun st1 h1 => ?_)
  obtain ⟨hr1, -, hS1, hfr1⟩ := h1
  have hr1' := hr1
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hr1
  wram_step
  wram_step
  set M2 := Function.update (Function.update st1.mem (E.KLO + (E.N - 1)) 0) (E.HEAD + (E.N - 1))
    (E.N - 1) with hM2
  have fr2 : ∀ a, (a < E.KLO ∨ E.ORDL ≤ a) → M2 a = st1.mem a := fun a ha => by
    rw [hM2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hTI0 : KO.TI E T G M2 0 := by
    intro x hx hc
    rcases hc with e | ⟨hr, hp⟩
    · subst e
      refine ⟨?_, ?_⟩
      · rw [hM2, Function.update_of_ne (by omega), Function.update_self, ← hN, KT.lo_root]
      · rw [hM2, Function.update_self, ← hN, KT.hd_root]
    · have := (ht.par_lt x (by omega)).2; omega
  -- the second loop
  let I3 : ℕ → State → Prop := fun j st => E.R st ∧ st.regs 9 = j ∧ KO.TI E T G st.mem j ∧
    ∀ a, (a < E.KLO ∨ E.ORDL ≤ a) → st.mem a = st1.mem a
  have hL3 := Triple.forRange_const (p := p) (r := 9) (lo := .const 0)
    (hi := .bin .sub (.reg 1) (.reg 0)) (body := koB2)
    (P := fun st => E.R st ∧ st.mem = M2) (Inv := I3) 80 0 (E.N - E.n)
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hr.upd (by omega) _, by simp, by rw [hm]; exact hTI0,
      fun a ha => by rw [hm]; exact fr2 a ha⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; have := hI.1.1; eval_expr)
    (fun j _ hj st ω hI => by
      obtain ⟨hr, h9, hTI, hfr⟩ := hI
      have hr' := hr
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hr
      have hkn : G.n ≤ E.N - 1 - j := by omega
      have hkN : E.N - 1 - j < T.N := by omega
      obtain ⟨c1, c2⟩ := hE.ch (E.N - 1 - j) (by omega) (by omega)
      obtain ⟨-, -, hne, hlt1, hlt2⟩ := ht.ch _ hkn hkN
      have e11 : st.mem (E.KCH1 + (E.N - 1 - j)) = T.ch1 (E.N - 1 - j) := by
        rw [hfr _ (Or.inl (by omega)), hfr1 _ (Or.inl (by omega))]; exact c1
      have e12 : st.mem (E.KCH2 + (E.N - 1 - j)) = T.ch2 (E.N - 1 - j) := by
        rw [hfr _ (Or.inl (by omega)), hfr1 _ (Or.inl (by omega))]; exact c2
      have e15 : st.mem (E.KSZ + T.ch1 (E.N - 1 - j)) = T.sz G (T.ch1 (E.N - 1 - j)) := by
        rw [hfr _ (Or.inl (by omega))]; exact hS1 _ (by omega)
      have e16 : st.mem (E.KSZ + T.ch2 (E.N - 1 - j)) = T.sz G (T.ch2 (E.N - 1 - j)) := by
        rw [hfr _ (Or.inl (by omega))]; exact hS1 _ (by omega)
      have hk0 := (hTI (E.N - 1 - j) (by omega) (by
        by_cases hr : E.N - 1 - j + 1 < E.N
        · exact Or.inr ⟨hr, by have := (ht.par_lt (E.N - 1 - j) (by omega)).1; omega⟩
        · exact Or.inl (by omega))).1
      have hlo := (ht.all (E.N - 1 - j) |> fun _ => (KT.Under.lo ht hkN
        (show T.Under (E.N - 1 - j) (T.N - 1) from by
          obtain ⟨v, hv, hu⟩ := KT.exists_leaf ht _ hkN
          have := ht.all v hv
          rcases KT.Under.total hu this with h' | h'
          · exact h'
          · have := h'.le ht (by omega); rw [show T.N - 1 = E.N - 1 - j by omega]
            exact KT.Under.refl _)))
      rw [KT.lo_root, KT.sz_root ht] at hlo
      have hsz := KT.sz_inner ht hkn hkN
      have hb1 : st.mem (E.KLO + (E.N - 1 - j)) + st.mem (E.KSZ + st.mem (E.KCH1 + (E.N - 1 - j)))
          < 2 ^ w := by rw [e11, e15, hk0]; omega
      have e11' : st.mem (st.regs 3 + (E.N - 1 - j)) = T.ch1 (E.N - 1 - j) := by rw [b3]; exact e11
      have e12' : st.mem (st.regs 4 + (E.N - 1 - j)) = T.ch2 (E.N - 1 - j) := by rw [b4]; exact e12
      have hb1' : st.mem (st.regs 6 + (E.N - 1 - j)) +
          st.mem (st.regs 5 + st.mem (st.regs 3 + (E.N - 1 - j))) < 2 ^ w := by
        rw [b6, b5, b3]; exact hb1
      refine runs_start_le ?_
      dsimp only [koB2]
      have hRn : ∀ st' : State, (∀ i < 9, st'.regs i = st.regs i) → E.R st' := fun st' hs =>
        ⟨(hs 0 (by omega)).trans b0, (hs 1 (by omega)).trans b1, (hs 2 (by omega)).trans b2,
          (hs 3 (by omega)).trans b3, (hs 4 (by omega)).trans b4, (hs 5 (by omega)).trans b5,
          (hs 6 (by omega)).trans b6, (hs 7 (by omega)).trans b7, (hs 8 (by omega)).trans b8⟩
      wram_run
      · have hlt : T.sz G (T.ch1 (E.N - 1 - j)) < T.sz G (T.ch2 (E.N - 1 - j)) := by
          rw [b5, b3, b4, e11, e12, e15, e16] at hcond; exact hcond
        have key := KO.TI.step' (a := T.ch2 (E.N - 1 - j)) (b := T.ch1 (E.N - 1 - j)) hE hTI hj
          ⟨by unfold KT.heavy; rw [if_neg (by omega)], by unfold KT.light; rw [if_neg (by omega)]⟩
          (M := st.mem) (A1 := _) (A2 := _) (A3 := _) (A4 := _) (V1 := _) (V2 := _) (V3 := _)
          (V4 := _) rfl rfl rfl rfl rfl rfl rfl rfl
        refine ⟨⟨hRn _ (fun i hi => by simp only [Function.update_apply]; split_ifs <;> omega),
          by simp, ?_, fun x hx => ?_⟩, by simp [h9]⟩
        · convert key.1 using 2 <;> simp [b3, b4, b5, b6, b7, e11, e12, e15]
        · refine Eq.trans ?_ (hfr x hx)
          have hc1N : T.ch1 (E.N - 1 - j) < E.N := by omega
          have hc2N : T.ch2 (E.N - 1 - j) < E.N := by omega
          simp only [Function.update_apply]
          split_ifs <;> first | rfl | omega
      · wram_cost
      · have hlt : ¬ T.sz G (T.ch1 (E.N - 1 - j)) < T.sz G (T.ch2 (E.N - 1 - j)) := by
          rw [b5, b3, b4, e11, e12, e15, e16] at hcond; exact hcond
        have key := KO.TI.step' (a := T.ch1 (E.N - 1 - j)) (b := T.ch2 (E.N - 1 - j)) hE hTI hj
          ⟨by unfold KT.heavy; rw [if_pos (by omega)], by unfold KT.light; rw [if_pos (by omega)]⟩
          (M := st.mem) (A1 := _) (A2 := _) (A3 := _) (A4 := _) (V1 := _) (V2 := _) (V3 := _)
          (V4 := _) rfl rfl rfl rfl rfl rfl rfl rfl
        refine ⟨⟨hRn _ (fun i hi => by simp only [Function.update_apply]; split_ifs <;> omega),
          by simp, ?_, fun x hx => ?_⟩, by simp [h9]⟩
        · convert key.1 using 2 <;> simp [b3, b4, b5, b6, b7, e11, e12, e15]
        · refine Eq.trans ?_ (hfr x hx)
          have hc1N : T.ch1 (E.N - 1 - j) < E.N := by omega
          have hc2N : T.ch2 (E.N - 1 - j) < E.N := by omega
          simp only [Function.update_apply]
          split_ifs <;> first | rfl | omega
      · wram_cost)
  refine runs_seq_triple_le hL3 ⟨hr1'.mem _, by first | rfl | simp only [hM2, a1, a6, a7]⟩
    (fun st3 h3 => ?_)
  obtain ⟨hr3, -, hTI3, hfr3⟩ := h3
  have hr3' := hr3
  have hTIall : ∀ x < E.N, st3.mem (E.KLO + x) = T.lo G x ∧ st3.mem (E.HEAD + x) = T.hd G x :=
    fun x hx => hTI3 x hx (by
      by_cases hr : x + 1 < E.N
      · exact Or.inr ⟨hr, by have := ht.par_internal x (by omega); omega⟩
      · exact Or.inl (by omega))
  -- the last loop
  let I4 : ℕ → State → Prop := fun v st => E.R st ∧ st.regs 9 = v ∧ KO.OI E T G st.mem v ∧
    ∀ a, (a < E.ORDL ∨ E.ORDL + E.n ≤ a) → st.mem a = st3.mem a
  have hL4 := Triple.forRange_const (p := p) (r := 9) (lo := .const 0) (hi := .reg 0)
    (body := .store (.bin .add (.reg 8) (.load (.bin .add (.reg 6) (.reg 9)))) (.reg 9))
    (P := fun st => st = st3) (Inv := I4) 20 0 E.n
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      exact ⟨by eval_expr, hr3'.upd (by omega) _, by simp, fun v hv => absurd hv (by omega),
        fun a _ => rfl⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun v _ hv st ω hI => by
      obtain ⟨hr, h9, hO, hfr⟩ := hI
      have hr' := hr
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hr
      have hlo : st.mem (E.KLO + v) = T.lo G v := by
        rw [hfr _ (Or.inl (by omega))]; exact (hTIall v (by omega)).1
      have hlt : T.lo G v < E.n := hn ▸ KT.lo_lt ht (by omega)
      have hlo' : st.mem (st.regs 6 + st.regs 9) = T.lo G v := by rw [b6, h9]; exact hlo
      have hw' : st.regs 8 + st.mem (st.regs 6 + st.regs 9) < 2 ^ w := by
        rw [hlo', b8]; omega
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨(hr'.mem _).upd (by omega) _, by simp, ?_, fun a ha => ?_⟩, h9⟩
        · convert hO.step hE hv using 2 <;> simp [b6, h9, hlo]
        · show Function.update st.mem _ _ a = st3.mem a
          rw [Function.update_of_ne (by rw [hlo]; omega)]; exact hfr a ha
      · wram_cost)
  refine runs_seq_triple_le hL4 rfl (fun st4 h4 => ?_)
  obtain ⟨-, -, hO4, hfr4⟩ := h4
  refine runs_ret_le (by eval_expr) (fun E' he => ?_) ?_
  · obtain rfl := KO.eq_of_args he
    refine ⟨fun k hk => ⟨?_, ?_, ?_⟩, hO4, fun a ha => ?_⟩
    · rw [hfr4 _ (Or.inl (by omega)), hfr3 _ (Or.inl (by omega))]; exact hS1 k hk
    · rw [hfr4 _ (Or.inl (by omega))]; exact (hTIall k hk).1
    · rw [hfr4 _ (Or.inl (by omega))]; exact (hTIall k hk).2
    · rcases ha with ha | ha
      · rw [hfr4 _ (Or.inl (by omega)), hfr3 _ (Or.inl (by omega)), hfr1 _ (Or.inl ha)]
      · rw [hfr4 _ (Or.inr ha), hfr3 _ (Or.inr (by omega)), hfr1 _ (Or.inr (by omega))]
  · simp only [koC, KO.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    simp only [Nat.sub_zero]
    omega

end MinCostFlow.LowStretch
