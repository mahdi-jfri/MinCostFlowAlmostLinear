module

public import MinCostFlow.LowStretch.ProgPreMath
public import MinCostFlow.LowStretch.ProgArcs2
public import MinCostFlow.LowStretch.ProgEntryWord

/-!
# The blocks of the first cluster

The root procedure (`ProgRecRoot.lean`) writes the global block `rootGlob` at the heap pointer
`H` of the entry and the record block `rootRecL` of the first cluster right after it. Then it
calls the cluster procedure with the heap pointer `H + 30`. This file shows that the
precondition `RecPre` of the cluster procedure holds at that call (`rootPre`).

The two new numbers of the global block are these.
* The bound `J = pσ + pa + 4` of the classes of Dijkstra. Since `8 B n < 2 ^ pσ` and
  `n < 2 ^ pa`, we get `128 B n² < 2 ^ J` (`lt_two_pow_J`). Also `2 ^ J ≤ 2^16 (n + 4)^4`
  (`two_pow_J_le`), so the room that `RecPre` asks for is a polynomial in the heap pointer and
  the largest weight (`root_room`).
* The bound `INF = 2 n Mw + 1` of the distances, for the largest rounded weight `Mw`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

theorem lt_two_pow_J (n : ℕ) : 128 * pB n * n ^ 2 < 2 ^ rootJ n := by
  have h1 : 8 * pB n * n < 2 ^ pσ n := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : n < 2 ^ pa n := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 2)
    unfold pa; omega
  have e : 2 ^ rootJ n = 16 * (2 ^ pσ n * 2 ^ pa n) := by
    unfold rootJ; rw [pow_add, pow_add]; ring
  have e2 : 128 * pB n * n ^ 2 = 16 * (8 * pB n * n * n) := by ring
  rw [e, e2]
  have h3 : 8 * pB n * n * n < 2 ^ pσ n * 2 ^ pa n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · calc 8 * pB n * n * n < 2 ^ pσ n * n := Nat.mul_lt_mul_of_pos_right h1 hn
        _ ≤ 2 ^ pσ n * 2 ^ pa n := Nat.mul_le_mul_left _ h2.le
  omega

theorem two_pow_J_le (n : ℕ) : 2 ^ rootJ n ≤ 2 ^ 16 * (n + 4) ^ 4 := by
  have hB := pB_le_poly n
  have a1 : 2 ^ pσ n ≤ 2 * (8 * pB n * n + 1) := by
    have := pow_log_le_succ (8 * pB n * n)
    unfold pσ; rw [pow_succ]; omega
  have a2 : 2 ^ pa n ≤ 2 * (n + 3) := by
    have := pow_log_le_succ (n + 2)
    unfold pa; rw [pow_succ]; omega
  have a3 : 8 * pB n * n + 1 ≤ 513 * (n + 4) ^ 3 := by
    have h1 : pB n * n ≤ 64 * (n + 4) ^ 2 * (n + 4) := Nat.mul_le_mul hB (by omega)
    have h2 : 1 ≤ (n + 4) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have e1 : 8 * pB n * n = 8 * (pB n * n) := by ring
    have e2 : 64 * (n + 4) ^ 2 * (n + 4) = 64 * (n + 4) ^ 3 := by ring
    omega
  have e : 2 ^ rootJ n = 16 * (2 ^ pσ n * 2 ^ pa n) := by
    unfold rootJ; rw [pow_add, pow_add]; ring
  calc 2 ^ rootJ n = 16 * (2 ^ pσ n * 2 ^ pa n) := e
    _ ≤ 16 * ((2 * (513 * (n + 4) ^ 3)) * (2 * (n + 4))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (a1.trans (by omega)) (a2.trans (by omega)))
    _ = 32832 * (n + 4) ^ 4 := by ring
    _ ≤ 2 ^ 16 * (n + 4) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)

/-- **The room at the first cluster.** With `X = H + M + 2`, the room that `RecPre` asks for
follows from a bound on `X` and on the cost `C`. -/
theorem root_room {n m N H Mw M R C w : ℕ} (hn : n ≤ H) (hm : m ≤ H) (hN : N ≤ H) (hMw : Mw ≤ M)
    (hRC : R ≤ C)
    (hw : H + 30 + 2 ^ 63 * (H + M + 2) ^ 14 + 2 ^ 21 * (H + M + 2) ^ 4 * C < 2 ^ w) :
    H + 30 + (rootJ n + 2) * R + 2 ^ (2 * rootJ n + 20) * (N + m + 2) ^ 3 * (Mw + 2) ^ 3 <
      2 ^ w := by
  set X := H + M + 2 with hX
  have hJ : 2 ^ rootJ n ≤ 2 ^ 20 * X ^ 4 :=
    calc 2 ^ rootJ n ≤ 2 ^ 16 * (n + 4) ^ 4 := two_pow_J_le n
      _ ≤ 2 ^ 16 * (2 * X) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = 2 ^ 20 * X ^ 4 := by ring
  have h1 : (rootJ n + 2) * R ≤ 2 ^ 21 * X ^ 4 * C := by
    have : rootJ n + 2 ≤ 2 * 2 ^ rootJ n := by
      have := Nat.lt_two_pow_self (n := rootJ n)
      have : 1 ≤ 2 ^ rootJ n := Nat.one_le_two_pow
      omega
    refine Nat.mul_le_mul (this.trans ?_) hRC
    calc 2 * 2 ^ rootJ n ≤ 2 * (2 ^ 20 * X ^ 4) := Nat.mul_le_mul_left _ hJ
      _ = 2 ^ 21 * X ^ 4 := by ring
  have h2 : 2 ^ (2 * rootJ n + 20) * (N + m + 2) ^ 3 * (Mw + 2) ^ 3 ≤ 2 ^ 63 * X ^ 14 := by
    have e : 2 ^ (2 * rootJ n + 20) = 2 ^ 20 * (2 ^ rootJ n) ^ 2 := by
      rw [pow_add, mul_comm (2 ^ (2 * rootJ n)), ← pow_mul, mul_comm (rootJ n)]
    rw [e]
    calc 2 ^ 20 * (2 ^ rootJ n) ^ 2 * (N + m + 2) ^ 3 * (Mw + 2) ^ 3 ≤
        2 ^ 20 * (2 ^ 20 * X ^ 4) ^ 2 * (2 * X) ^ 3 * X ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hJ 2))
            (Nat.pow_le_pow_left (by omega) 3)) (Nat.pow_le_pow_left (by omega) 3)
      _ = 2 ^ 63 * X ^ 14 := by ring
  omega

variable {G : WGraph} {T : KT}

/-- The global block of the first cluster, with the largest rounded weight `Mw`. -/
def rootGlob (E : EA) (G : WGraph) (T : KT) (Mw : ℕ) : GlobL :=
  ⟨G.n, G.m, T.N, E.IN, E.PW, E.EXP, E.LAB, E.LOC, E.KPAR, E.KCH1, E.KCH2, E.KMW, E.KSZ, E.KLO,
    E.HEAD, E.ORDL, E.GOFF, E.GORD, pB G.n, rootJ G.n, 2 * G.n * Mw + 1⟩

/-- The record block of the first cluster: center and target `0`, no stored highway. -/
def rootRecL (E : EA) : RecL := ⟨E.s, E.nS, E.SA, E.lθ, E.NODES, 0, 0, 0, 0⟩

theorem rootCl_card : (rootCl T G).X.card = G.n := by simp [rootCl, root, pgOf]

theorem mem_rootCl {v : ℕ} : v ∈ (rootCl T G).X ↔ v < G.n := by simp [rootCl, root, pgOf]

/-- **The precondition of the cluster procedure at the first cluster**, when the two blocks are
at `H` and `H + 21` and the memory below `H` is the memory after the preprocessing. -/
theorem rootPre {w A : ℕ} {E : EA} {mem mem' : ℕ → ℕ} {Mw : ℕ} (hE : E.Pre w G T mem)
    (hw : E.H + 30 + 2 ^ 63 * (E.H + (pgOf G).maxω + 2) ^ 14 +
      2 ^ 21 * (E.H + (pgOf G).maxω + 2) ^ 4 * clCost w A G T < 2 ^ w)
    (hMw : ∀ p < G.m, (pgOf G).pω p ≤ Mw) (hMw' : Mw ≤ (pgOf G).maxω)
    (hgl : GlobL.read mem' E.H = rootGlob E G T Mw) (hrl : RecL.read mem' (E.H + 21) = rootRecL E)
    (hfr : ∀ a < E.H, mem' a = mem a) (hz : ZeroFrom mem' (E.H + 30)) :
    RecPre w A T (pgOf G) (par G.n G.m) (rootCl T G) (rootRec T G) E.H (E.H + 21) E.OUT
      (E.H + 30) mem' := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19,
    l20, l21⟩ := hE.lay
  have hn := hE.hn
  have hm := hE.hm
  have hN := hE.hN
  have hs := hE.hs
  have hnS := hE.hnS
  have hok := hE.ok
  have hT := hok.tree
  have hθ := one_le_rootθ (T := T) (G := G)
  have hpm : (pgOf G).m = G.m := pgOf_m
  have hpn : (pgOf G).n = G.n := by simp [pgOf]
  have hlab : ∀ v < G.n, mem' (E.LAB + v) = T.hd (pgOf G) (T.top (rootθ T G) v) := fun v hv => by
    rw [hfr _ (by omega)]; exact hE.lab v hv
  have hhd : ∀ v < G.n, T.hd (pgOf G) (T.top (rootθ T G) v) < T.N := fun v hv =>
    KT.hd_lt hT (KT.top_lt_N hT (by rwa [hpn]) hθ)
  refine ⟨⟨hok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [par, pgOf], ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [hgl, hrl, rootGlob, rootRecL, rootCl_card, hpm, hpn]
  · -- the global block
    refine ⟨hpn.symm, hpm.symm, rfl, rfl, hT, hok.hG, hok.hGo, fun k hk => ?_, fun k h1 h2 => ?_,
      fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun v hv => ?_,
      fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, ?_, fun p hp => ?_, hok.hB, ?_,
      fun p hp => ?_⟩
    all_goals try dsimp only
    · rw [hfr _ (by omega)]; exact (hE.par k hk).1
    · rw [hfr _ (by omega), hfr _ (by omega)]
      exact ⟨(hE.ch k h1 h2).1, (hE.ch k h1 h2).2.1⟩
    · rw [hfr _ (by omega)]; exact (hE.par k hk).2
    · rw [hfr _ (by omega)]; exact (hE.ko k hk).1
    · rw [hfr _ (by omega)]; exact (hE.ko k hk).2.1
    · rw [hfr _ (by omega)]; exact (hE.ko k hk).2.2
    · have := KT.lo_lt hT (show v < (pgOf G).n from hv)
      rw [hfr _ (by rw [hpn] at this; omega)]; exact hE.ordl v hv
    · rw [hpm] at hp
      rw [hfr _ (by omega), hfr _ (by omega)]; exact hE.ends p hp
    · rw [hpm] at hp
      rw [hfr _ (by omega)]; exact hE.pw p hp
    · rw [hpm] at hp
      rw [hfr _ (by omega)]; exact hE.ex p hp
    · refine ⟨fun q => mem (E.LCA + q), fun q hq => hE.lca q (by rwa [hpm] at hq),
        fun u hu => ?_, fun u hu j hj => ?_⟩
      · rw [hfr _ (by omega), hpm]; exact hE.goff u hu
      · simp only [hpm] at hj ⊢
        have h1 := offOf_succ (fun q => mem (E.LCA + q)) G.m u
        have h2 := offOf_le (fun q => mem (E.LCA + q)) G.m (u + 1)
        rw [hfr _ (by omega)]; exact hE.gord u hu j hj
    · exact hE.allowed.fit.ω p hp
    · exact lt_two_pow_J G.n
    · have := Nat.mul_le_mul_left (2 * G.n) (hMw p (by rwa [hpm] at hp))
      rw [hpn]; omega
  · -- the record block
    refine ⟨⟨hnS, hs, fun j hj => ?_, fun j hj => ?_, fun p hp => ?_, fun p hp => ?_,
      fun p hp => ?_, fun v hv => ?_, hE.th⟩, fun i hi => ?_, rfl, rfl, ?_,
      fun j hj => absurd hj (by simp), fun v hv => ?_⟩
    all_goals try dsimp only [RecL.af]
    · rw [hfr _ (by omega)]; exact (hE.sa j hj).1
    · rw [hfr _ (by omega)]; exact (hE.sa j hj).2
    · rw [hpm] at hp
      rw [hfr _ (by omega), hfr _ (by omega)]; exact hE.ends p hp
    · rw [hpm] at hp
      rw [hfr _ (by omega)]; exact hE.pw p hp
    · rw [hpm] at hp
      rw [hfr _ (by omega)]; exact hE.ex p hp
    · have hv' : v < G.n := mem_rootCl.mp hv
      have hk := hok.top_mem hv
      have := hhd v hv'
      rw [hlab v hv', hfr _ (by omega)]
      exact hE.loc _ hk
    · rw [hfr _ (by omega), hE.nodes i hi, List.getD_eq_getElem _ _ hi]
    · simp [Cl.hwE, rootCl, root]
    · exact hlab v (mem_rootCl.mp hv)
  · exact fun v hv => (hlab v hv).symm ▸ hhd v hv
  · exact hz
  · simp only [recRegs, RecL.regs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros <;> omega
  · omega
  · omega
  · unfold RegDisj; omega
  · simp only [recRegs, RecL.regs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, RegDisj]
    and_intros <;> omega
  · simp only [recRegs, RecL.regs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, RegDisj]
    and_intros <;> omega
  · refine ⟨Mw, hMw, ?_, ?_⟩
    · have e : 4 * G.n * Mw = 2 * (2 * G.n * Mw) := by ring
      omega
    · have hR : recCost w A T (pgOf G) (par G.n G.m) (rootCl T G) (rootRec T G) ≤
          clCost w A G T := by
        unfold clCost; omega
      have := root_room (n := G.n) (m := G.m) (N := T.N) (Mw := Mw) (by omega) (by omega)
        (by omega) hMw' hR hw
      omega
  · intro x hx
    rw [hfr _ (by omega)]
    exact hE.loc_w x hx
  · omega
  · simp only [recRegs, RecL.regs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, RegDisj]
    and_intros <;> omega
  · unfold RegDisj; omega
  · unfold RegDisj; omega

end MinCostFlow.LowStretch
