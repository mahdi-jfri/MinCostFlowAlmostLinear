module

public import MinCostFlow.LowStretch.ProgClusterSetupLd

/-!
# The setup of a cluster: the words of the loads from `ClPre`

Under `ClPre`, the loads of `setupP` read the words of the global block and of the record
block (`suVOf`), and every address they read is a word (`ClPre.suFacts`). The bound on the
addresses comes from `ClPre.room`, which leaves `2^24` free words above the heap pointer
(`ClPre.room_h`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- The words that the loads of `setupP` put in the registers, read from the memory. -/
def suVOf (GB RB h : ℕ) (mem : ℕ → ℕ) : SuV :=
  let E := GlobL.read mem GB
  let L := RecL.read mem RB
  ⟨GB, RB, h, E.n, E.m, E.IN, E.PW, E.EXP, E.LAB, E.LOC, E.B, E.J, E.INF, L.s, L.nS, L.SA, L.lθ,
    mem (E.LOC + mem (E.LAB + L.x0)), L.t, L.nH, L.HW, mem (E.LOC + mem (E.LAB + L.t))⟩

/-- **Room above the heap**: `h + 2^24 < 2^w`. -/
theorem ClPre.room_h (hp : ClPre w A T G P c R GB RB h mem) : h + 2 ^ 24 < 2 ^ w := by
  obtain ⟨Mw, -, -, hr⟩ := hp.room_sq
  have h1 : 2 ^ 20 ≤ 2 ^ (2 * (GlobL.read mem GB).J + 20) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ 2 ≤ (T.N + G.m + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : 2 ^ 2 ≤ (Mw + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h4 : 2 ^ 20 * 2 ^ 2 * 2 ^ 2 ≤ 2 ^ (2 * (GlobL.read mem GB).J + 20) * (T.N + G.m + 2) ^ 2 *
      (Mw + 2) ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have h5 : (2 : ℕ) ^ 24 = 2 ^ 20 * 2 ^ 2 * 2 ^ 2 := by norm_num
  omega

/-- The target of a cluster is one of its vertices. -/
theorem Cl.Inv.t_mem (hc : c.Inv G P) : c.t ∈ c.X := by
  have := hc.good.high.hv_mem (i := 0) (Nat.zero_le _); rwa [Cl.hv_zero] at this

/-- **The facts of the loads** under `ClPre`. -/
theorem ClPre.suFacts (hp : ClPre w A T G P c R GB RB h mem) : SuFacts w (suVOf GB RB h mem) mem := by
  have hroom := hp.room_h
  have hGB : GB + 21 ≤ h := hp.below (GB, 21) (by simp [recRegs])
  have hRB : RB + 9 ≤ h := hp.below (RB, 9) (by simp [recRegs])
  have hx0 : mem (RB + 5) = c.x0 := hp.recAt.x0
  have ht : mem (RB + 6) = c.t := hp.recAt.t
  have hx0n : c.x0 < G.n := hp.ok.n_of_mem hp.ok.inv.good.conn.1
  have htn : c.t < G.n := hp.ok.n_of_mem hp.ok.inv.t_mem
  have hn : (GlobL.read mem GB).n = G.n := hp.glob.n
  have hlab := hp.lab_below
  have hloc := hp.loc_below
  have hl1 := hp.lab_lt c.x0 hx0n
  have hl2 := hp.lab_lt c.t htn
  have e1 : (RecL.read mem RB).x0 = mem (RB + 5) := rfl
  have e2 : (RecL.read mem RB).t = mem (RB + 6) := rfl
  have e3 : (GlobL.read mem GB).LAB = mem (GB + 6) := rfl
  have e4 : (GlobL.read mem GB).LOC = mem (GB + 7) := rfl
  rw [e3] at hlab hl1 hl2
  rw [e4] at hloc
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, show GB + 21 < 2 ^ w by omega, show RB + 9 < 2 ^ w by omega,
    show h + 51 < 2 ^ w by omega, ?_, ?_⟩
  · simp only [suVOf, e1, e2, e3, hx0, ht]; omega
  · simp only [suVOf, e1, e2, e3, e4, hx0, ht]; omega

end MinCostFlow.LowStretch
