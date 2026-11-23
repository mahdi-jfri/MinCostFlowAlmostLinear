module

public import MinCostFlow.LowStretch.ProgRecFit
public import MinCostFlow.LowStretch.ProgRecLoop

/-!
# The body: a single vertex, or the node part

The body of the cluster procedure first reads the number `s` of super-vertices of the record.
A cluster with at most one super-vertex is a single vertex (`Rec.Ok.card_le_one`): all its
vertices are joined to the center by light pairs, so its radius is `0`, and a cluster with two
vertices has a positive radius (`Cl.Inv.Δ_pos`). Then the body writes the end `h + 4` of its heap
and returns at once. It must not run the setup there: the setup pays `150 J` for its queues, and
a single vertex has no child to pay for it.

Otherwise the cluster has at least two vertices (`Rec.Ok.two_le`), and the body calls the *node
part* (`MeetsNode`): the setup, the petals and the child step. `bodyP_meets` shows that the body
meets `MeetsBody` when the node part meets `MeetsNode`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec}

/-! ### A single vertex -/

/-- **A record with at most one super-vertex holds a single vertex.** -/
theorem Rec.Ok.card_le_one (h : R.Ok T G P c) (hs : R.nodes.length ≤ 1) : c.X.card ≤ 1 := by
  have hc := h.inv
  have hx0 := hc.good.conn.1
  by_contra hX
  have hpos := hc.Δ_pos h.hB (by omega)
  have hzero : c.Δ G = 0 := by
    refine Nat.eq_zero_of_le_zero (Finset.sup_le fun y hy => ?_)
    have hsame : T.top c.θ c.x0 = T.top c.θ y := by
      obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem (h.top_mem hx0)
      obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem (h.top_mem hy)
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0 hj0
      rw [← hiy, ← hjy]
    obtain ⟨ps, hps⟩ := (Cl.lconn_iff h.tree h.hG h.sat h.sub hc.one_le hx0 hy).mpr hsame
    have := PG.dist_le (len := c.len G) (hps.mono le_rfl (Set.subset_univ _))
    rw [Cl.wlen_light hps] at this
    exact this
  omega

/-- **A record with two super-vertices holds at least two vertices**: each super-vertex has a
leaf below it, and the two leaves are different vertices of the cluster. -/
theorem Rec.Ok.two_le (h : R.Ok T G P c) (hs : 2 ≤ R.nodes.length) : 2 ≤ c.X.card := by
  have hmem : ∀ i (hi : i < R.nodes.length), ∃ v ∈ c.X, T.top c.θ v = R.nodes[i] := by
    intro i hi
    have hk := List.getElem_mem hi
    obtain ⟨v, hv, hu⟩ := KT.exists_leaf h.tree _ (h.node_lt _ hk)
    have htop := h.node_top _ hk v hv hu
    exact ⟨v, (h.X_iff v).mpr ⟨hv, htop ▸ hk⟩, htop⟩
  obtain ⟨a, ha, hta⟩ := hmem 0 (by omega)
  obtain ⟨b, hb, htb⟩ := hmem 1 (by omega)
  have hne : a ≠ b := by
    intro e
    subst e
    have := (List.Nodup.getElem_inj_iff h.nodup).mp (hta.symm.trans htb)
    omega
  exact Finset.one_lt_card.mpr ⟨a, ha, b, hb, hne⟩

/-! ### The contract of the node part -/

/-- **The contract of the node part.** Procedure `f` of `p`, called with `[GB, RB, h]` on a
memory that meets `ClPre`, with volume weights at least `1`, for a record with at least two super-vertices, ends as `BodyPost`
says, with `20` steps to spare for the body around it. -/
def MeetsNode (w A : ℕ) (p : Program) (f : ℕ) : Prop :=
  ∀ (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (GB RB h : ℕ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool), ClPre w A T G P c R GB RB h mem → (∀ q, 1 ≤ P.cw q) → P = par G.n G.m →
    2 ≤ R.nodes.length →
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' cost,
      Runs w p ω body (startState [GB, RB, h] mem pos) o st' cost ∧
      BodyPost w A T G P c R (GlobL.read mem GB) h mem st'.mem (cost + 20)

/-! ### The body -/

/-- **The body**, called with `[GB, RB, h]`. On a record with at most one super-vertex it writes
`h + 4` at `h + 2` and returns (the cell `h` is `0` already). Otherwise it calls the node part at
`bNode`. -/
def bodyP (bNode : ℕ) : Stmt :=
  .seq (.assign 3 (.load (.reg 1)))
  (.cond (.bin .lt (.const 1) (.reg 3))
    (.seq (.call 4 bNode [.reg 0, .reg 1, .reg 2]) (.ret (.const 0)))
    (.seq (.store (.bin .add (.reg 2) (.const 2)) (.bin .add (.reg 2) (.const 4)))
      (.ret (.const 0))))

theorem bodyP_noRand (bNode : ℕ) : (bodyP bNode).NoRand := by
  simp [bodyP, Stmt.NoRand]

/-- A smaller cost keeps `BodyPost`. -/
theorem BodyPost.mono {w A : ℕ} {E : GlobL} {h : ℕ} {mem mem' : ℕ → ℕ} {cost cost' : ℕ}
    (hb : BodyPost w A T G P c R E h mem mem' cost) (hc : cost' ≤ cost) :
    BodyPost w A T G P c R E h mem mem' cost' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with ⟨a, b, d, e⟩ | ⟨D, cs, Rs, a, b, d, e, f, g⟩
  · exact Or.inl ⟨a, b, d, by omega⟩
  · exact Or.inr ⟨D, cs, Rs, a, b, d, e, f, by omega⟩

/-- **The body meets its contract** when the node part does, for `A ≥ 100`. -/
theorem bodyP_meets {w A : ℕ} {p : Program} {f bNode : ℕ}
    (hp : p.procs[f]? = some (bodyP bNode)) (hN : MeetsNode w A p bNode) (hA : 100 ≤ A) :
    MeetsBody w A p f := by
  intro T G P c R GB RB h mem pos ω hpre hcw hPp
  have hL : 1 ≤ P.L := hpre.L_eq ▸ pL_pos _
  obtain ⟨Mw, -, -, hroom⟩ := hpre.room_sq
  have h20 : 2 * (GlobL.read mem GB).J + 20 < 2 ^ (2 * (GlobL.read mem GB).J + 20) :=
    Nat.lt_two_pow_self
  have hpos : 1 ≤ (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 :=
    Nat.mul_pos (pow_pos (by omega) 2) (pow_pos (by omega) 2)
  have hbig : h + 20 < 2 ^ w := by
    generalize 2 ^ (2 * (GlobL.read mem GB).J + 20) = K at h20 hroom
    have := Nat.mul_le_mul (le_refl K) hpos
    have e : K * (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 = K * ((T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2) := by
      ring
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hs : (RecL.read mem RB).s = R.nodes.length := hpre.recAt.arcs.s
  have hs' : mem RB = R.nodes.length := hs
  refine ⟨_, hp, ?_⟩
  by_cases h2 : 2 ≤ R.nodes.length
  · obtain ⟨body, hb, o, st', cn, hr, hpost⟩ := hN T G P c R GB RB h mem pos ω hpre hcw hPp h2
    obtain ⟨o', st'', c', hr', hq, hc⟩ :
        ∃ o' st'' c', Runs w p ω (bodyP bNode) (startState [GB, RB, h] mem pos) o' st'' c' ∧
          st''.mem = st'.mem ∧ c' ≤ cn + 20 := by
      refine runs_start_le ?_
      unfold bodyP
      refine runs_seq_assign_le (v := R.nodes.length)
        (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hs') ?_
      refine runs_cond_le (v := 1) (Expr.eval_lt_true (Expr.eval_const hw1)
        (Expr.eval_reg_of_eq (v := R.nodes.length) (by simp)) (by omega) hw1) (fun _ => ?_) (fun h0 => absurd h0 (by omega))
      refine runs_seq_call_runs (vs := [GB, RB, h])
        (Post := fun c v M => c = cn ∧ M = st'.mem) ⟨body, hb, o, st', cn, hr, rfl, rfl⟩
        (by simp [evalArgs, Expr.eval, startState]) ?_
      rintro c v M pos' ⟨rfl, rfl⟩
      refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) rfl ?_
      simp only [Expr.size, argsSize]
      omega
    exact ⟨o', st'', c', hr', hq ▸ hpost.mono (by omega)⟩
  · have hX := hpre.ok.card_le_one (by omega)
    have hzero := hpre.zero
    have hlab := hpre.lab_below
    have hloc := hpre.loc_below
    obtain ⟨o', st'', c', hr', hq, hc⟩ :
        ∃ o' st'' c', Runs w p ω (bodyP bNode) (startState [GB, RB, h] mem pos) o' st'' c' ∧
          st''.mem = Function.update mem (h + 2) (h + 4) ∧ c' ≤ 30 := by
      refine runs_start_le ?_
      unfold bodyP
      refine runs_seq_assign_le (v := R.nodes.length)
        (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hs') ?_
      refine runs_cond_le (v := 0) (Expr.eval_lt_false (Expr.eval_const hw1)
        (Expr.eval_reg_of_eq (v := R.nodes.length) (by simp)) (by omega) hw1) (fun h0 => absurd rfl h0) (fun _ => ?_)
      refine runs_seq_store_le (x := h + 2) (v := h + 4)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
          (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
          (by omega)) ?_
      refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) (by simp [startState]) ?_
      simp only [Expr.size]
      omega
    refine ⟨o', st'', c', hr', ?_⟩
    rw [hq]
    have hAL : 100 ≤ A * P.L := le_trans hA (Nat.le_mul_of_pos_right _ hL)
    refine ⟨fun a ha _ => Function.update_of_ne (by omega) _ _, fun u hu => ?_, fun x hx => ?_,
      by simp, fun a ha => ?_, Or.inl ⟨hX, ?_, ?_, ?_⟩⟩
    · rw [Function.update_of_ne (by omega)]
      exact hpre.lab_lt u hu
    · rw [Function.update_of_ne (by omega)]
      exact hpre.loc_w x hx
    · simp only [Function.update_self] at ha
      rw [Function.update_of_ne (by omega)]
      exact hzero a (by omega)
    · rw [Function.update_of_ne (by omega)]
      exact hzero h le_rfl
    · simp
    · have := Nat.le_mul_of_pos_right (A * P.L) (Nat.succ_pos R.S.length)
      generalize A * P.L * (R.S.length + 1) = Y at this ⊢
      omega

end MinCostFlow.LowStretch
