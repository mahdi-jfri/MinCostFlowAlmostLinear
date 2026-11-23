module

public import MinCostFlow.Spanner.ProgFlatten
public import MinCostFlow.Spanner.ProgDedup

@[expose] public section

/-!
# The Kept Edges

The kept edges of `Sparsify` are the edges of `J` used by the embedding of `W` into `J`, without
repeats: `(flatEdges embWJ W.m).dedup`. The procedure `keptEdgesBody` first lists the edges of
all walks (`flatEdgesBody`) at `h0`, and then removes the repeats (`dedupListBody`) into the
words right after that list. It returns the number of kept edges. The result is
`keptEdges_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- Every listed edge is an edge of one of the first `k` walks. -/
lemma mem_flatEdges {emb : ℕ → Walk} {k x : ℕ} (hx : x ∈ flatEdges emb k) :
    ∃ e < k, x ∈ (emb e).edges := by
  unfold flatEdges at hx
  rw [List.mem_flatMap] at hx
  obtain ⟨e, he, hxe⟩ := hx
  exact ⟨e, List.mem_range.mp he, hxe⟩

/-- Procedure body, at `args = [E, m, h0, L, bound]`. `ff` holds `flatEdgesBody` and `fd` holds
`dedupListBody`. -/
def keptEdgesBody (ff fd : ℕ) : Stmt :=
  .call 5 ff [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 6 fd [.reg 2, .reg 5, .reg 4, .bin .add (.reg 2) (.reg 5),
    .bin .add (.bin .add (.reg 2) (.reg 5)) (.reg 5)] ;;
  .ret (.reg 6)

/-- The pre of `keptEdgesBody`: the pre of `flatEdgesBody` at `h0`, every edge below `bound`,
free memory from `h0` on, and room for three lists and the marker table. -/
def KeptEdgesPre (mem : ℕ → ℕ) (E m h0 L bound : ℕ) (emb : ℕ → Walk) (w : ℕ) : Prop :=
  FlatEdgesPre mem E m h0 L emb w ∧ (∀ e < m, ∀ x ∈ (emb e).edges, x < bound) ∧
    ZeroFrom mem h0 ∧ h0 + 3 * (m * L) + bound < 2 ^ w

/-- Contract of `keptEdgesBody`. -/
def keptEdgesContract (w : ℕ) : Contract where
  pre args mem := ∃ E m h0 L bound emb, args = [E, m, h0, L, bound] ∧
    KeptEdgesPre mem E m h0 L bound emb w
  post args mem v mem' := ∀ E m h0 L bound emb, args = [E, m, h0, L, bound] →
    KeptEdgesPre mem E m h0 L bound emb w →
    v = (flatEdges emb m).dedup.length ∧
      ListAt mem' (h0 + (flatEdges emb m).length) (flatEdges emb m).dedup ∧
      ∀ x < h0, mem' x = mem x
  cost args _ :=
    args.getD 1 0 * (20 * args.getD 3 0 + 120) + 115 * (args.getD 1 0 * args.getD 3 0) + 120

theorem keptEdges_meetsContract {w : ℕ} {p : Program} {f ff fd : ℕ}
    (hproc : p.procs[f]? = some (keptEdgesBody ff fd))
    (hff : MeetsContract w p ff (flatEdgesContract w))
    (hfd : MeetsContract w p fd (dedupListContract w)) :
    MeetsContract w p f (keptEdgesContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨E, m, h0, L, bound, emb, rfl, hK⟩ := hpre
  have hK' := hK
  obtain ⟨hF, hlt, hZ, hroom⟩ := hK'
  have hF' := hF
  obtain ⟨hEmb, hBnd, hL, hdw, hw1⟩ := hF'
  have hflat := flatEdges_length_le hL m
  have hw : ∀ a ∈ [E, m, h0, L, bound], a < 2 ^ w := hwords
  have hEw := hw E (by simp); have hmw := hw m (by simp); have hhw := hw h0 (by simp)
  have hLw := hw L (by simp); have hbw := hw bound (by simp)
  refine runs_start_le ?_
  refine runs_seq_call_le (vs := [E, m, h0, L]) hff
    (by simp [evalArgs, Expr.eval, startState, hEw, hmw, hhw, hLw]) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> assumption)
    ⟨E, m, h0, L, emb, rfl, hF⟩ ?_
  intro v1 mem1 pos1 hpost1
  obtain ⟨hv1, hlist1, hout1⟩ := hpost1 E m h0 L emb rfl hF
  set xs := flatEdges emb m with hxs
  have hv1w : v1 < 2 ^ w := by omega
  let st1 : State :=
    { mem := mem1, regs := Function.update (startState [E, m, h0, L, bound] mem pos).regs 5 v1,
      pos := pos1 }
  have r2 : st1.regs 2 = h0 := by simp [st1, startState]
  have r4 : st1.regs 4 = bound := by simp [st1, startState]
  have r5 : st1.regs 5 = v1 := by simp [st1]
  refine runs_seq_call_le (vs := [h0, v1, bound, h0 + v1, h0 + v1 + v1]) hfd ?_ ?_
    ⟨h0, v1, bound, h0 + v1, h0 + v1 + v1, xs, rfl, hv1.symm, ?_, ?_, hw1, by omega, by omega,
      by omega, ?_⟩ ?_
  · have a1 : (Expr.bin .add (.reg 2) (.reg 5)).eval w st1 = some (h0 + v1) :=
      ev_add (ev_reg r2 hhw) (ev_reg r5 hv1w) (by omega)
    have a2 : (Expr.bin .add (.bin .add (.reg 2) (.reg 5)) (.reg 5)).eval w st1 =
        some (h0 + v1 + v1) := ev_add a1 (ev_reg r5 hv1w) (by omega)
    show evalArgs w st1 _ = _
    simp [evalArgs, ev_reg r2 hhw, ev_reg r5 hv1w, ev_reg r4 hbw, a1, a2]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  · exact hlist1
  · intro x hx
    obtain ⟨e, he, hxe⟩ := mem_flatEdges hx
    exact hlt e he x hxe
  · intro a ha
    show mem1 a = 0
    rw [hout1 a (Or.inr (by omega))]
    exact hZ a (by omega)
  intro v2 mem2 pos2 hpost2
  obtain ⟨hv2, hlist2, -, hbelow2, -⟩ :=
    hpost2 h0 v1 bound (h0 + v1) (h0 + v1 + v1) xs rfl hv1.symm hlist1
  refine runs_ret_le (v := v2) (ev_reg (by simp) (by
    have := (List.dedup_sublist xs).length_le; omega)) (fun E' m' h0' L' bound' emb' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
    have hE : xs = flatEdges emb' m :=
      flatEdges_congr fun j hj => walkAt_unique (hEmb j hj) (h2.1.1 j hj)
    rw [← hE, ← hv1]
    exact ⟨hv2, hlist2, fun x hx => (hbelow2 x (by omega)).trans (hout1 x (Or.inl hx))⟩
  · simp only [Expr.size, argsSize, flatEdgesContract, dedupListContract, keptEdgesContract,
      List.getD_cons_succ, List.getD_cons_zero]
    have := Nat.mul_le_mul_left 115 (hv1 ▸ hflat : v1 ≤ m * L)
    omega

end MinCostFlow.Spanner
