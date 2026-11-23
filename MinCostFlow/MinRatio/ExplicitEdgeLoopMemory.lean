module

public import MinCostFlow.MinRatio.ExplicitEdgeLoop

/-!
# Memory invariant for the explicit route scan

Algorithm 2 (page 29) applies the scaled circulation and accumulates
its absolute value. The scan preserves the two route arrays and the
multiplier. Its heap bound reserves one update workspace for each
remaining row, even though repeated rows require none.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- The stable inputs and the records after processing the first `i` rows. -/
@[expose] def ExplicitEdgeLoopMemory (w h base a L start : ℕ) (edges : List (ℕ × Bool))
    (address : ℕ → ℕ) (old : ℕ → PathEdgeValue) (num : ℤ)
    (original : ℕ → ℕ) (i heap : ℕ) (mem : ℕ → ℕ) : Prop :=
  start ≤ heap ∧ heap + (edges.length - i) * (17 * L + 3) < 2 ^ w ∧
  ExplicitEdgesAt mem base edges ∧ PathIntAt mem a h L num ∧ ZeroFrom mem heap ∧
  ExplicitEdgePrefixAt mem h L edges address old num i ∧ heap ≤ start + i * (17 * L + 3) ∧
  ∀ x < start, (∀ e ∈ edges.map Prod.fst, x < address e + 2 + 2 * L ∨
    address e + 2 + 4 * L ≤ x) → mem x = original x

/-- The original records and the zero tail initialize the scan before
any row has been visited. -/
theorem explicitEdgeLoopMemory_zero {w h base a L start : ℕ} {mem : ℕ → ℕ}
    {edges : List (ℕ × Bool)} {address : ℕ → ℕ} {old : ℕ → PathEdgeValue} {num : ℤ}
    (hroom : start + edges.length * (17 * L + 3) < 2 ^ w)
    (hr : ExplicitEdgesAt mem base edges) (hn : PathIntAt mem a h L num)
    (hz : ZeroFrom mem start)
    (hold : ∀ e ∈ edges.map Prod.fst, PathEdgeAt mem (address e) h L (some (old e))) :
    ExplicitEdgeLoopMemory w h base a L start edges address old num mem 0 start mem :=
  ⟨Nat.le_refl _, hroom, hr, hn, hz, explicitEdgePrefixAt_zero hold, by simp, fun _ _ _ => rfl⟩

/-- With fitting increments and a resolved address array, the machine
loop realizes the prefix updates using the stated quadratic scan cost. -/
theorem explicitEdgeLoop_memory {w h visit base addrBase a L start : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (address : ℕ → ℕ) (old : ℕ → PathEdgeValue) (num : ℤ)
    (original : ℕ → ℕ) (hplaced : base + 2 * edges.length ≤ start ∧ addrBase + edges.length ≤ start ∧ a + L ≤ start)
    (hword : start + 2 < 2 ^ w)
    (hname : ∀ e ∈ edges.map Prod.fst, e < 2 ^ w)
    (hbelow : ∀ e ∈ edges.map Prod.fst,
      address e + 2 + 4 * L ≤ min base (min addrBase a))
    (hdisj : ∀ e ∈ edges.map Prod.fst, ∀ f ∈ edges.map Prod.fst, e ≠ f →
      address e + 2 + 4 * L ≤ address f ∨ address f + 2 + 4 * L ≤ address e)
    (hfit : ∀ e ∈ edges.map Prod.fst,
      let n := (edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)
      Num.Fits h L n ∧ Num.Fits h L (num * n) ∧ Num.Fits h L |num * n| ∧
        Num.Fits h L ((old e).flow + num * n) ∧ Num.Fits h L ((old e).detector + |num * n|))
    (hvisit : ∀ i, MeetsContract w p visit
      (explicitEdgeVisitContract w h edges i (old ((edges[i]?.getD (0, false)).1)) num)) :
    let addresses := edges.map (fun row => address row.1)
    let inv := explicitEdgeLoopInv base addrBase a L addresses
      (ExplicitEdgeLoopMemory w h base a L start edges address old num original)
    Triple w p (inv 0) (explicitEdgeLoop visit) (normalPost (inv edges.length))
      (fun _ => edges.length * (136 * edges.length + 152 * L^2 + 561 * L + 800) + 4) := by
  dsimp only
  obtain ⟨hb, ht, ha⟩ := hplaced
  have hlen : (edges.map (fun row => address row.1)).length = edges.length := List.length_map _
  simpa only [hlen] using
    (explicitEdgeLoop_triple (h := h) (p := p) (visit := visit) (addrBase := addrBase)
      edges (edges.map (fun row => address row.1)) (fun i => old ((edges[i]?.getD (0, false)).1)) num
      (ExplicitEdgeLoopMemory w h base a L start edges address old num original) hlen
      (by rw [hlen]; exact ⟨by omega, by omega, by omega, by omega⟩)
      (by
        intro x hx
        obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hx
        have hb' := hbelow row.1 (List.mem_map.mpr ⟨row, hr, rfl⟩)
        omega)
      hvisit (by
        intro i hi' heap mem hin
        have hi : i < edges.length := hlen ▸ hi'
        have he : edges[i].1 ∈ edges.map Prod.fst :=
          List.mem_map.mpr ⟨edges[i], List.getElem_mem hi, rfl⟩
        obtain ⟨hst, hroom, hr, hn, hz, hrec, hused, hframe⟩ := hin
        have hroom' : heap + (17 * L + 3) < 2 ^ w := by
          have hm := Nat.mul_le_mul_right (17 * L + 3) (show 1 ≤ edges.length - i by omega)
          omega
        have hed := hbelow edges[i].1 he
        rw [List.getElem?_eq_getElem hi]
        refine ⟨by omega, base, address edges[i].1, a, L, heap, hi, ?_, hr, by omega, hname _ he, ?_⟩
        · simp only [hlen, List.getElem_map]
        · intro fresh
          obtain ⟨hc, hp, habs, hf, hd⟩ := hfit _ he
          have hold : PathEdgeAt mem (address edges[i].1) h L (some (old edges[i].1)) := by
            simpa only [explicitEdgePrefixValue, ite_eq_right fresh] using hrec _ he
          exact ⟨base, address edges[i].1, a, L, heap, rfl, hr, by omega,
            ⟨address edges[i].1, a, L, heap, rfl, by omega, by omega, hold, by omega, hn,
              hc, hp, habs, hf, hd, hz, by omega⟩, hroom'⟩)
      (by
        intro i hi' heap mem ret out hin harr hp
        have hi : i < edges.length := hlen ▸ hi'
        have he : edges[i].1 ∈ edges.map Prod.fst :=
          List.mem_map.mpr ⟨edges[i], List.getElem_mem hi, rfl⟩
        obtain ⟨hst, hroom, hr, hn, hz, hrec, hused, hframe⟩ := hin
        simp only [hlen, List.getElem_map, List.getElem?_eq_getElem hi, Option.getD_some] at hp
        have hout := explicitEdgeVisit_preserves_prefix hi address old num
          (fun e he => by have := hbelow e he; omega) (fun e hem hne => hdisj e hem _ he hne) hrec hp
        obtain ⟨_, hp⟩ := hp
        have hrem : edges.length - i = (edges.length - (i + 1)) + 1 := by omega
        rw [hrem, Nat.add_mul, Nat.one_mul] at hroom
        by_cases fresh : edges[i].1 ∉ (edges.take i).map Prod.fst
        · rw [ite_eq_left fresh] at hp
          have hret : ret = heap + (17 * L + 3) := hp.1
          have hcells : ∀ x < heap, x < address edges[i].1 + 2 + 2 * L ∨
              address edges[i].1 + 2 + 4 * L ≤ x → out x = mem x := hp.2.2.1
          have hf : ∀ x < heap, address edges[i].1 + 2 + 4 * L ≤ x → out x = mem x :=
            fun x hx hx' => hp.2.2.1 x hx (Or.inr hx')
          have hed := hbelow edges[i].1 he
          exact ⟨harr.congr (fun x hx hx' => hf x (by omega) (by omega)),
            by omega, by omega, hr.congr (fun x hx hx' => hf x (by omega) (by omega)),
            hn.congr (fun j hj => hf _ (by omega) (by omega)), hp.2.2.2, hout, by rw [Nat.add_mul, Nat.one_mul]; omega,
            fun x hx houtside => (hcells x (by omega) (houtside _ he)).trans (hframe x hx houtside)⟩
        · rw [ite_eq_right fresh] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact ⟨harr, hst, by omega, hr, hn, hz, hout, by rw [Nat.add_mul, Nat.one_mul]; omega, hframe⟩))

end MinCostFlow.MinRatio
