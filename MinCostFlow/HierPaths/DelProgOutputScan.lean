module

public import MinCostFlow.HierPaths.DelProgOutput

/-!
# Scanning touched vertices for output

The scan appends first reports, sets their bits, and preserves its input. The vertex read is
an expression, so the same scan can read terminal owners or stored walk vertices.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The state after a prefix of a scan over touched vertices. -/
def DelReportScanInv (x : HierConcrete) (b base lo r : ℕ) (vs L : List ℕ)
    (mem0 R : ℕ → ℕ) (i : ℕ) (s : State) : Prop :=
  let seen := vs.take (i - lo)
  let out := L ++ x.delReports seen
  s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
  (∀ j, 60 ≤ j → s.regs j = Function.update R r i j) ∧
  ListAt s.mem b (x.afterReports seen).encode ∧ ListAt s.mem base out ∧
  ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
    (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j

/-- Extending the touched prefix updates the block and output by one report step. -/
theorem delReportScanBody_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base lo r i : ℕ} {vs L : List ℕ} {mem0 R : ℕ → ℕ} (vertex : Expr)
    (hr : 60 ≤ r) (hb : b + x.encode.length ≤ base)
    (hw : base + L.length + x.n + 1 < 2 ^ w)
    (hv : ∀ v ∈ vs, v < x.n)
    (hlo : lo ≤ i) (hi : i < lo + vs.length)
    (hread : ∀ s, DelReportScanInv x b base lo r vs L mem0 R i s →
      vertex.eval w s = some (vs.getD (i - lo) 0)) :
    Triple w p (DelReportScanInv x b base lo r vs L mem0 R i) (delReportRead vertex)
      (normalPost fun s => DelReportScanInv x b base lo r vs L mem0 R (i + 1)
        { s with regs := Function.update s.regs r (i + 1) } ∧ s.regs r = i)
      (fun _ => vertex.size + 167) := by
  have hk : i - lo < vs.length := by omega
  have hsub : i + 1 - lo = i - lo + 1 := by omega
  let v := vs[i - lo]
  let seen := vs.take (i - lo)
  let y := x.afterReports seen
  let out := L ++ x.delReports seen
  let out' := out ++ y.delReports [v]
  have hnext : vs.take (i + 1 - lo) = seen ++ [v] := by
    rw [hsub, List.take_succ_eq_append_getElem hk]
  have hylen : y.encode.length = x.encode.length := x.length_encode_withVhat _
  have hyn : y.n = x.n := rfl
  have hstate : x.afterReports (vs.take (i + 1 - lo)) = y.afterReports [v] := by
    rw [hnext, x.afterReports_append_one]
    simpa only [List.nil_append, HierConcrete.afterReports_nil] using
      (y.afterReports_append_one [] v).symm
  have hlist : L ++ x.delReports (vs.take (i + 1 - lo)) = out' := by
    rw [hnext, x.delReports_append, ← List.append_assoc]
    rfl
  have hlen : out.length ≤ L.length + x.n := by
    simp only [out, List.length_append]
    exact Nat.add_le_add_left (x.delReports_length_le (fun v hm => hv v (List.mem_of_mem_take hm))) _
  have hlen₁ : L.length ≤ out.length := by simp [out]
  have hlen₂ : out.length ≤ out'.length := by simp [out']
  have hfit : base + out.length + 1 < 2 ^ w := by omega
  have hsep : b + y.encode.length ≤ base := (congrArg (b + ·) hylen).le.trans hb
  intro s ω hs
  have hvertex := hread s hs
  rw [List.getD_eq_getElem _ _ hk] at hvertex
  obtain ⟨h0, h58, h59, hex, hB, hL, hf⟩ := hs
  have H := delReportRead_triple (w := w) (p := p) (R := s.regs) (L := out) (mem0 := s.mem)
    y h0 h58 h59 (by rw [hyn]; exact hv _ (List.getElem_mem hk)) hsep hfit
    (fun t hregs hm => by
      have hts : DelReportScanInv x b base lo r vs L mem0 R i t := by
        exact ⟨hregs.symm ▸ h0, hregs.symm ▸ h58, hregs.symm ▸ h59, hregs.symm ▸ hex,
          hm.symm ▸ hB, hm.symm ▸ hL, hm.symm ▸ hf⟩
      simpa only [List.getD_eq_getElem _ _ hk] using hread t hts)
  have HF := Triple.regs_frame (delReportRead_writesBelow vertex) H s.regs
  obtain ⟨o, s', c, hrun, hpost, hc⟩ := HF s ω ⟨⟨rfl, hB, hL, rfl⟩, fun _ _ => rfl⟩
  cases o <;> try exact False.elim hpost.1
  obtain ⟨⟨h0', h58', h59', hB', hL', hf'⟩, hex'⟩ := hpost
  change s'.regs 59 = out'.length at h59'
  change ∀ j, (j < b ∨ b + y.encode.length ≤ j) →
    (j < base + out.length ∨ base + out'.length ≤ j) → s'.mem j = s.mem j at hf'
  change ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
    (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j at hf
  refine ⟨_, s', c, hrun, ?_, hc⟩
  change DelReportScanInv x b base lo r vs L mem0 R (i + 1) _ ∧ _
  simp only [DelReportScanInv, hstate, hlist]
  have hn0 : 0 ≠ r := by omega
  have hn58 : 58 ≠ r := by omega
  have hn59 : 59 ≠ r := by omega
  refine ⟨⟨by simpa [Function.update_of_ne hn0] using h0',
    by simpa [Function.update_of_ne hn58] using h58',
    by simpa [Function.update_of_ne hn59] using h59',
    ?_, hB', hL', ?_⟩, (hex' r hr).trans (by simp [hex r hr])⟩
  · intro j hj
    by_cases he : j = r
    · subst j; simp
    · simpa [Function.update_of_ne he] using (hex' j hj).trans (hex j hj)
  · intro j hj hj'
    have hjy : j < b ∨ b + y.encode.length ≤ j := by rwa [hylen]
    rw [hf' j hjy (by omega)]
    exact hf j hj (by omega)

/-- Scan a fixed interval of touched vertices and append all first reports in that interval. -/
theorem delReportScan_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base lo r rhi : ℕ} {vs L : List ℕ} {mem0 R : ℕ → ℕ} (start vertex : Expr)
    (hr : 60 ≤ r) (hrhi : 60 ≤ rhi) (hne : rhi ≠ r)
    (hb : b + x.encode.length ≤ base) (hw : base + L.length + x.n + 1 < 2 ^ w)
    (hhi : lo + vs.length < 2 ^ w) (hRhi : R rhi = lo + vs.length)
    (hv : ∀ v ∈ vs, v < x.n)
    (hstart : ∀ s, s.regs = R → ListAt s.mem b x.encode → start.eval w s = some lo)
    (hread : ∀ i, lo ≤ i → i < lo + vs.length → ∀ s,
      DelReportScanInv x b base lo r vs L mem0 R i s →
      vertex.eval w s = some (vs.getD (i - lo) 0))
    (h0 : R 0 = b) (h58 : R 58 = base) (h59 : R 59 = L.length) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0)
      (forRange r start (.reg rhi) (delReportRead vertex))
      (normalPost fun s =>
        let out := L ++ x.delReports vs
        s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
        (∀ j, 60 ≤ j → j ≠ r → s.regs j = R j) ∧
        ListAt s.mem b (x.afterReports vs).encode ∧ ListAt s.mem base out ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => vs.length * (vertex.size + 176) + (start.size + 6)) := by
  have hone : 1 < 2 ^ w := by omega
  have H := Triple.forRange_const (w := w) (p := p) (r := r) (lo := start) (hi := .reg rhi)
    (Inv := DelReportScanInv x b base lo r vs L mem0 R) (vertex.size + 167) lo (lo + vs.length)
    (Nat.le_add_right ..) hone (fun _ => hhi)
    (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem base L ∧ s.mem = mem0)
    (fun s hs => ⟨hstart s hs.1 hs.2.1, ?_⟩)
    (fun i s _ _ h => by simpa using h.2.2.2.1 r hr)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq (by
      rw [h.2.2.2.1 rhi hrhi, Function.update_of_ne hne, hRhi]))
    (fun i hlo hi => delReportScanBody_triple x vertex hr hb hw hv hlo hi (hread i hlo hi))
  · refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by simp [Expr.size, Nat.add_assoc])
    cases o <;> try contradiction
    change DelReportScanInv x b base lo r vs L mem0 R (lo + vs.length) s at h
    simp only [DelReportScanInv, Nat.add_sub_cancel_left, List.take_length] at h
    obtain ⟨h0', h58', h59', hex, hB, hL, hf⟩ := h
    exact ⟨h0', h58', h59', fun j hj hne' => by simpa [Function.update_of_ne hne'] using hex j hj,
      hB, hL, hf⟩
  · obtain ⟨he, hB, hL, hm⟩ := hs
    simp only [DelReportScanInv, Nat.sub_self, List.take_zero, HierConcrete.afterReports_nil]
    have ho : x.delReports [] = [] := rfl
    rw [ho, List.append_nil]
    refine ⟨?_, ?_, ?_, ?_, hB, hL, fun j _ _ => congrFun hm j⟩
    · simpa [he, Function.update_of_ne (show 0 ≠ r by omega)] using h0
    · simpa [he, Function.update_of_ne (show 58 ≠ r by omega)] using h58
    · simpa [he, Function.update_of_ne (show 59 ≠ r by omega)] using h59
    · intro j _
      rw [he]

end MinCostFlow.HierPaths

end
