module

public import MinCostFlow.HierPaths.DelProgOutputScan

/-!
# Reporting pruned terminal owners

Scan the lost terminal work list, read each owner, and report vertices whose support cursor
has reached the end. The lost terminal work list is preserved.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Read the owner of the lost-terminal entry at offset register 62. -/
def delOutputOwnerExpr : Expr :=
  readSec numSec 0 1 (.load (.bin .add (.reg 60) (.reg 62)))

/-- Scan the lost-terminal list at register 60 with length in register 61. -/
def delOutputOwners : Stmt := forRange 62 (.const 0) (.reg 61) (delReportRead delOutputOwnerExpr)

theorem delOutputOwners_noRand : delOutputOwners.NoRand := by
  simp [delOutputOwners, forRange, forUp, Stmt.NoRand, delReportRead_noRand]

/-- Report the newly pruned owners of the lost terminals in linear time. -/
theorem delOutputOwners_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base src : ℕ} {ts L : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h58 : R 58 = base) (h59 : R 59 = L.length)
    (h60 : R 60 = src) (h61 : R 61 = ts.length)
    (hb : b + x.encode.length ≤ base) (hsep : base + L.length + x.n ≤ src)
    (hw : base + L.length + x.n + 1 < 2 ^ w) (hsw : src + ts.length < 2 ^ w)
    (ht : ∀ t ∈ ts, t < x.H.A.C.numTerm)
    (hv : ∀ t ∈ ts, x.H.A.C.owner t < x.n)
    (hsrc : ListAt mem0 src ts) :
    let vs := ts.map x.H.A.C.owner
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0) delOutputOwners
      (normalPost fun s =>
        let out := L ++ x.delReports vs
        s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
        (∀ j, 63 ≤ j → s.regs j = R j) ∧
        ListAt s.mem b (x.afterReports vs).encode ∧ ListAt s.mem base out ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => ts.length * (delOutputOwnerExpr.size + 176) + 7) := by
  dsimp only
  let vs := ts.map x.H.A.C.owner
  have hlen : vs.length = ts.length := List.length_map ..
  have hv' : ∀ v ∈ vs, v < x.n := by
    intro v hm
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hm
    exact hv t ht'
  have H := delReportScan_triple (w := w) (p := p) (r := 62) (rhi := 61) (lo := 0)
    (vs := vs) (L := L) (mem0 := mem0) x (.const 0) delOutputOwnerExpr (by decide) (by decide)
    (by decide) hb hw (by rw [hlen]; omega) (by simpa only [Nat.zero_add, hlen] using h61)
    hv' (fun _ _ _ => Expr.eval_const (by omega)) ?_ h0 h58 h59
  · refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by simp [hlen, Expr.size])
    cases o <;> try contradiction
    obtain ⟨h0', h58', h59', he, hB, hL, hf⟩ := h
    exact ⟨h0', h58', h59', fun j hj => he j (by omega) (by omega), hB, hL, hf⟩
  · intro i _ hi s hs
    have hit : i < ts.length := by simpa [hlen] using hi
    let t := ts[i]
    let y := x.afterReports (vs.take (i - 0))
    obtain ⟨hr0, _, _, hregs, hblock, _, hf⟩ := hs
    have hbytes : y.encode.length = x.encode.length := x.length_encode_withVhat _
    have hby : b + y.encode.length < 2 ^ w := by rw [hbytes]; omega
    have hcap := x.delReports_length_le (vs := vs.take (i - 0))
      (fun v hm => hv' v (List.mem_of_mem_take hm))
    have ht' := ht t (List.getElem_mem hit)
    have hs60 : s.regs 60 = src := by
      rw [hregs 60 (by decide), Function.update_of_ne (show 60 ≠ 62 by decide), h60]
    have hs62 : s.regs 62 = i := by rw [hregs 62 (by decide), Function.update_self]
    have hload : (.load (.bin .add (.reg 60) (.reg 62)) : Expr).eval w s = some t := by
      refine Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq hs60) (Expr.eval_reg_of_eq hs62) (by omega)) ?_
      rw [hf _ (Or.inr (by omega))]
      · exact hsrc i hit
      · right
        simp only [List.length_append]
        omega
    have hs1 : y.sections.getD 1 [] = tabList x.H.A.C.numTerm x.H.A.C.owner := rfl
    have hidx : t < (y.sections.getD 1 []).length := by rw [hs1]; simpa using ht'
    have howner : (y.sections.getD 1 [])[t] = x.H.A.C.owner t := by
      rw [← List.getD_eq_getElem _ 0 hidx, hs1]
      simp [tabList, List.getD_eq_getElem?_getD, ht']
    have h := eval_readSec (w := w)
      (show ListAt s.mem b (layoutList y.sections) from hblock)
      hby (r := 0) hr0 (i := 1) (by rw [y.length_sections']; decide) hload hidx
    rw [y.length_sections', howner] at h
    have hivi : i < vs.length := by rwa [hlen]
    simpa only [delOutputOwnerExpr, Nat.sub_zero, List.getD_eq_getElem _ _ hivi, vs, List.getElem_map, t] using h

end MinCostFlow.HierPaths

end
