module

public import MinCostFlow.NarrowProg.Stage0ResFwd
public import MinCostFlow.NarrowProg.Stage0FeasBuild
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 5 (Pass Rev & Builder): `stage0ResRevStep`, `stage0ResPassRev`, and `stage0ResBuild`

Builds the reverse residual arcs (`f e > 0`, pointing capacity directly into `pFeasFlow`) and
combines Pass Fwd, Pass Rev, and `writeStage1Hdr` into `stage0ResBuild`, producing the complete
Stage 1 input descriptor and arrays for `R' = ((shiftedGraph I hv).residual f).withoutZeroEdges`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Helper lemmas for Pass Rev -/

private theorem resRev_set_map {α : Type} (xs ys : List α) (g h : α → ℕ) (a : α) (cap : ℕ)
    (hlt : xs.length + ys.length < cap) :
    ((xs.map g ++ ys.map h) ++ List.replicate (cap - (xs.length + ys.length)) 0).set
        (xs.length + ys.length) (h a) =
      (xs.map g ++ (ys ++ [a]).map h) ++ List.replicate (cap - (xs.length + (ys ++ [a]).length)) 0 := by
  have hlen : (xs.map g ++ ys.map h).length = xs.length + ys.length := by simp
  have h1 := list_set_append_replicate (xs := xs.map g ++ ys.map h) (cap := cap) (v := h a) (by omega)
  have hcap : cap - (xs.length + ys.length + 1) = cap - (xs.length + (ys ++ [a]).length) := by
    simp; omega
  rw [hlen] at h1
  rw [h1, List.map_append, List.map_singleton, hcap]
  simp only [List.append_assoc]

private theorem resRev_set_costPtrs (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (pCostBuf2 cap i : ℕ) (hi : i < I.m)
    (hpos : 0 < (f ⟨i, hi⟩).toNat)
    (hlt : (resFwdPos I hv f I.m).length + (resRevPos I f i).length < cap) :
    let fwd := resFwdPos I hv f I.m
    let fwdCL := edgeCostLimbList I fwd
    let ys := resRevPos I f i
    let cl := fwdCL ++ edgeCostLimbList I ys
    (List.ofFn (fun t : Fin (fwd.length + ys.length) =>
        pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
        List.replicate (cap - (fwd.length + ys.length)) 0).set
        (fwd.length + ys.length) (pCostBuf2 + cl.flatten.length) =
      List.ofFn (fun t : Fin (fwd.length + (resRevPos I f (i + 1)).length) =>
        pCostBuf2 + (((fwdCL ++ edgeCostLimbList I (resRevPos I f (i + 1))).take t.val).map List.length).sum) ++
        List.replicate (cap - (fwd.length + (resRevPos I f (i + 1)).length)) 0 := by
  dsimp only
  set e0 : Fin I.m := ⟨i, hi⟩
  set k := narrowLimbWidth I
  set fwd := resFwdPos I hv f I.m
  set fwdCL := edgeCostLimbList I fwd
  set ys := resRevPos I f i
  set cl := fwdCL ++ edgeCostLimbList I ys
  have hsucc' : resRevPos I f (i + 1) = ys ++ [e0] := by
    rw [resRevPos_succ I f hi, ite_eq_left hpos]
  have hcl_next : fwdCL ++ edgeCostLimbList I (resRevPos I f (i + 1)) =
      cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs] := by
    rw [hsucc']; simp [edgeCostLimbList, cl, k, List.append_assoc]
  have hcl_len : cl.length = fwd.length + ys.length := by simp [cl, fwdCL, edgeCostLimbList]
  have h1 := list_set_append_replicate
    (xs := List.ofFn (fun t : Fin (fwd.length + ys.length) => pCostBuf2 + ((cl.take t.val).map List.length).sum))
    (cap := cap) (v := pCostBuf2 + cl.flatten.length) (by simp; exact hlt)
  simp only [List.length_ofFn] at h1
  rw [h1, hcl_next, hsucc']
  have hsnoc := resCostPtrs_snoc pCostBuf2 cl (Nat.digits (2 ^ k) (I.edge e0).cost.natAbs)
  have hlen_cl1 : (cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs]).length =
      fwd.length + (ys ++ [e0]).length := by simp [hcl_len]; omega
  have hof1 : List.ofFn (fun t : Fin (fwd.length + (ys ++ [e0]).length) =>
      pCostBuf2 + (((cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs]).take t.val).map List.length).sum) =
      List.ofFn (fun t : Fin (cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs]).length =>
      pCostBuf2 + (((cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs]).take t.val).map List.length).sum) := by
    apply List.ext_getElem (by simp [hlen_cl1])
    intro r _ _; simp only [List.getElem_ofFn]
  have hof0 : List.ofFn (fun t : Fin cl.length =>
      pCostBuf2 + ((cl.take t.val).map List.length).sum) =
      List.ofFn (fun t : Fin (fwd.length + ys.length) =>
      pCostBuf2 + ((cl.take t.val).map List.length).sum) := by
    apply List.ext_getElem (by simp [hcl_len])
    intro r _ _; simp only [List.getElem_ofFn]
  rw [hof1, hsnoc, hof0]; simp; omega

/-! ### `stage0ResRevStep`: single iteration of the reverse residual pass -/

wram_def stage0ResRevStep (cLen revEmit : ℕ)
    (pEdges, eOff, pFeasFlow, fOff, pCostBuf2, cOff, L, i, j,
     pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut) {
  capLen := cLen(pFeasFlow + fOff, L)
  if 0 < capLen {
    cLenE := revEmit(pEdges, eOff, pFeasFlow + fOff, pCostBuf2, cOff, capLen, i, j,
      pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2)
    mem[pCOffOut] := cOff + cLenE
    return j + 1
  } else {
    mem[pCOffOut] := cOff
    return j
  }
}

structure ResRevStepData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  cap : ℕ
  bufCap : ℕ
  pCapBuf2 : ℕ
  cOffCell : ℕ
  i : ℕ
  hi : i < I.m

def stage0ResRevStepSpec (w : ℕ) : Spec ResRevStepData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pFeasFlow : ℕ) (pCostBuf2 : ℕ)
      (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let fwdCL := edgeCostLimbList d.I fwd
    let ys := resRevPos d.I d.f d.i
    let cl := fwdCL ++ edgeCostLimbList d.I ys
    ⌜args = [pEdges, d.i * 11, pFeasFlow, d.i * d.L, pCostBuf2, cl.flatten.length, d.L, d.i,
        fwd.length + ys.length,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut] ∧
      1 ≤ d.L ∧ 2 * d.I.m ≤ d.cap ∧ 2 * totCostLimbs d.I ≤ d.bufCap ∧
      (∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (d.f e).toNat).length ≤ d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pCostBuf2 + d.bufCap < 2 ^ w ∧ d.bufCap < 2 ^ w ∧
      pTail2 + d.cap ≤ 2 ^ w ∧ pHead2 + d.cap ≤ 2 ^ w ∧
      pCapPtr2 + d.cap ≤ 2 ^ w ∧ pCapLen2 + d.cap ≤ 2 ^ w ∧
      pCostSign2 + d.cap ≤ 2 ^ w ∧ pCostPtr2 + d.cap ≤ 2 ^ w ∧
      pCostLen2 + d.cap ≤ 2 ^ w ∧ pOrigIdx2 + d.cap ≤ 2 ^ w ∧ d.cap < 2 ^ w ∧ d.L < 2 ^ w ∧ d.I.n < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) *
    Assn.list pCostBuf2 (cl.flatten ++ List.replicate (d.bufCap - cl.flatten.length) 0) *
    Assn.list pTail2 ((fwd.map (fun e => (d.I.edge e).tail) ++ ys.map (fun e => (d.I.edge e).head)) ++
      List.replicate (d.cap - (fwd.length + ys.length)) 0) *
    Assn.list pHead2 ((fwd.map (fun e => (d.I.edge e).head) ++ ys.map (fun e => (d.I.edge e).tail)) ++
      List.replicate (d.cap - (fwd.length + ys.length)) 0) *
    Assn.list pCapPtr2 ((fwd.map (fun e => d.pCapBuf2 + e.val * d.L) ++ ys.map (fun e => pFeasFlow + e.val * d.L)) ++
      List.replicate (d.cap - (fwd.length + ys.length)) 0) *
    Assn.list pCapLen2 ((fwd.map (fun e =>
        (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
      ys.map (fun e => (Nat.digits (2 ^ k) (d.f e).toNat).length)) ++
      List.replicate (d.cap - (fwd.length + ys.length)) 0) *
    Assn.list pCostSign2 ((fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
      ys.map (fun e => if -(d.I.edge e).cost < 0 then 1 else 0)) ++
      List.replicate (d.cap - (fwd.length + ys.length)) 0) *
    Assn.list pCostPtr2 (List.ofFn (fun t : Fin (fwd.length + ys.length) =>
      pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
      List.replicate (d.cap - (fwd.length + ys.length)) 0) *
    Assn.list pCostLen2 ((fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
      ys.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length)) ++
      List.replicate (d.cap - (fwd.length + ys.length)) 0) *
    Assn.list pOrigIdx2 ((fwd.map Fin.val ++ ys.map Fin.val) ++
      List.replicate (d.cap - (fwd.length + ys.length)) 0) *
    (pCOffOut ↦ d.cOffCell)
  post := fun d args res => ⨆ (pEdges : ℕ) (pFeasFlow : ℕ) (pCostBuf2 : ℕ)
      (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let fwdCL := edgeCostLimbList d.I fwd
    let ys0 := resRevPos d.I d.f d.i
    let cl0 := fwdCL ++ edgeCostLimbList d.I ys0
    let ys1 := resRevPos d.I d.f (d.i + 1)
    let cl1 := fwdCL ++ edgeCostLimbList d.I ys1
    ⌜args = [pEdges, d.i * 11, pFeasFlow, d.i * d.L, pCostBuf2, cl0.flatten.length, d.L, d.i,
        fwd.length + ys0.length,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut] ∧
      res = fwd.length + ys1.length⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) *
    Assn.list pCostBuf2 (cl1.flatten ++ List.replicate (d.bufCap - cl1.flatten.length) 0) *
    Assn.list pTail2 ((fwd.map (fun e => (d.I.edge e).tail) ++ ys1.map (fun e => (d.I.edge e).head)) ++
      List.replicate (d.cap - (fwd.length + ys1.length)) 0) *
    Assn.list pHead2 ((fwd.map (fun e => (d.I.edge e).head) ++ ys1.map (fun e => (d.I.edge e).tail)) ++
      List.replicate (d.cap - (fwd.length + ys1.length)) 0) *
    Assn.list pCapPtr2 ((fwd.map (fun e => d.pCapBuf2 + e.val * d.L) ++ ys1.map (fun e => pFeasFlow + e.val * d.L)) ++
      List.replicate (d.cap - (fwd.length + ys1.length)) 0) *
    Assn.list pCapLen2 ((fwd.map (fun e =>
        (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
      ys1.map (fun e => (Nat.digits (2 ^ k) (d.f e).toNat).length)) ++
      List.replicate (d.cap - (fwd.length + ys1.length)) 0) *
    Assn.list pCostSign2 ((fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
      ys1.map (fun e => if -(d.I.edge e).cost < 0 then 1 else 0)) ++
      List.replicate (d.cap - (fwd.length + ys1.length)) 0) *
    Assn.list pCostPtr2 (List.ofFn (fun t : Fin (fwd.length + ys1.length) =>
      pCostBuf2 + ((cl1.take t.val).map List.length).sum) ++
      List.replicate (d.cap - (fwd.length + ys1.length)) 0) *
    Assn.list pCostLen2 ((fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
      ys1.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length)) ++
      List.replicate (d.cap - (fwd.length + ys1.length)) 0) *
    Assn.list pOrigIdx2 ((fwd.map Fin.val ++ ys1.map Fin.val) ++
      List.replicate (d.cap - (fwd.length + ys1.length)) 0) *
    (pCOffOut ↦ cl1.flatten.length)

theorem stage0ResRevStep_meets {w : ℕ} {p : Program} {f cLen revEmit : ℕ}
    {Tcan Tre : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResRevStep cLen revEmit))
    (hcan : Meets w p cLen (canonLenSpec.withCost fun x _ => Tcan x.2.length))
    (hre : Meets w p revEmit ((stage0ResRevEmitSpec w).withCost fun x _ =>
      Tre (narrowMaxCostLimbs x.I))) :
    Meets w p f ((stage0ResRevStepSpec w).withCost fun d _ =>
      Tcan d.L + Tre (narrowMaxCostLimbs d.I) + 70) := by
  sep_enter d with hL1 h2mcap h2totBuf hfDig hpE h11m hpFF hmL
    hpCoB hbufW hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOI hcapW hLW hnW
  set k := narrowLimbWidth d.I
  set e0 : Fin d.I.m := ⟨d.i, d.hi⟩
  set fwd := resFwdPos d.I d.hv d.f d.I.m
  set fwdCL := edgeCostLimbList d.I fwd
  set ys := resRevPos d.I d.f d.i
  set cl := fwdCL ++ edgeCostLimbList d.I ys
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hb2k : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  have hw11 : 11 < 2 ^ w := by have := d.hi; omega
  have hfwd_le : fwd.length ≤ d.I.m := resFwdPos_length_le d.I d.hv d.f d.I.m
  have hfwdCL_le : fwdCL.flatten.length ≤ totCostLimbs d.I :=
    edgeCostLimbList_flatten_len_le d.I fwd (resFwdPos_nodup d.I d.hv d.f d.I.m)
  have hys_le : ys.length ≤ d.i := resRevPos_length_le d.I d.f d.i
  have hys_cap : fwd.length + ys.length < d.cap := by have := d.hi; omega
  have hmem : d.i ∈ Finset.range d.I.m := Finset.mem_range.mpr d.hi
  have hiL_lt : d.i * d.L < d.I.m * d.L := Nat.mul_lt_mul_of_pos_right d.hi (by omega)
  have hcpW : pFeasFlow + d.i * d.L < 2 ^ w := by omega
  have hspFF : (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) =
      Assn.list (pFeasFlow + d.i * d.L) (padLimbs (Nat.digits (2 ^ k) (d.f e0).toNat) d.L) *
      (∏ e ∈ (Finset.range d.I.m).erase d.i,
        Assn.list (pFeasFlow + e * d.L)
          (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) := by
    rw [← Finset.mul_prod_erase _ _ hmem, dite_eq_left d.hi]
  generalize hF_arr :
    (Assn.list pTail2 ((fwd.map (fun e => (d.I.edge e).tail) ++ ys.map (fun e => (d.I.edge e).head)) ++
       List.replicate (d.cap - (fwd.length + ys.length)) 0) *
     Assn.list pHead2 ((fwd.map (fun e => (d.I.edge e).head) ++ ys.map (fun e => (d.I.edge e).tail)) ++
       List.replicate (d.cap - (fwd.length + ys.length)) 0) *
     Assn.list pCapPtr2 ((fwd.map (fun e => d.pCapBuf2 + e.val * d.L) ++ ys.map (fun e => pFeasFlow + e.val * d.L)) ++
       List.replicate (d.cap - (fwd.length + ys.length)) 0) *
     Assn.list pCapLen2 ((fwd.map (fun e =>
         (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
       ys.map (fun e => (Nat.digits (2 ^ k) (d.f e).toNat).length)) ++
       List.replicate (d.cap - (fwd.length + ys.length)) 0) *
     Assn.list pCostSign2 ((fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
       ys.map (fun e => if -(d.I.edge e).cost < 0 then 1 else 0)) ++
       List.replicate (d.cap - (fwd.length + ys.length)) 0) *
     Assn.list pCostPtr2 (List.ofFn (fun t : Fin (fwd.length + ys.length) =>
       pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
       List.replicate (d.cap - (fwd.length + ys.length)) 0) *
     Assn.list pCostLen2 ((fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
       ys.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length)) ++
       List.replicate (d.cap - (fwd.length + ys.length)) 0) *
     Assn.list pOrigIdx2 ((fwd.map Fin.val ++ ys.map Fin.val) ++
       List.replicate (d.cap - (fwd.length + ys.length)) 0)) = F_arr
  generalize hF_aux :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ e ∈ Finset.range d.I.m,
       Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])) *
     Assn.list pCostBuf2 (cl.flatten ++ List.replicate (d.bufCap - cl.flatten.length) 0) *
     (pCOffOut ↦ d.cOffCell)) = F_aux
  sep_apply hF_arr; sep_apply hF_aux
  sep_apply hspFF
  have hlen_f : (padLimbs (Nat.digits (2 ^ k) (d.f e0).toNat) d.L).length = d.L := by
    simp only [padLimbs, List.length_append, List.length_replicate]; have := hfDig e0; omega
  have hlim_f : Limbs k (padLimbs (Nat.digits (2 ^ k) (d.f e0).toNat) d.L) :=
    limbs_padLimbs (digits_limbs hk1 _) d.L
  have hof_f : Nat.ofDigits (2 ^ k) (padLimbs (Nat.digits (2 ^ k) (d.f e0).toNat) d.L) = (d.f e0).toNat := by
    rw [ofDigits_padLimbs, Nat.ofDigits_digits]
  sep_step from (k, padLimbs (Nat.digits (2 ^ k) (d.f e0).toNat) d.L)
  sep_apply hspFF.symm
  have hsucc := resRevPos_succ d.I d.f d.hi
  sep_step
  · have hpos : 0 < (d.f e0).toNat := by
      rw [hcapLen, hof_f] at hcond
      by_contra h0
      have heq0 : (d.f e0).toNat = 0 := by omega
      rw [heq0] at hcond; simp at hcond
    have hsucc' : resRevPos d.I d.f (d.i + 1) = ys ++ [e0] := by
      rw [hsucc, ite_eq_left hpos]
    have hcl_next : fwdCL ++ edgeCostLimbList d.I (resRevPos d.I d.f (d.i + 1)) =
        cl ++ [Nat.digits (2 ^ k) (d.I.edge e0).cost.natAbs] := by
      rw [hsucc']; simp [edgeCostLimbList, cl, k, List.append_assoc]
    have hflat_next : (fwdCL ++ edgeCostLimbList d.I (resRevPos d.I d.f (d.i + 1))).flatten =
        cl.flatten ++ Nat.digits (2 ^ k) (d.I.edge e0).cost.natAbs := by
      simp only [hcl_next, List.flatten_append, List.flatten_singleton]
    have hflat_le : (fwdCL ++ edgeCostLimbList d.I (resRevPos d.I d.f (d.i + 1))).flatten.length ≤ d.bufCap := by
      rw [List.flatten_append, List.length_append]
      have hys1 := edgeCostLimbList_flatten_len_le d.I _ (resRevPos_nodup d.I d.f (d.i + 1))
      omega
    have hfitC_cur : cl.flatten.length + (Nat.digits (2 ^ k) (d.I.edge e0).cost.natAbs).length ≤ d.bufCap := by
      rw [hflat_next, List.length_append] at hflat_le; exact hflat_le
    subst F_aux F_arr; sep_norm
    generalize hF_ff :
      ((∏ e ∈ Finset.range d.I.m,
          Assn.list (pFeasFlow + e * d.L)
            (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) *
       (pCOffOut ↦ d.cOffCell)) = F_ff
    sep_apply hF_ff
    have hcapLen_eq : capLen = (Nat.digits (2 ^ k) (d.f e0).toNat).length := by
      rw [hcapLen, hof_f]
    have hcapLen_lt : capLen < 2 ^ w := by
      rw [hcapLen_eq]; exact lt_of_le_of_lt (hfDig e0) hLW
    have hlen_m : ∀ (f g : Fin d.I.m → ℕ),
        ((fwd.map f ++ ys.map g) ++ List.replicate (d.cap - (fwd.length + ys.length)) 0).length = d.cap := by
      intro f g; simp only [List.length_append, List.length_map, List.length_replicate]; omega
    have hlen_cp : (List.ofFn (fun t : Fin (fwd.length + ys.length) =>
        pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
        List.replicate (d.cap - (fwd.length + ys.length)) 0).length = d.cap := by
      simp only [List.length_append, List.length_ofFn, List.length_replicate]; omega
    have hArcOk : ResArcEmitOk w
        ⟨d.I, d.hv, e0, pFeasFlow + d.i * d.L, capLen, cl.flatten, d.bufCap, d.cap, fwd.length + ys.length,
          (fwd.map (fun e => (d.I.edge e).tail) ++ ys.map (fun e => (d.I.edge e).head)) ++
            List.replicate (d.cap - (fwd.length + ys.length)) 0,
          (fwd.map (fun e => (d.I.edge e).head) ++ ys.map (fun e => (d.I.edge e).tail)) ++
            List.replicate (d.cap - (fwd.length + ys.length)) 0,
          (fwd.map (fun e => d.pCapBuf2 + e.val * d.L) ++ ys.map (fun e => pFeasFlow + e.val * d.L)) ++
            List.replicate (d.cap - (fwd.length + ys.length)) 0,
          (fwd.map (fun e =>
              (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
            ys.map (fun e => (Nat.digits (2 ^ k) (d.f e).toNat).length)) ++
            List.replicate (d.cap - (fwd.length + ys.length)) 0,
          (fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
            ys.map (fun e => if -(d.I.edge e).cost < 0 then 1 else 0)) ++
            List.replicate (d.cap - (fwd.length + ys.length)) 0,
          List.ofFn (fun t : Fin (fwd.length + ys.length) =>
            pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
            List.replicate (d.cap - (fwd.length + ys.length)) 0,
          (fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
            ys.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length)) ++
            List.replicate (d.cap - (fwd.length + ys.length)) 0,
          (fwd.map Fin.val ++ ys.map Fin.val) ++
            List.replicate (d.cap - (fwd.length + ys.length)) 0⟩
        pEdges pCostBuf2 pTail2 pHead2 pCapPtr2 pCapLen2 pCostSign2 pCostPtr2 pCostLen2 pOrigIdx2 :=
      ⟨hpE, h11m, hfitC_cur, hpCoB, hbufW, hys_cap, hcapW, hnW, hcpW, hcapLen_lt,
        hlen_m _ _, hlen_m _ _, hlen_m _ _, hlen_m _ _, hlen_m _ _, hlen_cp, hlen_m _ _, hlen_m _ _,
        hpT, hpH, hpCP, hpCL, hpCS, hpCoP, hpCoL, hpOI⟩
    clear hlen_m hlen_cp
    sep_step from (⟨d.I, d.hv, e0, pFeasFlow + d.i * d.L, capLen, cl.flatten, d.bufCap, d.cap, fwd.length + ys.length,
        (fwd.map (fun e => (d.I.edge e).tail) ++ ys.map (fun e => (d.I.edge e).head)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0,
        (fwd.map (fun e => (d.I.edge e).head) ++ ys.map (fun e => (d.I.edge e).tail)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0,
        (fwd.map (fun e => d.pCapBuf2 + e.val * d.L) ++ ys.map (fun e => pFeasFlow + e.val * d.L)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0,
        (fwd.map (fun e =>
            (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
          ys.map (fun e => (Nat.digits (2 ^ k) (d.f e).toNat).length)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0,
        (fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
          ys.map (fun e => if -(d.I.edge e).cost < 0 then 1 else 0)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0,
        List.ofFn (fun t : Fin (fwd.length + ys.length) =>
          pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0,
        (fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
          ys.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0,
        (fwd.map Fin.val ++ ys.map Fin.val) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0⟩ : ResArcEmitData)
    clear hArcOk
    rw [hcapLen_eq]
    subst F_ff; sep_norm
    rw [resRev_set_map fwd ys _ _ e0 d.cap hys_cap,
        resRev_set_map fwd ys _ _ e0 d.cap hys_cap,
        resRev_set_map fwd ys _ _ e0 d.cap hys_cap,
        resRev_set_map fwd ys _ _ e0 d.cap hys_cap,
        resRev_set_map fwd ys _ _ e0 d.cap hys_cap,
        resRev_set_map fwd ys _ _ e0 d.cap hys_cap,
        resRev_set_map fwd ys _ _ e0 d.cap hys_cap,
        resRev_set_costPtrs d.I d.hv d.f pCostBuf2 d.cap d.i d.hi hpos hys_cap,
        ← hsucc', ← hflat_next]
    have hc_lt : cl.flatten.length + cLenE < 2 ^ w := by
      rw [hcLenE]; dsimp only [k] at hfitC_cur; omega
    sep_step
    have hcoff_eq : cl.flatten.length + cLenE =
        (fwdCL ++ edgeCostLimbList d.I (resRevPos d.I d.f (d.i + 1))).flatten.length := by
      rw [hcLenE, hflat_next, List.length_append]
    have hcoff_eq2 : cl.flatten.length + (Nat.digits (2 ^ k) (d.I.edge e0).cost.natAbs).length =
        (fwdCL ++ edgeCostLimbList d.I (resRevPos d.I d.f (d.i + 1))).flatten.length := by
      rw [hflat_next, List.length_append]
    rw [hcoff_eq, hcoff_eq2]
    sep_step
    · rw [hlen_f]; omega
    · rw [hsucc']; simp [fwd]; omega
  · have hzero : ¬ (0 < (d.f e0).toNat) := by
      rw [hcapLen, hof_f] at hcond
      intro hpos
      have hne0 : (d.f e0).toNat ≠ 0 := by omega
      have hlen_pos : 0 < (Nat.digits (2 ^ k) (d.f e0).toNat).length := by
        rw [Nat.length_digits _ _ hb2k hne0]; omega
      omega
    have hsucc' : resRevPos d.I d.f (d.i + 1) = ys := by
      rw [hsucc, ite_eq_right hzero, List.append_nil]
    subst F_aux F_arr; sep_norm
    sep_step
    have hcl_next : cl = fwdCL ++ edgeCostLimbList d.I (resRevPos d.I d.f (d.i + 1)) := by
      rw [hsucc']
    rw [hcl_next, ← hsucc']
    sep_step
    · rw [hlen_f]; omega
    · rw [hsucc']
    · rw [hsucc']

/-! ### `stage0ResPassRev`: build reverse residual arcs -/

wram_def stage0ResPassRev (revStep : ℕ)
    (pEdges, m, pFeasFlow, pCostBuf2, L,
     pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, j0, pCOffOut) {
  j := j0
  cOff := mem[pCOffOut]
  eOff := 0
  fOff := 0
  for i in 0 .. m {
    j := revStep(pEdges, eOff, pFeasFlow, fOff, pCostBuf2, cOff, L, i, j,
      pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut)
    cOff := mem[pCOffOut]
    eOff := eOff + 11
    fOff := fOff + L
  }
  return j
}

structure ResPassRevData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  cap : ℕ
  bufCap : ℕ
  pCapBuf2 : ℕ

def stage0ResPassRevSpec (w : ℕ) : Spec ResPassRevData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pFeasFlow : ℕ) (pCostBuf2 : ℕ)
      (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let fwdCL := edgeCostLimbList d.I fwd
    ⌜args = [pEdges, d.I.m, pFeasFlow, pCostBuf2, d.L,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2,
        fwd.length, pCOffOut] ∧
      1 ≤ d.L ∧ 2 * d.I.m ≤ d.cap ∧ 2 * totCostLimbs d.I ≤ d.bufCap ∧
      (∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (d.f e).toNat).length ≤ d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pCostBuf2 + d.bufCap < 2 ^ w ∧ d.bufCap < 2 ^ w ∧
      pTail2 + d.cap ≤ 2 ^ w ∧ pHead2 + d.cap ≤ 2 ^ w ∧
      pCapPtr2 + d.cap ≤ 2 ^ w ∧ pCapLen2 + d.cap ≤ 2 ^ w ∧
      pCostSign2 + d.cap ≤ 2 ^ w ∧ pCostPtr2 + d.cap ≤ 2 ^ w ∧
      pCostLen2 + d.cap ≤ 2 ^ w ∧ pOrigIdx2 + d.cap ≤ 2 ^ w ∧ d.cap < 2 ^ w ∧ d.L < 2 ^ w ∧ d.I.n < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    Assn.list pCostBuf2 (fwdCL.flatten ++ List.replicate (d.bufCap - fwdCL.flatten.length) 0) *
    Assn.list pTail2 (fwd.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - fwd.length) 0) *
    Assn.list pHead2 (fwd.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCapPtr2 (fwd.map (fun e => d.pCapBuf2 + e.val * d.L) ++ List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCapLen2 (fwd.map (fun e =>
      (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
      List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCostSign2 (fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
      List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCostPtr2 (List.ofFn (fun t : Fin fwd.length =>
      pCostBuf2 + ((fwdCL.take t.val).map List.length).sum) ++ List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCostLen2 (fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
      List.replicate (d.cap - fwd.length) 0) *
    Assn.list pOrigIdx2 (fwd.map Fin.val ++ List.replicate (d.cap - fwd.length) 0) *
    (pCOffOut ↦ fwdCL.flatten.length)
  post := fun d args res => ⨆ (pEdges : ℕ) (pFeasFlow : ℕ) (pCostBuf2 : ℕ)
      (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let rev := resRevPos d.I d.f d.I.m
    let allCL := edgeCostLimbList d.I fwd ++ edgeCostLimbList d.I rev
    ⌜args = [pEdges, d.I.m, pFeasFlow, pCostBuf2, d.L,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2,
        fwd.length, pCOffOut] ∧
      res = fwd.length + rev.length⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    Assn.list pCostBuf2 (allCL.flatten ++ List.replicate (d.bufCap - allCL.flatten.length) 0) *
    Assn.list pTail2 ((fwd.map (fun e => (d.I.edge e).tail) ++ rev.map (fun e => (d.I.edge e).head)) ++
      List.replicate (d.cap - (fwd.length + rev.length)) 0) *
    Assn.list pHead2 ((fwd.map (fun e => (d.I.edge e).head) ++ rev.map (fun e => (d.I.edge e).tail)) ++
      List.replicate (d.cap - (fwd.length + rev.length)) 0) *
    Assn.list pCapPtr2 ((fwd.map (fun e => d.pCapBuf2 + e.val * d.L) ++ rev.map (fun e => pFeasFlow + e.val * d.L)) ++
      List.replicate (d.cap - (fwd.length + rev.length)) 0) *
    Assn.list pCapLen2 ((fwd.map (fun e =>
        (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
      rev.map (fun e => (Nat.digits (2 ^ k) (d.f e).toNat).length)) ++
      List.replicate (d.cap - (fwd.length + rev.length)) 0) *
    Assn.list pCostSign2 ((fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
      rev.map (fun e => if -(d.I.edge e).cost < 0 then 1 else 0)) ++
      List.replicate (d.cap - (fwd.length + rev.length)) 0) *
    Assn.list pCostPtr2 (List.ofFn (fun t : Fin (fwd.length + rev.length) =>
      pCostBuf2 + ((allCL.take t.val).map List.length).sum) ++
      List.replicate (d.cap - (fwd.length + rev.length)) 0) *
    Assn.list pCostLen2 ((fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
      rev.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length)) ++
      List.replicate (d.cap - (fwd.length + rev.length)) 0) *
    Assn.list pOrigIdx2 ((fwd.map Fin.val ++ rev.map Fin.val) ++
      List.replicate (d.cap - (fwd.length + rev.length)) 0) *
    (pCOffOut ↦ allCL.flatten.length)

theorem stage0ResPassRev_meets {w : ℕ} {p : Program} {f revStep : ℕ}
    {Tstep : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResPassRev revStep))
    (hstep : Meets w p revStep ((stage0ResRevStepSpec w).withCost fun x _ =>
      Tstep (narrowMaxCostLimbs x.I) x.L)) :
    Meets w p f ((stage0ResPassRevSpec w).withCost fun d _ =>
      (Tstep (narrowMaxCostLimbs d.I) d.L + 65) * d.I.m + 50) := by
  sep_enter d with hL1 h2mcap h2totBuf hfDig hpE h11m hpFF hmL
    hpCoB hbufW hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOI hcapW hLW hnW
  set k := narrowLimbWidth d.I
  set fwd := resFwdPos d.I d.hv d.f d.I.m
  set fwdCL := edgeCostLimbList d.I fwd
  sep_step; sep_step; sep_step; sep_step
  subst j cOff
  have hrev0 : resRevPos d.I d.f 0 = [] := rfl
  sep_for (fun i =>
      let ys := resRevPos d.I d.f i
      let cl := fwdCL ++ edgeCostLimbList d.I ys
      ⟨[pEdges, d.I.m, pFeasFlow, pCostBuf2, d.L,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2,
        fwd.length, pCOffOut,
        fwd.length + ys.length, cl.flatten.length, i * 11, i * d.L, i],
       i ≤ d.I.m,
       (Tstep (narrowMaxCostLimbs d.I) d.L + 50) * (d.I.m - i) + 20,
       [Assn.list 0 (narrowEncode d.I),
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])),
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pFeasFlow + e * d.L)
            (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])),
        Assn.list pCostBuf2 (cl.flatten ++ List.replicate (d.bufCap - cl.flatten.length) 0),
        Assn.list pTail2 ((fwd.map (fun e => (d.I.edge e).tail) ++ ys.map (fun e => (d.I.edge e).head)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0),
        Assn.list pHead2 ((fwd.map (fun e => (d.I.edge e).head) ++ ys.map (fun e => (d.I.edge e).tail)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0),
        Assn.list pCapPtr2 ((fwd.map (fun e => d.pCapBuf2 + e.val * d.L) ++ ys.map (fun e => pFeasFlow + e.val * d.L)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0),
        Assn.list pCapLen2 ((fwd.map (fun e =>
            (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
          ys.map (fun e => (Nat.digits (2 ^ k) (d.f e).toNat).length)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0),
        Assn.list pCostSign2 ((fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
          ys.map (fun e => if -(d.I.edge e).cost < 0 then 1 else 0)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0),
        Assn.list pCostPtr2 (List.ofFn (fun t : Fin (fwd.length + ys.length) =>
          pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0),
        Assn.list pCostLen2 ((fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
          ys.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length)) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0),
        Assn.list pOrigIdx2 ((fwd.map Fin.val ++ ys.map Fin.val) ++
          List.replicate (d.cap - (fwd.length + ys.length)) 0),
        (pCOffOut ↦ cl.flatten.length)]⟩)
  · have hi : i < d.I.m := hhi
    have hw11 : 11 < 2 ^ w := by omega
    have hnext11 : i * 11 + 11 = (i + 1) * 11 := by ring
    have hnextL : i * d.L + d.L = (i + 1) * d.L := by ring
    have hnextL_lt : (i + 1) * d.L ≤ d.I.m * d.L := Nat.mul_le_mul_right d.L (by omega)
    sep_step from (⟨d.I, d.hv, d.f, d.hf, d.L, d.cap, d.bufCap, d.pCapBuf2,
      (fwdCL ++ edgeCostLimbList d.I (resRevPos d.I d.f i)).flatten.length, i, hi⟩ : ResRevStepData)
    sep_step; sep_step; sep_step
  · sep_step
  all_goals simp only [hrev0, edgeCostLimbList, List.map_nil, List.append_nil, List.length_nil, add_zero, Fin.val_cast]
  · have hcr : (0 : ℤ) ≤ ↑((Tstep (narrowMaxCostLimbs d.I) d.L + 65) * d.I.m + 50) - 13 -
        ↑((d.I.m - 0) * 9 + 8) - ((↑(Tstep (narrowMaxCostLimbs d.I) d.L) + 50) * (↑d.I.m - ↑0) + 20) := by
      have hm0 : (0 : ℤ) ≤ (d.I.m : ℤ) := Nat.cast_nonneg _
      simp only [Nat.sub_zero, sub_zero]; push_cast; ring_nf; linarith only [hm0]
    exact le_trans (Assn.mul_le_mul_of_le (Assn.credits_le_gc hcr) le_rfl) (by rw [mul_comm])

/-! ### `stage0ResBuild`: combine Pass Fwd, Pass Rev, and `writeStage1Hdr` -/

wram_def stage0ResBuild (passFwd passRev writeHdr : ℕ)
    (pEdges, m, n, k, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, L,
     pIn2, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut) {
  m2Fwd := passFwd(pEdges, m, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, L, k,
    pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut)
  m2 := passRev(pEdges, m, pFeasFlow, pCostBuf2, L,
    pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, m2Fwd, pCOffOut)
  d := writeHdr(pIn2, n, m2, k, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2)
  mem[pCOffOut] := m2
  return m2Fwd
}

structure ResBuildData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  cOff0 : ℕ

def stage0ResBuildSpec (w : ℕ) : Spec ResBuildData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pCapBuf2 : ℕ)
      (pCostBuf2 : ℕ) (pIn2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let bufCap := 2 * totCostLimbs d.I
    let cap := 2 * d.I.m
    ⌜args = [pEdges, d.I.m, d.I.n, k, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, d.L,
        pIn2, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut] ∧
      1 ≤ d.L ∧ 2 * k + 1 ≤ w ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧
      pCapBuf2 + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pCostBuf2 + bufCap < 2 ^ w ∧ bufCap < 2 ^ w ∧ pIn2 + 10 ≤ 2 ^ w ∧
      pTail2 + cap ≤ 2 ^ w ∧ pHead2 + cap ≤ 2 ^ w ∧
      pCapPtr2 + cap ≤ 2 ^ w ∧ pCapLen2 + cap ≤ 2 ^ w ∧
      pCostSign2 + cap ≤ 2 ^ w ∧ pCostPtr2 + cap ≤ 2 ^ w ∧
      pCostLen2 + cap ≤ 2 ^ w ∧ pOrigIdx2 + cap ≤ 2 ^ w ∧ cap < 2 ^ w ∧ d.L < 2 ^ w ∧ d.I.n < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m, Assn.list (pCapBuf2 + i * d.L) (List.replicate d.L 0)) *
    Assn.list pCostBuf2 (List.replicate bufCap 0) *
    Assn.list pIn2 (List.replicate 10 0) *
    Assn.list pTail2 (List.replicate cap 0) *
    Assn.list pHead2 (List.replicate cap 0) *
    Assn.list pCapPtr2 (List.replicate cap 0) *
    Assn.list pCapLen2 (List.replicate cap 0) *
    Assn.list pCostSign2 (List.replicate cap 0) *
    Assn.list pCostPtr2 (List.replicate cap 0) *
    Assn.list pCostLen2 (List.replicate cap 0) *
    Assn.list pOrigIdx2 (List.replicate cap 0) *
    (pCOffOut ↦ d.cOff0)
  post := fun d args res => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pCapBuf2 : ℕ)
      (pCostBuf2 : ℕ) (pIn2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let rev := resRevPos d.I d.f d.I.m
    ⌜args = [pEdges, d.I.m, d.I.n, k, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, d.L,
        pIn2, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut] ∧
      res = fwd.length⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pCapBuf2 + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k)
            (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩ : ℤ) - d.f ⟨i, hlt⟩).toNat) d.L
        else [])) *
    Assn.list pIn2 [R'.n, R'.m, k, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2] *
    Assn.list pTail2 (List.ofFn fun e : Fin R'.m => (R'.tail e).val) *
    Assn.list pHead2 (List.ofFn fun e : Fin R'.m => (R'.head e).val) *
    Assn.list pCapPtr2 (resCapPtrs d.I d.hv d.f pCapBuf2 pFeasFlow d.L) *
    Assn.list pCapLen2 ((resCapLimbs d.I d.hv d.f).map List.length) *
    Assn.list pCostSign2 (List.ofFn fun e : Fin R'.m => if R'.cost e < 0 then 1 else 0) *
    Assn.list pCostPtr2 (resCostPtrs d.I d.hv d.f pCostBuf2) *
    Assn.list pCostLen2 ((resCostLimbs d.I d.hv d.f).map List.length) *
    (∏ j ∈ Finset.range R'.m,
      Assn.list ((resCostPtrs d.I d.hv d.f pCostBuf2).getD j 0) ((resCostLimbs d.I d.hv d.f).getD j [])) *
    Assn.list pOrigIdx2 ((fwd.map Fin.val ++ rev.map Fin.val) ++ List.replicate (2 * d.I.m - R'.m) 0) *
    (pCOffOut ↦ R'.m) *
    Assn.gc

theorem stage0ResBuild_meets {w : ℕ} {p : Program} {f passFwd passRev writeHdr : ℕ}
    {Tfwd Trev : ResBuildData → ℕ} {Thdr : ℕ}
    (hp : p.procs[f]? = some (stage0ResBuild passFwd passRev writeHdr))
    (hfwd : Meets w p passFwd ((stage0ResPassFwdSpec w).withCost fun x _ =>
      Tfwd ⟨x.I, x.hv, x.f, x.hf, x.L, x.cOff0⟩))
    (hrev : Meets w p passRev ((stage0ResPassRevSpec w).withCost fun x _ =>
      Trev ⟨x.I, x.hv, x.f, x.hf, x.L, 0⟩))
    (hhdr : Meets w p writeHdr ((writeStage1HdrSpec w).withCost fun _ _ => Thdr)) :
    Meets w p f ((stage0ResBuildSpec w).withCost fun d _ =>
      Tfwd d + Trev ⟨d.I, d.hv, d.f, d.hf, d.L, 0⟩ + Thdr + 80) := by
  sep_enter d with hL1 h2k1 hcapDig hpE h11m hpSC hpFF hpCB2 hmL
    hpCoB hbufW hpIn2 hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOI hcapW hLW hnW
  set k := narrowLimbWidth d.I
  set R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
  set fwd := resFwdPos d.I d.hv d.f d.I.m
  set rev := resRevPos d.I d.f d.I.m
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hb2k : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  have hm_eq : R'.m = fwd.length + rev.length := res_m_eq d.I d.hv d.f
  have hn_eq : R'.n = d.I.n := rfl
  have hfDig : ∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (d.f e).toNat).length ≤ d.L := fun e => by
    have ⟨h0, hle⟩ := d.hf e
    exact le_trans (digits_length_mono hb2k (by omega : (d.f e).toNat ≤ (FlowReduction.shiftedGraph d.I d.hv).capacity e))
      (hcapDig e)
  sep_step from (⟨d.I, d.hv, d.f, d.hf, d.L, 2 * d.I.m, 2 * totCostLimbs d.I, d.cOff0⟩ : ResPassFwdData)
  generalize hF1 :
    ((∏ i ∈ Finset.range d.I.m,
        Assn.list (pShCapBuf + i * d.L)
          (if hlt : i < d.I.m then
            padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
          else [])) *
     (∏ i ∈ Finset.range d.I.m,
        Assn.list (pCapBuf2 + i * d.L)
          (if hlt : i < d.I.m then
            padLimbs (Nat.digits (2 ^ k)
              (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩ : ℤ) - d.f ⟨i, hlt⟩).toNat) d.L
          else [])) *
     Assn.list pIn2 (List.replicate 10 0)) = F1
  sep_apply hF1
  sep_step from (⟨d.I, d.hv, d.f, d.hf, d.L, 2 * d.I.m, 2 * totCostLimbs d.I, pCapBuf2⟩ : ResPassRevData)
  subst F1; sep_norm
  sep_step from (⟨d.I.n, fwd.length + rev.length, k, pTail2, pHead2, pCapPtr2, pCapLen2,
    pCostSign2, pCostPtr2, pCostLen2, List.replicate 10 0⟩ : WriteStage1HdrData)
  sep_step
  have hcl_eq : edgeCostLimbList d.I fwd ++ edgeCostLimbList d.I rev = resCostLimbs d.I d.hv d.f :=
    resCostLimbs_eq_two_pass d.I d.hv d.f
  have htail_eq := resTails_eq_two_pass d.I d.hv d.f
  have hhead_eq := resHeads_eq_two_pass d.I d.hv d.f
  have hcapL_eq := resCapLens_eq_two_pass d.I d.hv d.f
  have hcsign_eq := resCostSigns_eq_two_pass d.I d.hv d.f
  have hcapP_eq : fwd.map (fun e => pCapBuf2 + e.val * d.L) ++ rev.map (fun e => pFeasFlow + e.val * d.L) =
      resCapPtrs d.I d.hv d.f pCapBuf2 pFeasFlow d.L := rfl
  have hcostL_eq : fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
      rev.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) =
      (resCostLimbs d.I d.hv d.f).map List.length := by
    rw [← hcl_eq, List.map_append]; simp [edgeCostLimbList, k, Function.comp_def]
  have hcostP_eq : List.ofFn (fun t : Fin (fwd.length + rev.length) =>
      pCostBuf2 + (((edgeCostLimbList d.I fwd ++ edgeCostLimbList d.I rev).take t.val).map List.length).sum) =
      resCostPtrs d.I d.hv d.f pCostBuf2 := by
    apply List.ext_getElem
    · rw [List.length_ofFn, resCostPtrs_length, ← hm_eq]
    · intro j h1 h2
      simp only [List.getElem_ofFn, resCostPtrs, hcl_eq]
  rw [hcostP_eq, hcl_eq, htail_eq, hhead_eq, hcapP_eq, hcapL_eq, hcsign_eq, hcostL_eq, ← hm_eq, ← hn_eq]
  sep_apply res_split_costBuf d.I d.hv d.f pCostBuf2
  sep_apply Assn.list_append pTail2 _ _
  sep_apply Assn.list_append pHead2 _ _
  sep_apply Assn.list_append pCapPtr2 _ _
  sep_apply Assn.list_append pCapLen2 _ _
  sep_apply Assn.list_append pCostSign2 _ _
  sep_apply Assn.list_append pCostPtr2 _ _
  sep_apply Assn.list_append pCostLen2 _ _
  have hm2_eq : m2 = R'.m := by rw [hm2, hm_eq]
  rw [hm2_eq]
  sep_step

end MinCostFlow.NarrowProg
